open HolKernel Parse boolLib bossLib dep_rewrite BasicProvers;

open pairTheory optionTheory listTheory pred_setTheory finite_mapTheory;
open typeclassASTTheory mlmapTheory mlstringTheory
     typeclass_texpTheory typeclass_env_map_implTheory
     pure_varsTheory typeclass_typesTheory typeclass_typingTheory
     pure_miscTheory pure_configTheory;

val _ = new_theory "ast_to_cexp";

val _ = set_grammar_ancestry [
          "typeclassAST", "mlmap", "typeclass_texp",
          "typeclass_types","pure_vars","typeclass_typing",
          "typeclass_env_map_impl"]

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"

Definition build_tyinfo_def:
  build_tyinfo A [] = A ∧
  build_tyinfo A (d :: ds) =
  case d of
    declData opnm args cons =>
      build_tyinfo (insert A (implode opnm) (args, MAP (implode ## I) cons)) ds
        (* datatype name |-> [type construtor, the types of their arguments] *)
  | _ => build_tyinfo A ds
End


Definition compose_types_def:
  (compose_types t [] = t) ∧
  compose_types t (t'::ts) = compose_types (Cons t t') ts
End

(* nm_map maps type-operator names to their indices in the typing
   signature/map; the arg_map maps type variables (the vector vs after
   something like data Op vs = ...) into integers
 *)
Definition translate_type_def:
  translate_type nm_map arg_map (tyOp (INR s) tys) =
  (if s = "Fun" then
     do
       args <- OPT_MMAP (translate_type nm_map arg_map) tys;
       return $ compose_types (Atom $ CompPrimTy Function) args
     od
   else if s = "Bool" then do assert (tys = []); return $ Atom $ PrimTy Bool; od
   else if s = "Integer" then do assert (tys = []); return $ Atom $ PrimTy Integer od
   else if s = "String" then do assert (tys = []); return $ Atom $ PrimTy String od
   else if s = "IO" then do
                            t <- OPT_MMAP (translate_type nm_map arg_map) tys;
                            return $ compose_types (Atom $ CompPrimTy M) t;
                         od
   else if s = "Array" then do
                               t <- OPT_MMAP (translate_type nm_map arg_map) tys;
                               return $ compose_types (Atom $ CompPrimTy Array) t;
                            od
  else
     do
       opidx <- lookup nm_map (implode s);
       args <- OPT_MMAP (translate_type nm_map arg_map) tys;
       return $ compose_types (UserType opidx) args
     od) ∧
  translate_type nm_map arg_map (tyVarOp s tys) =
  do
    varidx <- lookup arg_map (implode s);
    args <- OPT_MMAP (translate_type nm_map arg_map) tys ;
    return $ compose_types (Atom $ VarTypeCons varidx) args
  od ∧
  translate_type nm_map arg_map (tyOp (INL n) tys) =
  do
    args <- OPT_MMAP (translate_type nm_map arg_map) tys;
    return $ compose_types (Atom $ CompPrimTy $ Tuple n) args;
  od
Termination
  WF_REL_TAC ‘measure (λ(_,_,ty). tyAST_size ty)’
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

Definition translate_predtype_def:
   translate_predtype nm_map arg_map (Predty preds ty) = do
     t <- (translate_type nm_map arg_map ty);
     preds' <- OPT_MMAP (λ(cl,t). do
          t' <- translate_type nm_map arg_map t;
          return (implode cl,t');
        od) preds;
     return $ PredType preds' t;
   od
End

Definition build_arg_map_def:
  (build_arg_map m (n:num) (tyOp _ ts) =
    FOLDL (λ(m',n') t. build_arg_map m' n' t) (m,n) ts) ∧
  (build_arg_map m n (tyVarOp v ts) =
    FOLDL (λ(m',n') t. build_arg_map m' n' t) (insert m (implode v) n,n + 1) ts)
Termination
  WF_REL_TAC ‘measure (λ(_,_,ty). tyAST_size ty)’
End

Definition translate_predtype_scheme_def:
  translate_predtype_scheme nm_map arg_map i (Predty preds ty) = do
    (arg_map,n) <<- build_arg_map arg_map i ty ;
    t <- translate_predtype nm_map arg_map (Predty preds ty) ;
    return (n,t)
  od
End

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

Definition translate_patcase_def:
  translate_patcase tyinfo pnm pat rhs = ARB
End

(*
Definition translate_patNest_def:
  translate_patNest (patTup pvs) =
  do
    vs <- OPT_MMAP translate_patNest pvs;
    return $ cepatCons «» vs
  od ∧
  translate_patNest (patApp s pvs) =
  do
    vs <- OPT_MMAP translate_patNest pvs ;
    return $ cepatCons (implode s) vs
  od ∧
  (* TODO: what should be done for int and string lit *)
  translate_patNest (patLit l) = SOME ARB ∧
  translate_patNest patUScore = SOME cepatUScore ∧
  translate_patNest (patVar s) = SOME $ cepatVar (implode s)
Termination
  WF_REL_TAC `measure patAST_size`
End
*)

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
  Induct >> simp[strip_comb_def, expAST_size_eq]
  >- (
    simp[expAST_size_def] >> rpt strip_tac >>
    rename [‘(I ## _) (strip_comb f) = (f0, es)’] >>
    Cases_on ‘strip_comb f’ >> gvs[] >>
    first_x_assum drule >> simp[]
  ) >>
  rw[strip_comb_def] >>
  last_x_assum drule >>
  rw[expAST_size_def] >>
  first_x_assum drule >> simp[]
QED

Overload If = “λg t e. typeclass_texp$NestedCase g «»
  (cepatCons «True» []) t
  [((cepatCons «False» []), e)]”

Definition dest_pvar_def[simp]:
  dest_pvar (patVar s) = SOME (implode s) ∧
  dest_pvar _ = NONE
End

Definition translate_headop_def:
  (translate_headop (typeclass_texp$Var ts s) =
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
       NONE =>
        if s = «seq»
        then SOME $ Prim Seq
        else SOME $ App (Var ts s)
     | SOME op => SOME $ Prim (AtomOp op)) ∧
  translate_headop e = SOME (App e)
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
  mkLam [] e = e ∧
  mkLam vs e = Lam (MAP (λv. (v,NONE)) vs) e
End

Overload Bind = “λa1 a2. typeclass_texp$Prim (Cons «Bind») [a1;a2]”

Definition case_then_map_def:
  case_then_map NONE f = SOME NONE ∧
  case_then_map (SOME x) f = do
    y <- f x ;
    return $ SOME y
  od
End

(*
Definition translate_args_def:
  translate_args nm_map args =
    OPT_MMAP (λ(pat,pty). do
      pat' <- dest_pvar pat ;
      pt' <- case_then_map pty $ translate_type nm_map empty ;
      return (pat',pt')
    od) args
End
*)

Definition translate_exp_def: (* translate_exp: translate exp to texp *)
  translate_exp nm_map tyinfo (expVar s) =
    SOME (typeclass_texp$Var [] $ implode s) ∧
  translate_exp nm_map tyinfo (expUserAnnot ty e) =
  do
    t <- translate_type nm_map empty ty;
    e' <- translate_exp nm_map tyinfo e;
    return $ UserAnnot t e'
  od ∧
  translate_exp nm_map tyinfo (expCon s es) =
  do
    rs <- OPT_MMAP (translate_exp nm_map tyinfo) es;
    SOME (Prim (Cons $ implode s) rs)
  od ∧
  translate_exp nm_map tyinfo (expOp op es) =
  do
    rs <- OPT_MMAP (translate_exp nm_map tyinfo) es;
    return (Prim (AtomOp op) rs)
  od ∧
  translate_exp nm_map tyinfo (expTup es) =
  do
    rs <- OPT_MMAP (translate_exp nm_map tyinfo) es;
    SOME (Prim (Cons «») rs)
  od ∧
  translate_exp nm_map tyinfo (expApp fe xe) =
  do
    (* TODO: Currently, when we strip_comb, we may remove the
    * type annotation *)
    (fe0, es) <<- strip_comb fe ;
    f <- translate_exp nm_map tyinfo fe0 ;
    lhs <- translate_headop f;
    args <- OPT_MMAP (translate_exp nm_map tyinfo) (es ++ [xe]) ;
    SOME (lhs args)
  od ∧
  (translate_exp nm_map tyinfo (expAbs p e) =
   case p of
     patVar n => do
                  body <- translate_exp nm_map tyinfo e ;
         (* TODO: currently, we cannot annotate the types of
          * the variables in lambda *)
                  SOME (Lam [(implode n,NONE)] body)
                od
   | _ => do
           ce <- translate_patcase tyinfo «» p e;
           SOME (Lam [(«»,NONE)] ce)
         od) ∧
  (translate_exp nm_map tyinfo (expIf g t e) =
   do
     gc <- translate_exp nm_map tyinfo g ;
     tc <- translate_exp nm_map tyinfo t ;
     ec <- translate_exp nm_map tyinfo e ;
     SOME (If gc tc ec)
   od) ∧
  (translate_exp nm_map tyinfo (expLit (litInt i)) =
   SOME (Prim (AtomOp $ Lit (Int i)) [])) ∧
  (translate_exp nm_map tyinfo (expLit (litString s)) =
   SOME (Prim (AtomOp $ Lit (Str s)) [])) ∧
  (translate_exp nm_map tyinfo (expLet ds body) =
   do
     recbinds <- translate_edecs nm_map tyinfo empty empty ds;
     bodyce <- translate_exp nm_map tyinfo body;
     SOME (typeclass_texp$Letrec recbinds bodyce)
   od) ∧
   (translate_exp nm_map tyinfo (expCase ge pats) =
   do
     assert (¬NULL pats);
     g <- translate_exp nm_map tyinfo ge;
     (pats',usopt) <<-
        case LAST pats of
          (patUScore, ue) => (FRONT pats, SOME ue)
        | _ => (pats, NONE) ;
     pes <- OPT_MMAP (λ(p_e,rhs_e). do
                                (conname, conargs) <- translate_pat p_e ;
                                rhs <- translate_exp nm_map tyinfo rhs_e ;
                                return (cepatCons conname (MAP cepatVar conargs),rhs)
                              od)
                     pats' ;
     cepats <- case usopt of
       |  NONE => return pes
       | SOME us_e => do e <- translate_exp nm_map tyinfo us_e ;
                      (* unused <- find_unused_siblings tyinfo (MAP FST pes) ; *)
                         return $ pes ++ [(cepatUScore,e)]
                      od ;
     (pat,e) <<- HD cepats;
     return $ typeclass_texp$NestedCase g «» pat e (TL cepats)
   od) ∧
  (translate_exp nm_map tyinfo (expDo dostmts finalexp) =
   (* see https://www.haskell.org/onlinereport/haskell2010/haskellch3.html
      section 3.14 *)
   case dostmts of
   | [] => translate_exp nm_map tyinfo finalexp
   | expdostmtExp ee :: reste =>
       do
         e <- translate_exp nm_map tyinfo ee;
         rest <- translate_exp nm_map tyinfo (expDo reste finalexp) ;
         return (Bind e $ Lam [«»,NONE] rest)
       od
   | expdostmtBind pe ee :: reste =>
       do
         case pe of
         | patVar n =>
             do
               e <- translate_exp nm_map tyinfo ee ;
               rest <- translate_exp nm_map tyinfo (expDo reste finalexp) ;
               return (Bind e $ Lam [implode n,NONE] rest)
             od
         | patUScore =>
             do
               e <- translate_exp nm_map tyinfo ee ;
               rest <- translate_exp nm_map tyinfo (expDo reste finalexp) ;
               return (Bind e $ Lam [«»,NONE] rest)
             od
         | _ => NONE (*
             do
               e <- translate_exp nm_map tyinfo ee ;
               rest <- translate_exp nm_map tyinfo (expDo reste finalexp) ;
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
         recbinds <- translate_edecs nm_map tyinfo empty empty decs ;
         rest <- translate_exp nm_map tyinfo (expDo reste finalexp);
         SOME (Letrec recbinds rest)
       od) ∧


  (* we use sigs to keep track of the function signatures,
  * and use funcs to keep track of the outermost-level function
  * names *)
  (translate_edecs nm_map tyinfo sigs funcs [] =
  do
    assert $ all (λname x. lookup funcs name ≠ NONE) sigs;
    return $ foldrWithKey (λname func binds.
        case lookup sigs name of
        | SOME t => ((name, SOME t), func) :: binds
        | NONE => ((name, NONE), func)::binds
      ) [] funcs;
  od) ∧
  (translate_edecs nm_map tyinfo sigs funcs (d::ds) =
   case d of
     expdecTysig name t =>
       do
         assert (lookup sigs (implode name) = NONE);
         t' <- translate_predtype_scheme nm_map empty 0 t;
         sigs' <<- insert sigs (implode name) t';
         translate_edecs nm_map tyinfo sigs' funcs ds;
       od
   | expdecPatbind (patVar s) e =>
       do
         assert (lookup funcs (implode s) = NONE);
         ce <- translate_exp nm_map tyinfo e ;
         funcs' <<- insert funcs (implode s) ce;
         translate_edecs nm_map tyinfo sigs funcs' ds;
       od
   | expdecPatbind _ _ => NONE
   | expdecFunbind s args body =>
       do
         assert (lookup funcs (implode s) = NONE);
         vs <- OPT_MMAP dest_pvar args;
         bce <- translate_exp nm_map tyinfo body ;
         funcs' <<- insert funcs (implode s) (mkLam vs bce) ;
         translate_edecs nm_map tyinfo sigs funcs' ds;
       od)
Termination
  WF_REL_TAC
  ‘measure (λs. case s of
                  INL (_,_, e) => typeclassAST$expAST_size e
                | INR (_,_,_,_, ds) => list_size expdecAST_size ds)’ >>
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
  translate_expl nm_map tyi [] = SOME [] ∧
  translate_expl nm_map tyi (h::t) =
  do
    e <- translate_exp nm_map tyi h ;
    es <- translate_expl nm_map tyi t ;
    return (e::es)
  od
End

Theorem OPT_MMAP_translate_exp[local]:
  OPT_MMAP (translate_exp nm tyi) = translate_expl nm tyi
Proof
  simp[FUN_EQ_THM] >> Induct >> simp[]
QED

Theorem translate_this_translate_exp =
        SRULE [SF ETA_ss, OPT_MMAP_translate_exp] translate_exp_def

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

Type sig_map_impl = ``:(mlstring, pred_type_scheme) map``;

Definition add_pred_def:
  add_pred p pt = pt with <| predicates := p::pt.predicates |>
End

Definition collect_type_vars_impl_def:
   (collect_type_vars_impl (Cons t1 t2) =
    union (collect_type_vars_impl t1)
      (collect_type_vars_impl t2)) ∧
  (collect_type_vars_impl (Atom $ VarTypeCons v) =
    insert (empty numOrd) v ()) /\
  (collect_type_vars_impl _ = empty numOrd)
End

Theorem map_ok_collect_type_vars_impl:
  map_ok (collect_type_vars_impl t) ∧
  cmp_of (collect_type_vars_impl t) = numOrd
Proof
  Induct_on `t` >>
  rw[] >>
  simp[Once $ oneline collect_type_vars_impl_def,union_thm] >>
  CASE_TAC >>
  simp[empty_thm,totoTheory.TO_numOrd,insert_thm]
QED

Theorem collect_type_vars_impl_thm:
  (lookup (collect_type_vars_impl t) v = SOME ()) ⇔
  v ∈ collect_type_vars t
Proof
  Induct_on `t` >>
  rw[] >>
  simp[Once $ oneline collect_type_vars_impl_def,
    Once $ oneline collect_type_vars_def]
  >- (
    CASE_TAC >>
    DEP_REWRITE_TAC[lookup_thm] >>
    simp[empty_thm,totoTheory.TO_numOrd,insert_thm,
      FLOOKUP_UPDATE]
  ) >>
  DEP_REWRITE_TAC[pure_varsTheory.lookup_union] >>
  simp[map_ok_collect_type_vars_impl] >>
  TOP_CASE_TAC >> gvs[]
QED

Theorem collect_type_vars_impl_NONE_thm:
  (lookup (collect_type_vars_impl t) v = NONE) ⇔
  v ∉ collect_type_vars t
Proof
  Cases_on `lookup (collect_type_vars_impl t) v` >>
  rw[] >>
  rpt strip_tac
  >- (drule $ iffRL collect_type_vars_impl_thm >> gvs[]) >>
  Cases_on `x` >>
  drule $ iffLR collect_type_vars_impl_thm >> gvs[]
QED

Definition no_pred_contains_def:
  no_pred_contains v pt =
    EVERY (λ(c,t). lookup (collect_type_vars_impl t) v = NONE)
      pt.predicates
End

Theorem no_pred_contains_thm:
  (no_pred_contains v pt) ⇔
  (∀c t. MEM (c,t) pt.predicates ⇒ v ∉ collect_type_vars t)
Proof
  rw[no_pred_contains_def,EVERY_MEM,EQ_IMP_THM]
  >- (res_tac >> fs[collect_type_vars_impl_NONE_thm]) >>
  pairarg_tac >> gvs[] >>
  res_tac >> gvs[collect_type_vars_impl_NONE_thm]
QED

(* sig_map contains all top level function signatures,
* meths contains signatures of the methods in the class, and
* impls contains default implmentations *)
(* NOTE: 0 in arg_map represents the class instance *)
(* We do not allow the class variable to be in the constraints of the
* method (see ConstrainedClassMethods in Haskell) *)
Definition extract_class_expdec_def:
  (extract_class_expdec nm_map arg_map tyinfo clname sig_map meths impls [] =
    SOME (sig_map,meths,impls)) ∧
  (extract_class_expdec nm_map arg_map tyinfo clname sig_map meths impls (expdecTysig s predty::decs) = do
      (* first check no other functions has used the same function name *)
      s <<- implode s;
      assert (mlmap$lookup sig_map s = NONE);
      (* 0 is reserved for the class variable *)
      (n,pred') <- translate_predtype_scheme nm_map arg_map 1 predty;
      (* we do not allow constraints on the class variable *)
      assert $ no_pred_contains 0 pred';
      meths' <<- insert meths s (n,pred');
      sig_map <<- insert sig_map s
        (n,add_pred (clname,Atom $ VarTypeCons 0) pred');
      extract_class_expdec nm_map arg_map tyinfo clname sig_map meths' impls decs;
    od) ∧
  (extract_class_expdec nm_map arg_map tyinfo clname sig_map meths impls (expdecFunbind s args exps::decs) = do
      s <<- implode s;
      assert (lookup sig_map s ≠ NONE);
      assert (mlmap$lookup impls s = NONE);
      vs <-  OPT_MMAP dest_pvar args;
      bce <- translate_exp nm_map tyinfo exps;
      impl <<- mkLam vs bce;
      impls' <<- insert impls s impl;
      extract_class_expdec nm_map arg_map tyinfo clname sig_map meths impls' decs;
    od) ∧
  (* rejects expdecPatbind *)
  extract_class_expdec nm_map arg_map tyinfo clname sig_map meths impls (_ :: decs) = NONE
End

Definition extract_inst_expdec_def:
  (extract_inst_expdec nm_map arg_map tyinfo impls [] = SOME impls) ∧
  (extract_inst_expdec nm_map arg_map tyinfo impls
    (expdecFunbind s args exps::ds) = do
      s <<- implode s;
      assert (mlmap$lookup impls s = NONE);
      vs <- OPT_MMAP dest_pvar args;
      bce <- translate_exp nm_map tyinfo exps;
      meth <<- mkLam vs bce;
      extract_inst_expdec nm_map arg_map tyinfo (insert impls s meth) ds;
    od) ∧
  (* raise error for both expdecTysig and expdecPatbind *)
  (extract_inst_expdec nm_map arg_map tyinfo impls (_::ds) = NONE)
End

Definition to_FuncDecl_def:
  to_FuncDecl sig_map func_map =
  do
    assert $ all (λname _ . lookup func_map name ≠ NONE) sig_map;
    MFOLDL (λ(name,func) m.
    do
      (_,sig) <- lookup sig_map name;
      return (insert m name $ FuncDecl sig func);
    od) (toAscList func_map) empty;
  od
End

Definition translate_tycons_def:
  translate_tycons nm_map (INL n) = SOME $ INR $ CompPrimT (Tuple n) ∧
  translate_tycons nm_map (INR s) =
  if s = "Fun" then SOME $ INR $ CompPrimT Function
  else if s = "Bool" then SOME $ INR $ PrimT Bool
  else if s = "Integer" then SOME $ INR $ PrimT Integer
  else if s = "String" then SOME $ INR $ PrimT String
  else if s = "IO" then SOME $ INR $ CompPrimT M
  else if s = "Array" then SOME $ INR $ CompPrimT Array
  else do
    opidx <- lookup nm_map (implode s);
    return $ INL opidx;
  od
End

(* passes over declarations;
   ignoring datatype declarations because they've already
   been extracted
 *)
Definition translate_decs_def:
  translate_decs nm_map tyinfo (sig_map:sig_map_impl)
    (cl_map:num class_map_impl)
    (inst_map:num inst_map_impl) func_map [] =
  do
    func_decl_map <- to_FuncDecl sig_map func_map;
    return (sig_map,cl_map,inst_map,func_decl_map)
  od ∧
  translate_decs nm_map tyinfo sig_map cl_map inst_map func_map
    (declTysig name t :: ds) =
  do
    t' <- translate_predtype_scheme nm_map empty 0 t;
    sig_map <<- insert sig_map (implode name) t';
    translate_decs nm_map tyinfo sig_map cl_map inst_map func_map ds
  od ∧
  translate_decs nm_map tyinfo sig_map cl_map inst_map func_map
    (declData _ _ _  :: ds) =
    translate_decs nm_map tyinfo sig_map cl_map inst_map func_map ds ∧
  translate_decs nm_map tyinfo sig_map cl_map inst_map func_map
    (declClass spcls cl v minimpl exps :: ds) =
  do
    minimpl <<- MAP (MAP implode) minimpl;
    assert $ EVERY ALL_DISTINCT minimpl;
    clname <<- implode cl;
    assert (lookup cl_map clname = NONE);
    (sig_map',msigs,defimpl) <- extract_class_expdec nm_map
      (insert empty (implode v) 0) tyinfo clname sig_map empty empty exps;
    assert $ EVERY (EVERY (λs. lookup msigs s ≠ NONE)) minimpl;
    cl_map' <<- insert cl_map clname (* mlstring *)
      <| supers := MAP implode spcls
       ; kind := NONE
       (* do kind inference after collection all the classinfos *)
       ; methodsig := msigs
       ; defaults := defimpl|>;
    translate_decs nm_map tyinfo sig_map' cl_map' inst_map func_map ds
  od ∧
  translate_decs nm_map tyinfo sig_map cl_map inst_map func_map
    (declInst constraints cl tc vs exps :: ds) =
  do
    assert $ ALL_DISTINCT vs;
    t <- translate_tycons nm_map tc ;
    arg_map <<- fromList str_compare
      (GENLIST (λn. (implode $ EL n vs,n)) $ LENGTH vs);
    impls <- extract_inst_expdec nm_map arg_map tyinfo empty exps;
    cstr' <- OPT_MMAP (λ(c,v). do
        v' <- lookup arg_map (implode v) ;
        return (implode c,v')
      od) constraints ;
    (* class <- FLOOKUP classinfo cl;
    (* check if every function inside are in the typeclass *)
    assert $ FEVERY (λ(s,_). s IN FDOM cl.methodsig) impls;
    (* check if it implements non-default methods *)
    assert $ FEVERY (λ(s,_). s IN FDOM cl.methodsig \/ s IN FDOM cl.defaults) impls;
    (* check if it satisfies minImpls *)
    assert $ EXISTS (EVERY (λ(s,_). s IN FDOM impls)) cl.minImp;
    (* check all the classes are in the classinfo *)
    assert $ set (map FST constraints) SUBSET (FDOM classinfos)
    (* check if all variables in the constraints are bound in the insttype *)
    assert $ set (map snd constraints) SUBSET (collect_type_vars t); *)
    inst_map' <- add_instance inst_map (implode cl) t (LENGTH vs)
      (<|cstr := cstr'; impls := impls|>);
    translate_decs nm_map tyinfo sig_map cl_map inst_map' func_map ds
  od ∧
  translate_decs nm_map tyinfo sig_map cl_map inst_map func_map
    (declFunbind s args body :: ds) =
  do
    vs <- OPT_MMAP dest_pvar args;
    bce <- translate_exp nm_map tyinfo body ;
    func_map' <<- insert func_map (implode s) (mkLam vs bce);
    translate_decs nm_map tyinfo sig_map cl_map inst_map func_map' ds
  od ∧
  translate_decs nm_map tyinfo sig_map cl_map inst_map func_map
    (declPatbind p e :: ds) =
  do
    v <- dest_pvar p ;
    ce <- translate_exp nm_map tyinfo e ;
    func_map' <<- insert func_map v ce;
    translate_decs nm_map tyinfo sig_map cl_map inst_map func_map' ds
  od
End

Definition listinfo_def:
  listinfo = (["a"], [(«[]», []);
    («::», [tyVarOp "a" []; tyOp (INR "[]") [tyVarOp "a" []]])])
End

Definition decls_to_tcdecl_def:
  decls_to_tcdecl ds =
  do
    tyinfo <<- build_tyinfo (empty str_compare) ds ;
    tyinfo_l <<- toAscList tyinfo ;
    (nm_map, nops) <<- FOLDL (λ(m,i) (opn, info). (insert m opn i, i + 1))
                             (insert (empty str_compare) «[]» 0n, 1)
                             tyinfo_l ;
    sig0 <- MFOLDL (build_tysig1 nm_map) tyinfo_l
      (MAP (LENGTH ## I) $ SND initial_namespace) ;
    (sig_map,cl_map,inst_map,func_map) <- translate_decs nm_map
      (insert tyinfo «[]» listinfo) empty empty init_inst_map empty ds ;
    SOME (func_map,sig_map,cl_map,inst_map)
  od
End

(********** closedness **********)

Definition cepat_vars_impl_def:
  cepat_vars_impl cepatUScore = empty ∧
  cepat_vars_impl (cepatVar v) = insert empty v () ∧
  cepat_vars_impl (cepatCons s ps) = cepat_vars_impl_l ps ∧

  cepat_vars_impl_l [] = empty ∧
  cepat_vars_impl_l (p::ps) = union (cepat_vars_impl p) (cepat_vars_impl_l ps)
End

Theorem cepat_vars_impl_ok:
  (∀pat. map_ok (cepat_vars_impl pat) ∧
    cmp_of (cepat_vars_impl pat) = var_cmp) ∧
  (!l. map_ok (cepat_vars_impl_l l) ∧
    cmp_of (cepat_vars_impl_l l) = var_cmp)
Proof
  ho_match_mp_tac pure_cexpTheory.cepat_induction >>
  rw[] >>
  gvs[cepat_vars_impl_def,insert_thm,union_thm]
QED

Theorem balanced_map_foldrWithKey_APPEND_toAscList:
  ∀l.
  balanced_map$foldrWithKey (λk x xs. (k,x)::xs) l t =
    toAscList t ++ l
Proof
  Induct_on `t`
  >- simp[balanced_mapTheory.toAscList_def,
      balanced_mapTheory.foldrWithKey_def] >>
  simp[balanced_mapTheory.foldrWithKey_def] >>
  rpt strip_tac >>
  irule EQ_TRANS >>
  irule_at (Pat `_ = toAscList (Bin _ _ _ _ _)`)
    $ GSYM balanced_mapTheory.toAscList_def >>
  simp[balanced_mapTheory.foldrWithKey_def]
QED

Theorem toAscList_alt:
  toAscList Tip = [] ∧
  toAscList (Bin v0 kx x l r) = toAscList l ++ [kx,x] ++ toAscList r
Proof
  simp[balanced_mapTheory.toAscList_def,
    balanced_mapTheory.foldrWithKey_def] >>
  Induct_on `l` >>
  simp[balanced_mapTheory.toAscList_def,
    balanced_mapTheory.foldrWithKey_def] >>
  gvs[balanced_map_foldrWithKey_APPEND_toAscList]
QED

Theorem balanced_map_foldrWithKey_FOLDR:
  ∀m f x. foldrWithKey f x (m: ('a,'b) balanced_map) =
    FOLDR (UNCURRY f) x (toAscList m)
Proof
  Induct_on `m` >>
  simp[balanced_mapTheory.foldrWithKey_def,toAscList_alt] >>
  simp[rich_listTheory.FOLDR_APPEND]
QED

Theorem foldrWithKey_list_delete:
  foldrWithKey (λk v x. delete x k) x m =
    list_delete x $ REVERSE $ MAP FST $ toAscList m
Proof
  Cases_on `m` >>
  simp[foldrWithKey_def,toAscList_def] >>
  simp[balanced_map_foldrWithKey_FOLDR,list_delete_def,
    rich_listTheory.FOLDL_REVERSE,rich_listTheory.FOLDR_MAP,
    LAMBDA_PROD]
QED

(* unused *)
Definition freevars_texp_impl_def:
  freevars_texp_impl (typeclass_texp$Var c v) = mlmap$insert empty v () ∧
  freevars_texp_impl (Prim op es) = freevars_texp_impl_l es ∧
  freevars_texp_impl (App e es) =
    union (freevars_texp_impl e) (freevars_texp_impl_l es) ∧
  freevars_texp_impl (Lam vs e) =
    list_delete (freevars_texp_impl e) (MAP FST vs) ∧
  freevars_texp_impl (Let (v,t) e1 e2) =
    union (freevars_texp_impl e1) (delete (freevars_texp_impl e2) v) ∧
  freevars_texp_impl (UserAnnot t e) = freevars_texp_impl e ∧
  freevars_texp_impl (PrimSeq t e1 e2) =
    union (freevars_texp_impl e1) (freevars_texp_impl e2) ∧
  freevars_texp_impl (Letrec fns e) = (
    let (fs, bodies) = UNZIP (MAP (λx. (FST $ FST x, SND x)) fns) in
    list_delete (union (freevars_texp_impl e) (freevars_texp_impl_l bodies)) fs) ∧

  freevars_texp_impl (NestedCase e v pat e1 rest) = (
    let pat_vars =
      freevars_texp_impl_pat_l ((pat,e1)::rest) in
    mlmap$union (freevars_texp_impl e) (delete pat_vars v)) ∧

  freevars_texp_impl_l [] = empty ∧
  freevars_texp_impl_l (e::es) =
    union (freevars_texp_impl e) (freevars_texp_impl_l es) ∧

  freevars_texp_impl_pat pat e1 =
    foldrWithKey (λk v x. delete x k) (freevars_texp_impl e1)
      (cepat_vars_impl pat) ∧

  freevars_texp_impl_pat_l [] = empty ∧
  freevars_texp_impl_pat_l ((pat,e1)::rest) =
    union (freevars_texp_impl_pat pat e1)
      (freevars_texp_impl_pat_l rest)
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λs. case s of
    | INL e => (texp_size (K 0) e,1n)
    | INR (INL l) => (list_size (texp_size (K 0)) l,1n)
    | INR (INR (INL pe)) => (texp4_size (K 0) pe,0n)
    | INR (INR (INR l)) => (texp3_size (K 0) l,0n))` >>
  conj_tac
  >- (
    rpt strip_tac >>
    Cases_on `v` >> rw[mlstring_size_def]
  ) >>
  ntac 1 gen_tac >>
  Induct >>
  rw[texp_size_def] >> gvs[list_size_def] >>
  Cases_on `UNZIP (MAP (λx. (FST (FST x), SND x)) fns)` >>
  PairCases_on `h` >> gvs[texp_size_def]
End

Triviality delete_cmp_of:
  cmp_of (delete m k) = cmp_of m
Proof
  Cases_on `m` >>
  simp[delete_def,cmp_of_def]
QED

Triviality FDOM_FLOOKUP_unit:
  FLOOKUP m x = SOME () <=> x IN FDOM m
Proof
  simp[miscTheory.FDOM_FLOOKUP]
QED

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

Triviality MAP_FST_toAscList_cepat_vars_impl:
  set (MAP FST (toAscList $ cepat_vars_impl pat)) =
    cepat_vars pat
Proof
  qspec_then `pat` assume_tac $ cj 1 cepat_vars_impl >>
  gvs[] >>
  drule MAP_FST_toAscList >>
  rw[]
QED

Theorem freevars_texp_impl:
  (∀(e:'a texp) s. freevars_texp_impl e = s ⇒
    map_ok s ∧ cmp_of s = var_cmp ∧
    FDOM (to_fmap s) = freevars_texp e) ∧
  (∀(es:'a texp list) s. freevars_texp_impl_l es = s ⇒
    map_ok s ∧ cmp_of s = var_cmp ∧
    FDOM (to_fmap s) = BIGUNION (set (MAP freevars_texp es))) ∧
  (∀pat (e:'a texp) s. freevars_texp_impl_pat pat e = s ⇒
    map_ok s ∧ cmp_of s = var_cmp ∧
    FDOM (to_fmap s) = freevars_texp e DIFF cepat_vars pat) ∧
  (∀(pes: (cepat # 'a texp) list) s.
    freevars_texp_impl_pat_l pes = s ⇒
    map_ok s ∧ cmp_of s = var_cmp ∧
    FDOM (to_fmap s) = BIGUNION (set
      (MAP (λ(p,e). freevars_texp e DIFF cepat_vars p) pes)))
Proof
  ho_match_mp_tac freevars_texp_impl_ind >>
  gvs[freevars_texp_impl_def,UNZIP_MAP, SF ETA_ss,
    foldrWithKey_list_delete,MAP_MAP_o] >>
  gvs[insert_thm, union_thm, delete_thm, list_delete_thm] >>
  gvs[pure_miscTheory.FDOM_FDIFF_alt] >>
  gvs[LAMBDA_PROD,combinTheory.o_DEF] >>
  simp[ELIM_UNCURRY,MAP_FST_toAscList_cepat_vars_impl]
QED

Definition contains_def:
  contains (s:var_set) v = (lookup s v = SOME ())
End

Definition closed_under_def:
  closed_under vs (typeclass_texp$Var ts v) = contains vs v ∧
  closed_under vs (UserAnnot t e) = closed_under vs e ∧
  closed_under vs (Prim op es) = EVERY (closed_under vs) es ∧
  closed_under vs (PrimSeq t e1 e2) =
    (closed_under vs e1 ∧ closed_under vs e2) ∧
  closed_under vs (App e es) = (closed_under vs e ∧ EVERY (closed_under vs) es) ∧
  closed_under vs (Lam xs e) = closed_under (list_insert_set vs (MAP FST xs)) e ∧
  closed_under vs (Let (x,t) e1 e2) =
    (closed_under vs e1 ∧ closed_under (insert vs x ()) e2) ∧
  closed_under vs (Letrec fns e) = (
    let (fs, bodies) = UNZIP (MAP (λx. (FST (FST x),SND x)) fns) in
    let vs' = list_insert_set vs fs in
    closed_under vs' e ∧ EVERY (closed_under vs') bodies) ∧

  closed_under vs (NestedCase g gv p e pes) = (
    closed_under vs g ∧
    let vs' = insert vs gv () in
    EVERY (λ(pat,e).
      closed_under (mlmap$union (cepat_vars_impl pat) vs') e) ((p,e)::pes))
Termination
  WF_REL_TAC `measure $ texp_size (K 0) o SND` >>
  gvs[UNZIP_MAP, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> conj_tac >>
  gen_tac >>
  Induct >> rw[] >> gvs[texp_size_def] >> res_tac >> simp[] >>
  first_x_assum $ qspecl_then [`p`,`gv`,`e`] assume_tac >> gvs[]
End

Theorem closed_under:
  ∀m e. map_ok m ∧ cmp_of m = var_cmp ⇒
  closed_under m e = (freevars_texp e ⊆ FDOM (to_fmap m))
Proof
  recInduct closed_under_ind >> rw[closed_under_def, contains_def] >>
  gvs[union_thm, lookup_thm, insert_thm, list_insert_set_thm, FDOM_FUPDATE_LIST] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, UNZIP_MAP] >>
  gvs[pure_miscTheory.DIFF_SUBSET, SUBSET_INSERT_DELETE] >>
  gvs[AC UNION_ASSOC UNION_COMM]
  >- gvs[FLOOKUP_DEF]
  >- (Induct_on `es` >> rw[])
  >- (AP_TERM_TAC >> Induct_on `es` >> rw[])
  >- metis_tac[]
  >- (
    AP_TERM_TAC >> rename1 `list_insert_set _ fs` >>
    Induct_on `fns` >> rw[] >> PairCases_on `h` >> gvs[]
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

Theorem texp_wf_strong_alt_def[compute]:
  (∀v0 v. texp_wf_strong (Var v0 v : 'a texp) ⇔ T) ∧
  (∀op es.
    texp_wf_strong (Prim op es : 'a texp) ⇔
    num_args_ok op (LENGTH es) ∧
    EVERY (λa. texp_wf_strong a) es ∧
    (case op of
     | AtomOp (Lit (Int i)) => T
     | AtomOp (Lit (Str s)) => T
     | AtomOp (Lit _) => F
     | AtomOp (Message m) => m ≠ ""
     | _ => T)) ∧
  (∀es e.
    texp_wf_strong (App e es : 'a texp) ⇔
    texp_wf_strong e ∧ EVERY (λa. texp_wf_strong a) es ∧
    ¬ NULL es) ∧
  (∀vs e. texp_wf_strong (Lam vs e : 'a texp) ⇔
    texp_wf_strong e ∧ ¬ NULL vs) ∧
  (∀sv e2 e1. texp_wf_strong (Let sv e1 e2 : 'a texp) ⇔
    texp_wf_strong e1 ∧ texp_wf_strong e2) ∧
  (∀fns e.
    texp_wf_strong (Letrec fns e : 'a texp) ⇔
    EVERY (λa. texp_wf_strong a) (MAP (λx. (SND x)) fns) ∧
    texp_wf_strong e ∧ ¬ NULL fns) ∧
  (∀pes p gv g e.
   texp_wf_strong (NestedCase g gv p e pes : 'a texp) ⇔
   texp_wf_strong g ∧ texp_wf_strong e ∧
   EVERY (λa. texp_wf_strong a) (MAP SND pes) ∧
   ¬MEM gv (FLAT (MAP (cepat_vars_l ∘ FST) ((p,e)::pes)))) ∧
  (∀t e2 e1. texp_wf_strong (PrimSeq t e1 e2 : 'a texp) ⇔
    texp_wf_strong e1 ∧ texp_wf_strong e2) ∧
  (∀t e. texp_wf_strong (UserAnnot t e : 'a texp) =
    texp_wf_strong e)
Proof
  rw[] >> simp[texp_wf_strong_def] >> gvs[NULL_EQ]
  >- (
    eq_tac >> rw[] >> gvs[] >>
    rpt (FULL_CASE_TAC >> gvs[]))
QED

val _ = export_theory();
