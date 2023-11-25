open HolKernel Parse boolLib bossLib dep_rewrite BasicProvers;

open pairTheory optionTheory listTheory pred_setTheory finite_mapTheory
open pureASTTheory mlmapTheory mlstringTheory pure_tcexpTheory
     pure_varsTheory pure_typingTheory
     (* pure_cexpTheory: probably don't need it *)

val _ = new_theory "ast_to_cexp";

(*
val _ = set_grammar_ancestry [
          "pureAST", "mlmap", "pure_cexp", "pure_typing", "pure_vars"] *)
val _ = set_grammar_ancestry [
          "pureAST", "mlmap", "pure_tcexp","pure_typing","pure_vars"]

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

(* nm_map maps type-operator names to their indices in the typing
   signature/map; the arg_map maps type variables (the vector vs after
   something like data Op vs = ...) into integers
 *)
Definition translate_type_def:
  translate_type nm_map arg_map (tyOp (INR s) tys) =
  (if s = "Fun" then
     do
       assert (LENGTH tys <= 2);
       args <- OPT_MMAP (translate_type nm_map arg_map) tys;
       return $ TypeCons (INR Function) args
     od
   else if s = "Bool" then do assert (tys = []); return $ PrimTy Bool; od
   else if s = "Integer" then do assert (tys = []); return $ PrimTy Integer od
   else if s = "String" then do assert (tys = []); return $ PrimTy String od
   else if s = "IO" then do assert (LENGTH tys <= 1);
                            t <- OPT_MMAP (translate_type nm_map arg_map) tys;
                            return $ TypeCons (INR M) t;
                         od
   else if s = "Array" then do assert (LENGTH tys <= 1);
                               t <- OPT_MMAP (translate_type nm_map arg_map) tys;
                               return $ TypeCons (INR Array) t;
                            od
  else
     do
       opidx <- lookup nm_map (implode s) ;
       args <- OPT_MMAP (translate_type nm_map arg_map) tys ;
       return $ TypeCons (INL opidx) args
     od) ∧
  translate_type nm_map arg_map (tyVarOp s tys) =
  do
    varidx <- lookup arg_map (implode s);
    args <- OPT_MMAP (translate_type nm_map arg_map) tys ;
    return $ VarTypeCons varidx args
  od ∧
  translate_type nm_map arg_map (tyOp (INL n) tys) =
  do
    args <- OPT_MMAP (translate_type nm_map arg_map) tys;
    return $ TypeCons (INR $ Tuple n) args;
  od
Termination
  WF_REL_TAC ‘measure (λ(_,_,ty). tyAST_size ty)’ >> rw[] >>
  rename [‘LENGTH tys = _’] >> Cases_on ‘tys’ >> gvs[tyAST_size_def] >>
  rename [‘LENGTH tys = _’] >> Cases_on ‘tys’ >>
  gvs[tyAST_size_def, listTheory.oEL_def]
End

Definition translate_predtype_def:
   translate_predtype nm_map arg_map (Predty preds ty) = do
     t <- (translate_type nm_map arg_map ty);
     preds' <- OPT_MMAP (λ(cl,t). do
          t' <- translate_type nm_map arg_map t;
          return (implode cl,t');
        od) preds;
     return $ Pred preds' t;
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
  translate_predtype_scheme nm_map (Predty preds ty) = do
    (arg_map,n) <<- build_arg_map (empty:(mlstring,num) map) 0 ty ;
    t <- translate_predtype nm_map arg_map (Predty preds ty) ;
    return (n,t)
  od
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
  Induct >> simp[strip_comb_def, expAST_size_eq] >>
  simp[expAST_size_def] >> rpt strip_tac >>
  rename [‘(I ## _) (strip_comb f) = (f0, es)’] >>
  Cases_on ‘strip_comb f’ >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Overload If = “λty g t e. NestedCase ty g «»
  (cepatCons «True» []) t
  [((cepatCons «False» []), e)]”

Definition dest_pvar_def[simp]:
  dest_pvar (patVar s) = SOME (implode s) ∧
  dest_pvar _ = NONE
End

Definition translate_headop_def:
  (* if we find that t is a cop, we will drop the type t *)
  (* t' is an user-annotated type of the result of the application *)
  (translate_headop (pure_tcexp$Var t s) t' =
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
        then (do
            assert (t = NONE);
            return $ Prim t' Seq
          od)
        else SOME $ App t' (Var t s)
     | SOME op => do
        assert (t = NONE);
        return $ Prim t' (AtomOp op)
      od) ∧
  translate_headop e t' = SOME (App t' e)
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
  mkLam t [] e = e ∧
  mkLam t vs e = Lam t vs e
End

Overload Bind = “λa1 a2. pure_tcexp$Prim NONE (Cons «Bind») [a1;a2]”

Definition case_then_map_def:
  case_then_map NONE f = SOME NONE ∧
  case_then_map (SOME x) f = do
    y <- f x ;
    return $ SOME y
  od
End

Definition bind_type_def:
  bind_type name t [] = NONE ∧
  (bind_type name t ((NONE,s,e)::rest) = (if s = name
      then SOME $ (SOME t,s,e)::rest
      else do
        rest' <- bind_type name t rest ;
        return $ (NONE,s,e)::rest'
      od)) ∧
  bind_type name t ((SOME t',s,e)::rest) = (if s = name
      then NONE
      else do
        rest' <- bind_type name t rest ;
        return $ (SOME t',s,e)::rest'
      od)
End

Definition translate_exp_def: (* translate_exp: translate exp to tcexp *)
  translate_exp nm_map tyinfo (expVar s t) =
  do
    t' <- case_then_map t $ translate_predtype nm_map empty ;
    return (pure_tcexp$Var t' $ implode s)
  od ∧
  translate_exp nm_map tyinfo (expCon s es t) =
  do
    rs <- OPT_MMAP (translate_exp nm_map tyinfo) es;
    t' <- case_then_map t $ translate_predtype nm_map empty;
    SOME (Prim t' (Cons $ implode s) rs)
  od ∧
  translate_exp nm_map tyinfo (expOp op es t) =
  do
    rs <- OPT_MMAP (translate_exp nm_map tyinfo) es;
    t' <- case_then_map t $ translate_predtype nm_map empty;
    return (Prim t' (AtomOp op) rs)
  od ∧
  translate_exp nm_map tyinfo (expTup es t) =
  do
    rs <- OPT_MMAP (translate_exp nm_map tyinfo) es;
    t' <- case_then_map t $ translate_predtype nm_map empty;
    SOME (Prim t' (Cons «») rs)
  od ∧
  translate_exp nm_map tyinfo (expApp fe xe t) =
  do
    (fe0, es) <<- strip_comb fe ;
    f <- translate_exp nm_map tyinfo fe0 ;
    t' <- case_then_map t $ translate_predtype nm_map empty ;
    lhs <- translate_headop f t';
    args <- OPT_MMAP (translate_exp nm_map tyinfo) (es ++ [xe]) ;
    SOME (lhs args)
  od ∧
  (translate_exp nm_map tyinfo (expAbs p aty e ty) =
   let aty = (case_then_map aty $ translate_predtype nm_map empty) in
   let ty = (case_then_map ty $ translate_predtype nm_map empty) in
   case p of
     patVar n => do
                  aty' <- aty ;
                  ty' <- ty ;
                  body <- translate_exp nm_map tyinfo e ;
                  SOME (Lam ty' [(aty',implode n)] body)
                od
   | _ => do
           ty' <- ty ;
           ce <- translate_patcase tyinfo «» p e;
           SOME (Lam ty' [(ARB,«»)] ce)
         od) ∧
  (translate_exp nm_map tyinfo (expIf g t e ty) =
   do
     ty' <- case_then_map ty $ translate_predtype nm_map empty;
     gc <- translate_exp nm_map tyinfo g ;
     tc <- translate_exp nm_map tyinfo t ;
     ec <- translate_exp nm_map tyinfo e ;
     SOME (If ty' gc tc ec)
   od) ∧
  (translate_exp nm_map tyinfo (expLit (litInt i)) =
   SOME (Prim NONE (AtomOp $ Lit (Int i)) [])) ∧
  (translate_exp nm_map tyinfo (expLit (litString s)) =
   SOME (Prim NONE (AtomOp $ Lit (Str s)) [])) ∧
  (translate_exp nm_map tyinfo (expLet ds body bty) =
   do
     recbinds <- translate_edecs nm_map tyinfo ds;
     bodyce <- translate_exp nm_map tyinfo body;
     ty' <- case_then_map bty $ translate_predtype nm_map empty ;
     SOME (Letrec ty' recbinds bodyce) 
   od) ∧
   (translate_exp nm_map tyinfo (expCase ge pats t) =
   do
     assert (¬NULL pats);
     g <- translate_exp nm_map tyinfo ge;
     t' <- case_then_map t $ translate_predtype nm_map empty ;
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
     return $ pure_tcexp$NestedCase t' g «» pat e (TL cepats)
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
         return (Bind e $ Lam NONE [NONE,«»] rest)
       od
   | expdostmtBind pe ee :: reste =>
       do
         case pe of
         | patVar n =>
             do
               e <- translate_exp nm_map tyinfo ee ;
               rest <- translate_exp nm_map tyinfo (expDo reste finalexp) ;
               return (Bind e $ Lam NONE [NONE,implode n] rest)
             od
         | patUScore =>
             do
               e <- translate_exp nm_map tyinfo ee ;
               rest <- translate_exp nm_map tyinfo (expDo reste finalexp) ;
               return (Bind e $ Lam NONE [NONE,«»] rest)
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
         recbinds <- translate_edecs nm_map tyinfo decs ;
         rest <- translate_exp nm_map tyinfo (expDo reste finalexp);
         SOME (Letrec NONE recbinds rest)
       od) ∧

  (translate_edecs nm_map tyinfo [] = SOME []) ∧
  (translate_edecs nm_map tyinfo (d::ds) =
   do
     rest <- translate_edecs nm_map tyinfo ds ;
     case d of
       expdecTysig name t =>
         do
           t' <- translate_predtype_scheme nm_map t;
           bind_type (implode name) t' rest
         od
     | expdecPatbind (patVar s) e =>
         do
           ce <- translate_exp nm_map tyinfo e ;
           SOME ((NONE, implode s, ce) :: rest)
         od
     | expdecPatbind _ _ => NONE
     | expdecFunbind s args body =>
         do
           vs <- OPT_MMAP (λ(pat,pty). do
               pat' <- dest_pvar pat ;
               pt' <- case_then_map pty $ translate_predtype nm_map empty ;
               return (pt',pat')
             od) args ;
           bce <- translate_exp nm_map tyinfo body ;
           SOME ((NONE, implode s, mkLam NONE vs bce) :: rest)
         od
   od)
Termination
  WF_REL_TAC
  ‘measure (λs. case s of
                  INL (_,_, e) => pureAST$expAST_size e
                | INR (_,_, ds) => list_size expdecAST_size ds)’ >>
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

Definition extract_class_expdec_def:
  (extract_class_expdec nm_map arg_map tyinfo sigs impl [] = SOME (sigs,impl)) ∧
  (extract_class_expdec nm_map arg_map tyinfo sigs impl (expdecTysig s predty::decs) = do
      s <<- implode s;
      assert (s ∉ FDOM sigs);
      pred' <- translate_predtype nm_map arg_map predty;
      extract_class_expdec nm_map arg_map tyinfo (sigs |+ (s,pred')) impl decs;
    od) ∧
  (extract_class_expdec nm_map arg_map tyinfo sigs impl (expdecFunbind s args exps::decs) = do
      s <<- implode s;
      assert (s ∉ FDOM impl);
      meth <- translate_exp nm_map tyinfo exps;
      extract_class_expdec nm_map arg_map tyinfo sigs (impl |+ (s, meth)) decs;
    od) ∧
  (* ignore expdecPatbind *)
  extract_class_expdec nm_map arg_map tyinfo sigs impl (_ :: decs) = NONE
End

Definition extract_inst_expdec_def:
  (extract_inst_expdec nm_map arg_map tyinfo impls [] = SOME impls) ∧
  (extract_inst_expdec nm_map arg_map tyinfo impls
    (expdecFunbind s args exps::ds) = do
      s <<- implode s;
      assert (s ∉ FDOM impls);
      meth <- translate_exp nm_map tyinfo exps;
      extract_inst_expdec nm_map arg_map tyinfo (impls |+ (s,meth)) ds;
    od) ∧
  (* raise error for both expdecTysig and expdecPatbind? *)
  (extract_inst_expdec nm_map arg_map tyinfo impls (_::ds) = NONE)
End

Definition add_instance_def:
  add_instance inst_map cl ty info =
    case FLOOKUP inst_map cl of
      | NONE => SOME $ inst_map |+ (cl, [(ty,info)])
      | SOME l =>
        (case ALOOKUP l ty of
          | NONE => SOME $ inst_map |+ (cl, (ty,info)::l)
          | _ => NONE)
End

(* passes over declarations;
   ignoring datatype declarations because they've already
   been extracted
 *)
Definition translate_decs_def:
  translate_decs nm_map tyinfo [] = SOME ([],FEMPTY,FEMPTY) ∧
  translate_decs nm_map tyinfo (declTysig name t :: ds) =
  do
    (rest,cl_map,inst_map) <- translate_decs nm_map tyinfo ds;
    t' <- translate_predtype_scheme nm_map t;
    rest' <- bind_type (implode name) t' rest;
    return (rest',cl_map,inst_map)
  od ∧
  translate_decs nm_map tyinfo (declData _ _ _  :: ds) = translate_decs nm_map tyinfo ds ∧
  translate_decs nm_map tyinfo (declClass spcls cl v minimpl exps :: ds) =
  do
    (rest,cl_map,inst_map) <- translate_decs nm_map tyinfo ds ;
    minimpl <<- MAP (MAP implode) minimpl;
    clname <<- implode cl;
    assert (clname ∉ FDOM cl_map);
    (* assert $ EVERY ALL_DISTINCT minimpl; *)
    (msigs,defimpl) <- extract_class_expdec nm_map (insert empty (implode v) 0) tyinfo FEMPTY FEMPTY exps;
    (* assert $ FEVERY (λ(funname,_). funname IN FDOM msigs) defimpl; *)
    (* assert $ EVERY (EVERY (λx. x IN FDOM msigs)) minimpl; *)
    return (rest,cl_map |+ (clname, (* mlstring *)
      <| super := MAP implode spcls
       (* do kind inference after collection all the classinfos *)
       ; methodsig := msigs
       ; minImp := minimpl
       ; defaults := defimpl|>), inst_map) ;
  od ∧
  translate_decs nm_map tyinfo (declInst constraints cl ty exps :: ds) =
  do
    (rest,cl_map,inst_map) <- translate_decs nm_map tyinfo ds ;
    (arg_map,max_v) <<- build_arg_map empty 0 ty ;
    t <- translate_type nm_map arg_map ty ;
    impls <- extract_inst_expdec nm_map arg_map tyinfo FEMPTY exps ;
    cstr' <- OPT_MMAP (λ(c,v). do
        v' <- mlmap$lookup arg_map (implode v) ;
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
    inst_map' <- add_instance inst_map cl t (<|cstr := cstr';impl := impls|>);
    return (rest, cl_map, inst_map')
  od ∧
  translate_decs nm_map tyinfo (declFunbind s args body :: ds) =
  do
    (rest,cl_map,inst_map) <- translate_decs nm_map tyinfo ds ;
    vs <- OPT_MMAP (λ(pat,pty). do
               pat' <- dest_pvar pat ;
               pt' <- case_then_map pty $ translate_predtype nm_map empty ;
               return (pt',pat')
             od) args ;
           bce <- translate_exp nm_map tyinfo body ;
    bce <- translate_exp nm_map tyinfo body ;
    SOME ((NONE,implode s, mkLam NONE vs bce) :: rest,cl_map,inst_map)
  od ∧
  translate_decs nm_map tyinfo (declPatbind p e :: ds) =
  do
    (rest,cl_map,inst_map) <- translate_decs nm_map tyinfo ds ;
    v <- dest_pvar p ;
    ce <- translate_exp nm_map tyinfo e ;
    SOME ((NONE,v,ce) :: rest,cl_map,inst_map)
  od
End

Definition listinfo_def:
  listinfo = (["a"], [(«[]», []);
    («::», [tyVarOp "a" []; tyOp (INR "[]") [tyVarOp "a" []]])])
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
    (binds,cl_map,inst_map) <- translate_decs nm_map (insert tyinfo «[]» listinfo) ds ;
    SOME (Letrec NONE binds (pure_tcexp$Var (SOME $ Pred [] $ TypeCons (INR M) [Unit]) «main»),
      REVERSE sig0,cl_map,inst_map)
  od
End

(********** closedness **********)

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

val _ = export_theory();
