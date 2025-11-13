Theory pure_tcexp_typingProof
Ancestors
  pair arithmetic integer string option list rich_list alist
  finite_map pred_set pure_misc pure_config pure_exp
  pure_exp_lemmas pure_semantics pure_eval pure_tcexp
  pure_tcexp_lemmas typeclass_types typeclass_kindCheck
  typeclass_typesProps typeclass_typing typeclass_typingProps
  pure_tcexp_typing pure_tcexp_typingProps pure_obs_sem_equal
  pure_congruence pure_exp_rel
Libs
  BasicProvers dep_rewrite

(* we need to open the typeclass typing theories as some
* definitions are shared  *)

(* TODO replace existing get_atoms_SOME_SOME_eq *)
Theorem get_atoms_SOME_SOME_eq:
  ∀ls as. get_atoms ls = SOME (SOME as) ⇔ ls = MAP wh_Atom as
Proof
  rw[get_atoms_SOME_SOME_eq] >>
  rw[LIST_EQ_REWRITE, LIST_REL_EL_EQN] >> eq_tac >> gvs[EL_MAP]
QED

Theorem eval_op_type_safe:
  (type_atom_op op ts t ∧ t ≠ Bool ∧
   LIST_REL type_lit ls ts ⇒
  ∃res.
    eval_op op ls = SOME (INL res) ∧
    type_lit res t) ∧
  (type_atom_op op ts Bool ∧
   LIST_REL type_lit ls ts ⇒
  ∃res.
    eval_op op ls = SOME (INR res))
Proof
  rw[type_atom_op_cases, type_lit_cases] >> gvs[type_lit_cases, PULL_EXISTS]
  >- (
    ntac 2 $ last_x_assum mp_tac >> map_every qid_spec_tac [`ts`,`ls`] >>
    Induct_on `LIST_REL` >> rw[] >> gvs[type_lit_cases, concat_def]
    )
  >- (
    ntac 2 $ last_x_assum mp_tac >> map_every qid_spec_tac [`ts`,`ls`] >>
    Induct_on `LIST_REL` >> rw[] >> gvs[type_lit_cases, implode_def]
    )
  >- (IF_CASES_TAC >> gvs[])
QED

Inductive type_wh:
  (type_tcexp ns db st env (Prim (Cons $ implode s) ces) t ∧
   MAP exp_of ces = es ⇒
    type_wh ns db st env (wh_Constructor s es) t) ∧

  (type_tcexp ns db st env (Lam [implode s] ce) t ∧
   exp_of ce = e ⇒
    type_wh ns db st env (wh_Closure s e) t) ∧

  (type_tcexp ns db st env (Prim (AtomOp $ Lit l) []) t ⇒
    type_wh ns db st env (wh_Atom l) t) ∧

  (type_ok (SND ns) db t ⇒ type_wh ns db st env wh_Diverge t)
End

Theorem type_wh_PrimTy_eq_wh_Atom[local]:
  type_wh ns db st env wh (Atom $ PrimTy pt) ∧ pt ≠ Bool ⇒
    wh = wh_Diverge ∨ ∃a. wh = wh_Atom a
Proof
  rw[type_wh_cases] >>
  gvs[Once type_tcexp_cases,cons_types_EQ_Atom,
    tcons_to_type_def] >>
  Cases_on `arg_tys` >> gvs[Functions_def]
QED

Theorem type_wh_PrimTy_Bool_eq_wh_Constructor[local]:
  type_wh ns db st env wh (Atom $ PrimTy Bool) ⇒
    wh = wh_Diverge ∨ wh = wh_Constructor "True" [] ∨
    wh = wh_Constructor "False" []
Proof
  rw[type_wh_cases] >> gvs[Once type_tcexp_cases,
    mlstringTheory.implode_def,cons_types_EQ_Atom,
    tcons_to_type_def]
  >- (Cases_on `arg_tys` >> gvs[Functions_def])
  >- (gvs[get_PrimTys_def, type_atom_op_cases, type_lit_cases])
QED

Theorem Monad_cons_types[local]:
  Monad t = cons_types (Atom $ CompPrimTy $ M) [t]
Proof
  simp[cons_types_def]
QED

Theorem type_wh_Function_eq_wh_Closure[local]:
  type_wh ns db st env wh
    (cons_types (Atom $ CompPrimTy Function) [at; t]) ⇒
    wh = wh_Diverge ∨ ∃x body. wh = wh_Closure x body
Proof
  rw[type_wh_cases] >>
  gvs[Once type_tcexp_cases,Monad_cons_types,
    cons_types_EQ_Atom,tcons_to_type_def,
    cons_types_Atom_EQ] >>
  gvs[cons_types_def]
QED

Theorem Array_cons_types[local]:
  Cons (Atom (CompPrimTy Array)) t =
  cons_types (Atom $ CompPrimTy Array) [t]
Proof
  simp[cons_types_def]
QED

Theorem type_wh_TypeCons_eq_wh_Constructor[local]:
  type_wh ns db st env wh (tcons_to_type (INL id) ts) ⇒
    wh = wh_Diverge ∨ ∃cname es. wh = wh_Constructor cname es
Proof
  rw[type_wh_cases] >>
  gvs[Once type_tcexp_cases, exp_of_def,Array_cons_types,
    tcons_to_type_def,Monad_cons_types,get_PrimTys_def,
    cons_types_Atom_EQ,cons_types_EQ_Atom] >>
  Cases_on `arg_tys` >>
  gvs[Functions_cons_types,cons_types_Atom_EQ]
QED

Theorem type_wh_Array_eq_Loc[local]:
  type_wh ns db st env wh (Cons (Atom $ CompPrimTy Array) t) ⇒
    wh = wh_Diverge ∨ ∃a n. wh = wh_Atom (Loc n) ∧ oEL n st = SOME t
Proof
  rw[type_wh_cases] >> gvs[Once type_tcexp_cases]
  >- (
    Cases_on `ts` using SNOC_CASES >>
    gvs[cons_types_def,cons_types_EQ_Atom,cons_types_SNOC]
  )
  >- (
    last_x_assum mp_tac >>
    rpt $ pop_assum kall_tac >>
    Induct_on `tyargs` using SNOC_INDUCT >>
    gvs[cons_types_def,tcons_to_type_def,
      cons_types_EQ_Atom,cons_types_SNOC]
  ) >>
  Cases_on `arg_tys` >> gvs[Functions_def]
QED

Theorem type_wh_Tuple_eq_wh_Constructor[local]:
  type_wh ns db st env wh (cons_types (Tup n) ts) ⇒
    wh = wh_Diverge ∨ ∃es. wh = wh_Constructor "" es
Proof
  rw[type_wh_cases] >>
  gvs[Once type_tcexp_cases, exp_of_def, mlstringTheory.implode_def,
    Monad_cons_types,Array_cons_types,tcons_to_type_def,
    cons_types_EQ_Atom,cons_types_Atom_EQ] >>
  Cases_on `arg_tys` >>
  gvs[Functions_cons_types,cons_types_Atom_EQ]
QED

Theorem type_wh_Exception_eq_wh_Constructor[local]:
  type_wh ns db st env wh (Atom Exception) ⇒
    wh = wh_Diverge ∨ ∃cn es. wh = wh_Constructor cn es
Proof
  rw[type_wh_cases] >> gvs[Once type_tcexp_cases, exp_of_def] >>
  Cases_on `arg_tys` >> gvs[Functions_def]
QED

Theorem eval_wh_to_Case_wh_Diverge:
  closed (exp_of e) ∧ eval_wh_to k (exp_of e) = wh_Diverge ∧ es ≠ [] ⇒
  eval_wh_to k (exp_of (Case e v es eopt)) = wh_Diverge
Proof
  rw[exp_of_def, eval_wh_to_def, bind1_def] >>
  Cases_on `es` >> gvs[rows_of_def] >>
  PairCases_on `h` >> gvs[rows_of_def, subst1_def] >>
  rw[eval_wh_to_def] >>
  IF_CASES_TAC >> gvs[] >>
  qsuff_tac `eval_wh_to (k - 3) (exp_of e) = wh_Diverge` >> gvs[] >>
  CCONTR_TAC >> drule eval_wh_inc >> simp[] >> qexists_tac `k` >> simp[]
QED

Theorem eval_wh_to_lets_for:
  ∀vs e k cn v b.
  closed e ∧ vs ≠ [] ∧ ¬ MEM v vs ⇒
  ∃res.
    eval_wh_to k
      (subst1 (explode v) e
       (lets_for cn ar (explode v) (MAPi (λi v. (i,explode v)) vs) b)) =
    res ∧
    (res = wh_Diverge ∨
     k ≠ 0 ∧
     res =
      eval_wh_to (k - 1)
      (subst
        (FEMPTY |++
         MAPi (λi v. (explode v, If (IsEq cn ar T e) (Proj cn i e) Bottom)) vs)
        (subst1 (explode v) e b)))
Proof
  Induct using SNOC_INDUCT >> rw[SNOC_APPEND, lets_for_def, lets_for_APPEND] >>
  Cases_on `vs = []` >> gvs[]
  >- (
    simp[lets_for_def, bind1_def, subst1_def, eval_wh_to_def, Bottom_def] >>
    IF_CASES_TAC >> gvs[] >> simp[FUPDATE_LIST_THM]
    ) >>
  last_x_assum drule >> disch_then drule >>
  strip_tac >> gvs[] >>
  simp[lets_for_APPEND, indexedListsTheory.MAPi_APPEND, lets_for_def] >>
  pop_assum $ qspecl_then
    [`k`,`cn`,
     ‘Let (explode x)
      (If (IsEq cn ar T (Var $ explode v))
       (Proj cn (LENGTH vs) (Var $ explode v)) Bottom) b’]
    assume_tac >>
  gvs[] >>
  simp[subst_def, FLOOKUP_UPDATE, DOMSUB_FUPDATE_NEQ] >>
  simp[FUPDATE_LIST_APPEND, GSYM FUPDATE_EQ_FUPDATE_LIST] >>
  qmatch_goalsub_abbrev_tac `FEMPTY |++ m` >>
  simp[eval_wh_to_def] >> IF_CASES_TAC >> gvs[] >> simp[bind1_def] >>
  reverse $ rw[DISJ_EQ_IMP] >- gvs[Bottom_def, subst_def] >>
  drule eval_wh_inc >>
  disch_then $ qspec_then `k - 1` $ mp_tac o GSYM >> rw[] >>
  AP_TERM_TAC >> DEP_REWRITE_TAC[subst_subst_FUNION] >> simp[] >> conj_tac
  >- (
    simp[DOMSUB_FUPDATE_LIST] >>
    ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> simp[] >>
    simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, MEM_FILTER] >>
    unabbrev_all_tac >> simp[indexedListsTheory.MEM_MAPi, PULL_EXISTS, Bottom_def]
    ) >>
  AP_THM_TAC >> AP_TERM_TAC >>
  rw[fmap_eq_flookup, FLOOKUP_FUNION, FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM] >>
  every_case_tac >> gvs[Bottom_def, subst_def]
QED

Theorem MAPi_MAP_o:
  ∀f g. MAPi f (MAP g l) = MAPi (flip ($o o f) g) l
Proof
  Induct_on ‘l’ >> simp[combinTheory.o_DEF, combinTheory.C_DEF]
QED

Theorem eval_wh_to_Case:
  ∀css c ce v k e es cname vs.
  eval_wh_to k (exp_of e) = wh_Constructor (explode cname) es ∧
  closed (exp_of e) ∧
  ALOOKUP css cname = SOME (vs, ce) ∧
  ¬ MEM v vs ∧
  explode cname ∉ monad_cns ∧
  LENGTH vs = LENGTH es
  ⇒ ∃res.
      eval_wh_to k (exp_of (pure_tcexp$Case e v css eopt)) = res ∧
      (res = wh_Diverge ∨
       k ≠ 0 ∧
       res =
        eval_wh_to (k - 1)
          (subst (FEMPTY |++
                  MAPi (λi v. (explode v,
                               exp_of (SafeProj cname (LENGTH es) i e))) vs)
           (subst1 (explode v) (exp_of e) (exp_of ce))))
Proof
  Induct >> rw[exp_of_def, eval_wh_to_def, bind1_def] >>
  PairCases_on `h` >> gvs[] >>
  qmatch_goalsub_abbrev_tac ‘rows_of _ _ eoptcase’ >>
  gvs[AllCaseEqs()] >>
  simp[rows_of_def, subst1_def, eval_wh_to_def] >>
  IF_CASES_TAC >> gvs[] >> simp[eval_wh_to_def] >> IF_CASES_TAC >> gvs[] >>
  Cases_on `eval_wh_to (k − 3) (exp_of e) = wh_Diverge` >> gvs[] >>
  drule eval_wh_inc >> disch_then $ qspec_then `k` $ mp_tac o GSYM >> rw[]
  >- (
    Cases_on `h1 = []` >> simp[lets_for_def, FUPDATE_LIST_THM]
    >- (
      rw[DISJ_EQ_IMP] >>
      drule eval_wh_inc >> disch_then $ irule o GSYM >> simp[]
      ) >>
    drule_all eval_wh_to_lets_for >>
    disch_then $
      qspecl_then [`LENGTH es`,`k - 2`,`explode cname`,`exp_of ce`] mp_tac >>
    gvs[] >>
    rw[] >> gvs[MAPi_MAP_o, combinTheory.o_ABS_R, combinTheory.C_ABS_L] >>
    gvs[combinTheory.o_DEF] >>
    rw[DISJ_EQ_IMP] >>
    drule eval_wh_inc >> disch_then $ irule o GSYM >> simp[]
    )
  >- (
    `eval_wh_to (k - 1) (exp_of e) = wh_Constructor (explode cname) es` by (
      drule eval_wh_inc >> simp[]) >>
    last_x_assum drule >> simp[] >> disch_then drule >>
    gvs[exp_of_def, eval_wh_to_def, bind1_def] >>
    rw[] >> gvs[] >> rw[DISJ_EQ_IMP] >>
    drule eval_wh_inc >> disch_then $ irule o GSYM >> simp[]
    )
QED

Definition Disj'_def:
  Disj' ve [] = Cons "False" [] ∧
  Disj' ve ((cn,l)::xs) =
    If (IsEq cn l T ve) (Cons "True" []) (Disj' ve xs)
End

Theorem subst1_Disj_Disj':
  subst1 v e (Disj v cn_ars) = Disj' e cn_ars
Proof
  Induct_on `cn_ars` >> rw[pureLangTheory.Disj_def, Disj'_def] >>
  PairCases_on `h` >> rw[subst1_def, pureLangTheory.Disj_def, Disj'_def]
QED

Theorem eval_wh_to_Disj':
  eval_wh e = wh_Constructor cname es ∧ cname ∉ monad_cns ⇒
  ∃res.
    eval_wh_to k (Disj' e cn_ars) = res ∧
    (res = wh_Diverge ∨
     res =
      case ALOOKUP cn_ars cname of
      | NONE => wh_False
      | SOME ar => if ar = LENGTH es then wh_True else wh_Error)
Proof
  qid_spec_tac `k` >>
  Induct_on `cn_ars` >> rw[] >> simp[Disj'_def, eval_wh_to_def] >>
  PairCases_on `h` >> simp[Disj'_def, eval_wh_to_def] >> Cases_on `k = 0` >- gvs[] >>
  simp[eval_wh_to_def] >> Cases_on `k ≤ 1` >- gvs[] >>
  simp[] >> Cases_on `eval_wh_to (k - 2) e = wh_Diverge` >> simp[] >>
  qspecl_then [`eval_wh_to (k - 2) e`,`k - 2`,`e`]
    mp_tac $ GEN_ALL $ GSYM eval_wh_to_IMP_eval_wh >>
  simp[] >> strip_tac >> IF_CASES_TAC >> simp[] >> fs[] >> IF_CASES_TAC >> simp[]
QED

Theorem eval_wh_to_Case_catchall:
  ∀css k.
    eval_wh_to k (exp_of e) = wh_Constructor cname es ∧
    closed (exp_of e) ∧ cname ∉ monad_cns ∧
    ALOOKUP css (implode cname) = NONE ⇒
    ∃res.
      eval_wh_to k (exp_of (pure_tcexp$Case e v css eopt)) = res ∧
      (res = wh_Diverge ∨
       k ≠ 0 ∧
       res =
       eval_wh_to (k - 1)
                  (subst1 (explode v) (exp_of e)
                   (case eopt of | NONE => Fail | SOME (pats,cae) =>
                    case ALOOKUP pats (implode cname) of
                      | NONE => Fail | SOME ar =>
                        if ar = LENGTH es then exp_of cae else Fail)))
Proof
  simp[exp_of_def, eval_wh_to_def, SF CONJ_ss, AllCaseEqs()] >>
  ‘∀E. closed (exp_of e) ⇒
       bind1 (explode v) (exp_of e) E = subst1 (explode v) (exp_of e) E’
    by simp[bind_def, FLOOKUP_DEF, AllCaseEqs()] >> simp[] >>
  Induct_on ‘css’ >>
  simp[rows_of_def, FORALL_PROD, AllCaseEqs(), subst_def, FLOOKUP_DEF] >>
  simp[eval_wh_to_def] >> rw[]
  >- (
    TOP_CASE_TAC >> gvs[] >> PairCases_on `x` >> gvs[] >> Cases_on `k = 0` >> gvs[] >>
    simp[pureLangTheory.IfDisj_def, subst1_def, subst1_Disj_Disj'] >>
    simp[eval_wh_to_def] >> IF_CASES_TAC >> gvs[] >>
    `eval_wh (exp_of e) = wh_Constructor cname es` by (
      qspecl_then [`eval_wh_to k (exp_of e)`,`k`,`exp_of e`]
        mp_tac $ GEN_ALL $ GSYM eval_wh_to_IMP_eval_wh >> simp[]) >>
    drule_all eval_wh_to_Disj' >>
    disch_then $ qspecl_then [`k - 2`,`MAP (explode ## I) x0`] assume_tac >> gvs[] >>
    pop_assum mp_tac >> TOP_CASE_TAC >> reverse $ rw[]
    >- (
      qsuff_tac `ALOOKUP x0 (implode cname) = NONE` >- simp[eval_wh_to_def] >>
      gvs[ALOOKUP_NONE, MEM_MAP, FORALL_PROD]
      )
    >- (
      qsuff_tac `ALOOKUP x0 (implode cname) = SOME x` >> simp[] >>
      qpat_x_assum `ALOOKUP _ _ = _` mp_tac >> rpt $ pop_assum kall_tac >>
      Induct_on `x0` >> rw[] >> PairCases_on `h` >> gvs[implodeEQ] >> rw[] >> gvs[]
      ) >>
    `ALOOKUP x0 (implode cname) = SOME (LENGTH es)` by (
      qpat_x_assum `ALOOKUP _ _ = _` mp_tac >> rpt $ pop_assum kall_tac >>
      Induct_on `x0` >> rw[] >> PairCases_on `h` >> gvs[implodeEQ] >> rw[] >> gvs[]) >>
    simp[] >> rw[DISJ_EQ_IMP] >>
    drule eval_wh_inc >> disch_then $ qspec_then `k - 1` mp_tac >> simp[]
    ) >>
  rename [
    ‘eval_wh_to (k - 2) (IsEq (explode pnm) (LENGTH pargs) T (exp_of e))’] >>
  Cases_on
    ‘eval_wh_to (k - 2) (IsEq (explode pnm) (LENGTH pargs) T (exp_of e)) =
     wh_Diverge’
  >- simp[] >>
  simp[eval_wh_to_def] >> Cases_on ‘k ≤ 2’ >> simp[] >>
  Cases_on ‘eval_wh_to (k - 3) (exp_of e) = wh_Diverge’ >> simp[] >>
  drule_then (qspec_then ‘k’ (assume_tac o SRULE[] o GSYM)) eval_wh_inc >>
  simp[] >> gs[implodeEQ] >>
  first_x_assum $ qspec_then ‘k - 1’ mp_tac >> simp[] >> impl_tac
  >- (qspecl_then [‘k - 1’, ‘exp_of e’, ‘k - 3’] mp_tac eval_wh_inc >> simp[])>>
  strip_tac >> simp[] >> simp[DECIDE “p ∨ q ⇔ ~p ⇒ q”] >> strip_tac >>
  dxrule_then (qspec_then ‘k-1’ assume_tac) eval_wh_inc >> gs[]
QED

(* defintions for proving type soundness of NestedCase
Definition check_pat_def:
  (check_pat cepatUScore e = T) ∧
  (check_pat (cepatVar v) e = T) ∧
  (check_pat (cepatCons cn ps) e =
    case eval_wh e of
    | wh_Constructor cn' es =>
      (cn = implode cn' ∧ cn' ∉ monad_cns ∧
        LIST_REL check_pat ps es)
    | _ => F)
End

(* returns the first pattern that matches the exp *)
Definition find_first_match_pattern_def:
  find_first_match_pattern [] v = NONE ∧
  find_first_match_pattern ((p,e)::pes) v =
    if check_pat p v
    then SOME (p,e)
    else find_first_match_pattern pes v
End

(* returns a fmap (variable |-> SafeProj) ? *)
Definition safe_proj_pat_aux_def:
  safe_proj_pat_aux (cepatCons cn ps) e acc =
  (* the order matters, check if this is the correct order *)
  FOLDR FUNION FEMPTY $ MAPi (λi p. safe_proj_pat_aux p e ((cn,LENGTH ps,i)::acc)) ps ∧
  safe_proj_pat_aux cepatUScore e acc = FEMPTY ∧
  safe_proj_pat_aux (cepatVar v) e acc =
  FEMPTY |+ (v,FOLDR (λ(cn,len,i) x. SafeProj cn len i x) e acc)
Termination
  WF_REL_TAC `measure (cepat_size o FST)`
End

Definition safe_proj_pat_def:
  safe_proj_pat pat e = safe_proj_pat_aux pat e []
End

Theorem eval_wh_to_NestedCase:
  closed (exp_of g) ∧
  (* if g terminates, find_first_match_pattern should return
  * SOME, given exhaustive patterns *)
  find_first_match_pattern ((p,e)::pes) (exp_of g) =
    SOME (matched_pat, ce)
  ⇒
  ∃res.
    eval_wh_to k (exp_of
      (pure_tcexp$NestedCase g gv p e pes)) = res ∧
    (res = wh_Diverge ∨
     k ≠ 0 ∧
    (* may takes more than 1 tick to match the pattern? *)
    k' < k ∧
     res = eval_wh_to (k - k')
      (subst
        (safe_proj_pat matched_pat g)
        (subst1 (explode gv) (exp_of g) (exp_of ce))))
Proof
  simp[exp_of_def,eval_wh_to_def,Excl"nested_rows_def"] >>
  IF_CASES_TAC >>
  rw[Excl"nested_rows_def"] >>
QED

TODO: relating tcexp_type_cepat with safe_proj_pat?
*)

Theorem MAPi_ID[local,simp]:
  ∀l. MAPi (λn v. v) l = l
Proof
  Induct >> rw[combinTheory.o_DEF]
QED

Theorem FUN_FMAP_SING:
  FUN_FMAP f {k} = FEMPTY |+ (k, f k)
Proof
  simp[fmap_EXT, FUN_FMAP_DEF]
QED

Theorem FUN_FMAP_IMAGE:
  FINITE A ⇒
  FUN_FMAP f (IMAGE explode A) = FUN_FMAP (f o explode) A f_o implode
Proof
  strip_tac >>
  ‘∀h. FINITE { x | mlstring$implode x ∈ FDOM h }’
    by (‘∀h. { x | implode x ∈ FDOM h } = IMAGE explode (FDOM h)’
          by simp[EXTENSION, GSYM implodeEQ] >>
        simp[]) >>
  simp[fmap_EXT, PULL_EXISTS, FUN_FMAP_DEF, FAPPLY_f_o] >>
  simp[EXTENSION, GSYM implodeEQ]
QED

Theorem FUN_FMAP_DOM:
  FUN_FMAP (λx. g (f ' x)) (FDOM f) = g o_f f
Proof
  simp[fmap_EXT, FUN_FMAP_DEF]
QED

Theorem o_f_FUDLIST_MAP:
  f o_f (fm |++ MAP (λ(k,v). (k, g v)) kvs) =
  (f o_f fm) |++ MAP (λ(k,v). (k, f (g v))) kvs
Proof
  qid_spec_tac ‘fm’ >> Induct_on ‘kvs’ >> simp[FUPDATE_LIST_THM] >>
  simp[fmap_EXT] >> simp[FDOM_FUPDATE_LIST, FORALL_PROD]
QED

Theorem FDOM_f_o_implode:
  { x | implode x ∈ FDOM fm } = IMAGE explode (FDOM fm) ∧
  FDOM (fm f_o implode) = IMAGE explode (FDOM fm)
Proof
  conj_asm1_tac >- simp[EXTENSION, GSYM implodeEQ] >>
  simp[FDOM_f_o]
QED

Theorem FUPDATE_f_o_implode:
  (fm |+ (k,v)) f_o implode = (fm f_o implode) |+ (explode k, v)
Proof
  simp[FAPPLY_f_o, fmap_EXT, FAPPLY_FUPDATE_THM, FDOM_f_o_implode,
       DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS]
QED

Theorem FUPDATE_LIST_MAP_f_o:
  ∀fm. (fm |++ MAP (λ(k,v). (k, f v)) kvs) f_o implode =
       (fm f_o implode) |++ MAP (λ(k,v). (explode k, f v)) kvs
Proof
  Induct_on ‘kvs’  >>
  simp[FUPDATE_LIST_THM] >>
  simp[fmap_EXT, FDOM_FUPDATE_LIST, FORALL_PROD, MEM_MAP, PULL_EXISTS,
       FDOM_f_o_implode, EXISTS_PROD, DISJ_IMP_THM, FORALL_AND_THM,
       FUPDATE_f_o_implode]
QED

Theorem FUPDATE_LIST_f_o_implode:
  ∀fm.
    (fm |++ kvs) f_o implode =
    (fm f_o implode) |++ (MAP (explode ## I) kvs)
Proof
  Induct_on ‘kvs’ >>
  simp[FUPDATE_LIST_THM, FUPDATE_f_o_implode, combinTheory.o_DEF,
       FORALL_PROD]
QED

Theorem LLOOKUP_MEM:
  LLOOKUP xs n = SOME x ⇒ MEM x xs
Proof
  rw[miscTheory.LLOOKUP_THM] >> metis_tac[EL_MEM]
QED

Theorem tcexp_prim_cons_not_monad_cns:
  type_tcexp ns db st [] (Prim (Cons (implode s)) ces) t' ∧
  tcexp_namespace_ok ns ∧
  tcexp_destruct_type_cons ns db t' cn tys ⇒
  s ∉ monad_cns
Proof
  rpt strip_tac >>
  qhdtm_x_assum ‘type_tcexp’ $ strip_assume_tac o PURE_ONCE_REWRITE_RULE [type_tcexp_cases] >> gvs[mlstringTheory.implode_def] >>
  gvs[monad_cns_def] >>
  gvs[oneline tcexp_destruct_type_cons_def,AllCaseEqs(),
      tcexp_type_cons_def
     ] >>
  gvs[split_ty_cons_def,split_ty_cons_aux_def] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
  gvs[type_exception_def,tcexp_namespace_ok_def,reserved_cns_def] >>
  imp_res_tac ALOOKUP_MEM >>
  imp_res_tac LLOOKUP_MEM >>
  gvs[ALL_DISTINCT_APPEND,MEM_MAP,PULL_EXISTS,SF DNF_ss,mlstringTheory.implode_def,
      FORALL_PROD,MEM_FLAT] >>
  metis_tac[]
QED

Theorem eval_wh_to_Bottom:
  eval_wh_to k Bottom = wh_Diverge
Proof
  mp_tac eval_wh_Bottom >>
  simp[eval_wh_def] >>
  DEEP_INTRO_TAC some_intro >>
  rw[]
QED

Theorem tcexp_prim_cons_length_eq:
  type_tcexp ns db st [] (Prim (Cons cn) ces) t' ∧
  tcexp_namespace_ok ns ∧
  tcexp_destruct_type_cons ns db t' cn tys ⇒
  LENGTH tys = LENGTH ces
Proof
  rpt strip_tac >>
  qhdtm_x_assum ‘type_tcexp’ $ strip_assume_tac o PURE_ONCE_REWRITE_RULE [type_tcexp_cases] >> gvs[mlstringTheory.implode_def] >>
  gvs[oneline tcexp_destruct_type_cons_def,AllCaseEqs(),
      tcexp_type_cons_def
     ] >>
  gvs[split_ty_cons_thm,head_ty_cons_def,ty_args_alt] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
  gvs[type_exception_def,tcexp_namespace_ok_def(*,reserved_cns_def*)] >>
  imp_res_tac ALOOKUP_MEM >>
  imp_res_tac LLOOKUP_MEM >>
  gvs[ALL_DISTINCT_APPEND,MEM_MAP,PULL_EXISTS,SF DNF_ss,mlstringTheory.implode_def,
      FORALL_PROD,MEM_FLAT] >>
  imp_res_tac LIST_REL_LENGTH >>
  gvs[] >>
  gvs[cons_types_EQ_Atom]
  >- (gvs[reserved_cns_def,SF DNF_ss] >> metis_tac[])
  >- gvs[head_ty_cons_cons_types,ty_args_cons_types,
          head_ty_cons_def,ty_args_alt]
  >- (gvs[tcons_to_type_def] >>
      gvs[cons_types_EQ_Atom])
  >- (gvs[tcons_to_type_def] >>
      gvs[cons_types_EQ_Atom] >>
      gvs[head_ty_cons_cons_types,ty_args_cons_types,
          head_ty_cons_def,ty_args_alt])
  >- (gvs[reserved_cns_def,SF DNF_ss] >> metis_tac[])
  >- (gvs[reserved_cns_def,SF DNF_ss] >> metis_tac[])
  >- (gvs[reserved_cns_def,SF DNF_ss] >> metis_tac[])
QED

Theorem tcexp_get_cases_NOT_EMPTY:
  tcexp_namespace_ok ns ∧
  tcexp_get_cases ns vt = SOME constructors ⇒
  constructors ≠ []
Proof
  Cases_on `ns` >>
  rw[tcexp_namespace_ok_def,tcexp_get_cases_def]
  >- (Cases_on `q` >> gvs[]) >>
  pairarg_tac >> gvs[] >>
  every_case_tac >>
  gvs[] >>
  pairarg_tac >>
  gvs[] >>
  drule_then assume_tac LLOOKUP_MEM >>
  qpat_x_assum `EVERY (λ(ak,td). td ≠ []) _` $
    drule o SRULE[EVERY_MEM] >>
  rw[]
QED

Theorem type_wh_tcexp_get_cases_eq_wh_constructor:
  tcexp_get_cases ns vt = SOME constructors ∧
  type_wh ns db st env wh vt ⇒
  ∃cn es ces.
    wh = wh_Diverge ∨
    (wh = wh_Constructor cn es ∧
      ALOOKUP constructors (implode cn) = SOME ces ∧
      LENGTH ces = LENGTH es)
Proof
  rw[tcexp_get_cases_def]
  >- (
    drule type_wh_Exception_eq_wh_Constructor >>
    rw[] >>
    gvs[Once type_wh_cases,MEM_MAP] >>
    gvs[Once type_tcexp_cases,tcons_to_type_def,
      cons_types_EQ_Atom,type_exception_def] >>
    simp[lambdify PAIR_MAP,ALOOKUP_MAP,LAMBDA_PROD] >>
    gvs[LIST_REL_EL_EQN]
  ) >>
  pairarg_tac >>
  gvs[] >>
  every_case_tac >>
  gvs[]
  >- (
    pairarg_tac >>
    gvs[] >>
    drule tcons_to_type_split_ty_cons >>
    disch_then $ assume_tac o GSYM >>
    gvs[] >>
    drule type_wh_TypeCons_eq_wh_Constructor >>
    rw[lambdify PAIR_MAP,ALOOKUP_MAP,LAMBDA_PROD,PULL_EXISTS] >>
    drule_then assume_tac LLOOKUP_MEM >>
    gvs[Once type_wh_cases,Once type_tcexp_cases,
      tcons_to_type_def,cons_types_Atom_EQ,Monad_cons_types,
      cons_types_EQ_Atom] >>
    gvs[tcexp_type_cons_def] >>
    gvs[LIST_REL_EL_EQN]
  )
  >- (
    drule tcons_to_type_split_ty_cons >>
    rw[tcons_to_type_def,cons_types_def] >>
    drule type_wh_PrimTy_Bool_eq_wh_Constructor >>
    rw[] >>
    simp[mlstringTheory.implode_def]
  )
  >- (
    drule tcons_to_type_split_ty_cons >>
    rw[tcons_to_type_def,cons_types_def] >>
    drule type_wh_Tuple_eq_wh_Constructor >>
    rw[] >>
    simp[mlstringTheory.implode_def] >>
    gvs[Once type_wh_cases] >>
    gvs[Once type_tcexp_cases] >>
    gvs[cons_types_Atom_EQ,LIST_REL_EL_EQN,Monad_cons_types,
      cons_types_EQ_Atom,tcons_to_type_def]
  )
QED

Theorem tcexp_get_cases_NOTIN_monad_cns:
  tcexp_namespace_ok ns ∧
  tcexp_get_cases ns vt = SOME constructors ∧
  MEM cn (MAP FST constructors) ⇒
  explode cn ∉ monad_cns
Proof
  Cases_on `ns` >>
  rw[tcexp_get_cases_def]
  >- (
    gvs[MEM_MAP,tcexp_namespace_ok_def,ALL_DISTINCT_APPEND,
      PULL_EXISTS] >>
    strip_tac >>
    drule $ SRULE[SUBSET_DEF]
      monad_cns_SUBSET_reserved_cns_DELETE >>
    strip_tac >>
    last_x_assum $ drule_then drule >>
    simp[] >> metis_tac[]
  ) >>
  pairarg_tac >> gvs[] >>
  every_case_tac >> gvs[]
  >- (
    pairarg_tac >>
    gvs[MEM_MAP,tcexp_namespace_ok_def,ALL_DISTINCT_APPEND,
      PULL_EXISTS] >>
    strip_tac >>
    drule $ SRULE[SUBSET_DEF]
      monad_cns_SUBSET_reserved_cns_DELETE >>
    strip_tac >>
    gvs[DISJ_IMP_THM,PULL_EXISTS,FORALL_AND_THM] >>
    first_x_assum $ drule_then drule >>
    rw[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
    drule_then (irule_at Any) LLOOKUP_MEM >>
    simp[] >>
    metis_tac[]
  ) >>
  simp[monad_cns_def]
QED

Theorem type_soundness_up_to:
  ∀k ce ns db st t.
    tcexp_namespace_ok ns ∧
    EVERY (type_ok (SND ns) db) st ∧
    type_tcexp ns db st [] ce t
  ⇒ ∃wh. eval_wh_to k (exp_of ce) = wh ∧ type_wh ns db st [] wh t
Proof
  strip_tac >> completeInduct_on `k` >>
  recInduct exp_of_ind >> rw[exp_of_def]
  >~ [‘Var’]
  >- (last_x_assum kall_tac >> gvs[Once type_tcexp_cases])
  >~ [‘Prim’]
  >- (
    Cases_on `p` >> gvs[pure_cexpTheory.op_of_def]
    >- (
      simp[eval_wh_to_def, type_wh_cases, SF ETA_ss] >>
      irule_at Any EQ_REFL >>
      simp[]
      )
    >- (
      rgs[Once type_tcexp_cases] >> gvs[]
      >- (simp[Once type_wh_cases] >> simp[Once type_tcexp_cases]) >>
      imp_res_tac get_PrimTys_SOME >>
      gvs[eval_wh_to_def, MAP_MAP_o, combinTheory.o_DEF] >>
      IF_CASES_TAC >> gvs[]
      >- (
        qspec_then `xs` assume_tac $ GEN_ALL get_atoms_MAP_Diverge >>
        reverse $ Cases_on `xs` >> gvs[combinTheory.K_DEF]
        >- simp[type_wh_cases, type_ok] >>
        simp[get_atoms_def] >>
        qspecl_then [`[]`,`pt`,`a`,`[]`]
          assume_tac $ GEN_ALL eval_op_type_safe >> gvs[] >>
        Cases_on `pt = Bool` >> gvs[]
        >- (IF_CASES_TAC >> simp[type_wh_cases] >>
            simp[Once type_tcexp_cases, mlstringTheory.implode_def]) >>
        simp[type_wh_cases] >> simp[Once type_tcexp_cases, get_PrimTys_def] >>
        simp[type_atom_op_cases]
        ) >>
      CASE_TAC >> gvs[] >- simp[type_wh_cases, type_ok] >>
      CASE_TAC >> gvs[]
      >- (
        gvs[get_atoms_SOME_NONE_eq, EXISTS_MEM, LIST_REL_EL_EQN, EL_MAP, MEM_EL,
            PULL_EXISTS] >>
        first_x_assum drule >> strip_tac >>
        last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
        disch_then drule_all >> strip_tac >>
        qmatch_asmsub_abbrev_tac `type_wh _ _ _ _ atom` >>
        imp_res_tac type_atom_op_no_Bool >>
        drule type_wh_PrimTy_eq_wh_Atom >> gvs[MEM_EL] >>
        impl_tac >- (CCONTR_TAC >> gvs[]) >> rw[] >>
        pop_assum kall_tac >> first_x_assum $ qspec_then `n` assume_tac >> gvs[]
        ) >>
      gvs[get_atoms_SOME_SOME_eq] >> rename1 `MAP wh_Atom atoms` >>
      gvs[MAP_EQ_EVERY2] >>
      `LIST_REL type_lit atoms pts` by (
        gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
        ntac 2 (first_x_assum drule >> strip_tac) >>
        last_x_assum $ qspec_then `k - 1` assume_tac >> gvs[] >>
        pop_assum drule_all >> gvs[] >> simp[Once type_wh_cases] >>
        simp[Once type_tcexp_cases, get_PrimTys_def, type_atom_op_cases]) >>
      qspecl_then [`pts`,`pt`,`a`,`atoms`]
        assume_tac $ GEN_ALL eval_op_type_safe >> gvs[] >>
      Cases_on `pt = Bool` >> gvs[]
      >- (IF_CASES_TAC >>
          simp[type_wh_cases, Once type_tcexp_cases,
               mlstringTheory.implode_def]) >>
      simp[type_wh_cases] >>
      simp[Once type_tcexp_cases, get_PrimTys_def, type_atom_op_cases]
      )
    >- (
      pop_assum mp_tac >> simp[Once type_tcexp_cases] >> rw[] >>
      simp[eval_wh_to_def] >> reverse $ IF_CASES_TAC >> gvs[]
      >- (FULL_CASE_TAC >> gvs[])
      >- (
        simp[type_wh_cases] >>
        irule type_tcexp_type_ok >> simp[] >>
        rpt $ goal_assum $ drule_at Any >> simp[]
        ) >>
      FULL_CASE_TAC >> gvs[SF DNF_ss] >>
      spose_not_then kall_tac >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      last_x_assum $ irule_at $ Pat ‘type_tcexp _ _ _ _ _ _’ >>
      simp[] >>
      reverse conj_tac >- rw[type_wh_cases] >>
      gvs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
      rw[] >>
      first_x_assum drule >>
      simp[type_ok_def] >>
      strip_tac >>
      irule kind_ok_shift_db >>
      first_x_assum $ irule_at $ Pos last >>
      simp[miscTheory.LLOOKUP_THM,EL_APPEND_EQN])
    )
  >~ [‘Let’]
  >- (
    rgs[eval_wh_to_def] >> rw[]
    >- (
      simp[type_wh_cases] >> irule type_tcexp_type_ok >> simp[] >>
      rpt $ goal_assum $ drule_at Any >> simp[]
      ) >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >> rw[Once type_tcexp_cases] >>
    last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
    ntac 2 $ disch_then drule >>
    disch_then $ qspecl_then [`subst_tc1 v x y`,`t`] mp_tac >>
    simp[subst_exp_of, FMAP_MAP2_FUPDATE] >> impl_tac
    >- (irule type_tcexp_closing_subst1 >> simp[] >> goal_assum drule >> simp[]) >>
    simp[bind1_def, FMAP_MAP2_FEMPTY] >> IF_CASES_TAC >> gvs[] >>
    imp_res_tac type_tcexp_freevars_tcexp >> gvs[closed_def, freevars_exp_of] >>
    simp[FUN_FMAP_SING])
  >~ [‘Apps’]
  >- (
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >> rw[Once type_tcexp_cases] >>
    rename1 `Functions _ rt` >>
    qpat_x_assum `∀a. MEM a _ ⇒ _` kall_tac >> qpat_x_assum `_ ≠ _` kall_tac >>
    first_x_assum drule_all >> strip_tac >>
    pop_assum mp_tac >> qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    map_every qid_spec_tac [`f`,`t`,`rt`,`ts`] >>
    pop_assum mp_tac >> map_every qid_spec_tac [`arg_tys`,`xs`] >>
    ho_match_mp_tac LIST_REL_strongind >> rw[] >> gvs[Apps_def, Functions_def] >>
    first_x_assum $ qspecl_then [`rt`,`App f [h1]`] mp_tac >>
    simp[exp_of_def, Apps_def] >> disch_then irule >> rw[]
    >- (simp[Once type_tcexp_cases] >> simp[PULL_EXISTS] >>
        qexists_tac `h2` >> simp[Functions_def]) >>
    simp[eval_wh_to_def] >>
    drule_at (Pos last) type_tcexp_type_ok >> simp[type_ok] >> strip_tac >>
    IF_CASES_TAC >- simp[type_wh_cases,type_ok_def] >>
    imp_res_tac(type_wh_Function_eq_wh_Closure |> SIMP_RULE (srw_ss()) [cons_types_def]) >>
    gvs[] >>
    IF_CASES_TAC >- simp[type_wh_cases,type_ok_def] >>
    imp_res_tac type_tcexp_freevars_tcexp >> gvs[] >>
    rw[bind1_def, closed_def, freevars_exp_of] >>
    qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >>
    simp[Once type_wh_cases] >> strip_tac >> gvs[] >>
    pop_assum mp_tac >> simp[Once type_tcexp_cases] >> strip_tac >> gvs[] >>
    rename1 `ats ≠ []` >> Cases_on `ats` >> gvs[Functions_def] >>
    last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
    disch_then $ qspec_then `subst_tc1 (implode x) h1 ce` mp_tac >>
    simp[subst_exp_of, FMAP_MAP2_FUPDATE, FMAP_MAP2_FEMPTY, FUN_FMAP_SING] >>
    disch_then irule >> simp[] >>
    irule type_tcexp_closing_subst1 >> simp[] >>
    goal_assum drule >> simp[]
    )
  >- ( (* Lams *)
    imp_res_tac type_tcexp_tcexp_wf >> gvs[tcexp_wf_def] >>
    Cases_on `vs` >> gvs[Lams_def] >> simp[eval_wh_to_def] >>
    simp[Once type_wh_cases] >> rename1 `Lams (MAP explode hs)` >>
    Cases_on `hs` >> gvs[]
    >- (gvs[Lams_def] >> irule_at Any EQ_REFL >> simp[]) >>
    rename1 `v1::v2::vs` >>
    qexists_tac `Lam (v2::vs) x` >> simp[exp_of_def] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    simp[Once type_tcexp_cases] >> strip_tac >> gvs[] >>
    ntac 2 $ simp[Once type_tcexp_cases, PULL_EXISTS] >>
    qexistsl_tac [`[HD arg_tys]`,`TL arg_tys`,`ret_ty`] >>
    simp[Functions_def] >> simp[GSYM Functions_def] >>
    Cases_on `arg_tys` >> gvs[] >> Cases_on `t` >> gvs[]
    )
  >~ [‘Letrec’]
  >- (simp[eval_wh_to_def] >> rw[]
      >- (
       simp[type_wh_cases] >> irule type_tcexp_type_ok >> simp[] >>
       rpt $ goal_assum $ drule_at Any >> simp[]
       ) >>
      qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >> rw[Once type_tcexp_cases] >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      ntac 2 $ disch_then drule >>
      disch_then $ qspecl_then
                 [`subst_tc (FEMPTY |++ MAP (λ(g,x). (g, Letrec rs x)) rs) x`,`t`] mp_tac >>
      simp[subst_exp_of, FMAP_MAP2_FUPDATE_LIST, FMAP_MAP2_FEMPTY] >> impl_tac
      >- (
       irule type_tcexp_closing_subst >> simp[] >> goal_assum $ drule_at Any >>
       imp_res_tac LIST_REL_LENGTH >> simp[MAP_REVERSE, MAP_ZIP] >>
       simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >> rw[] >>
       gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
       pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
       simp[Once type_tcexp_cases] >>
       qexists ‘MAP (tshift_kind_scheme (LENGTH vars)) schemes’ >>
       gvs[MAP_REVERSE, MAP_ZIP_ALT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
       first_assum drule >>
       pop_assum (fn th => pop_assum (fn th' => rewrite_tac[th,th'])) >>
       simp[] >> strip_tac >>
       reverse $ rw[]
       >- (
         gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> rw[] >>
         first_x_assum drule >> rw[] >>
         gvs[type_ok_def] >>
         drule kind_ok_shift_db >>
         disch_then match_mp_tac >>
         simp[miscTheory.LLOOKUP_THM,EL_APPEND_EQN]
         ) >>
       rw[LIST_REL_EL_EQN, EL_MAP] >> rename1 `EL m _` >>
       qmatch_goalsub_abbrev_tac `_ a (_ b)` >>
       PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
       first_x_assum drule >> rw[] >> drule type_tcexp_shift_db >> simp[] >>
       disch_then drule >>
       disch_then $ qspecl_then [`vars`] mp_tac >>
       simp[MAP_REVERSE, MAP_ZIP_ALT, MAP_MAP_o, combinTheory.o_DEF] >>
       simp[GSYM shift_db_shift_db] >> rw[] >>
       irule quotientTheory.EQ_IMPLIES >> goal_assum drule >>
       rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> simp[LAMBDA_PROD]
       ) >>
      simp[bind_def, subst_funs_def] >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, exp_of_def] >>
      IF_CASES_TAC >> gvs[] >>
      gvs[FUN_FMAP_IMAGE, combinTheory.o_DEF, FUN_FMAP_DOM, o_f_FUDLIST_MAP]
      >- (qmatch_abbrev_tac ‘type_wh _ _ _ [] (eval_wh_to _ (subst fm1 tt)) uu ⇒
                             type_wh _ _ _ [] (eval_wh_to _ (subst fm2 tt)) uu’ >>
          ‘fm1 = fm2’suffices_by simp[] >>
          simp[Abbr‘fm1’, Abbr‘fm2’, exp_of_def, FUPDATE_LIST_MAP_f_o]) >>
      rename1 `false` >>
      gvs[flookup_fupdate_list] >> every_case_tac >> gvs[] >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >> pairarg_tac >> gvs[] >>
      gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, freevars_exp_of]
      >- (
       gvs[MEM_EL, LIST_REL_EL_EQN] >>
       qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >>
       first_x_assum drule >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
       imp_res_tac type_tcexp_freevars_tcexp >>
       gvs[ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
       gvs[SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD, MEM_ZIP] >>
       metis_tac[MEM_EL]
       )
      >- (
       pop_assum kall_tac >>
       gvs[EXISTS_MAP, EXISTS_MEM] >> pairarg_tac >> gvs[freevars_exp_of] >>
       gvs[MEM_EL, LIST_REL_EL_EQN] >>
       qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >>
       first_x_assum drule >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
       imp_res_tac type_tcexp_freevars_tcexp >>
       gvs[ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
       gvs[SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD, MEM_ZIP] >>
       metis_tac[MEM_EL]
       )
    )
  >~ [‘Case’]
  >- (
    drule type_tcexp_freevars_tcexp >> rw[] >>
    drule_at (Pos last) type_tcexp_type_ok >> rw[] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    rw[Once type_tcexp_cases] >> gvs[] >>
    Cases_on `eval_wh_to k (exp_of x) = wh_Diverge`
    >- (
      drule_at Any eval_wh_to_Case_wh_Diverge >>
      gvs[closed_def, freevars_exp_of] >>
      disch_then $ qspecl_then [`v`,`rs`, ‘eopt’] mp_tac >>
      impl_tac
      >- (
        (drule_then $ drule_then assume_tac)
          tcexp_get_cases_NOT_EMPTY >>
        Cases_on `rs` >> gvs[] >>
        Cases_on `eopt` >> gvs[] >>
        metis_tac[PAIR]
      ) >>
      rw[exp_of_def, type_wh_cases]
    ) >>
    first_x_assum $ drule_all_then assume_tac >>
    drule_all type_wh_tcexp_get_cases_eq_wh_constructor >>
    rw[] >> gvs[] >>
    drule_then drule tcexp_get_cases_NOTIN_monad_cns >>
    `MEM (implode cn) $ MAP FST constructors`
    by (
      simp[MEM_MAP] >>
      drule_then (irule_at Any) ALOOKUP_MEM >>
      simp[]
    ) >>
    disch_then $ drule_then assume_tac >>
    qpat_x_assum `type_wh _ _ _ _ (wh_Constructor _ _) _` $
      strip_assume_tac o SRULE[Once type_wh_cases] >>
    (drule_then $ drule_then assume_tac)
      tcexp_prim_cons_length_eq >>
    `∃cn'. cn = explode cn'` by
      metis_tac[mlstringTheory.explode_implode]>>
    gvs[] >>
    Cases_on `ALOOKUP rs cn'`
    >- (
      drule eval_wh_to_Case_catchall >>
      simp[closed_def,freevars_exp_of] >>
      disch_then drule >>
      disch_then $ qspecl_then [`v`,`eopt`] mp_tac >>
      rw[]
      >- (
        gvs[exp_of_def] >>
        simp[Once type_wh_cases]
      ) >>
      gvs[exp_of_def] >>
      Cases_on `eopt` >>
      gvs[]
      >- gvs[EXTENSION,ALOOKUP_NONE] >>
      CASE_TAC >>
      gvs[] >>
      CASE_TAC >> gvs[]
      >- (
        gvs[EXTENSION,ALOOKUP_NONE,EQ_IMP_THM,FORALL_AND_THM] >>
        qpat_x_assum `∀x. MEM x (MAP FST constructors) ⇒ _` drule >>
        rw[]
      ) >>
      imp_res_tac ALOOKUP_MEM >>
      drule_then drule $ iffLR EVERY_MEM >>
      rw[] >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      ntac 2 $ disch_then drule >>
      rename [`subst1 (explode v) (exp_of x) (exp_of us_e)`] >>
      disch_then $ qspec_then `subst_tc1 v x us_e` mp_tac >>
      simp[subst_exp_of, FUN_FMAP_SING] >> disch_then irule >> simp[] >>
      irule type_tcexp_closing_subst1 >> simp[] >>
      goal_assum $ drule_at Any >> simp[]
    ) >>
    rename1 `ALOOKUP _ cn' = SOME ce` >>
    PairCases_on `ce` >>
    drule eval_wh_to_Case >>
    simp[closed_def,freevars_exp_of] >>
    disch_then drule >>
    drule_then assume_tac ALOOKUP_MEM >>
    drule_then drule $ iffLR EVERY_MEM >>
    simp[] >> strip_tac >>
    disch_then drule >>
    first_x_assum $ drule_then assume_tac >>
    imp_res_tac LIST_REL_LENGTH >>
    simp[] >>
    disch_then $ qspec_then `eopt` strip_assume_tac >>
    gvs[exp_of_def]
    >- simp[Once type_wh_cases] >>
    DEP_REWRITE_TAC[GSYM subst_subst1_UPDATE] >>
    simp[closed_def, freevars_exp_of] >>
    DEP_ONCE_REWRITE_TAC[GSYM FUPDATE_FUPDATE_LIST_COMMUTES] >>
    simp[combinTheory.o_DEF, GSYM FUPDATE_LIST_THM] >>
    simp[MEM_MAP] >>
    last_x_assum $ qspec_then `k - 1` mp_tac >>
    simp[] >>
    disch_then $ drule_then drule >>
    disch_then $ qspec_then
      `subst_tc (FEMPTY |++ ((v,x)::
        (MAPi
          (λi v. (v, SafeProj (cn') (LENGTH ces') i x))
          ce0))) ce1`
      mp_tac >>
    simp[subst_exp_of, FUN_FMAP_IMAGE, exp_of_def,
      combinTheory.o_DEF, FUN_FMAP_DOM, o_f_FUPDATE_LIST,
      FUPDATE_LIST_f_o_implode, FUPDATE_LIST_THM,
      FUPDATE_f_o_implode] >>
    imp_res_tac LIST_REL_LENGTH >> gvs[] >>
    disch_then irule >> simp[] >>
    simp[GSYM FUPDATE_LIST_THM] >>
    imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM] >>
    first_x_assum drule >> simp[] >> strip_tac >>
    irule type_tcexp_closing_subst >> rpt $ goal_assum $ drule_at Any >>
    simp[MAP_REVERSE, MAP_ZIP, combinTheory.o_DEF, MAP_MAP_o] >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    first_x_assum drule >> strip_tac >>
    simp[Once type_tcexp_cases] >>
    rpt $ goal_assum $ drule_at Any >> simp[oEL_THM]
   )
  >~ [‘NestedCase’]
  >- (
    drule type_tcexp_freevars_tcexp >> rw[] >>
    drule_at (Pos last) type_tcexp_type_ok >> rw[] >>
    qpat_x_assum `type_tcexp _ _ _ _ (NestedCase _ _ _ _ _) _` $
      strip_assume_tac o SRULE[Once type_tcexp_cases] >>
    cheat
     )
  >~ [‘SafeProj’]
  >- ( (* SafeProj *)
    drule type_tcexp_freevars_tcexp >> rw[] >>
    drule_at (Pos last) type_tcexp_type_ok >> rw[] >>
    gvs[eval_wh_to_def] >> rw[] >- simp[type_wh_cases] >>
    simp[eval_wh_to_def] >> IF_CASES_TAC >> gvs[] >- simp[type_wh_cases] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >> rw[Once type_tcexp_cases] >>
    reverse PURE_CASE_TAC
    >- (rw[] >> rw[type_wh_cases])
    >- (rw[] >> rw[type_wh_cases] >>
        last_x_assum $ qspec_then ‘k-2’ mp_tac >>
        simp[] >>
        ntac 3 $ first_x_assum $ irule_at $ Pos hd >>
        simp[] >>
        rw[type_wh_cases])
    >- (rw[] >> rw[type_wh_cases] >>
        ‘eval_wh_to k (exp_of e) = wh_Atom l’
          by metis_tac[eval_wh_inc,wh_distinct,DECIDE “k-2 ≤ (k:num)”] >>
        first_x_assum drule >>
        rpt $ disch_then drule >>
        strip_tac >>
        gvs[] >>
        pop_assum mp_tac >>
        rw[type_wh_cases] >>
        rw[Once type_tcexp_cases] >>
        gvs[oneline tcexp_destruct_type_cons_def] >>
        rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
        gvs[split_ty_cons_def,split_ty_cons_aux_def])
    >- (rw[] >> rw[type_wh_cases] >>
        ‘eval_wh_to k (exp_of e) = wh_Closure s e'’
          by metis_tac[eval_wh_inc,wh_distinct,DECIDE “k-2 ≤ (k:num)”] >>
        first_x_assum drule >>
        rpt $ disch_then drule >>
        strip_tac >>
        gvs[] >>
        pop_assum mp_tac >>
        rw[type_wh_cases] >>
        rw[Once type_tcexp_cases] >>
        gvs[oneline tcexp_destruct_type_cons_def] >>
        rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
        gvs[quantHeuristicsTheory.LIST_LENGTH_1,Functions_def] >>
        gvs[split_ty_cons_def,split_ty_cons_aux_def]
       ) >>
    simp[] >>
    ‘eval_wh_to k (exp_of e) = wh_Constructor s l’
      by metis_tac[eval_wh_inc,wh_distinct,DECIDE “k-2 ≤ (k:num)”] >>
    first_x_assum drule >>
    rpt $ disch_then drule >>
    simp[] >>
    simp[Once type_wh_cases] >>
    strip_tac >>
    gvs[] >>
    drule tcexp_prim_cons_not_monad_cns >>
    rpt $ disch_then drule >>
    strip_tac >> simp[] >>
    IF_CASES_TAC
    >- (simp[eval_wh_to_Bottom] >>
        rw[Once type_wh_cases]) >>
    gvs[] >>
    imp_res_tac tcexp_prim_cons_length_eq >>
    gvs[] >>
    simp[EL_MAP] >>
    first_x_assum irule >>
    simp[] >>
    qhdtm_x_assum ‘type_tcexp’ mp_tac >>
    rw[Once type_tcexp_cases] >>
    gvs[monad_cns_def]
    >- (gvs[oneline tcexp_destruct_type_cons_def] >>
        gvs[cons_types_EQ_Atom] >>
        PURE_FULL_CASE_TAC >> gvs[] >>
        gvs[split_ty_cons_thm,ty_args_alt,
            head_ty_cons_cons_types,head_ty_cons_def,
            ty_args_cons_types,specialises_def,
            EL_MAP
           ] >>
        gvs[LIST_REL_EL_EQN] >>
        first_x_assum drule)
    >- (gvs[type_exception_def] >>
        gvs[oneline tcexp_destruct_type_cons_def] >>
        gvs[cons_types_EQ_Atom] >>
        PURE_FULL_CASE_TAC >> gvs[] >>
        gvs[type_exception_def] >>
        gvs[oneline specialises_def] >>
        PURE_FULL_CASE_TAC >> gvs[] >>
        gvs[LIST_REL_EL_EQN] >>
        first_x_assum drule >>
        gvs[EL_MAP] >>
        strip_tac >>
        gvs[EVERY_EL] >>
        last_x_assum drule >>
        simp[] >>
        strip_tac >>
        gvs[]) >>
    gvs[tcexp_type_cons_def] >>
    gvs[tcons_to_type_def] >>
    gvs[oneline tcexp_destruct_type_cons_def] >>
    gvs[cons_types_EQ_Atom] >>
    PURE_FULL_CASE_TAC >> gvs[] >>
    gvs[split_ty_cons_thm,ty_args_alt,
        head_ty_cons_cons_types,head_ty_cons_def,
        ty_args_cons_types,specialises_def,
        EL_MAP] >>
    gvs[tcexp_type_cons_def] >>
    gvs[EL_MAP] >>
    imp_res_tac LIST_REL_LENGTH >>
    fs[LENGTH_MAP] >>
    gvs[oneline specialises_def] >>
    pairarg_tac >> gvs[] >>
    gvs[LIST_REL_EL_EQN] >>
    first_x_assum drule >>
    simp[EL_MAP] >>
    strip_tac >>
    drule type_tcexp_subst_db >>
    disch_then drule >>
    simp[] >>
    disch_then $ qspec_then ‘[]’ mp_tac >>
    simp[] >>
    disch_then $ qspecl_then [‘ks’,‘db’,‘subs’] mp_tac >>
    simp[] >>
    impl_tac >- rw[LIST_REL_EL_EQN] >>
    simp[MAP_MAP_o,combinTheory.o_DEF] >>
    simp[tsubst_tshift])
QED

Theorem type_soundness_eval_wh:
  tcexp_namespace_ok ns ∧
  EVERY (type_ok (SND ns) db) st ∧
  type_tcexp ns db st [] ce t ⇒
  type_wh ns db st [] (eval_wh $ exp_of ce) t
Proof
  rw[] >> drule_all type_soundness_up_to >> strip_tac >>
  rw[eval_wh_def] >> DEEP_INTRO_TAC some_intro >> rw[] >> gvs[]
QED


(********************)


Theorem type_wh_monad:
  type_wh ns db st env wh (Monad t) ⇒
  wh = wh_Diverge ∨
  ∃cn es. wh = wh_Constructor cn es ∧ cn ∈ monad_cns
Proof
  rw[type_wh_cases] >>
  gvs[Once type_tcexp_cases, monad_cns_def, implodeEQ,
    Monad_cons_types,cons_types_Atom_EQ,cons_types_EQ_Atom,
    tcons_to_type_def] >>
  Cases_on `arg_tys` >>
  gvs[Functions_cons_types,cons_types_Atom_EQ]
QED

Definition type_exp_def:
  type_exp ns db st e t ⇔
    ∃tce. type_tcexp ns db st [] tce t ∧ exp_of tce = e
End

Datatype:
  cont_type = DoneT
            | BCT type type cont_type (* arg type, return type *)
            | HCT type cont_type      (* return type *)
End

Definition unwind_stack_def:
  unwind_stack DoneT = NONE ∧
  unwind_stack (BCT t1 t2 stack) = unwind_stack stack ∧
  unwind_stack (HCT t stack) = SOME (t, stack)
End

Inductive type_cont:
  type_cont ns db st Done DoneT ∧

  (type_exp ns db st cont
    (cons_types (Atom $ CompPrimTy Function) [t1;Monad t2]) ∧
   type_cont ns db st stack t ⇒
    type_cont ns db st (BC cont stack) (BCT t1 t2 t)) ∧

  (type_exp ns db st cont
    (cons_types (Atom $ CompPrimTy Function)
      [Atom Exception;Monad t1]) ∧
   type_cont ns db st stack t ⇒
    type_cont ns db st (HC cont stack) (HCT t1 t))
End

Inductive config_type_ok:
  config_type_ok (t, DoneT) t ∧

  (config_type_ok (t2, stack) t ∧
   (∀t3 stack'.
    unwind_stack stack = SOME (t3, stack') ⇒ config_type_ok (t3, stack') t) ⇒
      config_type_ok (t1, BCT t1 t2 stack) t) ∧

   (config_type_ok (t2, stack) t ∧
    config_type_ok (t1, stack) t ⇒
      config_type_ok (t1, HCT t2 stack) t)
End

Definition type_config_def:
  type_config ns db st (wh, stack, state) t ⇔
    ∃wh_ty stack_ty.
      LIST_REL (λes t. EVERY (λe. type_exp ns db st e t) es) state st ∧
      type_wh ns db st [] wh (Monad wh_ty) ∧
      type_cont ns db st stack stack_ty ∧
      config_type_ok (wh_ty, stack_ty) t
End

Inductive type_next_res:
  type_next_res ns db st Ret t ∧
  type_next_res ns db st Div t ∧
  ((∀y. type_config ns db st (wh_Constructor "Ret" [Lit $ Str y], stack, state) t) ⇒
    type_next_res ns db st (pure_semantics$Act a stack state) t)
End

Theorem config_type_ok_unwind_stack:
  ∀stack_ty wh_ty t.
    config_type_ok (wh_ty, stack_ty) t ⇒
  ∀t' s'. unwind_stack stack_ty = SOME (t',s') ⇒ config_type_ok (t',s') t
Proof
  Induct >> rw[unwind_stack_def]
  >- (
    first_x_assum irule >> simp[] >>
    qpat_x_assum `config_type_ok _ _` mp_tac >>
    once_rewrite_tac[config_type_ok_cases] >>
    strip_tac >> once_rewrite_tac[GSYM config_type_ok_cases] >> gvs[] >>
    goal_assum drule
    )
  >- (
    pop_assum mp_tac >>
    once_rewrite_tac[config_type_ok_cases] >>
    strip_tac >> once_rewrite_tac[GSYM config_type_ok_cases] >> gvs[]
    )
QED

Theorem type_cont_weaken_state:
  type_cont ns db st stack stack_ty ⇒
  type_cont ns db (st ++ st') stack stack_ty
Proof
  Induct_on `type_cont` >> rw[] >> simp[Once type_cont_cases] >>
  gvs[type_exp_def] >> irule_at Any EQ_REFL >>
  drule type_tcexp_weaken >>
  disch_then $ qspecl_then [`[]`,`st'`,`[]`] mp_tac >> simp[]
QED

Theorem type_soundness_next:
  ∀k st wh stack state t.
    tcexp_namespace_ok ns ∧ EVERY (type_ok (SND ns) db) st ∧
    type_config ns db st (wh, stack, state) t
  ⇒ ∃st'.
    type_next_res ns db (st ++ st') (next k wh stack state) t ∧
    EVERY (type_ok (SND ns) db) st'
Proof
  strip_tac >> completeInduct_on `k` >> rw[] >>
  last_x_assum $ qspec_then `k - 1` assume_tac >> gvs[] >>
  qpat_x_assum `type_config _ _ _ _ _` mp_tac >> rw[Once type_config_def] >>
  imp_res_tac type_wh_monad >> rgs[]
  >- (simp[next_def, type_next_res_cases] >> goal_assum drule) >>
  qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >> simp[type_wh_cases] >>
  simp[Once type_tcexp_cases] >> strip_tac >> rgs[monad_cns_def, implodeEQ] >>
  once_rewrite_tac[next_def] >> simp[]
  >- (
    TOP_CASE_TAC >> rgs [] \\ gvs []
    >- (simp[type_next_res_cases] >> goal_assum drule)
    >- (
      gvs[Once type_cont_cases, apply_closure_def, type_exp_def] >>
      IF_CASES_TAC >- (simp[type_next_res_cases] >> goal_assum drule) >>
      drule_all type_soundness_eval_wh >> strip_tac >>
      drule type_wh_Function_eq_wh_Closure >> rw[] >> simp[] >>
      IF_CASES_TAC >> gvs[] >- (simp[type_next_res_cases] >> goal_assum drule) >>
      last_x_assum drule >> disch_then irule >>
      simp[type_config_def, type_exp_def] >> goal_assum $ drule_at Any >>
      qpat_x_assum `config_type_ok _ _` mp_tac >>
      simp[Once config_type_ok_cases] >> strip_tac >> gvs[] >>
      goal_assum $ drule_at Any >>
      qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >> simp[Once type_wh_cases] >>
      strip_tac >> gvs[] >> pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      Cases_on `arg_tys` >> gvs[Functions_def] >>
      `closed (exp_of e)` by (
        imp_res_tac type_tcexp_freevars_tcexp >>
        gvs[closed_def, freevars_exp_of]) >>
      simp[bind1_def] >>
      drule type_tcexp_closing_subst1 >> simp[] >>
      gvs[cons_types_def] >>
      disch_then drule >> strip_tac >>
      drule_at (Pos last) type_soundness_eval_wh >>
      simp[subst_exp_of, FUN_FMAP_SING]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (simp[type_next_res_cases] >> goal_assum drule) >>
      first_x_assum irule >> simp[type_config_def] >>
      qpat_x_assum `type_cont _ _ _ _ _` mp_tac >> rw[Once type_cont_cases] >>
      goal_assum $ drule_at Any >>
      qpat_x_assum `config_type_ok _ _` mp_tac >> rw[Once config_type_ok_cases] >>
      goal_assum $ drule_at Any >>
      simp[type_wh_cases, PULL_EXISTS] >> irule_at Any EQ_REFL >>
      simp[Once type_tcexp_cases, implodeEQ]
      )
    )
  >- (
    IF_CASES_TAC >> gvs[] >- (simp[type_next_res_cases] >> goal_assum drule) >>
    first_x_assum irule >> simp[type_config_def] >>
    qexistsl_tac [`t1`,`BCT t1 wh_ty stack_ty`] >>
    simp[Once type_cont_cases, type_exp_def, PULL_EXISTS, GSYM CONJ_ASSOC] >>
    fs[Functions_cons_types] >>
    goal_assum $ drule_at Any >> simp[] >>
    irule_at Any type_soundness_eval_wh >> simp[] >>
    simp[Once config_type_ok_cases] >>
    ho_match_mp_tac config_type_ok_unwind_stack >> goal_assum drule
    )
  >- (
    TOP_CASE_TAC >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule)
    >- (
      IF_CASES_TAC >> gvs[] >- (simp[type_next_res_cases] >> goal_assum drule) >>
      first_x_assum irule >> simp[type_config_def] >>
      qpat_x_assum `type_cont _ _ _ _ _` mp_tac >> rw[Once type_cont_cases] >>
      goal_assum $ drule_at Any >>
      qpat_x_assum `config_type_ok _ _` mp_tac >>
      simp[Once config_type_ok_cases] >> strip_tac >> gvs[] >>
      goal_assum $ drule_at Any >>
      simp[type_wh_cases, PULL_EXISTS] >> irule_at Any EQ_REFL >>
      simp[Once type_tcexp_cases] >> gvs[type_exp_def] >>
      drule_at Any type_tcexp_type_ok >>
      gvs[type_ok, mlstringTheory.implode_def] >>
      simp[kind_ok_cons_types,PULL_EXISTS,kind_ok]
      )
    >- (
      gvs[Once type_cont_cases, apply_closure_def, type_exp_def] >>
      IF_CASES_TAC >- (simp[type_next_res_cases] >> goal_assum drule) >>
      drule_all type_soundness_eval_wh >> strip_tac >>
      drule type_wh_Function_eq_wh_Closure >> rw[] >> simp[] >>
      IF_CASES_TAC >> gvs[] >- (simp[type_next_res_cases] >> goal_assum drule) >>
      last_x_assum drule >> disch_then irule >>
      simp[type_config_def, type_exp_def] >> goal_assum $ drule_at Any >>
      qpat_x_assum `config_type_ok _ _` mp_tac >>
      simp[Once config_type_ok_cases] >> strip_tac >> gvs[] >>
      qexists_tac `t1` >> simp[] >>
      qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >> simp[Once type_wh_cases] >>
      strip_tac >> gvs[] >> pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      Cases_on `arg_tys` >> gvs[Functions_cons_types] >>
      `closed (exp_of e)` by (
        imp_res_tac type_tcexp_freevars_tcexp >>
        gvs[closed_def, freevars_exp_of]) >>
      simp[bind1_def] >>
      drule type_tcexp_closing_subst1 >> simp[] >>
      gvs[cons_types_Atom_EQ] >>
      disch_then drule >> strip_tac >>
      drule_at (Pos last) type_soundness_eval_wh >>
      simp[subst_exp_of, FUN_FMAP_SING]
      )
    )
  >- (
    IF_CASES_TAC >> gvs[] >- (simp[type_next_res_cases] >> goal_assum drule) >>
    first_x_assum irule >> simp[type_config_def] >>
    qexistsl_tac [`wh_ty`,`HCT wh_ty stack_ty`] >>
    simp[Once type_cont_cases, Once config_type_ok_cases] >>
    simp[type_exp_def, PULL_EXISTS] >>
    fs[Functions_cons_types] >>
    goal_assum $ drule_at Any >> simp[] >>
    irule type_soundness_eval_wh >> simp[]
    )
  >- (
    drule_at (Pos last) type_soundness_eval_wh >> rw[] >>
    drule type_wh_PrimTy_eq_wh_Atom >> simp[] >>
    simp[with_atom_def, with_atoms_def] >> strip_tac >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule) >>
    simp[pure_semanticsTheory.get_atoms_def] >> gvs[type_wh_cases] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    simp[Once type_tcexp_cases, get_PrimTys_def, type_atom_op_cases, type_lit_cases] >>
    strip_tac >> gvs[] >> qexists_tac `[]` >> simp[] >>
    rw[type_next_res_cases] >> simp[type_config_def] >>
    goal_assum $ drule_at Any >> simp[type_wh_cases, PULL_EXISTS] >>
    qexists_tac `Prim (AtomOp $ Lit $ Str y) []` >>
    simp[exp_of_def, pure_cexpTheory.op_of_def] >>
    simp[Once type_tcexp_cases,mlstringTheory.implode_def] >>
    disj1_tac >>
    simp[Once type_tcexp_cases,get_PrimTys_def,
      type_atom_op_cases,type_lit_cases]
    )
  >- (
    qpat_x_assum `_ (Atom _)` assume_tac >>
    drule_at (Pos last) type_soundness_eval_wh >> rw[] >>
    drule type_wh_PrimTy_eq_wh_Atom >> simp[] >>
    simp[with_atom_def, with_atoms_def] >> strip_tac >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule) >>
    simp[pure_semanticsTheory.get_atoms_def] >> gvs[type_wh_cases] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    simp[Once type_tcexp_cases, get_PrimTys_def, type_atom_op_cases, type_lit_cases] >>
    strip_tac >> gvs[] >> IF_CASES_TAC >> gvs[]
    >- (qexists_tac `[]` >> simp[type_next_res_cases]) >>
    Q.REFINE_EXISTS_TAC `[t'] ++ rest` >> simp[] >>
    `type_ok (SND ns) db t'` by (
      irule type_tcexp_type_ok >> simp[] >>
      goal_assum $ drule_at $ Pos last >> simp[]) >>
    simp[] >> first_x_assum irule >> simp[type_config_def, GSYM CONJ_ASSOC] >>
    irule_at Any type_cont_weaken_state >> goal_assum drule >>
    goal_assum $ drule_at Any >> conj_tac
    >- (
      gvs[LIST_REL_EL_EQN, EVERY_MEM] >> rw[] >>
      last_x_assum drule_all >> strip_tac >> gvs[type_exp_def] >>
      irule_at Any EQ_REFL >> drule type_tcexp_weaken >>
      disch_then $ qspecl_then [`[]`,`[t']`,`[]`] mp_tac >> simp[]
      ) >>
    simp[type_wh_cases, Once type_tcexp_cases, PULL_EXISTS,
         mlstringTheory.implode_def] >>
    qexists_tac `Prim (AtomOp $ Lit $ Loc $ LENGTH state) []` >>
    simp[exp_of_def, pure_cexpTheory.op_of_def] >>
    simp[Once type_tcexp_cases, oEL_THM, EL_APPEND_EQN] >>
    imp_res_tac LIST_REL_LENGTH >> gvs[] >>
    IF_CASES_TAC >> gvs[] >> rw[DISJ_EQ_IMP] >>
    simp[type_exp_def] >> irule_at Any EQ_REFL >>
    qpat_x_assum `_ e2 t'` assume_tac >> drule type_tcexp_weaken >>
    disch_then $ qspecl_then [`[]`,`[t']`,`[]`] mp_tac >> simp[]
    )
  >- (
    drule_at (Pos last) type_soundness_eval_wh >> rw[] >>
    drule type_wh_Array_eq_Loc >> simp[] >>
    simp[with_atom_def, with_atoms_def] >> strip_tac >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule) >>
    simp[pure_semanticsTheory.get_atoms_def] >> gvs[type_wh_cases, oEL_THM] >>
    imp_res_tac LIST_REL_LENGTH >> gvs[] >>
    IF_CASES_TAC >> gvs[] >- (simp[type_next_res_cases] >> goal_assum drule) >>
    first_x_assum irule >> simp[type_config_def] >>
    simp[type_wh_cases, PULL_EXISTS, GSYM CONJ_ASSOC] >>
    goal_assum $ drule_at Any >> simp[] >>
    qmatch_goalsub_abbrev_tac `Lit a` >>
    qexists_tac `Prim (AtomOp $ Lit a) []` >>
    simp[exp_of_def, pure_cexpTheory.op_of_def] >>
    simp[Once type_tcexp_cases,type_atom_op_cases,
      mlstringTheory.implode_def] >>
    unabbrev_all_tac >>
    simp[Once type_tcexp_cases,get_PrimTys_def,
      type_atom_op_cases,type_lit_cases]
    )
  >- (
    drule_at (Pos last) type_soundness_eval_wh >> simp[] >> strip_tac >>
    drule type_wh_PrimTy_eq_wh_Atom >> simp[] >>
    qpat_x_assum `type_tcexp _ _ _ _ e1 _` assume_tac >>
    drule_at (Pos last) type_soundness_eval_wh >> simp[] >> strip_tac >>
    drule type_wh_Array_eq_Loc >> simp[] >>
    simp[with_atom2_def, with_atoms_def] >> ntac 2 strip_tac >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule)
    >- (simp[type_next_res_cases] >> goal_assum drule)
    >- (simp[type_next_res_cases] >> goal_assum drule) >>
    simp[pure_semanticsTheory.get_atoms_def] >> gvs[type_wh_cases, oEL_THM] >>
    imp_res_tac LIST_REL_LENGTH >> gvs[] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ (Atom $ PrimTy _)` mp_tac >>
    simp[Once type_tcexp_cases, get_PrimTys_def, type_atom_op_cases, type_lit_cases] >>
    strip_tac >> gvs[] >>
    Cases_on `k = 0` >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule) >>
    IF_CASES_TAC >> gvs[]
    >- (
      first_x_assum irule >> simp[type_config_def] >>
      goal_assum $ drule_at Any >> simp[] >>
      simp[type_wh_cases, PULL_EXISTS] >>
      gvs[LIST_REL_EL_EQN] >>
      last_x_assum drule >> simp[EVERY_EL, type_exp_def] >>
      disch_then $ qspec_then `Num i` mp_tac >> simp[] >> impl_tac
      >- (Cases_on `i` >> gvs[]) >>
      strip_tac >> gvs[] >>
      goal_assum $ drule o GSYM >>
      simp[Once type_tcexp_cases, mlstringTheory.implode_def]
      ) >>
    first_x_assum irule >> simp[type_config_def] >>
    goal_assum $ drule_at Any >> simp[] >>
    simp[type_wh_cases, PULL_EXISTS] >>
    qexists_tac `Prim (Cons «Subscript») []` >>
    simp[exp_of_def, pure_cexpTheory.op_of_def] >>
    ntac 2 $ simp[Once type_tcexp_cases, mlstringTheory.implode_def] >>
    gvs[EVERY_EL, mlstringTheory.implode_def] >>
    drule type_exception_Subscript >> PairCases_on `ns` >>
    gvs[]
    )
  >- (
    qpat_x_assum `type_tcexp _ _ _ _ e2 _` assume_tac >>
    drule_at (Pos last) type_soundness_eval_wh >> simp[] >> strip_tac >>
    drule type_wh_PrimTy_eq_wh_Atom >> simp[] >>
    qpat_x_assum `type_tcexp _ _ _ _ e1 _` assume_tac >>
    drule_at (Pos last) type_soundness_eval_wh >> simp[] >> strip_tac >>
    drule type_wh_Array_eq_Loc >> simp[] >>
    simp[with_atom2_def, with_atoms_def] >> ntac 2 strip_tac >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule)
    >- (simp[type_next_res_cases] >> goal_assum drule)
    >- (simp[type_next_res_cases] >> goal_assum drule) >>
    simp[pure_semanticsTheory.get_atoms_def] >> gvs[type_wh_cases, oEL_THM] >>
    imp_res_tac LIST_REL_LENGTH >> gvs[] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ (Atom $ PrimTy _)` mp_tac >>
    simp[Once type_tcexp_cases, get_PrimTys_def, type_atom_op_cases, type_lit_cases] >>
    strip_tac >> gvs[] >>
    Cases_on `k = 0` >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule) >>
    IF_CASES_TAC >> gvs[]
    >- (
      first_x_assum irule >> simp[type_config_def] >>
      goal_assum $ drule_at Any >> simp[] >>
      simp[type_wh_cases, PULL_EXISTS] >>
      qexists_tac `Prim (Cons «») []` >>
      simp[exp_of_def, pure_cexpTheory.op_of_def, mlstringTheory.implode_def] >>
      ntac 2 $ simp[Once type_tcexp_cases] >>
      gvs[LIST_REL_EL_EQN, EVERY_EL] >>
      rw[EL_LUPDATE,cons_types_def] >>
      IF_CASES_TAC >> gvs[EL_LUPDATE] >>
      simp[type_exp_def] >>
      goal_assum drule >> simp[]
      ) >>
    first_x_assum irule >> simp[type_config_def] >>
    goal_assum $ drule_at Any >> simp[] >>
    simp[type_wh_cases, PULL_EXISTS] >>
    qexists_tac `Prim (Cons «Subscript») []` >>
    simp[exp_of_def, pure_cexpTheory.op_of_def] >>
    ntac 2 $ simp[Once type_tcexp_cases, type_ok, mlstringTheory.implode_def] >>
    drule type_exception_Subscript >> PairCases_on `ns` >>
    gvs[kind_arrows_def]
    )
  >> gvs[Monad_cons_types,tcons_to_type_def,cons_types_Atom_EQ]
QED

Theorem type_soundness_next_action:
  ∀ns db st wh stack state t.
    tcexp_namespace_ok ns ∧ EVERY (type_ok (SND ns) db) st ∧
    type_config ns db st (wh, stack, state) t
  ⇒ ∃st'.
      type_next_res ns db (st ++ st') (next_action wh stack state) t ∧
      EVERY (type_ok (SND ns) db) st'
Proof
  rw[next_action_def] >>
  DEEP_INTRO_TAC some_intro >> reverse $ rw[]
  >- (simp[type_next_res_cases] >> goal_assum drule) >>
  drule_all type_soundness_next >> simp[]
QED

Theorem type_soundness_interp:
  ∀ns db st wh stack state t.
    tcexp_namespace_ok ns ∧ EVERY (type_ok (SND ns) db) st ∧
    type_config ns db st (wh, stack, state) t
  ⇒ safe_itree (interp wh stack state)
Proof
  qsuff_tac
    `∀tree.
      (∃ns db st wh stack state t.
      (tcexp_namespace_ok ns ∧ EVERY (type_ok (SND ns) db) st ∧
      type_config ns db st (wh, stack, state) t ∧
      tree = interp wh stack state)) ∨ (∃e f. tree = Ret (FinalFFI e f))
    ⇒ safe_itree tree`
  >- (
    rw[] >> first_x_assum irule >> disj1_tac >>
    rpt $ goal_assum drule >> simp[]
    ) >>
  ho_match_mp_tac safe_itree_coind >> rw[] >>
  drule_all type_soundness_next_action >>
  simp[Once type_next_res_cases] >> strip_tac >> gvs[]
  >- (once_rewrite_tac[interp_def] >> simp[])
  >- (once_rewrite_tac[interp_def] >> simp[]) >>
  ntac 3 disj2_tac >> rw[Once interp_def] >>
  CASE_TAC >> gvs[] >> IF_CASES_TAC >> gvs[] >> disj1_tac >>
  goal_assum drule >> irule_at Any $ EQ_REFL >>
  first_x_assum $ qspec_then `y` assume_tac >>
  goal_assum $ drule_at $ Pos last >> simp[]
QED

Theorem type_soundness_tcexp:
  tcexp_namespace_ok ns ∧ type_tcexp ns db [] [] tce (Monad t) ⇒
  safe_itree (itree_of (exp_of tce))
Proof
  rw[itree_of_def, semantics_def] >>
  irule type_soundness_interp >>
  simp[type_config_def, PULL_EXISTS] >>
  simp[Once type_cont_cases, Once config_type_ok_cases] >>
  goal_assum drule >>
  irule_at Any type_soundness_eval_wh >> simp[] >>
  goal_assum drule
QED

Theorem type_soundness_cexp:
  tcexp_namespace_ok ns ∧ type_tcexp ns db [] [] (tcexp_of ce) (Monad t) ⇒
  safe_itree (itree_of (exp_of ce))
Proof
  rw[] >>
  `itree_of (exp_of ce) = itree_of (exp_of $ tcexp_of ce)` by (
    rw[itree_of_def] >>
    irule pure_obs_sem_equalTheory.bisimilarity_IMP_semantics_eq >>
    simp[pure_exp_relTheory.app_bisimilarity_eq] >>
    irule_at Any $ iffLR pure_congruenceTheory.exp_eq_sym >>
    irule_at Any exp_of_tcexp_of_exp_eq >>
    drule type_tcexp_freevars_tcexp >> strip_tac >>
    drule_at (Pos last) type_tcexp_tcexp_wf >> strip_tac >> gvs[] >>
    simp[closed_def, freevars_exp_of] >>
    gvs[freevars_tcexp_of, pure_tcexp_lemmasTheory.freevars_exp_of,
        pure_cexp_lemmasTheory.freevars_exp_of]
    ) >>
  rw[itree_of_def, semantics_def] >>
  irule type_soundness_interp >>
  simp[type_config_def, PULL_EXISTS] >>
  simp[Once type_cont_cases, Once config_type_ok_cases] >> goal_assum drule >>
  irule_at Any type_soundness_eval_wh >> simp[] >> goal_assum drule
QED


(********************)

