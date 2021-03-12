(*
  Prove that there exists values that cannot be computed by any
  PureCake program, or in other words, that eval is surjective.
*)
open HolKernel Parse boolLib bossLib term_tactic BasicProvers dep_rewrite;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     pairTheory ltreeTheory llistTheory bagTheory cardinalTheory
     pred_setTheory rich_listTheory combinTheory finite_mapTheory
open pure_evalTheory pure_expTheory pure_valueTheory pure_exp_lemmasTheory
     pure_miscTheory;

val _ = new_theory "pure_eval_surj";

Theorem char_countable:
  COUNTABLE 𝕌(:char)
Proof
  rw[countable_def] >>
  qexists_tac ‘ORD’ >>
  rw[INJ_DEF,ORD_11]
QED

Theorem list_countable:
  COUNTABLE 𝕌(:'a) ⇒ COUNTABLE 𝕌(:'a list)
Proof
  strip_tac >>
  qsuff_tac ‘∀n. COUNTABLE {s:'a list | LENGTH s = n}’
  >- (strip_tac >>
      ‘𝕌(:'a list) = BIGUNION(IMAGE (λn. {s:'a list | LENGTH s = n}) 𝕌(:num))’
        by(PURE_REWRITE_TAC[SET_EQ_SUBSET,SUBSET_DEF] >>
           rw[PULL_EXISTS]) >>
      pop_assum SUBST_ALL_TAC >>
      match_mp_tac COUNTABLE_BIGUNION >>
      simp[COUNTABLE_IMAGE,num_countable] >>
      metis_tac[]) >>
  Induct >- rw[countable_def,INJ_DEF] >>
  ‘{s | LENGTH s = SUC n} =
   BIGUNION {IMAGE (CONS c) {s:'a list | LENGTH s = n} | c ∈ 𝕌(:'a)}’
    by(PURE_REWRITE_TAC[SET_EQ_SUBSET,SUBSET_DEF] >>
       conj_tac >> Cases >> rw[IN_IMAGE,PULL_EXISTS]) >>
  pop_assum SUBST_ALL_TAC >>
  match_mp_tac COUNTABLE_BIGUNION >>
  conj_tac
  >- (simp[Once GSPEC_IMAGE] >>
      match_mp_tac COUNTABLE_IMAGE >>
      simp[o_DEF,GSYM UNIV_DEF]) >>
  rw[] >>
  simp[COUNTABLE_IMAGE]
QED

Theorem string_countable:
  COUNTABLE 𝕌(:string)
Proof
  metis_tac[list_countable,char_countable]
QED

Theorem prod_countable:
  COUNTABLE 𝕌(:'a) ∧ COUNTABLE 𝕌(:'b)
  ⇒
  COUNTABLE 𝕌(:'a # 'b)
Proof
  strip_tac >>
  ‘𝕌(:'a # 'b) = {(a,b) | a ∈ 𝕌(:'a) ∧ b ∈ 𝕌(:'b)}’
    by(PURE_REWRITE_TAC[SET_EQ_SUBSET,SUBSET_DEF] >>
       rw[ELIM_UNCURRY] >> metis_tac[PAIR]) >>
  pop_assum SUBST_ALL_TAC >>
  ho_match_mp_tac COUNTABLE_PRODUCT_DEPENDENT >>
  rw[]
QED

Theorem int_countable:
  COUNTABLE 𝕌(:int)
Proof
  irule (INST_TYPE [beta |-> ``:num``] inj_countable) >>
  qexistsl_tac [`λi. if i < 0 then 2 * (Num (-i)) else 2 * Num i + 1`,`univ(:num)`] >>
  simp[num_countable, INJ_IFF] >> rw[] >>
  Cases_on `i` >> gvs[] >>
  Cases_on `i'` >> gvs[]
  >- (
    rename1 `_ * n ≠ _ * m + _` >>
    qsuff_tac `EVEN (2 * n) ∧ ODD (2 * m + 1)`
    >- (strip_tac >> CCONTR_TAC >> gvs[ODD_EVEN]) >>
    simp[EVEN_DOUBLE, ODD_ADD, ODD_MULT]
    )
  >- (
    rename1 `_ * n + _ ≠ _ * m` >>
    qsuff_tac `EVEN (2 * m) ∧ ODD (2 * n + 1)`
    >- (strip_tac >> CCONTR_TAC >> gvs[ODD_EVEN]) >>
    simp[EVEN_DOUBLE, ODD_ADD, ODD_MULT]
    )
QED

Theorem atom_op_countable:
  COUNTABLE 𝕌(:atom_op)
Proof
  `𝕌(:atom_op) =
      {Eq; Add; Sub; Mul; Div; Mod; Lt; Leq; Gt; Geq;
       Len; Elem; Concat; Implode; Substring; StrLt; StrLeq; StrGt; StrGeq} ∪
      IMAGE Message 𝕌(:string) ∪
      IMAGE Lit 𝕌(:lit)` by (
        rw[EXTENSION] >> Cases_on `x` >> gvs[]) >>
  pop_assum SUBST_ALL_TAC >> simp[] >>
  `𝕌(:lit) = IMAGE Int 𝕌(:int) ∪ IMAGE Str 𝕌(:string)
             ∪ IMAGE Loc 𝕌(:num)
             ∪ IMAGE (λ(x,y). Msg x y) (𝕌(:string) × 𝕌(:string))` by (
      rw[EXTENSION,EXISTS_PROD] >> Cases_on `x` >> gvs[]) >>
  pop_assum SUBST_ALL_TAC >> simp[] >>
  simp[COUNTABLE_IMAGE, string_countable, int_countable] >>
  irule COUNTABLE_IMAGE >>
  irule COUNTABLE_IMAGE >>
  irule pred_setTheory.cross_countable >>
  fs [string_countable]
QED

Theorem op_countable:
  COUNTABLE 𝕌(:op)
Proof
  rpt strip_tac >>
  ‘𝕌(:op) = {If} ∪ IMAGE pure_exp$Cons 𝕌(:string)
                 ∪ IMAGE (UNCURRY pure_exp$IsEq) 𝕌(:string # num)
                 ∪ IMAGE (UNCURRY pure_exp$Proj) 𝕌(:string # num)
                 ∪ IMAGE pure_exp$AtomOp 𝕌(:atom_op)
                 ∪ {pure_exp$Seq}’
    by(PURE_REWRITE_TAC[SET_EQ_SUBSET,SUBSET_DEF] >>
       conj_tac >> Cases >> rw[ELIM_UNCURRY] >>
       metis_tac[FST,SND]) >>
  pop_assum SUBST_ALL_TAC >>
  simp[union_countable_IFF,COUNTABLE_IMAGE,
       string_countable,prod_countable,num_countable,atom_op_countable]
QED


Theorem list_countable_res:
  COUNTABLE {x | P x} ⇒ COUNTABLE {l | EVERY P l}
Proof
  strip_tac >>
  qsuff_tac ‘∀n. COUNTABLE {l | EVERY P l ∧ LENGTH l = n}’
  >- (strip_tac >>
      ‘{l | EVERY P l} = BIGUNION(IMAGE (λn. {l | EVERY P l ∧ LENGTH l = n}) 𝕌(:num))’
        by(PURE_REWRITE_TAC[SET_EQ_SUBSET,SUBSET_DEF] >>
           rw[PULL_EXISTS]) >>
      pop_assum SUBST_ALL_TAC >>
      match_mp_tac COUNTABLE_BIGUNION >>
      simp[COUNTABLE_IMAGE,num_countable] >>
      metis_tac[]) >>
  Induct >- rw[countable_def,INJ_DEF] >>
  ‘{l | EVERY P l ∧ LENGTH l = SUC n} =
   BIGUNION {IMAGE (CONS c) {l | EVERY P l ∧ LENGTH l = n} | c | P c}’
    by(PURE_REWRITE_TAC[SET_EQ_SUBSET,SUBSET_DEF] >>
       conj_tac >> Cases >> rw[IN_IMAGE,PULL_EXISTS]) >>
  pop_assum SUBST_ALL_TAC >>
  match_mp_tac COUNTABLE_BIGUNION >>
  conj_tac
  >- (simp[Once GSPEC_IMAGE] >>
      match_mp_tac COUNTABLE_IMAGE >>
      simp[o_DEF] >>
      ‘{x | P x} = (λc. P c)’ by(rw[FUN_EQ_THM]) >>
      metis_tac[]) >>
  rw[] >>
  simp[COUNTABLE_IMAGE]
QED

Theorem COUNTABLE_PRODUCT_2:
  COUNTABLE s ∧ COUNTABLE t ⇒
  COUNTABLE {f x y | s x ∧ t y }
Proof
  strip_tac >>
  qsuff_tac ‘COUNTABLE {f x y | s x ∧ K t x y}’
  >- rw[ELIM_UNCURRY] >>
  ho_match_mp_tac (COUNTABLE_PRODUCT_DEPENDENT |> SIMP_RULE std_ss [IN_DEF]) >>
  rw[] >> CONV_TAC (RAND_CONV ETA_CONV) >> fs []
QED

Theorem COUNTABLE_PRODUCT_3:
  COUNTABLE s ∧ COUNTABLE t ∧ COUNTABLE u ⇒
  COUNTABLE {f x y z | s x ∧ t y ∧ u z}
Proof
  strip_tac >>
  qsuff_tac ‘COUNTABLE {UNCURRY (f x) y | s x ∧ (t(FST y) ∧ u(SND y))}’
  >- rw[ELIM_UNCURRY] >>
  ho_match_mp_tac (COUNTABLE_PRODUCT_DEPENDENT |> SIMP_RULE std_ss [IN_DEF]) >>
  rw[] >>
  ‘(λy. t (FST y) ∧ u (SND y)) = {(y,z) | t y ∧ u z}’
    by(rw[ELIM_UNCURRY,FUN_EQ_THM]) >>
  pop_assum SUBST_ALL_TAC >>
  ho_match_mp_tac (COUNTABLE_PRODUCT_DEPENDENT |> SIMP_RULE std_ss [IN_DEF]) >>
  rw[] >> metis_tac[]
QED

Theorem exp_countable:
  COUNTABLE 𝕌(:pure_exp$exp)
Proof
  qsuff_tac ‘∀n. COUNTABLE {s:pure_exp$exp | exp_size s ≤ n}’
  >- (strip_tac >>
      ‘𝕌(:exp) = BIGUNION(IMAGE (λn. {s:exp | exp_size s ≤ n}) 𝕌(:num))’
        by(PURE_REWRITE_TAC[SET_EQ_SUBSET,SUBSET_DEF] >>
           rw[PULL_EXISTS] >> metis_tac[LESS_EQ_REFL]) >>
      pop_assum SUBST_ALL_TAC >>
      match_mp_tac COUNTABLE_BIGUNION >>
      simp[COUNTABLE_IMAGE,num_countable] >>
      metis_tac[]) >>
  Induct
  >- (rw[countable_def,INJ_DEF] >>
      qexists_tac ‘ARB’ >>
      Cases >> rw[exp_size_def]) >>
  rename1 ‘SUC n’ >>
  ‘{s:exp | exp_size s ≤ SUC n} ⊆
   IMAGE Var {vname | list_size char_size vname ≤ n} ∪
   IMAGE (UNCURRY Prim) {(op,arg) | op_size op ≤ n ∧ exp3_size arg ≤ n} ∪
   IMAGE (UNCURRY App) {(rator,rand) | exp_size rator ≤ n ∧ exp_size rand ≤ n} ∪
   IMAGE (UNCURRY Lam) {(vname,exp) | list_size char_size vname ≤ n ∧ exp_size exp ≤ n} ∪
   IMAGE (UNCURRY Letrec) {(funs,exp) | exp1_size funs ≤ n ∧ exp_size exp ≤ n}’
    by(PURE_REWRITE_TAC[SET_EQ_SUBSET,SUBSET_DEF] >>
       Cases >> rw[IN_IMAGE,PULL_EXISTS,exp_size_def]) >>
  dxrule_then match_mp_tac COUNTABLE_SUBSET >>
  rw[COUNTABLE_UNION]
  >- (rename1 ‘Var’ >>
      match_mp_tac COUNTABLE_IMAGE >>
      match_mp_tac COUNTABLE_SUBSET >>
      irule_at (Pos hd) SUBSET_UNIV >>
      simp[string_countable])
  >- (rename1 ‘pure_exp$Prim’ >>
      match_mp_tac COUNTABLE_IMAGE >>
      ho_match_mp_tac (COUNTABLE_PRODUCT_DEPENDENT |> SIMP_RULE std_ss [IN_DEF]) >>
      conj_tac
      >- (match_mp_tac COUNTABLE_SUBSET >>
          irule_at (Pos hd) SUBSET_UNIV >>
          simp[op_countable]) >>
      rw[] >>
      ‘COUNTABLE {l | EVERY (λs. exp_size s ≤ n) l}’
        by(match_mp_tac list_countable_res >> simp[]) >>
      drule_at_then (Pos last) match_mp_tac COUNTABLE_SUBSET >>
      rw[SUBSET_DEF,EVERY_MEM] >>
      imp_res_tac exp_size_lemma >> DECIDE_TAC)
  >- (rename1 ‘pure_exp$App’ >>
      match_mp_tac COUNTABLE_IMAGE >>
      ho_match_mp_tac (COUNTABLE_PRODUCT_DEPENDENT |> SIMP_RULE std_ss [IN_DEF]) >>
      rw[] >>
      ‘{x | exp_size x ≤ n} = (λx. exp_size x ≤ n)’ by(rw[FUN_EQ_THM]) >>
      gvs[])
  >- (rename1 ‘pure_exp$Lam’ >>
      match_mp_tac COUNTABLE_IMAGE >>
      ho_match_mp_tac (COUNTABLE_PRODUCT_DEPENDENT |> SIMP_RULE std_ss [IN_DEF]) >>
      conj_tac
      >- (match_mp_tac COUNTABLE_SUBSET >>
          irule_at (Pos hd) SUBSET_UNIV >>
          simp[string_countable]) >>
      ‘{x | exp_size x ≤ n} = (λx. exp_size x ≤ n)’ by(rw[FUN_EQ_THM]) >>
      gvs[])
  >- (rename1 ‘pure_exp$Letrec’ >>
      match_mp_tac COUNTABLE_IMAGE >>
      ho_match_mp_tac (COUNTABLE_PRODUCT_DEPENDENT |> SIMP_RULE std_ss [IN_DEF]) >>
      reverse conj_tac
      >- (‘{x | exp_size x ≤ n} = (λx. exp_size x ≤ n)’ by(rw[FUN_EQ_THM]) >>
          gvs[]) >>
      ‘COUNTABLE {l | EVERY (λ(s:string,exp). exp_size exp ≤ n) l}’
        by(match_mp_tac list_countable_res >>
           ‘{x | (λ(s:string,exp). exp_size exp ≤ n) x} =
            {(s,exp) | s = s ∧ (s' = s' ∧ exp_size exp ≤ n)}’
             by(rw[ELIM_UNCURRY]) >>
           pop_assum SUBST_ALL_TAC >>
           ho_match_mp_tac COUNTABLE_PRODUCT_2 >>
           rw[GSYM UNIV_DEF,string_countable] >>
           ‘{x | exp_size x ≤ n} = (λx. exp_size x ≤ n)’ by(rw[FUN_EQ_THM]) >>
           gvs[]) >>
      drule_at_then (Pos last) match_mp_tac COUNTABLE_SUBSET >>
      rw[SUBSET_DEF,EVERY_MEM] >>
      Cases_on ‘e’ >>
      imp_res_tac exp_size_lemma >>
      rw[ELIM_UNCURRY])
QED

Theorem v_lookup_gen_v:
  ∀path f.
    (∀path a len. f path = (a,len) ∧ (∀b. a ≠ Constructor' b) ⇒ len = 0) ∧
    (∀y. y ≼ path ∧ y ≠ path ⇒
       ∃b n. f y = (Constructor' b, n) ∧ EL (LENGTH y) path < n)
    ⇒ v_lookup path (gen_v f) = f path
Proof
  Induct >> rpt strip_tac >-
    (rw[v_lookup,Once gen_v] >>
     TOP_CASE_TAC >> gvs[AllCaseEqs()] >>
     res_tac >> gvs[]) >>
  rw[v_lookup,Once gen_v] >>
  first_assum(qspec_then ‘[]’ mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  fs[] >>
  simp[oEL_def] >>
  gvs[oEL_THM] >>
  last_x_assum(qspec_then ‘(λpath. f (h::path))’ mp_tac) >>
  reverse impl_tac >- simp[] >>
  conj_tac >- (rw[] >> metis_tac[]) >>
  rw[] >>
  first_x_assum(qspec_then ‘h::y’ mp_tac) >>
  reverse impl_tac >- simp[] >>
  simp[]
QED

Theorem v_lookup_gen_v_alt:
  ∀path f.
    v_lookup path (gen_v f) =
      if (∀y. y ≼ path ∧ y ≠ path ⇒
            ∃b n. f y = (Constructor' b, n) ∧ EL (LENGTH y) path < n) then
        (case f path of
            (Constructor' c, n) => (Constructor' c, n)
          | (pre, n)            => (pre, 0))
      else (Diverge', 0)
Proof
  Induct >> rpt strip_tac
  >- (rw[v_lookup, Once gen_v] >> TOP_CASE_TAC >> gvs[AllCaseEqs()]) >>
  reverse (rw[v_lookup, Once gen_v]) >> gvs[oEL_THM]
  >- (
    CASE_TAC >> CASE_TAC >> CASE_TAC >> gvs[] >>
    IF_CASES_TAC >> gvs[] >>
    Cases_on `y` >> gvs[] >>
    first_x_assum (qspec_then `t` assume_tac) >> gvs[]
    ) >>
  first_assum(qspec_then `[]` mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> fs[] >>
  IF_CASES_TAC >> gvs[] >>
  first_x_assum (qspec_then `h::path'` assume_tac) >> gvs[]
QED

Theorem v_uncountable:
  𝕌(:num -> bool) ≼ 𝕌(:v)
Proof
  rw[cardleq_SURJ,SURJ_DEF] >>
  qexists_tac ‘λv n. FST(v_lookup (REPLICATE n 1 ++ [0]) v) = Atom' ARB’ >>
  rw[] >>
  rename1 ‘_ = f’ >>
  qexists_tac ‘gen_v (λnl.
                       if nl = [] then (Constructor' ARB,2)
                       else if LAST nl = 1 then
                         (Constructor' ARB,2)
                       else if LAST nl = 0 then
                         (if f(LENGTH nl - 1) then
                            (Atom' ARB,0)
                          else
                            (Diverge',0))
                       else (Diverge',0))’ >>
  simp[FUN_EQ_THM] >>
  strip_tac >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [v_lookup_gen_v] >>
  conj_tac
  >- (rw[] >>
      TRY(Cases_on ‘a’ >> rw[] >> NO_TAC) >>
      TRY(Cases_on ‘n’ >> rw[] >> NO_TAC)
      >- (imp_res_tac IS_PREFIX_LENGTH >>
          gvs[EL_APPEND_EQN] >>
          rw[EL_REPLICATE] >>
          gvs[NOT_LESS] >>
          drule IS_PREFIX_NOT_EQ >> impl_tac >- simp[] >>
          rw[] >>
          ‘LENGTH nl - n = 0’ by DECIDE_TAC >>
          simp[])
      >- (qspec_then ‘nl’ strip_assume_tac SNOC_CASES >> gvs[SNOC_APPEND] >>
          rw[DISJ_EQ_IMP] >>
          gvs[IS_PREFIX_SNOC |> REWRITE_RULE[SNOC_APPEND]] >>
          gvs[IS_PREFIX_APPEND] >>
          gvs[LIST_EQ_REWRITE,EL_APPEND_EQN,EL_REPLICATE] >>
          first_x_assum(qspec_then ‘LENGTH l’ mp_tac) >>
          rw[])
      >- (qspec_then ‘nl’ strip_assume_tac SNOC_CASES >> gvs[SNOC_APPEND] >>
          rw[DISJ_EQ_IMP] >>
          gvs[IS_PREFIX_SNOC |> REWRITE_RULE[SNOC_APPEND]] >>
          gvs[IS_PREFIX_APPEND] >>
          gvs[LIST_EQ_REWRITE,EL_APPEND_EQN,EL_REPLICATE] >>
          first_x_assum(qspec_then ‘LENGTH l’ mp_tac) >>
          rw[])
      >- (qspec_then ‘nl’ strip_assume_tac SNOC_CASES >> gvs[SNOC_APPEND] >>
          rw[DISJ_EQ_IMP] >>
          gvs[IS_PREFIX_SNOC |> REWRITE_RULE[SNOC_APPEND]] >>
          gvs[IS_PREFIX_APPEND] >>
          gvs[LIST_EQ_REWRITE,EL_APPEND_EQN,EL_REPLICATE] >>
          rw[DISJ_EQ_IMP] >>
          qexists_tac ‘LENGTH l’ >> rw[])) >>
  rw[]
QED

Theorem eval_not_surj:
  ¬SURJ eval 𝕌(:exp) 𝕌(:v)
Proof
  assume_tac exp_countable >>
  spose_not_then strip_assume_tac >>
  ‘𝕌(:v) ≼ 𝕌(:exp)’ by(metis_tac[cardleq_SURJ]) >>
  metis_tac[v_uncountable,CANTOR_THM_UNIV,cardleq_TRANS,exp_countable,COUNTABLE_ALT_cardleq]
QED

(******************************************************************************)

Definition cons_names_def:
  (cons_names (Var v) = {}) ∧
  (cons_names (Prim op es) =
    let cons_es = BIGUNION (set (MAP (λe. cons_names e) es)) in
    case op of Cons c => c INSERT cons_es | _ => cons_es) ∧
  (cons_names (App e1 e2) = cons_names e1 ∪ cons_names e2) ∧
  (cons_names (Lam x body) = cons_names body) ∧
  (cons_names (Letrec fs e) =
    cons_names e ∪ BIGUNION (set (MAP (λ(f,e). cons_names e) fs)))
Termination
  WF_REL_TAC ‘measure exp_size’ >> fs[] >>
  conj_tac >> TRY (Induct_on `fs`) >> TRY (Induct_on `es`) >> rw[] >>
  gvs[fetch "pure_exp" "exp_size_def"] >> res_tac >>
  pop_assum (assume_tac o SPEC_ALL) >> fs[]
End

Theorem cons_names_FINITE:
  ∀e ns. cons_names e = ns ⇒ FINITE ns
Proof
  recInduct cons_names_ind >> reverse (rw[cons_names_def])
  >- (gvs[MEM_MAP] >> PairCases_on `y` >> gvs[] >> res_tac) >>
  TOP_CASE_TAC >> gvs[MEM_MAP, PULL_EXISTS]
QED

Theorem cons_names_subst:
  ∀ f e n.
    n ∈ cons_names (subst f e)
  ⇒ n ∈ cons_names e ∨ (∃k e'. FLOOKUP f k = SOME e' ∧ n ∈ cons_names e')
Proof
  recInduct subst_ind >> rw[cons_names_def, subst_def]
  >- (
    FULL_CASE_TAC >> gvs[cons_names_def] >>
    goal_assum drule >> simp[]
    )
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF] >>
    Cases_on `∃c. op = Cons c` >> gvs[]
    >- (
      gvs[MEM_MAP, PULL_EXISTS, PULL_FORALL] >>
      first_x_assum drule_all >> metis_tac[]
      ) >>
    `n ∈ BIGUNION (set (MAP (λa. cons_names (subst m a)) xs))` by (
      Cases_on `op` >> gvs[MEM_MAP, PULL_EXISTS] >>
      goal_assum drule >> simp[]) >>
    last_x_assum assume_tac >> last_x_assum kall_tac >>
    qsuff_tac `
      n ∈ BIGUNION (set (MAP (λe. cons_names e) xs)) ∨
      ∃k e'. FLOOKUP m k = SOME e' ∧ n ∈ cons_names e'`
    >- (CASE_TAC >> gvs[]) >>
    gvs[MEM_MAP, PULL_EXISTS, PULL_FORALL] >>
    first_x_assum drule_all >> metis_tac[]
    )
  >- (first_x_assum drule >> strip_tac >> simp[] >> metis_tac[])
  >- (first_x_assum drule >> strip_tac >> simp[] >> metis_tac[])
  >- (
    first_x_assum drule >> strip_tac >> simp[] >>
    gvs[DOMSUB_FLOOKUP_THM] >> metis_tac[]
    )
  >- (
    first_x_assum drule >> strip_tac >> simp[] >>
    gvs[FDIFF_def, FLOOKUP_DRESTRICT, MEM_MAP] >>
    metis_tac[]
    )
  >- (
    gvs[MEM_MAP, PULL_EXISTS, FDIFF_def, FLOOKUP_DRESTRICT] >>
    rename1 `MEM foo _` >> PairCases_on `foo` >> gvs[EXISTS_PROD] >>
    first_x_assum drule_all >> strip_tac >> metis_tac[]
    )
QED

Theorem cons_names_bind:
  ∀ f e n.
    n ∈ cons_names (bind f e)
  ⇒ n ∈ cons_names e ∨ (∃k e'. FLOOKUP f k = SOME e' ∧ n ∈ cons_names e')
Proof
  rw[bind_def, cons_names_def] >>
  irule cons_names_subst >> simp[]
QED

Theorem cons_names_bind1:
  ∀ x e' e n.
    n ∈ cons_names (bind1 x e' e)
  ⇒ n ∈ cons_names e ∨ n ∈ cons_names e'
Proof
  rw[] >>
  drule cons_names_bind >> strip_tac >> simp[] >>
  gvs[FLOOKUP_UPDATE]
QED

Theorem cons_names_subst_funs:
  ∀ f e n.
    n ∈ cons_names (subst_funs f e)
  ⇒ n ∈ cons_names e ∨ (∃e'. MEM e' (MAP SND f) ∧ n ∈ cons_names e')
Proof
  rw[subst_funs_def] >>
  drule cons_names_bind >> strip_tac >> simp[] >>
  gvs[flookup_fupdate_list] >> FULL_CASE_TAC >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >>
  gvs[MEM_REVERSE, MEM_MAP, PULL_EXISTS] >>
  PairCases_on `y` >> gvs[cons_names_def]
  >- (DISJ2_TAC >> goal_assum drule >> simp[]) >>
  gvs[MEM_MAP] >> PairCases_on `y` >> gvs[cons_names_def] >>
  DISJ2_TAC >> qexists_tac `(y0,y1')` >> simp[]
QED

Definition cons_names_wh_def:
  (cons_names_wh (wh_Constructor c es) =
    c INSERT BIGUNION (set (MAP (λe. cons_names e) es))) ∧
  (cons_names_wh (wh_Closure x body) = cons_names body) ∧
  (cons_names_wh _ = {})
End

Theorem cons_name_wh_trivial_simps[simp]:
  (∀a. cons_names_wh (wh_Atom a) = {}) ∧
  (∀x body. cons_names_wh (wh_Closure x body) = cons_names body) ∧
  (cons_names_wh wh_Error = {}) ∧
  (cons_names_wh wh_Diverge = {})
Proof
  rw[cons_names_wh_def]
QED

Theorem cons_name_wh_FINITE:
  ∀wh ns. cons_names_wh wh = ns ⇒ FINITE ns
Proof
  reverse Induct >> rw[cons_names_wh_def]
  >- (metis_tac[cons_names_FINITE]) >>
  gvs[FINITE_INSERT, MEM_MAP, PULL_EXISTS] >> rw[] >>
  metis_tac[cons_names_FINITE]
QED

Definition cons_names_v_def:
  cons_names_v v =
    {c | ∃path n. v_lookup path v = (Constructor' c, n)} ∪
    BIGUNION {cons_names e | ∃path x n. v_lookup path v = (Closure' x e, n)}
End

Theorem cons_names_v:
  (∀a. cons_names_v (Atom a) = {}) ∧
  (∀c vs. cons_names_v (Constructor c vs) =
    c INSERT BIGUNION (set (MAP (λv. cons_names_v v) vs))) ∧
  (∀x body. cons_names_v (Closure x body) = cons_names body) ∧
  (cons_names_v Diverge = {}) ∧
  (cons_names_v Error = {})
Proof
  rw[cons_names_v_def, EXTENSION, DISJ_EQ_IMP, PULL_EXISTS]
  >- (Cases_on `path` >> gvs[v_lookup])
  >- (Cases_on `path` >> gvs[v_lookup])
  >- (
    rename1 `Constructor' c'` >> eq_tac >> rw[]
    >- (
      gvs[MEM_MAP, PULL_EXISTS] >>
      simp[DISJ_EQ_IMP] >> gvs[GSYM EXTENSION] >>
      reverse (Cases_on
        `∀path n. v_lookup path (Constructor c vs) ≠ (Constructor' c', n)`) >>
      gvs[]
      >- (
        Cases_on `path` >> gvs[v_lookup, oEL_THM] >>
        FULL_CASE_TAC >> gvs[] >>
        qexists_tac `EL h vs` >> gvs[EL_MEM] >> rw[] >> res_tac
        ) >>
      rename1 `Closure' x body` >>
      Cases_on `path` >> gvs[v_lookup, oEL_THM] >>
      FULL_CASE_TAC >> gvs[] >>
      qexists_tac `EL h vs` >> gvs[EL_MEM] >> rw[] >>
      goal_assum drule >> goal_assum drule
      )
    >- (
      Cases_on `c' = c` >> gvs[]
      >- (first_x_assum (qspec_then `[]` assume_tac) >> gvs[v_lookup]) >>
      gvs[MEM_MAP, MEM_EL]
      >- (
        rename1 `foo < _` >>
        first_x_assum (qspec_then `foo::path` assume_tac) >>
        gvs[v_lookup, oEL_THM]
        ) >>
      simp[GSYM EXTENSION] >> goal_assum drule >>
      qexists_tac `n::path` >> gvs[v_lookup, oEL_THM]
      )
    )
  >- (
    rename1 `Constructor' c` >>
    `∀path n. v_lookup path (Closure x body) ≠ (Constructor' c, n)` by (
      Cases >> rw[v_lookup]) >>
    simp[] >> eq_tac >> rw[]
    >- (Cases_on `path` >> gvs[v_lookup]) >>
    goal_assum drule >>
    qexistsl_tac [`body`,`[]`,`x`,`0`] >> gvs[v_lookup]
    ) >>
  Cases_on `path` >> gvs[v_lookup]
QED

Theorem cons_names_v_exists_INFINITE:
  ∃v. INFINITE (cons_names_v v)
Proof
  rw[infinite_num_inj, INJ_DEF] >>
  qexists_tac
    `gen_v (λpath. (Constructor' (REPLICATE (LENGTH path) #"a"), 1))` >>
  qexists_tac `λn. REPLICATE n #"a"` >> reverse (rw[])
  >- (drule REPLICATE_11 >> simp[]) >>
  simp[cons_names_v_def, DISJ_EQ_IMP, PULL_EXISTS] >>
  rename1 `_ ⇒ false` >> rw[] >>
  CCONTR_TAC >> last_x_assum mp_tac >> simp[] >>
  qexistsl_tac [`REPLICATE x 0`,`1`] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [v_lookup_gen_v] >>
  simp[] >> rw[] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [EL_REPLICATE] >> simp[] >>
  drule IS_PREFIX_NOT_EQ >> gvs[]
QED

Definition cons_names_v_prefix_def[simp]:
  (cons_names_v_prefix (Constructor' c) = {c}) ∧
  (cons_names_v_prefix (Closure' x body) = cons_names body) ∧
  (cons_names_v_prefix _ = {})
End

Definition add_TF_def:
  add_TF s = s ∪ {"True";"False"}
End

Theorem cons_names_eval_wh_to:
  ∀ k e wh n.
    eval_wh_to k e = wh ∧
    n ∈ cons_names_wh wh
  ⇒ n ∈ add_TF (cons_names e)
Proof
  recInduct eval_wh_to_ind >> rw[eval_wh_to_def] >> gvs[cons_names_def]
  >- simp[add_TF_def]
  >- (
    Cases_on `eval_wh_to k x` >> gvs[dest_wh_Closure_def] >>
    FULL_CASE_TAC >> gvs[] >>
    first_x_assum drule >> strip_tac >>
    gvs[add_TF_def] >>
    drule cons_names_bind >> simp[FLOOKUP_UPDATE] >>
    strip_tac >> metis_tac[]
    )
  >- (
    first_x_assum drule >> strip_tac >>
    gvs[MEM_MAP, PULL_EXISTS, EXISTS_PROD, add_TF_def] >>
    drule cons_names_subst_funs >> strip_tac >> simp[] >>
    gvs[MEM_MAP] >> rename1 `MEM foo _` >> PairCases_on `foo` >> gvs[] >>
    metis_tac[]
    )
  THEN_LT Q.SELECT_GOALS_LT_THEN [`p = Proj _ _`]
  (
    Cases_on `∃c. p = Cons c` >> gvs[cons_names_wh_def, add_TF_def]
    >- metis_tac[] >>
    qsuff_tac
      `n ∈ BIGUNION (set (MAP (λe. cons_names e) xs)) ∨ n = "True" ∨ n = "False"`
    >- (CASE_TAC >> gvs[]) >>
    Cases_on `p` >> gvs[MEM_MAP, PULL_EXISTS] >>
    EVERY_CASE_TAC >> gvs[cons_names_wh_def, LENGTH_EQ_NUM_compute, MEM_MAP] >>
    res_tac >> simp[] >>
    first_x_assum irule >> simp[cons_names_wh_def, MEM_MAP, PULL_EXISTS] >>
    metis_tac[EL_MEM]
  ) >>
  (
    Cases_on `∃c. p = Cons c` >> gvs[cons_names_wh_def, add_TF_def]
    >- metis_tac[] >>
    qsuff_tac
      `n ∈ BIGUNION (set (MAP (λe. cons_names e) xs)) ∨ n = "True" ∨ n = "False"`
    >- (CASE_TAC >> gvs[]) >>
    Cases_on `p` >> gvs[MEM_MAP, PULL_EXISTS] >>
    EVERY_CASE_TAC >> gvs[cons_names_wh_def, LENGTH_EQ_NUM_compute, MEM_MAP] >>
    metis_tac[EL_MEM]
  )
QED

Theorem cons_names_eval_wh:
  ∀e wh n.
    eval_wh e = wh ∧
    n ∈ cons_names_wh wh
  ⇒ n ∈ add_TF (cons_names e)
Proof
  rw[eval_wh_def] >> FULL_CASE_TAC >> gvs[] >>
  last_x_assum mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >>
  irule cons_names_eval_wh_to >> irule_at Any EQ_REFL >>
  goal_assum drule
QED

Theorem cons_names_follow_path_eval_wh:
  ∀path e pre n nm.
    follow_path eval_wh e path = (pre, n) ∧
    nm ∈ cons_names_v_prefix pre
  ⇒ nm ∈ add_TF (cons_names e)
Proof
  Induct >> rw[follow_path_def]
  >- (
    EVERY_CASE_TAC >> gvs[] >>
    irule cons_names_eval_wh >> simp[cons_names_wh_def]
    ) >>
  EVERY_CASE_TAC >> gvs[oEL_THM] >>
  first_x_assum drule_all >>
  gvs[add_TF_def] >> strip_tac >> simp[] >>
  drule cons_names_eval_wh >>
  simp[cons_names_wh_def, MEM_MAP, PULL_EXISTS, add_TF_def] >>
  disch_then irule >> DISJ2_TAC >>
  goal_assum drule >> gvs[EL_MEM]
QED

Theorem cons_names_gen_v_follow_path_eval_wh:
  ∀e v n.
    gen_v (follow_path eval_wh e) = v ∧
    n ∈ cons_names_v v
  ⇒ n ∈ add_TF (cons_names e)
Proof
  gvs[cons_names_v_def, PULL_EXISTS, PULL_FORALL, v_lookup_gen_v_alt] >>
  rw[] >> pop_assum mp_tac >> IF_CASES_TAC >> gvs[] >>
  EVERY_CASE_TAC >> gvs[] >> rw[] >>
  irule cons_names_follow_path_eval_wh >>
  goal_assum drule >> simp[]
QED

Theorem cons_names_eval:
  ∀e v n.
    eval e = v ∧
    n ∈ cons_names_v v
  ⇒ n ∈ add_TF (cons_names e)
Proof
  rw[eval_def, v_unfold_def] >>
  irule cons_names_gen_v_follow_path_eval_wh >>
  irule_at Any EQ_REFL >> simp[]
QED

Theorem eval_not_surj_alt:
  ¬SURJ eval 𝕌(:exp) 𝕌(:v)
Proof
  rw[SURJ_DEF] >>
  assume_tac cons_names_v_exists_INFINITE >> fs[] >>
  qexists_tac `v` >> rw[] >>
  CCONTR_TAC >> fs[] >>
  drule cons_names_eval >> simp[] >>
  `FINITE (add_TF (cons_names y))` by (
    fs[add_TF_def] >> metis_tac[cons_names_FINITE]) >>
  irule IN_INFINITE_NOT_FINITE >> simp[]
QED

val _ = export_theory();
