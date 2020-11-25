(*
  Prove that there exists values that cannot be computed by any
  PureCake program, or in other words, that eval is surjective.
 *)
open HolKernel Parse boolLib bossLib term_tactic;
open expTheory valueTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     pure_langTheory pred_setTheory cardinalTheory BasicProvers rich_listTheory combinTheory;

val _ = new_theory "eval_surj";

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

Theorem op_countable:
  COUNTABLE 𝕌(:atom_op) ∧ COUNTABLE 𝕌(:lit)
  ⇒
  COUNTABLE 𝕌(:op)
Proof
  rpt strip_tac >>
  ‘𝕌(:op) = {If} ∪ IMAGE exp$Cons 𝕌(:string)
                 ∪ IMAGE (UNCURRY exp$IsEq) 𝕌(:string # num)
                 ∪ IMAGE (UNCURRY exp$Proj) 𝕌(:string # num)
                 ∪ IMAGE exp$AtomOp 𝕌(:atom_op)
                 ∪ IMAGE exp$Lit 𝕌(:lit)’
    by(PURE_REWRITE_TAC[SET_EQ_SUBSET,SUBSET_DEF] >>
       conj_tac >> Cases >> rw[ELIM_UNCURRY] >>
       metis_tac[FST,SND]) >>
  pop_assum SUBST_ALL_TAC >>
  simp[union_countable_IFF,COUNTABLE_IMAGE,string_countable,prod_countable,num_countable]
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

Theorem exp_size_MEM:
  MEM s x ⇒ exp_size s ≤ exp7_size x
Proof
  Induct_on ‘x’ >> rw[exp_size_def] >> res_tac >> DECIDE_TAC
QED

Theorem exp_size_MEM':
  MEM s x ⇒ exp_size(SND(SND s)) ≤ exp3_size x
Proof
  Induct_on ‘x’ >> simp[] >>
  PairCases >> rw[exp_size_def] >> rw[] >>
  res_tac >> DECIDE_TAC
QED

Theorem exp_size_MEM'':
  MEM s x ⇒ exp_size(SND(SND s)) ≤ exp1_size x
Proof
  Induct_on ‘x’ >> simp[] >>
  PairCases >> rw[exp_size_def] >> rw[] >>
  res_tac >> DECIDE_TAC
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
  COUNTABLE 𝕌(:atom_op) ∧ COUNTABLE 𝕌(:lit)
  ⇒
  COUNTABLE 𝕌(:exp)
Proof
  strip_tac >>
  qsuff_tac ‘∀n. COUNTABLE {s:exp | exp_size s ≤ n}’
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
   IMAGE (UNCURRY Prim) {(op,arg) | op_size op ≤ n ∧ exp7_size arg ≤ n} ∪
   IMAGE (UNCURRY App) {(rator,rand) | exp_size rator ≤ n ∧ exp_size rand ≤ n} ∪
   IMAGE (UNCURRY Lam) {(vname,exp) | list_size char_size vname ≤ n ∧ exp_size exp ≤ n} ∪
   IMAGE (UNCURRY Letrec) {(funs,exp) | exp3_size funs ≤ n ∧ exp_size exp ≤ n} ∪
   IMAGE (λ(x,y,z). exp$Case x y z) {(exp,pat,clauses) | exp_size exp ≤ n ∧ list_size char_size pat ≤ n ∧ exp1_size clauses ≤ n}’
    by(PURE_REWRITE_TAC[SET_EQ_SUBSET,SUBSET_DEF] >>
       Cases >> rw[IN_IMAGE,PULL_EXISTS,exp_size_def]) >>
  dxrule_then match_mp_tac COUNTABLE_SUBSET >>
  rw[COUNTABLE_UNION]
  >- (rename1 ‘Var’ >>
      match_mp_tac COUNTABLE_IMAGE >>
      match_mp_tac COUNTABLE_SUBSET >>
      irule_at (Pos hd) SUBSET_UNIV >>
      simp[string_countable])
  >- (rename1 ‘exp$Prim’ >>
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
      imp_res_tac exp_size_MEM >> DECIDE_TAC)
  >- (rename1 ‘exp$App’ >>
      match_mp_tac COUNTABLE_IMAGE >>
      ho_match_mp_tac (COUNTABLE_PRODUCT_DEPENDENT |> SIMP_RULE std_ss [IN_DEF]) >>
      rw[] >>
      ‘{x | exp_size x ≤ n} = (λx. exp_size x ≤ n)’ by(rw[FUN_EQ_THM]) >>
      gvs[])
  >- (rename1 ‘exp$Lam’ >>
      match_mp_tac COUNTABLE_IMAGE >>
      ho_match_mp_tac (COUNTABLE_PRODUCT_DEPENDENT |> SIMP_RULE std_ss [IN_DEF]) >>
      conj_tac
      >- (match_mp_tac COUNTABLE_SUBSET >>
          irule_at (Pos hd) SUBSET_UNIV >>
          simp[string_countable]) >>
      ‘{x | exp_size x ≤ n} = (λx. exp_size x ≤ n)’ by(rw[FUN_EQ_THM]) >>
      gvs[])
  >- (rename1 ‘exp$Letrec’ >>
      match_mp_tac COUNTABLE_IMAGE >>
      ho_match_mp_tac (COUNTABLE_PRODUCT_DEPENDENT |> SIMP_RULE std_ss [IN_DEF]) >>
      reverse conj_tac
      >- (‘{x | exp_size x ≤ n} = (λx. exp_size x ≤ n)’ by(rw[FUN_EQ_THM]) >>
          gvs[]) >>
      ‘COUNTABLE {l | EVERY (λ(s:string,s':string,exp). exp_size exp ≤ n) l}’
        by(match_mp_tac list_countable_res >>
           ‘{x | (λ(s:string,s':string,exp). exp_size exp ≤ n) x} = {(s,s',exp) | s = s ∧ (s' = s' ∧ exp_size exp ≤ n)}’
             by(rw[ELIM_UNCURRY]) >>
           pop_assum SUBST_ALL_TAC >>
           ho_match_mp_tac COUNTABLE_PRODUCT_3 >>
           rw[GSYM UNIV_DEF,string_countable] >>
           ‘{x | exp_size x ≤ n} = (λx. exp_size x ≤ n)’ by(rw[FUN_EQ_THM]) >>
           gvs[]) >>
      drule_at_then (Pos last) match_mp_tac COUNTABLE_SUBSET >>
      rw[SUBSET_DEF,EVERY_MEM] >>
      imp_res_tac exp_size_MEM' >>
      rw[ELIM_UNCURRY])
  >- (rename1 ‘exp$Case’ >>
      match_mp_tac COUNTABLE_IMAGE >>
      ho_match_mp_tac (COUNTABLE_PRODUCT_3) >>
      conj_tac
      >- (‘{x | exp_size x ≤ n} = (λx. exp_size x ≤ n)’ by(rw[FUN_EQ_THM]) >>
          gvs[]) >>
      conj_tac
      >- (match_mp_tac COUNTABLE_SUBSET >>
          irule_at (Pos hd) SUBSET_UNIV >>
          simp[string_countable]) >>
      ‘COUNTABLE {l | EVERY (λ(s:string,s':string list,exp). exp_size exp ≤ n) l}’
        by(match_mp_tac list_countable_res >>
           ‘{x | (λ(s:string,s':string list,exp). exp_size exp ≤ n) x} = {(s,s',exp) | s = s ∧ (s' = s' ∧ exp_size exp ≤ n)}’
             by(rw[ELIM_UNCURRY]) >>
           pop_assum SUBST_ALL_TAC >>
           ho_match_mp_tac COUNTABLE_PRODUCT_3 >>
           rw[GSYM UNIV_DEF,string_countable,list_countable] >>
           ‘{x | exp_size x ≤ n} = (λx. exp_size x ≤ n)’ by(rw[FUN_EQ_THM]) >>
           gvs[]) >>
      drule_at_then (Pos last) match_mp_tac COUNTABLE_SUBSET >>
      rw[SUBSET_DEF,EVERY_MEM] >>
      imp_res_tac exp_size_MEM'' >>
      rw[ELIM_UNCURRY])
QED

Theorem v_lookup_gen_v:
  ∀path f.
    (∀path a len. f path = (a,len) ∧ (∀b. a ≠ Constructor' b) ⇒ len = 0) ∧
    (∀y. y ≼ path ∧ y≠path ⇒
       ∃b n. f y = (Constructor' b, n) ∧ EL (LENGTH y) path < n
    ) ⇒
    v_lookup path (gen_v f) = f path
Proof
  Induct >> rpt strip_tac >-
    (rw[v_lookup,Once gen_v] >>
     TOP_CASE_TAC >> gvs[AllCaseEqs()] >>
     res_tac >> gvs[]) >>
  rw[v_lookup,Once gen_v] >>
  first_assum(qspec_then ‘[]’ mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
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

Theorem IS_PREFIX_NOT_EQ:
  ∀x y.
    IS_PREFIX x y ∧
    x ≠ y ⇒
    LENGTH y < LENGTH x
Proof
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  gvs[NOT_LESS] >>
  imp_res_tac IS_PREFIX_LENGTH >>
  ‘LENGTH x = LENGTH y’ by DECIDE_TAC >>
  metis_tac[IS_PREFIX_LENGTH_ANTI]
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
  COUNTABLE 𝕌(:atom_op) ∧ COUNTABLE 𝕌(:lit)
  ⇒
  ¬SURJ eval 𝕌(:exp) 𝕌(:v)
Proof
  strip_tac >>
  dxrule_all_then strip_assume_tac exp_countable >>
  spose_not_then strip_assume_tac >>
  ‘𝕌(:v) ≼ 𝕌(:exp)’ by(metis_tac[cardleq_SURJ]) >>
  metis_tac[v_uncountable,CANTOR_THM_UNIV,cardleq_TRANS,exp_countable,COUNTABLE_ALT_cardleq]
QED

val _ = export_theory();
