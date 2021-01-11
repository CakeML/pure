(*
   Correctness proof for top_sort implementation
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     sptreeTheory
open top_sortTheory;
(* fromCakeML: *)
open reachable_sptProofTheory

val _ = new_theory "top_sortProof";

Theorem needs_alt_def:
  ∀x y tree.
    needs x y tree ⇔
    ∃aSetx. lookup x tree = SOME aSetx ∧ lookup y aSetx = SOME ()
Proof
  rw[needs_def] >> EVERY_CASE_TAC >> gvs[] >>
  rename1 `lookup y z` >> Cases_on `lookup y z` >> gvs[]
QED

Theorem partition_lemma[local]:
  ∀n ks reach acc xas ybs zcs as bs cs.
    partition n ks reach acc = (xas,ybs,zcs) ∧
    acc = (as,bs,cs)
  ⇒ ∃xs ys zs. xas = xs ++ as ∧ ybs = ys ++ bs ∧ zcs = zs ++ cs ∧
    (set (xs ++ ys ++ zs) = set ks) ∧
    (∀x. MEM x xs ⇒ ¬ needs x n reach) ∧
    (∀y. MEM y ys ⇒ needs y n reach ∧ needs n y reach) ∧
    (∀z. MEM z zs ⇒ needs z n reach ∧ ¬ needs n z reach) ∧
    (∀k. MEM k ks ∧ ¬ needs k n reach ⇒ MEM k xs) ∧
    (∀k. MEM k ks ∧ needs k n reach ∧ needs n k reach ⇒ MEM k ys) ∧
    (∀k. MEM k ks ∧ needs k n reach ∧ ¬ needs n k reach ⇒ MEM k zs)
Proof
  recInduct partition_ind >> once_rewrite_tac[partition_def] >> gvs[] >> rw[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  reverse conj_tac
  >- (rpt conj_tac >> gen_tac >> strip_tac >> gvs[]) >>
  gvs[EXTENSION, GSYM DISJ_ASSOC] >> metis_tac[]
QED

Theorem partition_thm:
  ∀n ks reach as bs cs res.
    partition n ks reach (as, bs, cs) = res
  ⇒ ∃xs ys zs.
      partition n ks reach (as, bs, cs) = (xs ++ as, ys ++ bs, zs ++ cs) ∧
      (set (xs ++ ys ++ zs) = set ks) ∧
      (∀x. MEM x xs ⇒ ¬ needs x n reach) ∧
      (∀y. MEM y ys ⇒ needs y n reach ∧ needs n y reach) ∧
      (∀z. MEM z zs ⇒ needs z n reach ∧ ¬ needs n z reach) ∧
      (∀k. MEM k ks ∧ ¬ needs k n reach ⇒ MEM k xs) ∧
      (∀k. MEM k ks ∧ needs k n reach ∧ needs n k reach ⇒ MEM k ys) ∧
      (∀k. MEM k ks ∧ needs k n reach ∧ ¬ needs n k reach ⇒ MEM k zs)
Proof
  rw[] >>
  qspecl_then [`n`,`ks`,`reach`,`(as,bs,cs)`] assume_tac partition_lemma >>
  qpat_abbrev_tac `p = partition n ks reach acc` >>
  PairCases_on `p` >> gvs[] >>
  rw[] >> metis_tac[]
QED

Theorem ALL_DISTINCT_APPEND_SWAP:
  ∀l1 l2.  ALL_DISTINCT (l1 ++ l2) ⇔ ALL_DISTINCT (l2 ++ l1)
Proof
  Induct >> rw[] >> gvs[ALL_DISTINCT_APPEND] >> eq_tac >> rw[]
  >- (CCONTR_TAC >> gvs[])
  >- (CCONTR_TAC >> gvs[])
  >- (CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[])
  >- (CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[])
QED

Theorem partition_ALL_DISTINCT:
  ∀n ks reach acc xs ys zs as bs cs.
    partition n ks reach acc = (xs,ys,zs) ∧
    acc = (as,bs,cs) ∧
    ALL_DISTINCT (ks ++ as ++ bs ++ cs)
  ⇒ ALL_DISTINCT (xs ++ ys ++ zs)
Proof
  recInduct partition_ind >> once_rewrite_tac[partition_def] >>
  rpt conj_tac >- simp[] >> rpt gen_tac >> rpt strip_tac >>
  EVERY_CASE_TAC
  >- (
    gvs[] >> first_x_assum irule >>
    qpat_x_assum `ALL_DISTINCT _` mp_tac >>
    ntac 2 (once_rewrite_tac[ALL_DISTINCT_APPEND_SWAP] >> simp[])
    )
  >- (
    gvs[] >> first_x_assum irule >>
    qpat_x_assum `ALL_DISTINCT _` mp_tac >>
    ntac 3 (once_rewrite_tac[ALL_DISTINCT_APPEND_SWAP] >> simp[])
    )
  >- (
    gvs[] >> first_x_assum irule >>
    qpat_x_assum `ALL_DISTINCT _` mp_tac >>
    ntac 1 (once_rewrite_tac[ALL_DISTINCT_APPEND_SWAP] >> simp[])
    )
  >- (
    gvs[] >> first_x_assum irule >>
    qpat_x_assum `ALL_DISTINCT _` mp_tac >>
    ntac 3 (once_rewrite_tac[ALL_DISTINCT_APPEND_SWAP] >> simp[])
    )
QED

Theorem top_sort_aux_correct:
  ∀ns reach acc resacc.
    top_sort_aux ns reach acc = resacc ∧
    (∀n m. TC (λa b. needs a b reach) n m ⇒ needs n m reach) ∧
    ALL_DISTINCT ns
  ⇒ ∃res.
      resacc = res ++ acc ∧
      ALL_DISTINCT (FLAT res) ∧
      set (FLAT res) = set ns ∧
      ∀xss ys zss y.
        (* for any element ys in the result res, for any y in that ys: *)
        res = xss ++ [ys] ++ zss ∧ MEM y ys ⇒
        (* all dependencies of y must be defined in ys or earlier in xss *)
        ∀dep. needs y dep reach ∧ MEM dep ns ⇒ MEM dep (FLAT xss ++ ys)
Proof
  recInduct top_sort_aux_ind >> simp[top_sort_aux_def] >> rw[] >>
  qpat_abbrev_tac `parts = partition _ _ _ _` >>
  PairCases_on `parts` >> gvs[] >>
  drule partition_thm >> strip_tac >> gvs[] >>
  drule partition_ALL_DISTINCT >> simp[] >> strip_tac >>
  `ALL_DISTINCT parts0 ∧ ALL_DISTINCT parts2` by gvs[ALL_DISTINCT_APPEND] >>
  last_x_assum drule >> last_x_assum drule >> rw[] >>
  gvs [EXTENSION, GSYM DISJ_ASSOC] >> reverse (rw[])
  >- (
    gvs[MEM_FLAT, PULL_FORALL] >>
    qpat_x_assum `_ = _ ++ _ ++ _` (mp_tac o GSYM) >>
    simp[APPEND_EQ_APPEND_MID] >> strip_tac >> gvs[GSYM DISJ_ASSOC]
    >- (
      last_x_assum irule >> simp[PULL_EXISTS] >>
      goal_assum (drule_at Any) >> simp[] >>
      last_x_assum irule >> simp[] >>
      `MEM y parts0` by (
        qpat_x_assum `∀x. _ ⇔ MEM _ parts0` (assume_tac o GSYM) >> simp[] >>
        goal_assum (drule_at Any) >> simp[]) >>
      `¬ needs y n reach` by gvs[] >>
      CCONTR_TAC >> fs[] >>
      last_x_assum (qspecl_then [`y`,`n`] mp_tac) >> simp[] >>
      simp[Once TC_CASES1] >> goal_assum drule >> simp[Once TC_CASES1]
      )
    >- (
      Cases_on `l'` >> gvs[] >> `dep ≠ n` by (CCONTR_TAC >> gvs[]) >> gvs[] >>
      (qsuff_tac `¬needs dep n reach ∨ needs n dep reach` >- metis_tac[]) >>
      CCONTR_TAC >> gvs[] >>
      `needs y n reach ∧ needs n y reach` by gvs[] >>
      qpat_x_assum `¬ needs _ _ _` mp_tac >> simp[] >>
      last_x_assum irule >>
      simp[Once TC_CASES1] >> DISJ2_TAC >>
      goal_assum drule >> simp[Once TC_CASES1]
      )
    >- (
      Cases_on `MEM dep parts2`
      >- (
        first_x_assum (qspec_then `l` mp_tac) >> simp[] >>
        rpt (disch_then drule) >>
        strip_tac >> simp[] >> DISJ1_TAC >>
        goal_assum (drule_at Any) >> simp[]
        ) >>
      Cases_on `MEM dep parts0`
      >- (
        qpat_x_assum `∀x. _ ⇔ MEM _ parts0` (assume_tac o GSYM) >> fs[] >>
        DISJ1_TAC >> goal_assum (drule_at Any) >> simp[]
        ) >>
      `MEM dep parts1` by metis_tac[] >>
      DISJ1_TAC >> qexists_tac `n::parts1` >> simp[]
      )
    )
  >- (
    gvs[MEM_FLAT, PULL_FORALL] >>
    `¬ MEM y parts0` by metis_tac[] >>
    qpat_x_assum `_ = _ ++ _ ++ _` (mp_tac o GSYM) >>
    simp[APPEND_EQ_APPEND_MID] >> reverse strip_tac >> gvs[GSYM DISJ_ASSOC]
    >- (DISJ1_TAC >> qexists_tac `dep::parts1` >> simp[])
    >- (Cases_on `l'` >> gvs[]) >>
    irule FALSITY >> pop_assum mp_tac >> simp[] >>
    qpat_x_assum `∀x. _ ⇔ MEM _ parts0` (assume_tac o GSYM) >>
    simp[] >> goal_assum (drule_at Any) >> simp[]
    )
  >> gvs[ALL_DISTINCT_APPEND] >> CCONTR_TAC >> metis_tac[]
QED

(******************** TODO move to CakeML? ********************)

Theorem rtc_needs:
  s ⊆ t ∧ (∀k. k ∈ t ⇒ ∀n. needs k n tree ⇒ n ∈ t) ⇒
  ∀x y. (λa b. needs a b tree)꙳ x y ⇒ x ∈ s ⇒ y ∈ t
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
  fs[SUBSET_DEF] >> metis_tac []
QED

Theorem closure_spt_alt_thm:
  ∀ reachable tree closure (roots : num set).
    closure_spt_alt reachable tree = closure ∧
    roots ⊆ domain reachable ∧
    (∀k. k ∈ domain reachable ⇒ ∃n. n ∈ roots ∧ (λa b. needs a b tree)꙳ n k)
  ⇒ domain closure = {a | ∃n. n ∈ roots ∧ (λa b. needs a b tree)꙳ n a}
Proof
  recInduct closure_spt_alt_ind >> rw[] >>
  once_rewrite_tac[closure_spt_alt_def] >> simp[] >>
  IF_CASES_TAC
  >- (
    gvs[domain_difference, domain_spt_fold_union_eq, PULL_EXISTS,
        EXTENSION, SUBSET_DEF, superdomain_rewrite, subspt_domain] >>
    rw[] >> eq_tac >> rw[] >>
    gvs[DISJ_EQ_IMP, PULL_EXISTS] >>
    irule rtc_needs >>
    irule_at Any SUBSET_REFL >> gvs[SUBSET_DEF] >>
    goal_assum (drule_at Any) >> gvs[] >> rw[] >>
    first_x_assum irule >>
    gvs[lookup_inter, needs_alt_def, domain_lookup] >>
    qexistsl_tac [`aSetx`,`k`] >> simp[]
    ) >>
  first_x_assum irule >> simp[] >> rw[]
  >- (
    gvs[domain_union, domain_spt_fold_union_eq,
        superdomain_rewrite, lookup_inter] >>
    EVERY_CASE_TAC >> gvs[] >> rename1 `lookup r reachable` >>
    gvs[domain_lookup] >>
    first_x_assum drule >> strip_tac >>
    goal_assum drule >> gvs[] >>
    irule (iffRL RTC_CASES2) >> DISJ2_TAC >>
    goal_assum drule >> simp[needs_alt_def]
    )
  >- gvs[domain_union, SUBSET_DEF]
QED

Theorem closure_spt_alt_thm_strong:
  ∀ tree start.
    domain (closure_spt_alt start tree) =
      {a | ∃n. n ∈ domain start ∧ (λa b. needs a b tree)꙳ n a}
Proof
  rw[] >> irule closure_spt_alt_thm >>
  irule_at Any EQ_REFL >> simp[] >> rw[] >>
  goal_assum drule >> gvs[Once RTC_CASES1]
QED

(******************** END TODO ********************)

Triviality domain_lookup_num_set:
  ∀t k. k ∈ domain t ⇔ lookup k t = SOME ()
Proof
  rw[domain_lookup]
QED

Theorem trans_clos_correct:
  ∀nexts n m.
    needs n m (trans_clos nexts) ∨ n = m ⇔ (RTC (λx y. needs x y nexts)) n m
Proof
  rw[trans_clos_def, Once needs_alt_def] >>
  rw[lookup_map, PULL_EXISTS, GSYM domain_lookup_num_set] >>
  eq_tac >> rw[] >> gvs[]
  >- (
    qspecl_then [`nexts`,`x`] assume_tac closure_spt_alt_thm_strong >> gvs[] >>
    irule (iffRL RTC_CASES1) >> DISJ2_TAC >>
    goal_assum (drule_at Any) >> gvs[needs_alt_def, domain_lookup]
    )
  >- (
    gvs[Once RTC_CASES1, needs_alt_def] >> DISJ1_TAC >>
    qspecl_then [`nexts`,`aSetx`] assume_tac closure_spt_alt_thm_strong >>
    gvs[] >> gvs[domain_lookup, needs_alt_def] >>
    goal_assum drule >> simp[]
    )
QED

Theorem trans_clos_correct_imp:
  ∀nexts n m.
    (TC (λx y. needs x y nexts)) n m ⇒ needs n m (trans_clos nexts)
Proof
  simp[trans_clos_def] >> rw[] >> gvs[needs_alt_def] >>
  rw[lookup_map, PULL_EXISTS, GSYM domain_lookup_num_set] >>
  gvs[Once TC_CASES1] >>
  qspecl_then [`nexts`,`aSetx`] assume_tac closure_spt_alt_thm_strong >>
  gvs[] >> gvs[domain_lookup, needs_alt_def] >>
  goal_assum drule >> simp[] >>
  irule TC_RTC >> simp[]
QED

Theorem trans_clos_TC_closed:
  ∀t n m.
    (λa b. needs a b (trans_clos t))⁺ n m ⇒ needs n m (trans_clos t)
Proof
  strip_tac >> ho_match_mp_tac TC_INDUCT >> simp[] >> rw[] >>
  imp_res_tac trans_clos_correct >>
  rename1 `RTC _ l m` >>
  Cases_on `l = m` >> gvs[] >> Cases_on `n = l` >> gvs[] >>
  gvs[RTC_CASES_TC] >>
  irule trans_clos_correct_imp >>
  irule (TC_RULES |> SPEC_ALL |> CONJUNCT2) >>
  goal_assum drule >> simp[]
QED

Theorem top_sort_correct:
  ∀lets res.
    ALL_DISTINCT (MAP FST lets) ∧
    res = top_sort lets ⇒
      ALL_DISTINCT (FLAT res) ∧
      set (FLAT res) = set (MAP FST lets) ∧
      ∀xss ys zss y.
        (* for any element ys in the result res, for any y in that ys: *)
        res = xss ++ [ys] ++ zss ∧ MEM y ys ⇒
        (* all dependencies of y must be defined in ys or earlier, i.e. xss *)
        ∃deps. ALOOKUP lets y = SOME deps ∧
               ∀d. d ∈ domain deps ∧ MEM d (MAP FST lets)
               ⇒ MEM d (FLAT xss ++ ys)
Proof
  simp[top_sort_def] >> gen_tac >> strip_tac >>
  drule_at Any top_sort_aux_correct >> simp[] >>
  disch_then (qspecl_then [`trans_clos (fromAList lets)`,`[]`] mp_tac) >>
  simp[trans_clos_TC_closed] >> strip_tac >> rw[] >>
  gvs[EXTENSION, GSYM DISJ_ASSOC] >>
  `MEM y (MAP FST lets)` by res_tac >>
  gvs[MEM_MAP, PULL_EXISTS] >>
  rename1 `MEM y _` >> PairCases_on `y` >> gvs[] >>
  drule_all ALOOKUP_ALL_DISTINCT_MEM >> simp[] >> rw[] >>
  first_x_assum irule >> simp[] >>
  goal_assum drule >>
  irule trans_clos_correct_imp >>
  simp[Once TC_CASES1, needs_def] >> DISJ1_TAC >>
  simp[needs_def] >>
  gvs[domain_lookup, lookup_fromAList]
QED

Theorem to_nums_correct:
  ∀xs b res.
    to_nums b xs = res ∧
    ALL_DISTINCT (MAP FST b)
  ⇒ domain res = {c | ∃d. MEM d xs ∧ ALOOKUP b d = SOME c}
Proof
  Induct >> rw[to_nums_def] >> CASE_TAC >> gvs[EXTENSION] >>
  rw[] >> eq_tac >> rw[] >> gvs[] >> metis_tac[]
QED

Triviality ALL_DISTINCT_MAPi_ID:
  ∀l.  ALL_DISTINCT (MAPi (λi _. i) l)
Proof
  rw[EL_ALL_DISTINCT_EL_EQ]
QED

Triviality ALOOKUP_MAPi_ID:
  ∀l k. ALOOKUP (MAPi (λi n. (i,n)) l) k =
        if k < LENGTH l then SOME (EL k l) else NONE
Proof
  Induct using SNOC_INDUCT >> gvs[SNOC_APPEND] >>
  gvs[ALOOKUP_APPEND, EL_APPEND_EQN, indexedListsTheory.MAPi_APPEND] >> rw[]
QED

Triviality ALOOKUP_MAPi_ID_f:
  ∀l k. ALOOKUP (MAPi (λi n. (i,f n)) l) k =
        if k < LENGTH l then SOME (f (EL k l)) else NONE
Proof
  Induct using SNOC_INDUCT >> gvs[SNOC_APPEND] >>
  gvs[ALOOKUP_APPEND, EL_APPEND_EQN, indexedListsTheory.MAPi_APPEND] >> rw[]
QED

Triviality ALL_DISTINCT_ALOOKUP_EL:
  ∀n l. ALL_DISTINCT (MAP FST l) ∧ n < LENGTH l
  ⇒ ALOOKUP l (EL n (MAP FST l)) = SOME (EL n (MAP SND l))
Proof
  Induct >> rw[] >>
  Cases_on `l` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  IF_CASES_TAC >> gvs[MEM_MAP, EL_MAP] >>
  first_x_assum (qspec_then `EL n t` assume_tac) >> gvs[EL_MEM]
QED

Theorem top_sort_any_correct:
  ∀lets res.
    ALL_DISTINCT (MAP FST lets) ∧
    res = top_sort_any lets ⇒
      ALL_DISTINCT (FLAT res) ∧
      set (FLAT res) = set (MAP FST lets) ∧
      ∀xss ys zss y.
        (* for any element ys in the result res, for any y in that ys: *)
        res = xss ++ [ys] ++ zss ∧ MEM y ys ⇒
        (* all dependencies of y must be defined in ys or earlier, i.e. xss *)
        ∃deps. ALOOKUP lets y = SOME deps ∧
               ∀d. MEM d deps ∧ MEM d (MAP FST lets) ⇒ MEM d (FLAT xss ++ ys)
Proof
  once_rewrite_tac[top_sort_any_def] >>
  rpt gen_tac >> IF_CASES_TAC >- gvs[NULL_EQ] >>
  qabbrev_tac `names = MAP FST lets` >>
  qabbrev_tac `to_num = MAPi (λi n. (n,i)) names` >>
  qabbrev_tac `from_num = fromAList (MAPi (λi n. (i,n)) names)` >>
  qabbrev_tac `arg = MAPi (λi (n,ns). (i,to_nums to_num ns)) lets` >>
  gvs[] >> strip_tac >> gvs[] >>
  qspec_then `arg` assume_tac top_sort_correct >> gvs[] >>
  pop_assum mp_tac >> impl_keep_tac
  >- (
    gvs[Abbr `arg`, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[ALL_DISTINCT_MAPi_ID, GSYM LAMBDA_PROD]
    ) >>
  strip_tac >> gvs[GSYM MAP_FLAT] >> rw[]
  >- (
    irule ALL_DISTINCT_MAP_INJ >> rw[] >> gvs[MEM_MAP] >>
    rename1 `lookup_any (FST a) _ _ = lookup_any (FST b) _ _` >>
    PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
    gvs[miscTheory.lookup_any_def, Abbr `from_num`, lookup_fromAList] >>
    gvs[Abbr `arg`, Abbr `names`, indexedListsTheory.MEM_MAPi] >>
    rename1 `(a0,_) = _ (EL c _)` >> rename1 `(b0,_) = _ (EL d _)` >>
    qabbrev_tac `cc = EL c lets` >> qabbrev_tac `dd = EL d lets` >>
    PairCases_on `cc` >> PairCases_on `dd` >> gvs[] >>
    gvs[ALOOKUP_MAPi_ID, EL_ALL_DISTINCT_EL_EQ]
    )
  >- (
    gvs[EXTENSION, MEM_MAP, PULL_EXISTS] >> rw[] >> eq_tac >> rw[]
    >- (
      gvs[Abbr `names`, miscTheory.lookup_any_def] >>
      CASE_TAC >- (Cases_on `lets` >> gvs[]) >>
      gvs[MEM_MAP, Abbr `from_num`, lookup_fromAList] >>
      drule ALOOKUP_MEM >> strip_tac >>
      gvs[indexedListsTheory.MEM_MAPi, EL_MAP] >>
      irule_at Any EQ_REFL >> simp[EL_MEM]
      ) >>
    pop_assum mp_tac >> pop_assum kall_tac >> rw[] >>
    imp_res_tac MEM_EL >> gvs[] >>
    gvs[Abbr `names`, Abbr `from_num`, miscTheory.lookup_any_def, MEM_MAP] >>
    PairCases_on `y` >> gvs[] >>
    simp[lookup_fromAList, ALOOKUP_MAPi_ID, EXISTS_PROD] >>
    qexists_tac `n` >> simp[] >>
    gvs[Abbr `arg`, indexedListsTheory.MEM_MAPi] >>
    goal_assum drule >> Cases_on `EL n lets` >> gvs[]
    ) >>
  gvs[MAP_EQ_APPEND, GSYM MAP_FLAT, MEM_MAP, PULL_EXISTS] >>
  rename1 `top_sort _ = left ++ [mid] ++ right` >>
  gvs[Abbr `from_num`, miscTheory.lookup_any_def, lookup_fromAList] >>
  gvs[ALOOKUP_MAPi_ID] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    rename1 `false` >>
    gvs[Abbr `names`, Abbr `arg`, EXTENSION, GSYM DISJ_ASSOC] >> res_tac >>
    gvs[indexedListsTheory.MEM_MAPi] >>
    rename1 `EL m lets` >> Cases_on `EL m lets` >> gvs[]
    ) >>
  gvs[MEM_MAP, MEM_FLAT, PULL_EXISTS, miscTheory.lookup_any_def] >>
  gvs[Abbr `names`, ALL_DISTINCT_ALOOKUP_EL] >>
  simp[EL_MAP, Once MEM_EL, PULL_EXISTS] >> rw[] >> rename1 `m < _` >>
  first_x_assum (drule_at Any) >> disch_then (qspec_then `left` mp_tac) >>
  simp[] >>
  `arg = MAPi (λi ns. (i, to_nums to_num (SND ns))) lets` by (
    gvs[Abbr `arg`] >> AP_THM_TAC >> AP_TERM_TAC >>
    irule EQ_EXT >> rw[] >> irule EQ_EXT >> rw[] >>
    rename1 `_ foo = _` >> PairCases_on `foo` >> gvs[]) >>
  gvs[ALOOKUP_MAPi_ID_f] >>
  qspecl_then [`SND (EL n lets)`,`to_num`] mp_tac to_nums_correct >> gvs[] >>
  impl_keep_tac >- gvs[Abbr `to_num`, combinTheory.o_DEF] >>
  strip_tac >> simp[PULL_EXISTS] >> simp[Once SWAP_FORALL_THM] >>
  disch_then (qspec_then `EL m (SND (EL n lets))` mp_tac) >> simp[EL_MEM] >>
  `ALL_DISTINCT (MAP FST to_num)` by gvs[Abbr `to_num`] >>
  drule (GSYM miscTheory.MEM_ALOOKUP) >> strip_tac >> simp[] >>
  gvs[Abbr `to_num`, indexedListsTheory.MEM_MAPi, PULL_EXISTS] >>
  qpat_x_assum `MEM _ _` mp_tac >> simp[Once MEM_EL] >> strip_tac >>
  rename1 `l < _` >> simp[GSYM CONJ_ASSOC] >> disch_then drule >> simp[] >>
  strip_tac
  >- (
    rename1 `MEM _ l2` >> DISJ1_TAC >>
    goal_assum (drule_at Any) >> simp[EL_MAP]
    )
  >- (
    DISJ2_TAC >>
    goal_assum (drule_at Any) >> simp[EL_MAP]
    )
QED

val _ = export_theory();
