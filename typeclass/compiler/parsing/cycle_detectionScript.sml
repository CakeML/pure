open HolKernel Parse boolLib bossLib dep_rewrite BasicProvers;
open listTheory rich_listTheory pairTheory alistTheory
  pred_setTheory finite_mapTheory relationTheory
  sptreeTheory spt_closureTheory topological_sortTheory;

val _ = new_theory "cycle_detection";

Theorem top_sort_aux_same_partition:
  ∀ns reach acc xs.
  MEM xs (top_sort_aux ns reach acc) ==>
  ∀x y nexts.
  (reach = trans_clos nexts) ∧
  (∀as x y. MEM as acc ∧ x ≠ y ∧
    MEM x as ∧ MEM y as ⇒ needs x y reach) ∧
  x ≠ y ∧
  MEM x xs ∧ MEM y xs ==> needs x y reach
Proof
  ho_match_mp_tac top_sort_aux_ind >>
  rw[]
  >- (fs[Once $ top_sort_aux_def] >> metis_tac[]) >>
  qpat_x_assum `MEM _ (top_sort_aux _ _ _)` $
    assume_tac o SRULE[Once $ top_sort_aux_def,LET_THM] >>
  qmatch_asmsub_abbrev_tac `MEM _ (_ ps)` >>
  PairCases_on `ps` >>
  fs[] >>
  last_x_assum $ drule_then irule >>
  rw[]
  >- (
    drule partition_thm >>
    simp[] >>
    rpt strip_tac >>
    qpat_x_assum `set _ ∪ set _ ∪ set _ = set _` $
      assume_tac o GSYM >>
    Cases_on `x' = n`
    >- (fs[] >> metis_tac[]) >>
    Cases_on `y' = n`
    >- (fs[] >> metis_tac[]) >>
    `MEM x' ns ∧ MEM y' ns` by fs[] >>
    qpat_x_assum `set _ = _ ∪ _` $ assume_tac o GSYM >>
    fs[] >>
    irule trans_clos_TC_closed >>
    irule $ cj 2 TC_RULES >>
    qexists `n` >>
    irule_at (Pos hd) $ cj 1 TC_RULES >>
    irule_at (Pos $ el 2) $ cj 1 TC_RULES >>
    simp[]
  ) >>
  metis_tac[]
QED

Theorem top_sort_same_partition:
  MEM xs (top_sort graph) ∧ x ≠ y ∧
  MEM x xs ∧ MEM y xs ⇒
  needs x y (trans_clos $ fromAList graph)
Proof
  rw[top_sort_def] >>
  drule top_sort_aux_same_partition >>
  simp[]
QED

Triviality ALOOKUP_MAPi_ID:
  !l k. ALOOKUP (MAPi (\i n. (i,n)) l) k =
        if k < LENGTH l then SOME (EL k l) else NONE
Proof
  Induct using SNOC_INDUCT >> gvs[SNOC_APPEND] >>
  gvs[ALOOKUP_APPEND, EL_APPEND_EQN, indexedListsTheory.MAPi_APPEND] >> rw[]
QED

Triviality ALOOKUP_MAPi_ID_f:
  !l k. ALOOKUP (MAPi (\i n. (i,f n)) l) k =
        if k < LENGTH l then SOME (f (EL k l)) else NONE
Proof
  Induct using SNOC_INDUCT >> gvs[SNOC_APPEND] >>
  gvs[ALOOKUP_APPEND, EL_APPEND_EQN, indexedListsTheory.MAPi_APPEND] >> rw[]
QED

Triviality MAPi_MAP[simp]:
  !l. MAPi (\i n. f n) l = MAP f l
Proof
  Induct >> rw[combinTheory.o_DEF]
QED

Triviality MEM_ALOOKUP:
  !l k v.
    ALL_DISTINCT (MAP FST l)
  ==> (MEM (k,v) l <=> ALOOKUP l k = SOME v)
Proof
  Induct >> rw[FORALL_PROD] >> gvs[] >>
  PairCases_on `h` >> gvs[] >>
  IF_CASES_TAC >> gvs[MEM_MAP, FORALL_PROD] >>
  eq_tac >> simp[]
QED

Triviality domain_lookup_num_set:
  !t k. k IN domain t <=> lookup k t = SOME ()
Proof
  rw[domain_lookup]
QED

fun lambdify th =
  let
    val (bound_vars, body) = strip_forall (concl th)
    val right = rhs body
    val right_fun = list_mk_abs (bound_vars, right)
  in
    list_mk_comb (right_fun, bound_vars) |>
    LIST_BETA_CONV |> SYM |>
    TRANS (SPECL bound_vars th) |>
    GENL bound_vars |>
    REWRITE_RULE[GSYM FUN_EQ_THM]
  end

Theorem MEM_MEM_top_sort:
  ALL_DISTINCT (MAP FST l) ∧
  MEM xs $ top_sort l ∧
  MEM n xs ⇒
  MEM n (MAP FST l)
Proof
  strip_tac >>
  drule_all $ SRULE[]top_sort_correct >>
  strip_tac >>
  pop_assum kall_tac >>
  fs[EXTENSION] >>
  metis_tac[MEM_FLAT]
QED

Triviality ALL_DISTINCT_enc_graph:
  ALL_DISTINCT (MAP FST
       (MAPi
        (λi (n,ns).
             (i,to_nums (MAPi (λi n. (n,i)) (MAP FST graph)) ns))
        graph))
Proof
  simp[indexedListsTheory.MAPi_GENLIST] >>
  rw[ALL_DISTINCT_GENLIST] >>
  ntac 2 (pairarg_tac >> fs[])
QED

Theorem RTC_ALOOKUP_enc_graph_IMP_depends_on:
  ALL_DISTINCT (MAP FST graph) ⇒
  ∀n n'. RTC (λx y.
   ∃aSetx.
     ALOOKUP
       (MAPi
        (λi (n,ns).
             (i,to_nums (MAPi (λi n. (n,i)) (MAP FST graph)) ns))
        graph) x = SOME aSetx ∧
        lookup y aSetx = SOME ()) n n' ⇒
   depends_on graph (EL n (MAP FST graph)) (EL n' (MAP FST graph))
Proof
  strip_tac >>
  ho_match_mp_tac RTC_ind >>
  rw[depends_on_def] >>
  irule $ cj 2 RTC_RULES >>
  first_x_assum $ irule_at (Pos last) >>
  assume_tac ALL_DISTINCT_enc_graph >>
  fs[GSYM MEM_ALOOKUP] >>
  fs[indexedListsTheory.MEM_MAPi] >>
  pairarg_tac >>
  gvs[quantHeuristicsTheory.PAIR_EQ_EXPAND,EL_MAP] >>
  qexists `SND (EL i graph)` >>
  simp[PAIR,EL_MEM] >>
  fs[GSYM domain_lookup_num_set] >>
  `ALL_DISTINCT (MAP FST (MAPi (\i n.(n,i)) (MAP FST graph)))` by (
      simp[indexedListsTheory.MAP_MAPi,
       indexedListsTheory.MAPi_GENLIST] >>
      rw[ALL_DISTINCT_GENLIST] >>
      metis_tac[EL_ALL_DISTINCT_EL_EQ,LENGTH_MAP]) >>
  drule_then assume_tac (GSYM MEM_ALOOKUP) >>
  drule_then assume_tac $ SRULE[]to_nums_correct >>
  gvs[indexedListsTheory.MEM_MAPi,EL_MEM]
QED

Theorem top_sort_any_same_partition:
  ALL_DISTINCT (MAP FST graph) ∧
  MEM xs (top_sort_any graph) ∧
  MEM x xs ∧ MEM y xs ⇒
  depends_on graph x y
Proof
  rpt strip_tac >>
  Cases_on `x = y`
  >- simp[depends_on_def] >>
  fs[top_sort_any_def] >>
  Cases_on `NULL graph` >>
  fs[MEM_MAP,MEM_FLAT] >>
  gvs[MEM_MAP] >>
  `n ≠ n'`
    by (spose_not_then assume_tac >> gvs[]) >>
  qpat_x_assum `option_CASE _ _ _ ≠ option_CASE _ _ _`
    kall_tac >>
  qmatch_asmsub_abbrev_tac `MEM _ (top_sort enc_graph)` >>
  `ALL_DISTINCT (MAP FST enc_graph)`
    by (
    simp[Abbr`enc_graph`,indexedListsTheory.MAPi_GENLIST] >>
    rw[ALL_DISTINCT_GENLIST] >>
    ntac 2 (pairarg_tac >> fs[])) >>
  `∀x. MEM x (MAP FST enc_graph) ⇒ x < LENGTH graph`
    by (
      rw[Abbr`enc_graph`] >>
      gvs[indexedListsTheory.MEM_MAPi] >>
      pairarg_tac >>
      simp[]) >>
  `MEM n (MAP FST enc_graph)`
    by metis_tac[MEM_MEM_top_sort] >>
  `MEM n' (MAP FST enc_graph)`
    by metis_tac[MEM_MEM_top_sort] >>
  drule_all top_sort_same_partition >>
  strip_tac >>
  `is_reachable (fromAList enc_graph) n n'`
    by simp[GSYM trans_clos_correct] >>
  fs[is_reachable_def,lambdify is_adjacent_def,
    lookup_fromAList,ALOOKUP_MAPi_ID_f] >>
  metis_tac[RTC_ALOOKUP_enc_graph_IMP_depends_on]
QED

Definition has_cycle_def:
  has_cycle graph =
    ((EXISTS (λl. 1 < LENGTH l) $ top_sort_any graph) ∨
    EXISTS (λ(v,l). MEM v l) graph)
End

Theorem has_cycle_simp:
  has_cycle graph =
    (∃l. MEM l (top_sort_any graph) ∧ 1 < LENGTH l) ∨
    (∃v l. MEM (v,l) graph ∧ MEM v l)
Proof
  simp[has_cycle_def,EXISTS_MEM,LAMBDA_PROD,GSYM PEXISTS_THM] >>
  metis_tac[]
QED

Triviality TC_REFL_IMP:
  ∀x z. TC R x z ⇒ x = z ⇒
  (R x z ∨ (∃y. x ≠ y ∧ TC R x y ∧ TC R y z))
Proof
  ho_match_mp_tac TC_STRONG_INDUCT >>
  rw[] >>
  Cases_on `x = x'` >>
  metis_tac[]
QED

Triviality TC_REFL_CASES:
  TC R x x ⇔ (R x x ∨ (∃y. x ≠ y ∧ TC R x y ∧ TC R y x))
Proof
  iff_tac
  >- metis_tac[TC_REFL_IMP] >>
  metis_tac[TC_RULES]
QED

Definition TC_depends_on_def:
  TC_depends_on alist ⇔
  TC (λa b.
    ∃deps.
      ALOOKUP alist a = SOME deps ∧ MEM b deps ∧
      MEM b (MAP FST alist))
End

Triviality depends_on_IMP_MEM:
  ∀x y. depends_on graph x y ⇒ x ≠ y ⇒ MEM y (MAP FST graph)
Proof
  simp[depends_on_def] >>
  ho_match_mp_tac RTC_ind >>
  rw[] >>
  Cases_on `y = x'` >>
  simp[]
QED

Triviality MEM_SING_APPEND_CONTRAPOS:
  (∃a c. d = a ++ [b] ++ c) ⇔ MEM b d
Proof
  metis_tac[MEM_SING_APPEND]
QED

Theorem has_cycle_correct:
  ALL_DISTINCT (MAP FST graph) ⇒
  (has_cycle graph ⇔ ∃x. TC_depends_on graph x x)
Proof
  strip_tac >>
  drule_then (assume_tac o GSYM) miscTheory.MEM_ALOOKUP >>
  rw[EQ_IMP_THM,TC_depends_on_def,has_cycle_def,
    EXISTS_MEM,LAMBDA_PROD,GSYM PEXISTS_THM]
  >- (
    `∃x y. MEM x l ∧ MEM y l ∧ x ≠ y`
      by (
        qexistsl [`EL 0 l`,`EL 1 l`] >>
        simp[EL_MEM] >>
        drule (cj 1 $ SRULE[] top_sort_any_correct) >>
        rw[miscTheory.ALL_DISTINCT_FLAT] >>
        `ALL_DISTINCT l` by simp[] >>
        (drule_then $ drule_then strip_assume_tac) $
          iffLR EL_ALL_DISTINCT_EL_EQ >>
        pop_assum $ qspec_then `0` (assume_tac o SRULE[]) >>
        fs[]
      ) >>
    `depends_on graph x y` by
      metis_tac[top_sort_any_same_partition] >>
    `depends_on graph y x` by
      metis_tac[top_sort_any_same_partition] >>
    gvs[depends_on_def,RTC_CASES_TC] >>
    qexists `x` >>
    irule $ cj 2 TC_RULES >>
    metis_tac[]
  )
  >- (
    qexists `p1` >>
    irule $ cj 1 TC_RULES >>
    simp[] >>
    first_assum $ irule_at Any >>
    simp[MEM_MAP] >>
    first_assum $ irule_at Any >>
    simp[]
  ) >>
  fs[TC_REFL_CASES]
  >- (
    disj2_tac >>
    metis_tac[]
  ) >>
  disj1_tac >>
  `depends_on graph y x`
    by simp[RTC_CASES_TC,depends_on_def] >>
  `depends_on graph x y`
    by simp[RTC_CASES_TC,depends_on_def] >>
  rpt $ qpat_x_assum `TC _ _ _` kall_tac >>
  drule_then strip_assume_tac $
    SRULE[]top_sort_any_correct >>
  fs[EXTENSION] >>
  `MEM x (MAP FST graph)` by metis_tac[depends_on_IMP_MEM] >>
  qpat_x_assum `∀x. MEM _ _ ⇔ MEM _ _` $
    assume_tac o GSYM >>
  fs[MEM_FLAT] >>
  `∃xss zss. top_sort_any graph = xss ++ [l] ++ zss`
    by metis_tac[MEM_SING_APPEND] >>
  first_x_assum (drule_then $ drule_then drule) >>
  disch_then assume_tac >>
  `MEM y l` by fs[] >>
  qpat_x_assum `_ ∧ (depends_on _ _ _ ⇒ _)` kall_tac >>
  first_assum $ irule_at (Pos hd) >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
  irule_at (Pos last) CARD_LIST_TO_SET >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists `CARD {x;y}` >>
  irule_at (Pos last) CARD_SUBSET >>
  simp[]
QED

val _ = export_theory();
