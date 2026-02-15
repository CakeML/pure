Theory pure_misc
Ancestors
  string mlstring option pair list alist llist finite_map pred_set
  arithmetic rich_list sptree ltree fixedPoint sorting logroot
  cardinal[qualified]
Libs
  term_tactic BasicProvers dep_rewrite intLib[qualified]

(******************** Numbers ********************)

(* From wordsTheory *)
Theorem numeral_less_thm =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV prim_recTheory.LESS_THM


(******************** Finite maps ********************)

Theorem FDIFF_MAP_KEYS_BIJ:
  BIJ f 𝕌(:α) 𝕌(:β) ⇒
  FDIFF (MAP_KEYS f fm) (IMAGE f s) = MAP_KEYS f (FDIFF fm s)
Proof
  rpt strip_tac >>
  simp[FDIFF_def] >>
  ‘COMPL(IMAGE f s) = IMAGE f (COMPL s)’
    by(rw[COMPL_DEF,IMAGE_DEF,SET_EQ_SUBSET,SUBSET_DEF] >>
       gvs[BIJ_DEF,INJ_DEF,SURJ_DEF] >> metis_tac[]) >>
  pop_assum SUBST_ALL_TAC >>
  gvs[BIJ_DEF] >>
  simp[DRESTRICT_MAP_KEYS_IMAGE]
QED

Theorem fmap_rel_fupdate_list_MAP_FST:
  ∀R f1 f2 l1 l2.
    fmap_rel R (f1 |++ l1) (f2 |++ l2)
  ⇒ set (MAP FST l1) ∪ FDOM f1 = set (MAP FST l2) ∪ FDOM f2
Proof
  rw[fmap_rel_def, FDOM_FUPDATE_LIST] >>
  gvs[EXTENSION] >> metis_tac[]
QED

Theorem FRANGE_FDIFF_SUBSET:
  FRANGE (FDIFF m s) ⊆ FRANGE m
Proof
  rw[FRANGE_DEF, SUBSET_DEF, FDIFF_def, DRESTRICT_DEF] >>
  goal_assum drule >> simp[]
QED

Theorem FDOM_FDIFF_alt:
  FDOM (FDIFF m s) = FDOM m DIFF s
Proof
  rw[EXTENSION, FDOM_FDIFF]
QED

Theorem FDIFF_FMERGE:
  ∀f a b s. FDIFF (FMERGE f a b) s = FMERGE f (FDIFF a s) (FDIFF b s)
Proof
  rw[fmap_eq_flookup, FLOOKUP_FDIFF, FLOOKUP_FMERGE] >>
  TOP_CASE_TAC >> gvs[]
QED

Theorem FRANGE_ALT_DEF:
  ∀fm. FRANGE fm = IMAGE ($' fm) (FDOM fm)
Proof
  rw[FRANGE_DEF, EXTENSION] >> eq_tac >> rw[] >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem CARD_fmap_injection:
  ∀fm. CARD (FDOM fm) = CARD (FRANGE fm) ⇔
    (∀k1 k2 v. FLOOKUP fm k1 = SOME v ∧ FLOOKUP fm k2 = SOME v ⇒ k1 = k2)
Proof
  rw[] >> eq_tac >> rw[]
  >- (
    qspecl_then [`FRANGE fm`,`FDOM fm`,`$' fm`] mp_tac $ GEN_ALL FINITE_SURJ_BIJ >>
    simp[] >> impl_tac >> rw[]
    >- (rw[SURJ_DEF, FRANGE_DEF] >> goal_assum drule >> simp[]) >>
    simp[FRANGE_ALT_DEF] >> gvs[BIJ_DEF, INJ_DEF, FLOOKUP_DEF]
    )
  >- (
    simp[FRANGE_ALT_DEF] >> irule $ GSYM INJ_CARD_IMAGE_EQ >> simp[] >>
    qexists_tac `FRANGE fm` >> simp[FRANGE_ALT_DEF] >>
    gvs[INJ_DEF, FLOOKUP_DEF]
    )
QED

Theorem SUBMAP_FDIFF[simp]:
  ∀m s. FDIFF m s ⊑ m
Proof
  rw[SUBMAP_FLOOKUP_EQN, FLOOKUP_FDIFF]
QED

Theorem FUNION_FDIFF:
  FUNION m1 m2 = FUNION m1 (FDIFF m2 (FDOM m1))
Proof
  rw[fmap_eq_flookup, FLOOKUP_FUNION, FLOOKUP_FDIFF] >>
  CASE_TAC >> simp[] >> IF_CASES_TAC >> gvs[FLOOKUP_DEF]
QED

Theorem o_f_FUPDATE_LIST:
  ∀l m f. f o_f (m |++ l) = (f o_f m) |++ MAP (λ(k,v). (k, f v)) l
Proof
  Induct >> rw[FUPDATE_LIST_THM] >> PairCases_on `h` >> gvs[]
QED


(******************** Functions/Pairs/Options ********************)

Theorem PAIR_MAP_ALT:
  ∀f g. (f ## g) = λ(x,y). f x, g y
Proof
  rw[] >> irule EQ_EXT >> rw[] >>
  PairCases_on `x` >> gvs[]
QED

Theorem FST_THM:
  FST = λ(x,y). x
Proof
  irule EQ_EXT >> Cases >> simp[]
QED

Theorem SND_THM:
  SND = λ(x,y). y
Proof
  irule EQ_EXT >> rw[] >>
  PairCases_on `x` >> rw[]
QED

Theorem CURRY_thm:
  CURRY f = λ x y. f(x,y)
Proof
  rw[FUN_EQ_THM]
QED

Theorem I_def:
  I = \x. x
Proof
  rw [combinTheory.I_DEF, combinTheory.S_DEF]
QED

Theorem OPTION_MAP2_OPTION_MAP:
  OPTION_MAP2 f (SOME x) y = OPTION_MAP (f x) y
Proof
  Cases_on `y` >> simp[]
QED


(******************** Lists ********************)

Theorem NIL_iff_NOT_MEM:
  ∀l. l = [] ⇔ ∀x. ¬MEM x l
Proof
  Induct >> rw[] >>
  qexists_tac `h` >> fs[]
QED

Theorem EVERY2_refl_EQ:
  LIST_REL R ls ls ⇔ (∀x. MEM x ls ⇒ R x x)
Proof
  simp[EQ_IMP_THM,EVERY2_refl] >>
  Induct_on ‘ls’ >> rw[] >>
  metis_tac[]
QED

Theorem MAP_ID_ON:
  (∀x. MEM x l ⇒ f x = x) ⇒ MAP f l = l
Proof
  Induct_on ‘l’ >> rw[]
QED

Theorem ALOOKUP_SOME_EL:
  ∀l k v. ALOOKUP l k = SOME v ⇒ ∃n. n < LENGTH l ∧ EL n l = (k,v)
Proof
  Induct >> rw[] >>
  PairCases_on `h` >> gvs[] >>
  FULL_CASE_TAC >> gvs[]
  >- (qexists_tac `0` >> gvs[]) >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `SUC n` >> gvs[]
QED

Theorem ALOOKUP_SOME_EL_2:
  ∀(l1: ('k # 'a) list) (l2: ('k # 'b) list) k v.
    ALOOKUP l1 k = SOME v ∧
    MAP FST l1 = MAP FST l2
  ⇒ ∃v'. ALOOKUP l2 k = SOME v' ∧
      ∃n. n < LENGTH l1 ∧ EL n l1 = (k,v) ∧ EL n l2 = (k,v')
Proof
  Induct >> rw[] >>
  PairCases_on `h` >> gvs[] >>
  FULL_CASE_TAC >> gvs[]
  >- (
    qexists_tac `SND (EL 0 l2)` >>
    Cases_on `l2` >> gvs[] >> PairCases_on `h` >> gvs[] >>
    qexists_tac `0` >> gvs[]
    ) >>
  first_x_assum drule >> Cases_on `l2` >> gvs[] >>
  disch_then (qspec_then `t` assume_tac) >> gvs[] >>
  PairCases_on `h` >> gvs[] >>
  qexists_tac `SUC n` >> gvs[]
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

Theorem REPLICATE_11:
  ∀n m e. REPLICATE n e = REPLICATE m e ⇒ n = m
Proof
  Induct >> rw[] >>
  Cases_on `m` >> gvs[] >>
  first_x_assum irule >> goal_assum drule
QED

Theorem LIST_REL_SYM:
  (∀x y. R x y ⇔ R y x) ⇒
  ∀xs ys. LIST_REL R xs ys ⇔ LIST_REL R ys xs
Proof
  strip_tac \\ Induct
  \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs [] \\ metis_tac []
QED

Theorem LIST_REL_TRANS:
  (∀x y z. R x y ∧ R y z ⇒ R x z) ⇒
  ∀xs ys zs. LIST_REL R xs ys ∧ LIST_REL R ys zs ⇒ LIST_REL R xs zs
Proof
  strip_tac \\ Induct
  \\ fs [] \\ rw [] \\ fs [] \\ rw [] \\ fs [] \\ metis_tac []
QED

Theorem LIST_REL_mono:
  (∀x y. R x y ∧ MEM x xs ∧ MEM y ys ⇒ R1 x y) ==>
  LIST_REL R xs ys ⇒ LIST_REL R1 xs ys
Proof
  qid_spec_tac ‘ys’ \\ Induct_on ‘xs’ \\ fs [] \\ rw []
QED

Theorem MAP_PAIR_MAP:
  MAP FST (MAP (f ## g) l) = MAP f (MAP FST l) ∧
  MAP SND (MAP (f ## g) l) = MAP g (MAP SND l)
Proof
  rw[MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f]
QED

Theorem ALOOKUP_SOME:
  ALOOKUP l k = SOME v ⇒ MEM k (MAP FST l)
Proof
  rw[] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem LIST_REL_imp_OPTREL_ALOOKUP:
  ∀(R:'a -> 'b -> bool) l1 l2.
    LIST_REL R (MAP SND l1) (MAP SND l2) ∧ MAP FST l1 = MAP FST l2
  ⇒ ∀k. OPTREL R (ALOOKUP l1 k) (ALOOKUP l2 k) ∧
        OPTREL R (ALOOKUP (REVERSE l1) k) (ALOOKUP (REVERSE l2) k)
Proof
  rw[LIST_REL_EL_EQN]
  >- (
    Cases_on `ALOOKUP l1 k` >> Cases_on `ALOOKUP l2 k` >> gvs[ALOOKUP_NONE] >>
    imp_res_tac ALOOKUP_SOME >> gvs[] >>
    drule_all_then strip_assume_tac ALOOKUP_SOME_EL_2 >> gvs[] >>
    last_x_assum drule >> simp[EL_MAP]
    )
  >- (
    Cases_on `ALOOKUP (REVERSE l1) k` >>
    Cases_on `ALOOKUP (REVERSE l2) k` >> gvs[ALOOKUP_NONE] >>
    imp_res_tac ALOOKUP_SOME >> gvs[MAP_REVERSE] >>
    ‘MAP FST (REVERSE l1) = MAP FST (REVERSE l2)’ by fs [MAP_REVERSE] >>
    drule_all_then strip_assume_tac ALOOKUP_SOME_EL_2 >> gvs[MAP_REVERSE] >>
    drule (GSYM EL_REVERSE) >>
    qspecl_then [`n`,`l1`] mp_tac (GSYM EL_REVERSE) >> rw[] >> gvs[] >>
    qmatch_asmsub_abbrev_tac `EL k1 _` >>
    `k1 < LENGTH l2` by (unabbrev_all_tac >> DECIDE_TAC) >>
    last_x_assum drule >> simp[EL_MAP]
    )
QED

Theorem LIST_REL_OPTREL:
  ∀xs ys.
    LIST_REL (λ(f,x) (g,y). f = g ∧ R x y) xs ys ⇒
      OPTREL R (ALOOKUP (REVERSE xs) k) (ALOOKUP (REVERSE ys) k)
Proof
  qsuff_tac ‘
    ∀xs ys.
      LIST_REL (λ(f,x) (g,y). f = g ∧ R x y) xs ys ⇒
        OPTREL R (ALOOKUP xs k) (ALOOKUP ys k)’
  >- rw []
  \\ ho_match_mp_tac LIST_REL_ind
  \\ simp [OPTREL_def]
  \\ Cases \\ Cases \\ rw []
QED

Theorem ALL_DISTINCT_FLAT_IMP:
  ∀l m. ALL_DISTINCT (FLAT l) ∧ MEM m l ⇒ ALL_DISTINCT m
Proof
  Induct >> rw[] >> gvs[ALL_DISTINCT_APPEND]
QED

Theorem ALL_DISTINCT_FLAT_IMP_APPEND:
  ∀l m1 m2. ALL_DISTINCT (FLAT l) ∧ MEM m1 l ∧ MEM m2 l ∧ m1 ≠ m2
  ⇒ ALL_DISTINCT (m1 ++ m2)
Proof
  Induct >> reverse (rw[])
  >- (last_x_assum irule >> gvs[ALL_DISTINCT_APPEND]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  irule_at Any ALL_DISTINCT_FLAT_IMP >> goal_assum drule >> simp[] >> rw[] >>
  CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[MEM_FLAT] >>
  goal_assum drule >> simp[]
QED

Theorem MAPi_EQ_l:
  ∀l1 l2 f.
    LENGTH l1 = LENGTH l2 ∧
    (∀n. n < LENGTH l1 ⇒ f n (EL n l1) = f n (EL n l2))
  ⇔ MAPi f l1 = MAPi f l2
Proof
  Induct using SNOC_INDUCT >> rw[] >>
  gvs[SNOC_APPEND, indexedListsTheory.MAPi_APPEND] >>
  Cases_on `l2` using SNOC_CASES >>
  gvs[SNOC_APPEND, indexedListsTheory.MAPi_APPEND, EL_APPEND_EQN] >> rw[] >>
  eq_tac >> rw[] >> res_tac
  >- (
    first_x_assum $ irule o iffLR >> rw[] >>
    first_x_assum $ qspec_then `n` mp_tac >> simp[]
    )
  >- (first_x_assum $ qspec_then `LENGTH l1` mp_tac >> simp[])
  >- (IF_CASES_TAC >> gvs[] >> `n = LENGTH l` by gvs[] >> simp[])
QED

Theorem MAP_ZIP_ALT:
  LENGTH l1 = LENGTH l2 ⇒
  MAP (λ(a,b). (a, g b)) (ZIP (l1, l2)) = ZIP (l1, MAP g l2) ∧
  MAP (λ(a,b). (f a, b)) (ZIP (l1, l2)) = ZIP (MAP f l1, l2)
Proof
  rw[LIST_EQ_REWRITE, EL_MAP, EL_ZIP]
QED

Theorem PERM_FLAT:
  ∀l1 l2. PERM l1 l2 ⇒ PERM (FLAT l1) (FLAT l2)
Proof
  Induct_on `PERM` >> rw[]
  >- (irule PERM_CONG >> simp[])
  >- (irule PERM_CONG >> simp[] >> simp[Once PERM_FUN_APPEND])
  >- (irule PERM_TRANS >> goal_assum drule >> simp[])
QED

Theorem ALL_DISTINCT_LENGTH_EQ_MEM:
  ∀l1 l2.
    ALL_DISTINCT l1 ∧ LENGTH l2 ≤ LENGTH l1 ∧
    (∀x. MEM x l1 ⇒ MEM x l2)
  ⇒ (∀x. MEM x l2 ⇒ MEM x l1)
Proof
  Induct >> rw[DISJ_EQ_IMP] >>
  first_x_assum irule >> simp[] >>
  qexists_tac `FILTER ($<> h) l2` >> rw[] >> gvs[MEM_FILTER]
  >- (CCONTR_TAC >> gvs[]) >>
  first_x_assum $ qspec_then `h` assume_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `FILTER P` >>
  qspecl_then [`P`,`l2`] mp_tac rich_listTheory.LENGTH_FILTER_LESS >>
  impl_tac >> gvs[EXISTS_MEM] >>
  goal_assum drule >> unabbrev_all_tac >> gvs[]
QED

Theorem PERM_ALL_DISTINCT_LENGTH:
  ∀l1 l2.
    ALL_DISTINCT l1 ∧ LENGTH l2 ≤ LENGTH l1 ∧
    (∀x. MEM x l1 ⇒ MEM x l2)
  ⇒ PERM l1 l2
Proof
  Induct >> rw[] >>
  first_assum $ qspec_then `h` mp_tac >> rewrite_tac[] >>
  strip_tac >> imp_res_tac MEM_SPLIT >> gvs[] >>
  gvs[sortingTheory.PERM_CONS_EQ_APPEND] >>
  irule_at Any EQ_REFL >> last_x_assum irule >> gvs[DISJ_IMP_THM] >> rw[] >>
  first_x_assum drule >> rw[] >> gvs[]
QED

Theorem ALOOKUP_MAP_3:
  ∀f l. ALOOKUP (MAP (λ(x,y,z). (x,y,f z)) l) = OPTION_MAP (I ## f) o ALOOKUP l
Proof
  gen_tac >> Induct >> rw[FUN_EQ_THM] >>
  pairarg_tac >> gvs[] >> rw[]
QED

Theorem ZIP_EQ_APPEND:
  LENGTH xs = LENGTH ys ⇒
  (ZIP (xs,ys) = left ++ right ⇔
    ∃xs1 ys1 xs2 ys2. xs = xs1 ++ xs2 ∧ ys = ys1 ++ ys2 ∧ LENGTH xs1 = LENGTH ys1 ∧
     ZIP (xs1,ys1) = left ∧ ZIP (xs2,ys2) = right)
Proof
  simp[EQ_IMP_THM, SF DNF_ss] >> reverse conj_tac >>
  map_every qid_spec_tac [`right`,`left`,`ys`,`xs`] >> Induct >> rw[] >> gvs[]
  >- (Cases_on `xs1` >> gvs[] >> Cases_on `ys1` >> gvs[]) >>
  Cases_on `ys` >> gvs[] >> Cases_on `left` >> gvs[]
  >- (qexistsl [`[]`,`[]`] >> simp[]) >>
  last_x_assum $ qspecl_then [`t`,`t'`,`right`] mp_tac >> rw[] >>
  qexistsl [`h::xs1`,`h'::ys1`] >> simp[]
QED


(******************** Lazy lists ********************)

Theorem LNTH_NONE_LLENGTH:
  ∀ n l .
    LNTH n l = NONE
  ⇒ ∃ len.
      LLENGTH l = SOME len ∧
      len ≤ n
Proof
  Induct >> rw[] >>
  Cases_on `l` >> fs[LNTH] >>
  first_x_assum drule >>
  strip_tac >>
  qexists_tac `SUC len` >> fs[]
QED

Theorem LNTH_2:
  ∀ n ll. LNTH n ll =
        if n = 0 then LHD ll
        else OPTION_JOIN (OPTION_MAP (LNTH (n-1)) (LTL ll))
Proof
  rw[] \\ fs[LNTH] \\ Cases_on ‘n’ \\ fs[LNTH]
QED

Theorem LSET_fromList:
  ∀l. LSET (fromList l) = set l
Proof
  Induct \\ rw [fromList_def]
QED

Theorem ltree_lookup_APPEND:
  ∀ path1 path2 t.
    ltree_lookup t (path1 ++ path2) =
    OPTION_BIND (ltree_lookup t path1) (λsubtree. ltree_lookup subtree path2)
Proof
  Induct >> rw[optionTheory.OPTION_BIND_def] >>
  Cases_on `t` >> fs[ltree_lookup_def] >>
  Cases_on `LNTH h ts` >> fs[optionTheory.OPTION_BIND_def]
QED

Theorem ltree_lookup_SOME_gen_ltree:
  ∀ path f a ts.
    ltree_lookup (gen_ltree f) path = SOME (Branch a ts)
  ⇒ f path = (a, LLENGTH ts)
Proof
  Induct >> rw[]
  >- (
    Cases_on `f []` >> fs[] >>
    gvs[Once gen_ltree, ltree_lookup_def]
    ) >>
  Cases_on `f []` >> fs[] >> rename1 `f [] = (e1, e2)` >>
  rgs[Once gen_ltree, ltree_lookup_def] >>
  fs[LNTH_LGENLIST] >>
  Cases_on `e2` >> gvs[] >>
  Cases_on `h < x` >> fs[]
QED


(******************** Sets ********************)

Theorem EMPTY_iff_NOTIN:
  ∀s. s = {} ⇔ ∀x. x ∉ s
Proof
  rw[] >> eq_tac >> rw[] >>
  once_rewrite_tac[GSYM SUBSET_EMPTY] >>
  once_rewrite_tac[SUBSET_DEF] >> rw[]
QED

Theorem fresh_list:
  ∀s. FINITE s ⇒ ∃x. x ∉ s:('a list set)
Proof
  metis_tac[GSYM INFINITE_LIST_UNIV,NOT_IN_FINITE]
QED

Theorem DIFF_SUBSET:
  a DIFF b ⊆ c ⇔ a ⊆ b ∪ c
Proof
  rw[SUBSET_DEF, EXTENSION] >>
  eq_tac >> rw[] >> metis_tac[]
QED

Theorem UNION_DIFF_DISTRIBUTE:
  ∀A B C. A ∪ B DIFF C = (A DIFF C) ∪ (B DIFF C)
Proof
  rw[EXTENSION] >> metis_tac[]
QED

Theorem UNION_DIFF_EMPTY:
  ∀A B C. A ∪ B DIFF C = {} ⇒ B DIFF C = {}
Proof
  rw[EXTENSION] >> metis_tac[]
QED

Theorem monotone_compose:
  monotone f ∧ monotone g ⇒ monotone(f o g)
Proof
  rw[monotone_def,pred_setTheory.SUBSET_DEF,IN_DEF] >> res_tac >> metis_tac[]
QED

Theorem BIGUNION_DIFF:
  ∀as b. (BIGUNION as) DIFF b = BIGUNION (IMAGE (λa. a DIFF b) as)
Proof
  rw[EXTENSION] >> eq_tac >> rw[] >> gvs[]
  >- (qexists_tac `s DIFF b` >> fs[] >> goal_assum (drule_at Any) >> fs[])
  >- (goal_assum (drule_at Any) >> fs[])
QED

Theorem BIGUNION_DIFF_LIST_TO_SET:
  BIGUNION (set l) DIFF s = BIGUNION (set (MAP (λx. x DIFF s) l))
Proof
  rw[Once EXTENSION, MEM_MAP] >> eq_tac >> rw[PULL_EXISTS] >>
  goal_assum drule >> simp[]
QED

Theorem IMAGE_K_EMPTY:
  IMAGE (λx. {}) s = if s = {} then {} else {{}}
Proof
  rw[Once EXTENSION] >> eq_tac >> rw[] >> gvs[MEMBER_NOT_EMPTY]
QED


(******************** sptrees ********************)

Theorem wf_list_to_num_set:
  ∀l. wf (list_to_num_set l)
Proof
  Induct >> rw[list_to_num_set_def] >>
  irule wf_insert >> simp[]
QED

Theorem lrnext_alt_thm:
  ∀n. sptree$lrnext n = 2 ** (LOG 2 (n + 1))
Proof
  strip_tac >> completeInduct_on `n` >> rw[] >>
  rw[Once lrnext_def] >>
  first_x_assum $ qspec_then `(n - 1) DIV 2` mp_tac >>
  impl_tac >> rw[] >- simp[DIV_LT_X] >>
  simp[GSYM EXP] >> Cases_on `EVEN n` >>
  gvs[GSYM ODD_EVEN] >> imp_res_tac EVEN_ODD_EXISTS >> gvs[]
  >- (
    `(2 * m - 1) DIV 2 = m - 1` by intLib.ARITH_TAC >> simp[] >>
    simp[LOG_add_digit]
    )
  >- (
    once_rewrite_tac[Once MULT_COMM] >> simp[MULT_DIV] >>
    simp[ADD1] >> simp[Once LOG_RWT, SimpRHS] >>
    once_rewrite_tac[MULT_COMM] >> simp[ADD_DIV_ADD_DIV]
    )
QED

Theorem lrnext_lrnext:
  ∀n. sptree$lrnext (n + sptree$lrnext n) = 2 * sptree$lrnext n
Proof
  rw[lrnext_alt_thm] >>
  qpat_abbrev_tac `m = n + 1` >>
  `n + (2 ** LOG 2 m + 1) = m + 2 ** LOG 2 m` by (unabbrev_all_tac >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  Cases_on `m = 0` >> gvs[] >>
  `m + 2 ** LOG 2 m = 2 ** (LOG 2 m + 1) + m MOD 2 ** LOG 2 m` by (
    qspec_then `m` mp_tac $ GSYM LOG_MOD >> impl_tac >- simp[] >>
    simp[GSYM ADD1, EXP]) >>
  pop_assum SUBST_ALL_TAC >>
  once_rewrite_tac[ADD_COMM] >>
  DEP_REWRITE_TAC[LOG_ADD] >> simp[GSYM ADD1, EXP] >>
  qmatch_goalsub_abbrev_tac `_ MOD a` >>
  `a ≠ 0` by (unabbrev_all_tac >> simp[]) >>
  qspecl_then [`m`,`a`] mp_tac MOD_LESS >>
  impl_tac >- simp[] >> intLib.ARITH_TAC
QED

Theorem lrnext_lrnext_2:
  ∀n k. sptree$lrnext (n + 2 * sptree$lrnext n) = 2 * sptree$lrnext n
Proof
  rw[lrnext_alt_thm] >>
  qpat_abbrev_tac `m = n + 1` >>
  `n + (2 * 2 ** LOG 2 m + 1) = m + 2 * 2 ** LOG 2 m` by (unabbrev_all_tac >> simp[]) >>
  `n + 2 = m + 1` by (unabbrev_all_tac >> simp[]) >>
  ntac 2 $ pop_assum SUBST_ALL_TAC >>
  Cases_on `m = 0` >> gvs[] >>
  simp[GSYM EXP] >> DEP_REWRITE_TAC[LOG_ADD] >> simp[] >>
  qspecl_then [`2`,`m`] mp_tac LOG >> simp[ADD1]
QED

Theorem wf_difference:
  ∀t1 t2. wf t1 ⇒ wf (difference t1 t2)
Proof
  Induct >> rw[difference_def] >>
  CASE_TAC >> gvs[wf_def] >> metis_tac[wf_mk_BN, wf_mk_BS]
QED

(******************** mlstring ********************)

Theorem INFINITE_mlstring:
  INFINITE 𝕌(:mlstring)
Proof
  strip_assume_tac explode_BIJ
  \\ strip_tac
  \\ drule_all pred_setTheory.FINITE_BIJ
  \\ simp [INFINITE_LIST_UNIV]
QED

Theorem COUNTABLE_char:
  COUNTABLE 𝕌(:char)
Proof
  rw [countable_def]
  \\ qexists_tac ‘ORD’
  \\ rw [INJ_DEF, ORD_11]
QED

Theorem COUNTABLE_mlstring:
  COUNTABLE 𝕌(:mlstring)
Proof
  ‘COUNTABLE 𝕌(:string)’
     by metis_tac [cardinalTheory.COUNTABLE_LIST_UNIV, COUNTABLE_char]
  \\ gvs [countable_def, INJ_DEF]
  \\ qexists ‘f o explode’ \\ gvs [] \\ rw []
  \\ gvs [oneline explode_thm]
  \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ gvs []
QED

(****************************************)

Theorem LIST_REL_MEM:
  ∀xs ys. LIST_REL P xs ys ∧ MEM x xs ⇒ ∃y. MEM y ys ∧ P x y
Proof
  Induct \\ Cases_on ‘ys’ \\ fs [] \\ rw []
  \\ res_tac \\ fs [] \\ metis_tac []
QED

Theorem LIST_REL_MEM_ALT:
  ∀xs ys. LIST_REL P xs ys ∧ MEM y ys ⇒ ∃x. MEM x xs ∧ P x y
Proof
  Induct \\ Cases_on ‘ys’ \\ fs [] \\ rw []
  \\ res_tac \\ fs [] \\ metis_tac []
QED

Theorem LIST_REL_MAP_MAP:
  LIST_REL P (MAP f xs) (MAP g xs) = EVERY (λx. P (f x) (g x)) xs
Proof
  Induct_on ‘xs’ \\ fs []
QED

Theorem LIST_REL_SWAP:
  ∀R xs ys. LIST_REL R xs ys = LIST_REL (λx y. R y x) ys xs
Proof
  Induct_on ‘xs’ \\ fs []
QED

Theorem LIST_REL_MAP:
  ∀xs ys.
    LIST_REL R (MAP f xs) (MAP g ys) =
    LIST_REL (λx y. R (f x) (g y)) xs ys
Proof
  Induct \\ fs [MAP_EQ_CONS,PULL_EXISTS]
QED

Theorem FST_INTRO:
  (λ(p1,p2). p1) = FST
Proof
  fs [FUN_EQ_THM,FORALL_PROD]
QED

Theorem SND_INTRO:
  (λ(p1,p2). p2) = SND
Proof
  fs [FUN_EQ_THM,FORALL_PROD]
QED

Theorem LIST_REL_COMP:
  ∀xs ys zs.
    LIST_REL f xs ys ∧ LIST_REL g ys zs ⇒
    LIST_REL (λx z. ∃y. f x y ∧ g y z) xs zs
Proof
  Induct \\ fs [PULL_EXISTS]
  \\ metis_tac []
QED

Theorem LIST_REL_IMP_MAP_EQ:
  ∀xs ys P f g.
    (∀x y. MEM x xs ∧ MEM y ys ∧ P x y ⇒ f x = g y) ⇒
    LIST_REL P xs ys ⇒ MAP g ys = MAP f xs
Proof
  Induct \\ fs [PULL_EXISTS,SF DNF_ss] \\ metis_tac []
QED

Theorem FORALL_FRANGE:
  (∀x. x IN FRANGE v ⇒ p x) ⇔ ∀k x. FLOOKUP v k = SOME x ⇒ p x
Proof
  fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS]
QED

Theorem MAP_FST_ZIP:
  ∀xs ys. LENGTH xs = LENGTH ys ⇒ MAP FST (ZIP (xs,ys)) = xs
Proof
  gvs [MAP_ZIP]
QED

Theorem MAP_SND_ZIP:
  ∀xs ys. LENGTH xs = LENGTH ys ⇒ MAP SND (ZIP (xs,ys)) = ys
Proof
  gvs [MAP_ZIP]
QED

Theorem FLOOKUP_FUPDATE_LIST:
  ∀xs k m. FLOOKUP (m |++ xs) k =
           case ALOOKUP (REVERSE xs) k of
           | NONE => FLOOKUP m k
           | SOME x => SOME x
Proof
  Induct \\ fs [FUPDATE_LIST,FORALL_PROD,ALOOKUP_APPEND]
  \\ fs [FLOOKUP_UPDATE]
  \\ rw [] \\ fs []
  \\ CASE_TAC \\ fs []
QED

Theorem FDIFF_SING:
  FDIFF f {x} = f \\ x
Proof
  fs [FDIFF_def,fmap_EXT,DRESTRICT_DEF,DOMSUB_FAPPLY_NEQ]
  \\ gvs [EXTENSION]
QED

Theorem LIST_REL_same: (* TODO: auto? *)
  ∀xs. LIST_REL R xs xs = EVERY (λx. R x x) xs
Proof
  Induct \\ fs []
QED

Theorem MAP_ID_EQ:
  ∀xs f. (MAP f xs = xs) ⇔ ∀x. MEM x xs ⇒ f x = x
Proof
  Induct \\ fs [] \\ metis_tac []
QED

Theorem MEM_IMP_EQ:
  ∀b1 k p1 p2.
    MEM (k,p1) b1 ∧ MEM (k,p2) b1 ∧ ALL_DISTINCT (MAP FST b1) ⇒ p1 = p2
Proof
  Induct \\ fs [FORALL_PROD] \\ rw []
  \\ fs [MEM_MAP,EXISTS_PROD]
  \\ res_tac \\ fs []
QED

Theorem LIST_REL_MAP_CONG:
  ∀xs ys R Q f.
    (∀x y. R x y ∧ MEM x xs ∧ MEM y ys ⇒ Q (f x) (f y)) ∧ LIST_REL R xs ys ⇒
    LIST_REL Q (MAP f xs) (MAP f ys)
Proof
  Induct \\ fs [PULL_EXISTS] \\ metis_tac []
QED

Theorem ALL_DISTINCT_MEM_MEM:
  ALL_DISTINCT (MAP FST xs) ∧ MEM (x,y) xs ∧ MEM (x,y1) xs ⇒ y = y1
Proof
  rw [] \\ pop_assum mp_tac
  \\ rewrite_tac [MEM_SPLIT]
  \\ strip_tac \\ gvs []
  \\ gvs [MEM_SPLIT]
  \\ gvs [ALL_DISTINCT_APPEND,SF DNF_ss]
QED

