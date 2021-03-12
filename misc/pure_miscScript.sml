
open HolKernel Parse boolLib bossLib term_tactic BasicProvers;
open stringTheory optionTheory pairTheory listTheory alistTheory llistTheory
     finite_mapTheory pred_setTheory arithmeticTheory rich_listTheory
     ltreeTheory fixedPointTheory

val _ = new_theory "pure_misc";


(******************** Finite maps ********************)

Theorem FDIFF_FUNION:
  ∀fm1 fm2 s. FDIFF (fm1 ⊌ fm2) s = (FDIFF fm1 s) ⊌ (FDIFF fm2 s)
Proof
  rw[FDIFF_def, DRESTRICTED_FUNION] >>
  rw[fmap_eq_flookup] >>
  rw[FLOOKUP_DRESTRICT, FLOOKUP_FUNION] >> fs[] >>
  rw[FLOOKUP_DEF]
QED

Theorem BIGUNION_DIFF:
  ∀as b. (BIGUNION as) DIFF b = BIGUNION {a DIFF b | a ∈ as}
Proof
  rw[EXTENSION] >> eq_tac >> rw[] >> gvs[]
  >- (
    qexists_tac `s DIFF b` >> fs[] >>
    goal_assum (drule_at Any) >> fs[]
    )
  >- (
    goal_assum (drule_at Any) >> fs[]
    )
QED

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

Theorem DISJOINT_DRESTRICT_FEMPTY:
  ∀m s. DISJOINT s (FDOM m) ⇒ DRESTRICT m s = FEMPTY
Proof
  Induct >> rw[]
QED

Theorem fdiff_fdomsub_commute:
  FDIFF (f \\ x) p = FDIFF f p \\ x
Proof
  rw[fmap_eq_flookup,FDIFF_def,FLOOKUP_DRESTRICT,DOMSUB_FLOOKUP_THM] >> rw[]
QED

Theorem fdiff_fdomsub_INSERT:
  FDIFF (f \\ x) p = FDIFF f (x INSERT p)
Proof
  rw[fmap_eq_flookup,FDIFF_def,FLOOKUP_DRESTRICT,DOMSUB_FLOOKUP_THM] >> rw[] >> gvs[]
QED

Theorem fdiff_bound:
  FDIFF f p = FDIFF f (p ∩ FDOM f)
Proof
  rw[FDIFF_def,fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
  rw[] >> gvs[flookup_thm]
QED

Theorem FLOOKUP_FMAP_MAP2:
  ∀f m k. FLOOKUP (FMAP_MAP2 f m) k = OPTION_MAP (λv. f (k,v)) (FLOOKUP m k)
Proof
  rw[FLOOKUP_DEF, FMAP_MAP2_def, FUN_FMAP_DEF]
QED

Theorem DOMSUB_FMAP_MAP2:
  ∀f m s. (FMAP_MAP2 f m) \\ s = FMAP_MAP2 f (m \\ s)
Proof
  rw[fmap_eq_flookup, DOMSUB_FLOOKUP_THM, FLOOKUP_FMAP_MAP2] >>
  IF_CASES_TAC >> simp[]
QED

Theorem fmap_rel_fupdate_list_MAP_FST:
  ∀R f1 f2 l1 l2.
    fmap_rel R (f1 |++ l1) (f2 |++ l2)
  ⇒ set (MAP FST l1) ∪ FDOM f1 = set (MAP FST l2) ∪ FDOM f2
Proof
  rw[fmap_rel_def, FDOM_FUPDATE_LIST] >>
  gvs[EXTENSION] >> metis_tac[]
QED

(* This exists in finite_mapTheory, but with types unnecessarily specialised *)
Theorem fmap_rel_FEMPTY2:
  (fmap_rel (R : 'a -> 'b -> bool) FEMPTY (f1 : 'c |-> 'b) ⇔ f1 = FEMPTY) ∧
  (fmap_rel R (f2 : 'c |-> 'a) FEMPTY ⇔ f2 = FEMPTY)
Proof
  rw[fmap_rel_def] >> simp[FDOM_EQ_EMPTY] >> eq_tac >> rw[]
QED

Theorem fmap_rel_FUPDATE_I_rewrite:
  fmap_rel R (f1 \\ k) (f2 \\ k) ∧ R v1 v2 ⇔
  fmap_rel R (f1 |+ (k,v1)) (f2 |+ (k,v2))
Proof
  gvs[fmap_rel_OPTREL_FLOOKUP, FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM] >>
  reverse (eq_tac >> rw[])
  >- (pop_assum (qspec_then `k` mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `k'` mp_tac) >> simp[] >>
  EVERY_CASE_TAC >> gvs[]
QED

Theorem fmap_rel_ind:
  ∀R FR.
    FR FEMPTY FEMPTY ∧
    (∀k v1 v2 f1 f2.
      R v1 v2 ∧ FR (f1 \\ k) (f2 \\ k) ⇒ FR (f1 |+ (k,v1)) (f2 |+ (k,v2)))
  ⇒ ∀f1 f2. fmap_rel R f1 f2 ⇒ FR f1 f2
Proof
  rpt gen_tac >> strip_tac >>
  Induct >> rw[] >- gvs[fmap_rel_FEMPTY2] >>
  `x ∈ FDOM f2` by gvs[fmap_rel_def] >>
  imp_res_tac FM_PULL_APART >> gvs[] >>
  last_x_assum irule >> gvs[DOMSUB_NOT_IN_DOM] >>
  gvs[GSYM fmap_rel_FUPDATE_I_rewrite] >>
  first_x_assum irule >>
  gvs[DOMSUB_NOT_IN_DOM]
QED

Theorem FDIFF_FDIFF:
  ∀fm s1 s2. FDIFF (FDIFF fm s1) s2 = FDIFF fm (s1 ∪ s2)
Proof
  rw[FDIFF_def, DRESTRICT_DRESTRICT, fmap_eq_flookup, FLOOKUP_DRESTRICT]
QED

Theorem DOMSUB_FUPDATE_LIST:
  ∀l m x. (m |++ l) \\ x = (m \\ x) |++ (FILTER ($<> x o FST) l)
Proof
  Induct >> rw[FUPDATE_LIST_THM, fmap_eq_flookup] >>
  PairCases_on `h` >> gvs[] >>
  gvs[flookup_fupdate_list, DOMSUB_FLOOKUP_THM, FLOOKUP_UPDATE] >>
  CASE_TAC >> gvs[]
QED

Theorem FLOOKUP_FDIFF:
  FLOOKUP (FDIFF fm s) k = if k ∈ s then NONE else FLOOKUP fm k
Proof
  rw[FDIFF_def, FLOOKUP_DRESTRICT] >> gvs[]
QED

Theorem FDIFF_FUPDATE:
  FDIFF (fm |+ (k,v)) s =
  if k ∈ s then FDIFF fm s else (FDIFF fm s) |+ (k,v)
Proof
  rw[fmap_eq_flookup, FLOOKUP_FDIFF, FLOOKUP_UPDATE] >>
  EVERY_CASE_TAC >> gvs[]
QED

Theorem FDIFF_FEMPTY[simp]:
  FDIFF FEMPTY s = FEMPTY
Proof
  rw[fmap_eq_flookup, FLOOKUP_FDIFF]
QED


(******************** Functions/Pairs ********************)

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
  ∀l1 l2 k (v:'a).
    ALOOKUP l1 k = SOME v ∧
    MAP FST l1 = MAP FST l2
  ⇒ ∃v'. ALOOKUP l2 k = SOME (v':'a) ∧
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
  ∀(R:'a -> 'a -> bool) l1 l2.
    LIST_REL R (MAP SND l1) (MAP SND l2) ∧ MAP FST l1 = MAP FST l2
  ⇒ ∀k. OPTREL R (ALOOKUP l1 k) (ALOOKUP l2 k) ∧
        OPTREL R (ALOOKUP (REVERSE l1) k) (ALOOKUP (REVERSE l2) k)
Proof
  rw[LIST_REL_EL_EQN]
  >- (
    Cases_on `ALOOKUP l1 k` >> Cases_on `ALOOKUP l2 k` >> gvs[ALOOKUP_NONE] >>
    imp_res_tac ALOOKUP_SOME >> gvs[] >>
    drule ALOOKUP_SOME_EL_2 >>
    disch_then (qspec_then `l1` assume_tac) >> gvs[] >>
    last_x_assum drule >> simp[EL_MAP]
    )
  >- (
    Cases_on `ALOOKUP (REVERSE l1) k` >>
    Cases_on `ALOOKUP (REVERSE l2) k` >> gvs[ALOOKUP_NONE] >>
    imp_res_tac ALOOKUP_SOME >> gvs[MAP_REVERSE] >>
    drule ALOOKUP_SOME_EL_2 >>
    disch_then (qspec_then `REVERSE l1` assume_tac) >> gvs[MAP_REVERSE] >>
    drule (GSYM EL_REVERSE) >>
    qspecl_then [`n`,`l1`] mp_tac (GSYM EL_REVERSE) >> rw[] >> gvs[] >>
    qmatch_asmsub_abbrev_tac `EL k1 _` >>
    `k1 < LENGTH l2` by (unabbrev_all_tac >> DECIDE_TAC) >>
    last_x_assum drule >> simp[EL_MAP]
    )
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
  gvs[Once gen_ltree, ltree_lookup_def] >>
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

(****************************************)

val _ = export_theory();
