
open HolKernel Parse boolLib bossLib term_tactic BasicProvers dep_rewrite;
open arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory pred_setTheory finite_mapTheory;
open pure_miscTheory pure_cexpTheory pureLangTheory
     pure_expTheory pure_exp_lemmasTheory;

val _ = new_theory "pure_cexp_lemmas";

Theorem silly_cong_lemma[local]:
  ((∀a b. MEM (a,b) l2 ⇒ P a b) ⇔ (∀p. MEM p l2 ⇒ P (FST p) (SND p))) ∧
  ((∀a b c. MEM (a,b,c) l3 ⇒ Q a b c) ⇔
     (∀t. MEM t l3 ⇒ Q (FST t) (FST (SND t)) (SND (SND t))))
Proof
  simp[FORALL_PROD]
QED

Theorem freevars_cexp_equiv:
  ∀ce. freevars_cexp ce = set (freevars_cexp_l ce)
Proof
  recInduct freevars_cexp_ind >> simp[FORALL_OPTION] >>
  rw[] >>
  gvs[LIST_TO_SET_FLAT, MAP_MAP_o, combinTheory.o_DEF, Cong MAP_CONG,
      LIST_TO_SET_FILTER, UNCURRY, silly_cong_lemma] >>
  simp[Once EXTENSION, MEM_MAP, PULL_EXISTS, cepat_vars_l_correct] >>
  every_case_tac >> gvs[] >> metis_tac[]
QED

Theorem freevars_lets_for:
  ∀c v l b. freevars (lets_for c v l b) =
    case l of
      [] => freevars b DIFF set (MAP SND l)
    | _ => v INSERT (freevars b DIFF set (MAP SND l))
Proof
  recInduct lets_for_ind >> rw[lets_for_def] >>
  CASE_TAC >> gvs[] >> simp[EXTENSION] >> metis_tac[]
QED

Theorem freevars_rows_of:
  ∀v k l.
    freevars (rows_of v k l) =
    case l of
      [] => freevars k
    | _ => v INSERT freevars k ∪
           BIGUNION (set (MAP (λ(cn,vs,b). freevars b DIFF set vs) l))
Proof
  recInduct rows_of_ind >> rw[rows_of_def] >> simp[freevars_lets_for] >>
  Cases_on `rest` >> gvs[combinTheory.o_DEF] >>
  CASE_TAC >> gvs[EXTENSION] >> metis_tac[]
QED

Theorem set_MAPK[local]:
  set (MAP (λx. y) ps) = case ps of [] => ∅ | _ => {y}
Proof
   Induct_on ‘ps’ >> simp[] >> Cases_on ‘ps’ >> simp[]
QED

Theorem freevars_patguards:
  ∀eps gd binds.
    patguards eps = (gd, binds) ⇒
    freevars gd ⊆ BIGUNION (set (MAP (freevars o FST) eps)) ∧
    BIGUNION (set (MAP (freevars o SND) binds)) ⊆
    BIGUNION (set (MAP (freevars o FST) eps))
Proof
  recInduct patguards_ind >>
  simp[patguards_def, AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >>
  gvs[] >>~-
  ([‘MAPi’],
   pairarg_tac >> gvs[] >> gvs[combinTheory.o_DEF, set_MAPK] >>
   Cases_on ‘ps’ >> gvs[] >> gvs[SUBSET_DEF]) >>
  Cases_on ‘patguards eps’ >> gvs[] >> rw[] >> gvs[SUBSET_DEF]
QED

Theorem freevars_FOLDR_LetUB:
  (∀v b. MEM (v,b) binds ⇒ freevars b ⊆ B)
  ⇒
  freevars (FOLDR (λ(v,e) A. Let (explode v) e A) base binds) ⊆
  (freevars base DIFF set (MAP (explode o FST) binds)) ∪ B
Proof
  Induct_on ‘binds’ >> simp[FORALL_PROD] >> rw[] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  first_x_assum $ drule_at Any >>
  gs[SUBSET_DEF]
QED

Theorem freevars_FOLDR_LetLB:
  freevars base DIFF IMAGE explode (set (MAP FST binds)) ⊆
  freevars (FOLDR (λ(v,e) A. Let (explode v) e A) base binds)
Proof
  Induct_on ‘binds’ >> simp[FORALL_PROD, DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt strip_tac >> gs[SUBSET_DEF]
QED

Theorem patguards_binds_pvars:
  ∀eps gd binds.
    patguards eps = (gd, binds) ⇒
    set (MAP FST binds) = BIGUNION (set (MAP (cepat_vars o SND) eps))
Proof
  recInduct patguards_ind >>
  simp[combinTheory.o_DEF, patguards_def, AllCaseEqs(), PULL_EXISTS,
       FORALL_PROD] >> rpt strip_tac >> gvs[]
  >~ [‘patguards _ = (_, _)’]
  >- (Cases_on ‘patguards eps’ >> gvs[] >> simp[INSERT_UNION_EQ]) >>
  pairarg_tac >> gvs[SF ETA_ss]
QED

Theorem patguards_onebound_preserved:
  ∀eps gd binds.
    patguards eps = (gd, binds) ∧ (∀e p. MEM (e,p) eps ⇒ freevars e = B) ⇒
    (∀v e. MEM (v,e) binds ⇒ freevars e = B)
Proof
  recInduct patguards_ind >>
  simp[combinTheory.o_DEF, patguards_def, AllCaseEqs(), PULL_EXISTS,
       FORALL_PROD] >> rpt strip_tac >> gvs[]
  >~ [‘patguards eps = (_, _)’]
  >- (
    Cases_on ‘patguards eps’ >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
    metis_tac[]
    )
  >~ [‘patguards eps = (_, _)’]
  >- (
    Cases_on ‘patguards eps’ >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
    metis_tac[]
    ) >>
  pairarg_tac >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM, indexedListsTheory.MEM_MAPi,
      PULL_EXISTS] >> metis_tac[]
QED

Theorem freevars_nested_rows_UB:
  freevars (nested_rows e pes) ⊆
  if pes = [] then ∅
  else
    freevars e ∪
    BIGUNION
      (set (MAP (λ(p,e). freevars e DIFF IMAGE explode (cepat_vars p)) pes))
Proof
  Induct_on ‘pes’ >> simp[FORALL_PROD] >> qx_genl_tac [‘p’, ‘e0’] >>
  pairarg_tac >> simp[] >> rpt strip_tac
  >- (drule $ cj 1 freevars_patguards >> simp[] >>
      simp[SUBSET_DEF])
  >- (drule patguards_onebound_preserved >> simp[] >> strip_tac >>
      simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD, FORALL_PROD] >>
      qx_gen_tac ‘fv’ >> strip_tac >>
      drule_at Any $ SRULE [SUBSET_DEF] freevars_FOLDR_LetUB >>
      disch_then (qspec_then ‘freevars e’ mp_tac) >>
      simp[MEM_MAP, PULL_EXISTS, FORALL_PROD] >> impl_tac
      >- metis_tac[] >> rw[] >> simp[] >>
      drule patguards_binds_pvars >> simp[] >>
      simp[EXTENSION, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  Cases_on ‘pes = []’ >> gs[] >>
  gs[SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> metis_tac[]
QED

Theorem freevars_nested_rows_LB:
  BIGUNION
    (set (MAP (λ(p,e). freevars e DIFF IMAGE explode (cepat_vars p)) pes)) ⊆
  freevars (nested_rows e pes)
Proof
  Induct_on ‘pes’ >> simp[FORALL_PROD] >> rpt strip_tac >>
  pairarg_tac >> simp[] >~
  [‘freevars base DIFF IMAGE explode (cepat_vars pat) ⊆ _’]
  >- (drule patguards_onebound_preserved >> simp[] >> strip_tac >>
      drule_then (mp_tac o SYM) patguards_binds_pvars >>
      simp[] >> strip_tac >>
      irule SUBSET_TRANS >> irule_at Any freevars_FOLDR_LetLB >>
      simp[SUBSET_DEF]) >>
  gs[SUBSET_DEF]
QED

Theorem IMAGE_explode_DELETE[local]:
  IMAGE explode (s DELETE v) = IMAGE explode s DELETE explode v
Proof
  simp[EXTENSION, PULL_EXISTS] >> metis_tac[mlstringTheory.explode_11]
QED

Theorem freevars_IfDisj:
  ∀a v e. freevars (IfDisj v a e) =
    case a of
    | [] => freevars e
    | _ => explode v INSERT freevars e
Proof
  Induct >> rw[IfDisj_def, Disj_def] >>
  PairCases_on `h` >> gvs[IfDisj_def, Disj_def] >>
  simp[GSYM INSERT_SING_UNION, INSERT_UNION_EQ] >> CASE_TAC >> gvs[]
QED

val _ = temp_delsimps ["nested_rows_def"]
Theorem freevars_exp_of:
  ∀ce. freevars (exp_of ce) = IMAGE explode $ freevars_cexp ce
Proof
  recInduct freevars_cexp_ind >> simp[FORALL_OPTION] >> rw[exp_of_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, Cong MAP_CONG, UNCURRY,
      silly_cong_lemma, freevars_rows_of]>>
  simp[SF ETA_ss] >>~-
  ([‘nested_rows (Var (explode gv)) ((pat1, exp_of e1) :: MAP _ pes)’],
   irule SUBSET_ANTISYM >> conj_tac
   >- (simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
       rpt strip_tac >>
       drule (SRULE [SUBSET_DEF] freevars_nested_rows_UB) >>
       simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
       gs[FORALL_PROD] >> rpt strip_tac >>
       gvs[] >>
       last_x_assum $ drule_then assume_tac >> gvs[] >> metis_tac[]) >>
   simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> rpt strip_tac >>
   rename [‘explode vv ∈ freevars (nested_rows _ _) ∨ _’] >> disj1_tac >>
   irule (SRULE [SUBSET_DEF] freevars_nested_rows_LB) >>
   simp[MAP_MAP_o, MEM_MAP, EXISTS_PROD, combinTheory.o_ABS_R, PULL_EXISTS]>>
   gs[FORALL_PROD] >> metis_tac[IN_IMAGE])
  >~ [‘MEM v (FLAT (MAP _ css))’]
  >- (
    Cases_on ‘css’ >> gs[IMAGE_explode_DELETE, AC UNION_COMM UNION_ASSOC] >>
    every_case_tac >> gvs[freevars_IfDisj] >> every_case_tac >> gvs[] >>
    PairCases_on ‘h’ >> gvs[] >>
    gs[DISJ_IMP_THM, FORALL_AND_THM] >>
    simp[Once EXTENSION, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    metis_tac[mlstringTheory.explode_11]
    )
  >~ [‘MEM v (FLAT (MAP _ css))’]
  >- (
    Cases_on ‘css’ >> gs[IMAGE_explode_DELETE, AC UNION_COMM UNION_ASSOC] >>
    every_case_tac >> gvs[freevars_IfDisj] >> every_case_tac >> gvs[] >>
    PairCases_on ‘h’ >> gvs[] >>
    gs[DISJ_IMP_THM, FORALL_AND_THM] >>
    simp[Once EXTENSION, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    metis_tac[mlstringTheory.explode_11]
    )
  >>~- (
    [‘MEM v (FLAT (MAP _ css))’],
    Cases_on ‘css’ >> gs[IMAGE_explode_DELETE, AC UNION_COMM UNION_ASSOC] >>
    every_case_tac >> gvs[freevars_IfDisj] >> every_case_tac >> gvs[] >>
    gs[DISJ_IMP_THM, FORALL_AND_THM] >>
    simp[Once EXTENSION, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    metis_tac[mlstringTheory.explode_11]
    ) >>
  simp[Once EXTENSION, MEM_MAP, PULL_EXISTS] >>
  metis_tac[mlstringTheory.explode_11]
QED

Theorem subst_lets_for:
  ∀cn v l e f.  v ∉ FDOM f ⇒
    subst f (lets_for cn v l e) =
    lets_for cn v l (subst (FDIFF f (set (MAP SND l))) e)
Proof
  recInduct lets_for_ind >> rw[lets_for_def, subst_def] >>
  simp[FLOOKUP_DEF, FDIFF_FDOMSUB_INSERT]
QED

Theorem subst_rows_of:
  ∀v k l f.  v ∉ FDOM f ⇒
    subst f (rows_of v k l) =
    rows_of v (subst f k) (MAP (λ(a,b,c). (a,b, subst (FDIFF f (set b)) c)) l)
Proof
  recInduct rows_of_ind >> rw[rows_of_def, subst_def]
  >- simp[FLOOKUP_DEF] >>
  simp[subst_lets_for, combinTheory.o_DEF]
QED

Theorem subst_Disj:
  ∀cn_ars v. v ∉ FDOM f ⇒ subst f (Disj v cn_ars) = Disj v cn_ars
Proof
  Induct >> rw[Disj_def, subst_def] >>
  PairCases_on `h` >> rw[Disj_def, subst_def] >> gvs[FLOOKUP_DEF]
QED

Theorem subst_IfDisj:
  ∀a v e f. explode v ∉ FDOM f ⇒ subst f (IfDisj v a e) = IfDisj v a (subst f e)
Proof
  Induct >> rw[IfDisj_def, Disj_def, subst_def] >>
  PairCases_on `h` >> rw[Disj_def, subst_def]
  >- gvs[FLOOKUP_DEF]
  >- simp[subst_Disj]
QED

Theorem subst_FOLDR_Let:
  ∀f B.
    FDOM f ∩ B = ∅ ∧ (∀v e. MEM (v,e) l ⇒ freevars e ⊆ B) ⇒
    subst f (FOLDR (λ(u,e) A. Let (explode u) e A) base l) =
    FOLDR (λ(u,e) A. Let (explode u) e A)
          (subst (FDIFF f (IMAGE explode (set (MAP FST l)))) base)
          l
Proof
  Induct_on ‘l’ >>
  simp[FORALL_PROD, DISJ_IMP_THM, FORALL_AND_THM, subst_def] >>
  rpt strip_tac
  >- (rename [‘subst (f \\ explode vnm) (FOLDR _ _ _)’] >>
      ‘FDOM (f \\ explode vnm) ∩ B = ∅’ by simp[DELETE_INTER] >>
      first_x_assum drule_all >> simp[] >> disch_then kall_tac >>
      simp[FDIFF_FDOMSUB_INSERT]) >>
  irule subst_ignore >> irule SUBSET_DISJOINT >>
  irule_at (Pat ‘FDOM f ⊆ _’) SUBSET_REFL >>
  metis_tac[DISJOINT_DEF, INTER_COMM]
QED

Theorem patguards_subst:
  ∀eps gd binds f.
    patguards eps = (gd,binds) ⇒
    patguards (MAP (subst f ## I) eps) = (subst f gd, MAP (I ## subst f) binds)
Proof
  recInduct patguards_ind >> simp[patguards_def, FORALL_PROD] >> rw[] >>
  rename [‘cepat_CASE pat’] >>
  Cases_on ‘pat’ >> gvs[] >>
  pairarg_tac >> gs[] >> pairarg_tac >> gvs[subst_def, combinTheory.o_ABS_R]
QED

Theorem subst_nested_rows:
  FDOM f ∩ freevars e = ∅ ⇒
  subst f (nested_rows e pes) =
  nested_rows e
    (MAP (λ(p,e). (p, subst (FDIFF f (IMAGE explode $ cepat_vars p)) e)) pes)
Proof
  strip_tac >> Induct_on ‘pes’ >> simp[FORALL_PROD, nested_rows_def] >>
  qx_genl_tac [‘p’, ‘e0’] >> pairarg_tac >> simp[subst_def] >> conj_tac
  >- (irule subst_ignore >> simp[DISJOINT_DEF] >>
      drule freevars_patguards >> simp[] >> rpt strip_tac >>
      map_every (fn q => qpat_x_assum q mp_tac)
                [‘FDOM _ ∩ _ = ∅’, ‘freevars _ ⊆ freevars _’] >>
      simp[SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
  drule_then (assume_tac o SYM) patguards_binds_pvars >> gs[] >>
  irule subst_FOLDR_Let >> first_assum $ irule_at Any >>
  rpt strip_tac >> rename [‘freevars e0 ⊆ freevars e’] >>
  ‘freevars e0 = freevars e’ suffices_by simp[] >>
  irule patguards_onebound_preserved >> rpt (first_assum $ irule_at Any) >>
  simp[]
QED

Theorem FDIFF_FUN_FMAP:
  FINITE P ⇒
  FDIFF (FUN_FMAP f P) A = FUN_FMAP f (P DIFF A)
Proof
  simp[fmap_EXT, FDOM_FDIFF_alt, FDIFF_def, DRESTRICT_DEF, FUN_FMAP_DEF]
QED

Theorem FDOM_f_o_implode:
  { x | implode x ∈ FDOM fm } = IMAGE explode (FDOM fm) ∧
  FDOM (fm f_o implode) = IMAGE explode (FDOM fm)
Proof
  conj_asm1_tac
  >- (simp[EXTENSION, EQ_IMP_THM, PULL_EXISTS] >>
      metis_tac[mlstringTheory.explode_implode]) >>
  simp[FDOM_f_o]
QED

Theorem FUN_FMAP_IMAGE:
  FINITE A ⇒
  FUN_FMAP f (IMAGE explode A) = FUN_FMAP (f o explode) A f_o implode
Proof
  strip_tac >>
  simp[fmap_EXT, PULL_EXISTS, FUN_FMAP_DEF, FAPPLY_f_o, FDOM_f_o_implode]
QED

Theorem FUN_FMAP_CONG:
  A1 = A2 ∧ FINITE A2 ∧ (∀x. x ∈ A2 ⇒ f1 x = f2 x) ⇒
  FUN_FMAP f1 A1 = FUN_FMAP f2 A2
Proof
  rw[] >> simp[fmap_EXT, FUN_FMAP_DEF]
QED

Theorem FUN_FMAP_DELETE:
  FUN_FMAP (λx. g ((f \\ v) ' x)) (FDOM f DELETE v) =
  FUN_FMAP (λx. g (f ' x)) (FDOM f DELETE v)
Proof
  simp[Cong FUN_FMAP_CONG, DOMSUB_FAPPLY_THM]
QED

Theorem f_o_implode_DOMSUB_explode:
  f f_o implode \\ explode v = (f \\ v) f_o implode
Proof
  simp[fmap_EXT, FDOM_f_o, FDOM_f_o_implode, PULL_EXISTS, FAPPLY_f_o,
       DOMSUB_FAPPLY_THM] >>
  simp[EXTENSION, PULL_EXISTS] >>
  metis_tac[mlstringTheory.explode_11]
QED

Theorem FUN_FMAP_DOMSUB:
  FINITE A ⇒
  FUN_FMAP f A \\ e = FUN_FMAP f (A DELETE e)
Proof
  simp[fmap_EXT, FUN_FMAP_DEF, DOMSUB_FAPPLY_THM]
QED

Theorem IMAGE_explode_DELETE:
  IMAGE explode A DELETE explode v = IMAGE explode (A DELETE v)
Proof
  simp[EXTENSION] >> metis_tac[mlstringTheory.explode_11]
QED


Theorem combeq3:
  f = g ∧ x1 = y1 ∧ x2 = y2 ⇒ f x1 x2 = g y1 y2
Proof
  simp[]
QED

Theorem subst_exp_of:
  ∀f ce.
    exp_of (substc f ce) =
    subst
      (FUN_FMAP (λk. exp_of (f ' (implode k))) (IMAGE explode $ FDOM f))
      (exp_of ce)
Proof
  recInduct substc_ind >> rw[subst_def, substc_def, exp_of_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
      FLOOKUP_FUN_FMAP]
  >- (simp[FLOOKUP_DEF] >> CASE_TAC >> gvs[exp_of_def])
  >- simp[Cong MAP_CONG]
  >- (simp[subst_Apps, Cong MAP_CONG, MAP_MAP_o])
  >- (simp[subst_Lams, Cong MAP_CONG, FDIFF_FUN_FMAP, FDOM_FDIFF_alt] >>
      qmatch_abbrev_tac ‘subst f1 _ = subst f2 _’ >>
      ‘f1 = f2’ suffices_by simp[] >>
      simp[Abbr‘f1’, Abbr‘f2’, fmap_EXT, PULL_EXISTS, FUN_FMAP_DEF,
           MEM_MAP] >>
      simp[FDIFF_def, DRESTRICT_DEF] >>
      simp[EXTENSION, MEM_MAP, PULL_EXISTS, SF CONJ_ss] >> metis_tac[])
  >- (qmatch_abbrev_tac ‘subst f1 _ = subst f2 _’ >>
      ‘f1 = f2’ suffices_by simp[] >>
      simp[Abbr‘f1’, Abbr‘f2’, fmap_EXT, PULL_EXISTS, FUN_FMAP_DEF,
           DOMSUB_FAPPLY_THM] >>
      simp[EXTENSION, PULL_EXISTS] >> metis_tac[mlstringTheory.explode_11])
  >- (
    rw[MAP_EQ_f, FDIFF_FUN_FMAP] >> pairarg_tac >> rw[] >>
    first_x_assum drule >> rw[] >>
    qmatch_abbrev_tac ‘subst f1 _ = subst f2 _’ >>
    ‘f1 = f2’ suffices_by simp[] >>
    simp[Abbr‘f1’, Abbr‘f2’, fmap_EXT, PULL_EXISTS, FUN_FMAP_DEF,
         FUN_FMAP_DEF, MEM_MAP, EXISTS_PROD,
         FORALL_PROD, FDIFF_def, DRESTRICT_DEF] >>
    simp[EXTENSION, PULL_EXISTS, MEM_MAP, FORALL_PROD, SF CONJ_ss, CONJ_ASSOC]
    )
  >- (simp[FDIFF_FUN_FMAP, FDOM_FDIFF_alt] >>
      qmatch_abbrev_tac ‘subst f1 _ = subst f2 _’ >>
      ‘f1 = f2’ suffices_by simp[] >>
      simp[Abbr‘f1’, Abbr‘f2’, fmap_EXT, PULL_EXISTS, FUN_FMAP_DEF,
           MEM_MAP, FORALL_PROD, FDIFF_def, DRESTRICT_DEF] >>
      simp[EXTENSION, FORALL_PROD, MEM_MAP, SF CONJ_ss, PULL_EXISTS,
           CONJ_ASSOC]) >>~-
  ([‘rows_of’],
   simp[subst_rows_of, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
   Cases_on ‘eopt’ >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
   gs[FUN_FMAP_IMAGE, FDOM_f_o_implode, combinTheory.o_DEF, FAPPLY_f_o,
      FUN_FMAP_DELETE, f_o_implode_DOMSUB_explode, FUN_FMAP_DOMSUB,
      IMAGE_explode_DELETE] >>
   DEP_REWRITE_TAC[subst_IfDisj] >> simp[FDOM_f_o_implode] >>
   AP_TERM_TAC >> rw[MAP_EQ_f] >> pairarg_tac >> rw[] >>
   first_x_assum drule >> rw[] >> irule combeq3 >> simp[] >>
   simp[FDIFF_FUN_FMAP, fmap_EXT, PULL_EXISTS, FDOM_FDIFF_alt,
        FUN_FMAP_DEF, FDIFF_def, DRESTRICT_DEF, MEM_MAP, EXTENSION,
        PULL_EXISTS, SF CONJ_ss, CONJ_ASSOC, DOMSUB_FAPPLY_THM,
        FDOM_f_o_implode, FAPPLY_f_o]) >>
  rename [‘subst (FUN_FMAP _ _ \\ explode gv)’] >>
  ‘FDOM (FUN_FMAP (λk. exp_of (f ' (implode k))) (IMAGE explode (FDOM f)) \\
         explode gv) ∩ freevars (Var (explode gv)) = ∅’
    by simp[EXTENSION] >>
  drule_then assume_tac subst_nested_rows >>
  simp[MAP_MAP_o, FDIFF_FMAP_MAP2, combinTheory.o_ABS_R,
       pairTheory.o_UNCURRY_R] >>
  irule combeq3 >> simp[MAP_EQ_f, FORALL_PROD] >> rw[] >>
  irule combeq3 >> simp[] >>
  simp[fmap_EXT, FDOM_FDIFF_alt, PULL_EXISTS, EXTENSION, CONJ_ASSOC,
       SF CONJ_ss] >>
  simp[FDIFF_def, DRESTRICT_DEF, FUN_FMAP_DEF, DOMSUB_FAPPLY_THM]
QED

Theorem lets_for_APPEND:
  ∀ws1 ws2 cn ar v n w b.
    lets_for cn v (ws1 ++ ws2) b =
      lets_for cn v ws1 (lets_for cn v ws2 b)
Proof
  Induct >> rw[lets_for_def] >>
  PairCases_on `h` >> simp[lets_for_def]
QED


val _ = export_theory();
