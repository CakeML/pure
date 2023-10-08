
open HolKernel Parse boolLib bossLib term_tactic BasicProvers;
open stringTheory optionTheory pairTheory listTheory
     finite_mapTheory pred_setTheory dep_rewrite;
open pure_miscTheory pure_configTheory pure_expTheory;

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "pure_exp_lemmas";


(******************* subst ********************)
Theorem subst_ignore:
  ∀m e. DISJOINT (freevars e) (FDOM m) ⇒ subst m e = e
Proof
  ho_match_mp_tac subst_ind \\ rw [] \\ fs [subst_def] \\ rw[]
  >- fs[FLOOKUP_DEF]
  >- (Induct_on `xs` >> fs[])
  >- (
    first_x_assum irule >>
    fs[DISJOINT_DEF, EXTENSION] >>
    metis_tac[]
    )
  >- (
    rw[LIST_EQ_REWRITE] >> fs[MEM_EL, PULL_EXISTS, EL_MAP] >>
    Cases_on `EL x f` >> fs[] >> rename1 `(fn_name, fn_body)` >>
    first_x_assum drule >> fs[] >> disch_then irule >>
    fs[DISJOINT_DEF, EXTENSION] >> rw[] >> rename1 `var ∉ _` >>
    first_assum (qspec_then `var` assume_tac) >> fs[] >>
    first_x_assum (qspec_then `freevars fn_body` assume_tac) >> gvs[] >>
    pop_assum mp_tac >> simp[MEM_MAP] >> strip_tac >>
    pop_assum (qspec_then `(fn_name,fn_body)` assume_tac) >> gvs[MEM_EL] >>
    pop_assum mp_tac >> simp[MEM_EL] >> strip_tac >>
    pop_assum (qspec_then `x` assume_tac) >> gvs[]
    )
  >- (
    first_x_assum irule >>
    fs[DISJOINT_DEF, EXTENSION] >> rw[] >>
    first_x_assum (qspec_then `x` assume_tac) >> fs[]
    )
QED

Theorem subst_FEMPTY[simp]:
  ∀e. subst FEMPTY e = e
Proof
  rw[] >> irule subst_ignore >> fs[]
QED

Theorem closed_subst[simp]:
  ∀m e. closed e ⇒ subst m e = e
Proof
  rw [] \\ match_mp_tac subst_ignore \\ fs [closed_def]
QED

Theorem closed_simps[simp]:
  (∀n. closed (Var n) ⇔ F) ∧
  (∀op es. closed (Prim op es) ⇔ EVERY closed es) ∧
  (∀e1 e2. closed (App e1 e2) ⇔ closed e1 ∧ closed e2) ∧
  (∀n e. closed (Lam n e) ⇔ freevars e ⊆ {n}) ∧
  (∀fns e. closed (Letrec fns e) ⇔
    freevars e ⊆ set (MAP FST fns) ∧
    EVERY (λe. freevars e ⊆ set (MAP FST fns)) (MAP SND fns))
Proof
  rw[closed_def, freevars_def]
  >- (
    gvs[rich_listTheory.LIST_TO_SET_EQ_SING, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    eq_tac >> rw[] >> gvs[closed_def]
    )
  >- (
    rw[EXTENSION, SUBSET_DEF] >> eq_tac >> rw[] >> metis_tac[]
    )
  >- (
    gvs[SUBSET_DIFF_EMPTY, BIGUNION_SUBSET, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    simp[FORALL_PROD]
    )
QED

Theorem subst_subst:
  ∀m1 e m2.
    DISJOINT (FDOM m1) (FDOM m2) ∧
    (∀v1. v1 ∈ FRANGE m1 ⇒ closed v1) ∧
    (∀v2. v2 ∈ FRANGE m2 ⇒ closed v2)
  ⇒ subst m1 (subst m2 e) = subst m2 (subst m1 e)
Proof
  ho_match_mp_tac subst_ind >> rw[subst_def] >> gvs[]
  >- (
    fs[DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >>
    last_assum (qspec_then `s` assume_tac) >> fs[]
    >- (
      IF_CASES_TAC >> gvs[subst_def, FLOOKUP_DEF, IN_FRANGE] >>
      irule closed_subst >> first_x_assum irule >>
      goal_assum drule >> fs[]
      )
    >- (
      IF_CASES_TAC >> gvs[subst_def, FLOOKUP_DEF, IN_FRANGE] >>
      irule (GSYM closed_subst) >> last_x_assum irule >>
      goal_assum drule >> fs[]
      )
    )
  >- (
    fs[MAP_MAP_o, combinTheory.o_DEF] >>
    rw[MAP_EQ_f] >> first_x_assum irule >> fs[]
    )
  >- (first_x_assum irule >> fs[])
  >- (first_x_assum irule >> fs[])
  >- (
    first_x_assum irule >> fs[] >>
    gvs[IN_FRANGE, PULL_EXISTS, DOMSUB_FAPPLY_THM, DISJOINT_DEF, EXTENSION] >>
    rw[] >> Cases_on `x = s` >> fs[]
    )
  >- (
    rw[LIST_EQ_REWRITE] >> gvs[MEM_EL, PULL_EXISTS, EL_MAP] >>
    Cases_on `EL x f` >> rename1 `(fn_name, fn_body)` >> gvs[] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >>
    first_x_assum irule >>
    gvs[IN_FRANGE, PULL_EXISTS] >>
    simp[FDIFF_def, DRESTRICT_DEF, GSYM CONJ_ASSOC] >>
    goal_assum drule >> fs[] >>
    fs[DISJOINT_DEF, EXTENSION] >> rw[] >> rename1 `foo ∉ _` >>
    Cases_on `MEM foo (MAP FST f)` >> fs[]
    )
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >>
    first_x_assum irule >>
    gvs[IN_FRANGE, PULL_EXISTS] >>
    simp[FDIFF_def, DRESTRICT_DEF] >>
    fs[DISJOINT_DEF, EXTENSION] >> rw[] >> rename1 `foo ∉ _` >>
    Cases_on `MEM foo (MAP FST f)` >> fs[]
    )
QED

Theorem subst_subst_FUNION:
  ∀m1 e m2.
    (∀v. v ∈ FRANGE m2 ⇒ closed v)
  ⇒ subst m1 (subst m2 e) = subst (m2 ⊌ m1) e
Proof
  ho_match_mp_tac subst_ind >> rw[subst_def] >> gvs[FRANGE_FLOOKUP, PULL_EXISTS]
  >- (
    gvs[FLOOKUP_FUNION] >>
    reverse CASE_TAC >> gvs[subst_def]
    >- (irule closed_subst >> res_tac)
    )
  >- (
    fs[MAP_MAP_o, combinTheory.o_DEF] >>
    rw[MAP_EQ_f] >>
    first_x_assum irule >> simp[] >> gvs[]
    )
  >- (
    gvs[DOMSUB_FUNION] >>
    first_x_assum irule >>
    gvs[DOMSUB_FLOOKUP_THM] >> rw[] >>
    res_tac
    )
  >- (
    fs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >>
    rw[MAP_EQ_f] >> rename1 `MEM fn f` >> PairCases_on `fn` >> gvs[] >>
    rw[FDIFF_FUNION] >>
    first_x_assum irule >>
    gvs[FDIFF_def, FLOOKUP_DRESTRICT] >> rw[] >> res_tac >>
    goal_assum drule
    )
  >- (
    rw[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >>
    rw[FDIFF_FUNION] >>
    first_x_assum irule >>
    gvs[FDIFF_def, FLOOKUP_DRESTRICT] >> rw[] >> res_tac
    )
QED

Theorem subst_subst_DISJOINT_FUNION:
  ∀m1 e m2.
    DISJOINT (FDOM m1) (BIGUNION (IMAGE freevars (FRANGE m2)))
  ⇒ subst m1 (subst m2 e) = subst (m2 ⊌ m1) e
Proof
  recInduct subst_ind >> rw[] >> gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS]
  >- (
    simp[subst_def, FLOOKUP_FUNION] >>
    EVERY_CASE_TAC >> gvs[subst_def] >>
    irule subst_ignore >> metis_tac[DISJOINT_SYM]
    )
  >- (
    simp[subst_def, MAP_MAP_o, combinTheory.o_DEF] >>
    rw[MAP_EQ_f] >> last_x_assum irule >> simp[] >> metis_tac[]
    )
  >- (
    simp[subst_def] >> metis_tac[]
    )
  >- (
    simp[subst_def, DOMSUB_FUNION] >>
    last_x_assum irule >> simp[DOMSUB_FLOOKUP_THM] >> rw[] >>
    last_x_assum drule >> gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
    )
  >- (
    simp[subst_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[GSYM FST_THM] >> rw[MAP_EQ_f, FDIFF_FUNION]
    >- (
      PairCases_on `e` >> gvs[] >>
      last_x_assum irule >> simp[PULL_EXISTS] >> goal_assum (drule_at Any) >>
      rw[FDIFF_def, FLOOKUP_DRESTRICT, FDOM_DRESTRICT] >>
      first_x_assum drule >> simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]
      )
    >- (
      first_x_assum irule >> rw[FDIFF_def, FLOOKUP_DRESTRICT, FDOM_DRESTRICT] >>
      first_x_assum drule >> simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]
      )
    )
QED

Theorem subst_id:
  ∀f e.
    (∀k v. FLOOKUP f k = SOME v ⇒ v = Var k)
  ⇒ subst f e = e
Proof
  recInduct subst_ind >> rw[subst_def]
  >- (CASE_TAC >> res_tac >> gvs[])
  >- rw[MAP_ID_ON]
  >- (last_x_assum irule >> simp[DOMSUB_FLOOKUP_THM])
  >- (
    irule MAP_ID_ON >> simp[FORALL_PROD] >> rw[] >>
    last_x_assum irule >> simp[FDIFF_def, FLOOKUP_DRESTRICT] >> goal_assum drule
    )
  >- (first_x_assum irule >> simp[FDIFF_def, FLOOKUP_DRESTRICT])
QED


(******************* bind ********************)

Theorem bind_FEMPTY[simp]:
  ∀e. bind FEMPTY e = e
Proof
  rw[bind_def, subst_FEMPTY]
QED

Theorem bind_bind:
  ∀m1 m2 e.
    (∀v. v ∈ FRANGE m1 ⇒ closed v) ∧ DISJOINT (FDOM m1) (FDOM m2)
  ⇒ bind m1 (bind m2 e) = bind (m2 ⊌ m1) e
Proof
  rw[] >> fs[bind_def, FRANGE_FLOOKUP, PULL_EXISTS, DISJOINT_DEF, EXTENSION] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >>
    gvs[FLOOKUP_FUNION] >>
    imp_res_tac flookup_thm >> res_tac
    ) >>
  reverse (IF_CASES_TAC) >> gvs[FLOOKUP_FUNION]
  >- (
    IF_CASES_TAC >> gvs[subst_def] >>
    pop_assum (qspec_then `n` assume_tac) >> gvs[]
    ) >>
  reverse (IF_CASES_TAC) >> gvs[]
  >- (Cases_on `FLOOKUP m2 n` >> gvs[] >> res_tac) >>
  irule subst_subst_FUNION >> gvs[FRANGE_FLOOKUP, PULL_EXISTS]
QED

Theorem bind_Var:
  ∀m x.
    (∀v. v ∈ FRANGE m ⇒ closed v)
  ⇒ bind m (Var x) =
    case FLOOKUP m x of
      SOME e => e
    | NONE => Var x
Proof
  gvs[bind_def, FRANGE_FLOOKUP] >>
  reverse (rw[]) >> gvs[] >- res_tac >>
  fs[subst_def]
QED

Theorem bind_Lam:
  ∀m x e1.
    (∀v. v ∈ FRANGE m ⇒ closed v)
  ⇒ bind m (Lam x e1) = Lam x (bind (m \\ x) e1)
Proof
  gvs[bind_def, FRANGE_FLOOKUP] >>
  reverse (rw[]) >> gvs[PULL_EXISTS, subst_def]
  >- (goal_assum drule >> fs[])
  >- (goal_assum drule >> fs[])
  >- (gvs[DOMSUB_FLOOKUP_THM] >> res_tac)
QED

Theorem bind_App:
  ∀m e1 e2.
    (∀v. v ∈ FRANGE m ⇒ closed v)
  ⇒ bind m (App e1 e2) = App (bind m e1) (bind m e2)
Proof
  gvs[bind_def, FRANGE_FLOOKUP] >>
  reverse (rw[]) >> gvs[PULL_EXISTS]
  >- (goal_assum drule >> fs[]) >>
  simp[subst_def]
QED

Theorem bind_alt_def:
  ∀sub.
    (∀v. v ∈ FRANGE sub ⇒ closed v)
  ⇒
    (∀s.
      bind sub (Var s) = case FLOOKUP sub s of SOME v => v | NONE => Var s) ∧
    (∀op xs. bind sub (Prim op xs) = Prim op (MAP (λe. bind sub e) xs)) ∧
    (∀x y. bind sub (App x y) = App (bind sub x) (bind sub y)) ∧
    (∀s x. bind sub (Lam s x) = Lam s (bind (sub \\ s) x)) ∧
    (∀f x. bind sub (Letrec f x) =
      let sub1 = FDIFF sub (set (MAP FST f)) in
      Letrec (MAP (λ(n,e). (n, bind sub1 e)) f) (bind sub1 x))
Proof
  rw[]
  >- (drule bind_Var >> fs[])
  >- (
    gvs[FRANGE_FLOOKUP, PULL_EXISTS] >>
    reverse (rw[bind_def]) >> gvs[] >- res_tac >>
    fs[subst_def] >> res_tac
    )
  >- (drule bind_App >> fs[])
  >- (drule bind_Lam >> fs[])
  >- (
    gvs[FRANGE_FLOOKUP, PULL_EXISTS] >>
    reverse (rw[bind_def]) >> gvs[subst_def]
    >- res_tac
    >- res_tac
    >- (gvs[FDIFF_def, FLOOKUP_DRESTRICT] >> res_tac)
    )
QED

(******************* single subst/bind ********************)

Theorem subst1_def:
  (∀n v s. subst1 n v (Var s) = (if n = s then v else Var s)) ∧
  (∀n v op xs. subst1 n v (Prim op xs) = Prim op (MAP (subst1 n v) xs)) ∧
  (∀n v x y. subst1 n v (App x y) = App (subst1 n v x) (subst1 n v y)) ∧
  (∀n v s x. subst1 n v (Lam s x) = Lam s (if s = n then x else subst1 n v x)) ∧
  (∀n v f x. subst1 n v (Letrec f x) =
    (if MEM n (MAP FST f) then Letrec f x else
      Letrec (MAP (λ(g,z). (g, subst1 n v z )) f) (subst1 n v x)))
Proof
  rw[subst_def, FLOOKUP_UPDATE, FDIFF_def, subst_FEMPTY] >> gvs[]
  >- (
    MK_COMB_TAC >> fs[] >> AP_TERM_TAC >>
    irule DOMSUB_NOT_IN_DOM >> gvs[]
    )
  >- (
    rw[LIST_EQ_REWRITE] >> Cases_on `EL x f` >> fs[EL_MAP]
    )
QED

Theorem subst1_ignore:
  ∀ n v e. n ∉ freevars e ⇒ subst1 n v e = e
Proof
  rw[] >>
  irule subst_ignore >>
  gvs[pred_setTheory.EXTENSION, finite_mapTheory.FDOM_FUPDATE]
QED

Theorem subst1_subst1:
  ∀m n x y.
    closed x ∧ closed y ∧ m ≠ n ⇒
    subst1 n x (subst1 m y e) = subst1 m y (subst1 n x e)
Proof
  rw[] >>
  qspecl_then [
    `FEMPTY |+ (n,x)`, `e`, `FEMPTY |+ (m,y)`] assume_tac subst_subst_FUNION >>
  qspecl_then [
    `FEMPTY |+ (m,y)`, `e`, `FEMPTY |+ (n,x)`] assume_tac subst_subst_FUNION >>
  gvs[FRANGE_FLOOKUP, FLOOKUP_UPDATE] >>
  MK_COMB_TAC >> fs[] >> AP_TERM_TAC >>
  fs[fmap_eq_flookup, FLOOKUP_FUNION, FLOOKUP_UPDATE] >> rw[]
QED

Theorem subst_subst1_UPDATE:
  ∀m e n v.
    closed v ⇒
    subst (m |+ (n,v)) e = subst m (subst1 n v e)
Proof
  rw[] >>
  simp[Once FUPDATE_EQ_FUNION] >>
  irule (GSYM subst_subst_FUNION) >>
  fs[FRANGE_FLOOKUP, FLOOKUP_UPDATE, PULL_EXISTS]
QED

Theorem bind1_def:
  ∀n v e. bind1 n v e = if closed v then subst1 n v e else Fail
Proof
  rw[bind_def] >> gvs[FLOOKUP_UPDATE]
QED

Theorem bind1_bind1:
  ∀m n x y.
    closed x ∧ m ≠ n ⇒
    bind1 n x (bind1 m y e) = bind1 m y (bind1 n x e)
Proof
  rw[] >> fs[bind_def] >>
  IF_CASES_TAC >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  irule subst1_subst1 >> fs[] >>
  gvs[FLOOKUP_UPDATE]
QED

Theorem bind_bind1_UPDATE:
  ∀m e n v.
    closed v ∧ n ∉ FDOM m ⇒
    bind (m |+ (n,v)) e = bind m (bind1 n v e)
Proof
  rw[] >> fs[bind_def] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >>
    gvs[FLOOKUP_UPDATE] >>
    rename1 `if n1 = n2 then _ else _` >>
    Cases_on `n1 = n2` >> gvs[] >>
    res_tac
    ) >>
  reverse (IF_CASES_TAC) >> gvs[]
  >- (
    gvs[FLOOKUP_UPDATE] >>
    rename1 `FLOOKUP _ n2` >> rename1 `n1 ∉ _` >>
    `n1 ≠ n2` by (gvs[flookup_thm] >> CCONTR_TAC >> gvs[]) >>
    first_assum (qspec_then `n2` assume_tac) >> gvs[]
    ) >>
  IF_CASES_TAC >> gvs[FLOOKUP_UPDATE] >>
  fs[Once subst_subst1_UPDATE]
QED

(******************* freevars ********************)

Theorem freevars_equiv:
  ∀e. freevars e = set (freevars_l e)
Proof
  recInduct freevars_ind >> rw[]
  >- (
    gvs[LIST_TO_SET_FLAT, LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF] >>
    AP_TERM_TAC >> rw[EXTENSION] >> metis_tac[]
    )
  >- (
    simp[LIST_TO_SET_FILTER] >> rw[EXTENSION] >> eq_tac >> rw[]
    )
  >- (
    simp[LIST_TO_SET_FILTER, LIST_TO_SET_FLAT, LIST_TO_SET_MAP, FORALL_PROD] >>
    simp[IMAGE_IMAGE, combinTheory.o_DEF, LAMBDA_PROD] >>
    rw[EXTENSION, EXISTS_PROD] >> metis_tac[]
    )
QED

Theorem freevars_FINITE[simp]:
  ∀e. FINITE (freevars e)
Proof
  simp[freevars_equiv]
QED

Theorem freevars_expandLets:
  ∀y i cn nm vs cs.
    y ∈ freevars (expandLets i cn nm vs cs) ∧ y ≠ nm ⇒
    y ∈ freevars cs DIFF set vs
Proof
  strip_tac >>
  Induct_on ‘vs’ >> rw[expandLets_def] >>
  res_tac >> gvs[]
QED

Theorem freevars_expandRows:
  ∀y nm css.
    y ∈ freevars (expandRows nm css) ∧ y ≠ nm ⇒
      ∃cn vs cs. MEM (cn,vs,cs) css ∧ y ∈ freevars cs DIFF set vs
Proof
  strip_tac >>
  ho_match_mp_tac expandRows_ind >>
  rw[freevars_def,expandRows_def,freevars_expandLets] >>
  imp_res_tac freevars_expandLets >> gvs[] >>
  metis_tac[]
QED

Theorem freevars_expandCases:
  ∀y x nm css.
    y ∈ freevars (expandCases x nm css) ⇒
      (nm ≠ y ∧
       ∃cn vs cs. MEM (cn,vs,cs) css ∧ y ∈ freevars cs DIFF set vs) ∨
      y ∈ freevars x
Proof
  rw[expandCases_def,MEM_FILTER] >> simp[] >>
  disj1_tac >> drule freevars_expandRows >> simp[]
QED

Theorem freevars_subst:
  ∀m e.
  (∀v. v ∈ FRANGE m ⇒ closed v) ⇒
  freevars (subst m e) = freevars e DIFF (FDOM m)
Proof
  ho_match_mp_tac subst_ind >>
  rw[subst_def,closed_def] >>
  fs[FRANGE_FLOOKUP, PULL_EXISTS]
  >- fs[FLOOKUP_DEF]
  >- fs[FLOOKUP_DEF]
  >- (
    fs[LIST_TO_SET_FLAT, MAP_MAP_o, combinTheory.o_DEF, BIGUNION_DIFF] >>
    fs[EXTENSION, MEM_MAP, PULL_EXISTS] >>
    rw[] >> eq_tac >> rw[GSYM CONJ_ASSOC] >>
    rename1 `MEM e xs`
    >- (
      qexists_tac `freevars (subst m e)` >> fs[] >>
      qexists_tac `freevars e` >> fs[] >>
      goal_assum (drule_at Any) >> fs[]
      )
    >- (
      qexists_tac `freevars (subst m e)` >> fs[] >>
      qexists_tac `e` >> fs[]
      )
    )
  >- (gvs[EXTENSION] >> rw[] >> eq_tac >> rw[] >> gvs[])
  >- (
    gvs[FLOOKUP_DEF, LIST_TO_SET_FILTER, EXTENSION] >>
    rw[] >> eq_tac >> rw[] >> gvs[] >>
    last_assum mp_tac >> reverse impl_tac >> rw[] >> gvs[] >>
    first_x_assum drule >> fs[DOMSUB_FAPPLY_THM]
    )
  >- (
    gvs[LIST_TO_SET_FILTER] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY, LIST_TO_SET_FLAT] >>
    fs[EXTENSION, MEM_MAP, PULL_EXISTS] >>
    qpat_x_assum `_ ⇒ _` mp_tac >> impl_tac >> rw[] >> gvs[]
    >- (
      fs[FDIFF_def, FLOOKUP_DRESTRICT] >>
      first_x_assum irule >> goal_assum drule >> fs[]
      ) >>
    rw[] >> eq_tac >> rw[GSYM CONJ_ASSOC] >> gvs[]
    >- (first_x_assum (qspec_then `y` assume_tac) >> gvs[]) >>
    (
      rename1 `MEM fn f` >> PairCases_on `fn` >> gvs[] >>
      last_x_assum drule >> impl_tac >> rw[] >> gvs[] >>
      gvs[FDIFF_def, FLOOKUP_DRESTRICT]
      >- (first_x_assum irule >> goal_assum drule >> fs[])
    ) >> gvs[GSYM FDIFF_def]
    >- (
      DISJ2_TAC >>
      qexists_tac `freevars fn1` >>
      goal_assum (drule_at Any) >> fs[]
      )
    >- (qpat_x_assum `∀x. _ ≠ _ ∨ _` (qspec_then `y` assume_tac) >> gvs[])
    >- (qpat_x_assum `∀x. _ ≠ _ ∨ _` (qspec_then `y` assume_tac) >> gvs[])
    >- (
      DISJ2_TAC >>
      qexists_tac `freevars (subst (FDIFF m (set (MAP FST f))) fn1)` >>
      goal_assum (drule_at Any) >> fs[]
      )
    )
QED

Theorem freevars_subst1:
  ∀n v e.
    closed v ⇒
    freevars (subst1 n v e) = freevars e DELETE n
Proof
  rw[] >>
  qspec_then `FEMPTY |+ (n,v)` assume_tac freevars_subst >> fs[DELETE_DEF]
QED

Theorem freevars_subst_SUBSET:
  ∀e f. freevars (subst f e) ⊆ freevars e DIFF FDOM f ∪
                                (BIGUNION $ IMAGE freevars (FRANGE f))
Proof
  Induct using freevars_ind >> rw[subst_def, freevars_def] >>
  gvs[LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF] >>
  gvs[BIGUNION_SUBSET, PULL_EXISTS, SUBSET_DEF] >> rw[]
  >- (gvs[FLOOKUP_DEF, FRANGE_DEF] >> metis_tac[])
  >- (gvs[FLOOKUP_DEF, FRANGE_DEF] >> metis_tac[])
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (
    first_x_assum drule >> strip_tac >> gvs[] >> disj2_tac >>
    gvs[IN_FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM] >> rpt $ goal_assum drule
    )
  >- (
    gvs[FORALL_PROD] >> first_x_assum drule >> strip_tac >> gvs[]
    >- (Cases_on `x'` >> gvs[]) >>
    disj2_tac >> gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF] >> rpt $ goal_assum drule
    )
  >- (
    pairarg_tac >> gvs[FORALL_PROD] >> pairarg_tac >> gvs[] >>
    first_x_assum drule_all >> strip_tac >> gvs[EXISTS_PROD]
    >- metis_tac[] >>
    disj2_tac >> gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF] >> rpt $ goal_assum drule
    )
QED

Theorem subst1_subst1_eq:
  closed y ⇒ subst1 v x (subst1 v y e) = subst1 v y e
Proof
  rw [] \\ match_mp_tac subst1_ignore
  \\ fs [freevars_subst1]
QED

Theorem closed_subst1_iff:
  ∀ n e x y.
    closed x ∧ closed y
  ⇒ (closed (subst1 n x e) ⇔ closed (subst1 n y e))
Proof
  rw[] >> fs[closed_def] >>
  DEP_REWRITE_TAC[freevars_subst1] >> simp[closed_def]
QED

Theorem freevars_bind:
  ∀m y.
    freevars (bind m y) =
      if (∀v. v ∈ FRANGE m ⇒ closed v) then
        freevars y DIFF FDOM m
      else {}
Proof
  rw[bind_def] >> fs[]
  >- (drule freevars_subst >> fs[]) >>
  gvs[FRANGE_FLOOKUP] >> res_tac
QED

Theorem freevars_bind1:
  ∀ n v e.
    freevars (bind1 n v e) =
    if closed v then freevars e DELETE n else {}
Proof
  rw[bind_def] >> gvs[FLOOKUP_UPDATE] >>
  irule freevars_subst1 >> simp[]
QED

Theorem IMP_closed_subst:
  (∀v. v ∈ FRANGE m ⇒ closed v) ∧ freevars e ⊆ FDOM m ⇒
  closed (subst m e)
Proof
  rw [] \\ drule freevars_subst
  \\ disch_then (qspec_then ‘e’ mp_tac)
  \\ fs [EXTENSION,SUBSET_DEF,closed_def]
  \\ metis_tac[]
QED

Theorem IMP_closed_bind:
  ∀e m. freevars e ⊆ FDOM m ⇒ closed (bind m e)
Proof
  rw[bind_def] >>
  irule IMP_closed_subst >>
  simp[IN_FRANGE_FLOOKUP]
QED

Theorem subst_FDIFF':
  ∀f x p. (∀n. n ∈ p ⇒ n ∉ freevars x) ⇒ subst f x = subst (FDIFF f p) x
Proof
  recInduct subst_ind >> rw[subst_def]
  >- simp[FDIFF_def, FLOOKUP_DRESTRICT]
  >- (
    rw[MAP_EQ_f] >> first_x_assum irule >> rw[] >>
    gvs[MEM_MAP, PULL_EXISTS] >> metis_tac[]
    )
  >- (
    simp[GSYM FDIFF_FDOMSUB] >>
    first_x_assum $ qspec_then `p DELETE s` mp_tac >> gvs[] >> impl_tac
    >- (rw[] >> gvs[] >> res_tac) >>
    simp[FDIFF_FDOMSUB_INSERT] >> strip_tac >>
    AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> rw[EXTENSION] >> metis_tac[]
    )
  >- (
    rw[MAP_EQ_f] >> pairarg_tac >> gvs[FDIFF_FDIFF] >> simp[Once UNION_COMM] >>
    last_x_assum drule >>
    disch_then $ qspec_then `p DIFF set (MAP FST f)` mp_tac >>
    impl_tac >> simp[] >>
    gvs[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> rw[] >> metis_tac[]
    )
  >- (
    gvs[FDIFF_FDIFF] >> simp[Once UNION_COMM] >>
    first_x_assum $ qspec_then `p DIFF set (MAP FST f)` mp_tac >>
    impl_tac >> simp[] >> rw[] >>
    metis_tac[]
    )
QED

Theorem subst_fdomsub:
  ∀f e x. x ∉ freevars e ⇒ subst f e = subst (f \\ x) e
Proof
  rw[] >>
  `f \\ x = FDIFF f {x}` by (
    rw[fmap_eq_flookup, DOMSUB_FLOOKUP_THM, FLOOKUP_FDIFF] >> rw[]) >>
  simp[] >> irule subst_FDIFF' >> simp[]
QED

Theorem subst_FDIFF:
  ∀f x. subst f x = subst (DRESTRICT f (freevars x)) x
Proof
  rw[] >>
  SIMP_TAC std_ss [SimpR “$=”,Once(GSYM COMPL_COMPL)] >>
  SIMP_TAC std_ss [GSYM FDIFF_def] >>
  match_mp_tac subst_FDIFF' >>
  rw[]
QED

Theorem closed_subst1_freevars:
  ∀s x y.
    closed x ∧ closed(subst1 s x y) ⇒
    freevars y ⊆ {s}
Proof
  rw[] >> pop_assum mp_tac >> drule freevars_subst1 >>
  disch_then(qspecl_then [‘s’,‘y’] mp_tac) >> rw[] >>
  gvs[closed_def, DELETE_DEF, SUBSET_DIFF_EMPTY]
QED

Theorem closed_subst_freevars:
  ∀m e.
    (∀v. v ∈ FRANGE m ⇒ closed v) ∧
    closed (subst m e)
  ⇒ freevars e ⊆ FDOM m
Proof
  rw[] >> imp_res_tac freevars_subst >>
  gvs[closed_def, EXTENSION, NIL_iff_NOT_MEM, SUBSET_DEF, DISJ_EQ_IMP]
QED

Theorem closed_freevars_subst1:
  ∀s x y.
    closed x ∧ freevars y ⊆ {s} ⇒
    closed(subst1 s x y)
Proof
  rw[] >>
  drule freevars_subst1 >> disch_then (qspecl_then [‘s’,‘y’] mp_tac) >>
  gvs[DELETE_DEF, closed_def] >> rw[] >> gvs[SUBSET_DIFF_EMPTY]
QED

Triviality FDOMSUB_EQ_FDIFF:
  M \\ x = FDIFF M {x}
Proof
  rw [REWRITE_RULE [pred_setTheory.EXTENSION] fmap_EXT, FDIFF_def, DRESTRICT_DEF, DOMSUB_FAPPLY_NEQ]
QED

Triviality FDOM_FLOOKUP:
  x IN FDOM m <=> FLOOKUP m x <> NONE
Proof
  Cases_on `FLOOKUP m x` \\ fs [FLOOKUP_DEF]
QED

val subst_triv_cong = Q.prove (`m = m' /\ x = y ==> subst m x = subst m' y`, simp [])

Theorem subst_distrib:
  ∀ body f f2.
    (∀n v. FLOOKUP f2 n = SOME v ⇒ closed v) ∧
    DISJOINT (BIGUNION (IMAGE freevars (FRANGE f))) (boundvars body)
  ⇒ subst f2 (subst f body) = subst (subst f2 o_f f) (subst (FDIFF f2 (FDOM f)) body)
Proof
  ho_match_mp_tac freevars_ind
  \\ rw []
  \\ simp [subst_def]
  >- (
    simp [FDIFF_def, FLOOKUP_DRESTRICT, FDOM_FLOOKUP]
    \\ every_case_tac
    \\ simp [subst_def, FLOOKUP_o_f]
    \\ srw_tac [SatisfySimps.SATISFY_ss] [closed_subst]
  )
  >- (
    rw [listTheory.MAP_MAP_o, listTheory.MAP_EQ_f]
    \\ fs [PULL_EXISTS]
    \\ first_x_assum irule
    \\ fs [listTheory.MEM_MAP, PULL_EXISTS]
    \\ srw_tac [SatisfySimps.SATISFY_ss] []
  )
  >- (
    rw []
    \\ fs [PULL_EXISTS]
    \\ fs [pred_setTheory.DISJOINT_SYM]
    \\ srw_tac [SatisfySimps.SATISFY_ss] []
  )
  >- (
    irule EQ_TRANS \\ first_x_assum (irule_at Any)
    \\ fs [PULL_EXISTS]
    \\ srw_tac [SatisfySimps.SATISFY_ss] [DOMSUB_FLOOKUP_THM,
        REWRITE_RULE [SUBSET_DEF] FRANGE_DOMSUB_SUBSET]
    \\ rpt (irule_at Any subst_triv_cong)
    \\ simp [FDOMSUB_EQ_FDIFF, FDIFF_FDIFF, UNION_COMM]
    \\ irule_at Any o_f_cong
    \\ fs [FRANGE_FLOOKUP, PULL_EXISTS, FLOOKUP_FDIFF]
    \\ srw_tac [SatisfySimps.SATISFY_ss] [GSYM subst_FDIFF']
    \\ AP_TERM_TAC
    \\ simp [EXTENSION]
    \\ metis_tac []
  )
  >- (
    simp [pairTheory.UNCURRY, MAP_MAP_o, combinTheory.o_DEF, Q.ISPEC `FST` ETA_THM]
    \\ fs [MEM_MAP, pairTheory.EXISTS_PROD, PULL_EXISTS]
    \\ simp [MAP_EQ_f, pairTheory.FORALL_PROD]
    \\ conj_tac
    >- (
      rw []
      \\ irule EQ_TRANS \\ first_x_assum (irule_at Any)
      \\ first_assum (irule_at Any)
      \\ fs [FLOOKUP_FDIFF, FRANGE_FLOOKUP, PULL_EXISTS, DISJOINT_SYM]
      \\ rpt (irule_at Any subst_triv_cong)
      \\ simp [fmap_eq_flookup, FLOOKUP_FDIFF, FLOOKUP_o_f]
      \\ rw [] \\ fs [] \\ fs [] \\ srw_tac [SatisfySimps.SATISFY_ss] []
      \\ every_case_tac
      \\ irule (GSYM subst_FDIFF')
      \\ fs [IN_DISJOINT]
      \\ metis_tac []
    )
    \\ irule EQ_TRANS \\ first_x_assum (irule_at Any)
    \\ fs [FLOOKUP_FDIFF, FRANGE_FLOOKUP, PULL_EXISTS, DISJOINT_SYM]
    \\ srw_tac [SatisfySimps.SATISFY_ss] [GSYM subst_FDIFF']
    \\ rpt (irule_at Any subst_triv_cong)
    \\ simp [FDIFF_FDIFF, UNION_COMM]
    \\ simp [fmap_eq_flookup, FLOOKUP_FDIFF, FLOOKUP_o_f]
    \\ rw [] \\ fs [] \\ fs []
    \\ every_case_tac
    \\ irule (GSYM subst_FDIFF')
    \\ fs [IN_DISJOINT]
    \\ metis_tac []
  )
QED

Theorem subst1_distrib:
  ∀ body f v arg.
    (∀n v. FLOOKUP f n = SOME v ⇒ closed v) ∧
    DISJOINT (freevars arg) (boundvars body)
  ⇒ subst f (subst1 v arg body) = subst1 v (subst f arg) (subst (f \\ v) body)
Proof
  rw []
  \\ irule EQ_TRANS \\ irule_at Any subst_distrib
  \\ srw_tac [SatisfySimps.SATISFY_ss] []
  \\ rpt (irule_at Any subst_triv_cong)
  \\ simp [fmap_eq_flookup, FLOOKUP_FDIFF, DOMSUB_FLOOKUP_THM]
  \\ rw []
QED


(******************* boundvars ********************)

Theorem boundvars_equiv:
  ∀e. boundvars e = set (boundvars_l e)
Proof
  recInduct boundvars_l_ind >> rw[]
  >- (
    gvs[LIST_TO_SET_MAP, LIST_TO_SET_FLAT] >> AP_TERM_TAC >>
    rw[EXTENSION] >> metis_tac[]
    )
  >- (
    gvs[LIST_TO_SET_MAP, LIST_TO_SET_FLAT] >>
    simp[IMAGE_IMAGE, combinTheory.o_DEF, LAMBDA_PROD] >>
    rw[EXTENSION, EXISTS_PROD, PULL_EXISTS] >> eq_tac >> rw[] >> metis_tac[]
    )
QED

Theorem boundvars_FINITE[simp]:
  ∀e. FINITE (boundvars e)
Proof
  simp[boundvars_equiv]
QED

Theorem boundvars_Apps:
  boundvars (Apps e es) =
    boundvars e ∪ BIGUNION (set $ MAP boundvars es)
Proof
  qid_spec_tac `e` >> Induct_on `es` >> rw[Apps_def] >> simp[UNION_ASSOC]
QED

Theorem boundvars_Lams:
  boundvars (Lams xs e) = set xs ∪ boundvars e
Proof
  Induct_on `xs` >> rw[boundvars_def, Lams_def] >>
  rw[EXTENSION] >> metis_tac[]
QED


(******************* allvars ********************)

Theorem allvars_thm:
  allvars e = freevars e ∪ boundvars e
Proof
  Induct_on `e` using freevars_ind >>
  rw[allvars_def, freevars_def, boundvars_def]
  >- (Induct_on `es` >> rw[] >> gvs[] >> rw[Once EXTENSION] >> metis_tac[])
  >- (rw[EXTENSION] >> metis_tac[])
  >- (rw[EXTENSION] >> metis_tac[]) >>
  simp[AC UNION_ASSOC UNION_COMM] >> AP_TERM_TAC >>
  simp[UNION_ASSOC] >>
  qmatch_goalsub_abbrev_tac `_ = a ∪ b ∪ (c DIFF _)` >>
  `a ∪ b ∪ (c DIFF a) = a ∪ b ∪ c` by (rw[EXTENSION] >> metis_tac[]) >>
  rw[] >> unabbrev_all_tac >>
  simp[AC UNION_ASSOC UNION_COMM] >> ntac 2 AP_TERM_TAC >>
  ntac 2 $ pop_assum kall_tac >> Induct_on `lcs` >> rw[] >>
  pairarg_tac >> gvs[SF DNF_ss] >> last_x_assum drule >> rw[] >>
  rw[Once EXTENSION] >> metis_tac[]
QED


(******************* Apps / Lams ********************)

Theorem freevars_Lams[simp]:
  ∀vs e. freevars (Lams vs e) = freevars e DIFF set vs
Proof
  Induct >> rw[Lams_def] >> gvs[EXTENSION] >> rw[] >> metis_tac[]
QED

Theorem subst_Lams:
  ∀l x f. subst f (Lams l x) = Lams l (subst (FDIFF f (set l)) x)
Proof
  Induct >> rw[Lams_def] >> simp[subst_def, FDIFF_FDOMSUB_INSERT]
QED

Theorem Lams_SNOC:
  (∀e. Lams [] e = e) ∧
  (∀vs v. Lams (SNOC v vs) e = Lams vs (Lam v e))
Proof
  conj_tac >- rw[Lams_def] >>
  Induct >> rw[Lams_def]
QED

Theorem Lams_11[simp]:
  Lams vs bod1 = Lams vs bod2 ⇔ bod1 = bod2
Proof
  Induct_on ‘vs’ >> simp[exp_11, Lams_def]
QED

Theorem freevars_Apps[simp]:
  ∀es e. freevars (Apps e es) = freevars e ∪ BIGUNION (set (MAP freevars es))
Proof
  Induct >> rw[Apps_def] >> simp[UNION_ASSOC]
QED

Theorem subst_Apps:
  ∀l x f. subst f (Apps x l) = Apps (subst f x) (MAP (subst f) l)
Proof
  Induct >> rw[Apps_def, subst_def]
QED

Theorem Apps_SNOC:
  (∀x. Apps x [] = x) ∧
  (∀ys x y. Apps x (SNOC y ys) = App (Apps x ys) y)
Proof
  conj_tac >- rw[Apps_def] >>
  Induct >> rw[Apps_def]
QED

Theorem Let_Lams:
  Let x a (Lams ys e) = App (Lams (x::ys) e) a
Proof
  rw[Lams_def]
QED

Theorem closed_Apps[simp]:
  closed (Apps e es) ⇔ closed e ∧ EVERY closed es
Proof
  rw[closed_def, freevars_Apps] >> Cases_on `es` >> simp[] >>
  once_rewrite_tac[EXTENSION] >> simp[closed_def, MEM_MAP, EVERY_MEM] >>
  eq_tac >> rw[] >> metis_tac[]
QED

Theorem closed_Lams[simp]:
  closed (Lams vs e) ⇔ freevars e ⊆ set vs
Proof
  rw[closed_def, freevars_Lams] >> simp[SUBSET_DIFF_EMPTY]
QED

Theorem Apps_append:
  ∀xs ys x. Apps x (xs ++ ys) = Apps (Apps x xs) ys
Proof
  Induct \\ fs [Apps_def]
QED

Theorem Apps_11:
  ∀xs ys x y. Apps x xs = Apps y ys ∧ LENGTH xs = LENGTH ys ⇒ x = y ∧ xs = ys
Proof
  Induct \\ fs [Apps_def]
  \\ Cases_on ‘ys’ \\ fs [Apps_def]
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem subst_Seqs:
  ∀xs y. subst m (Seqs xs y) = Seqs (MAP (subst m) xs) (subst m y)
Proof
  Induct \\ fs [subst_def]
QED

Theorem subst_Apps:
  ∀xs m f. subst m (Apps f xs) = Apps (subst m f) (MAP (subst m) xs)
Proof
  Induct \\ fs [Apps_def,subst_def]
QED

Theorem letrecs_distinct_Apps:
  ∀l e. letrecs_distinct (Apps e l) ⇔ letrecs_distinct e ∧ EVERY letrecs_distinct l
Proof
  Induct \\ gs [letrecs_distinct_def, Apps_def, GSYM CONJ_ASSOC]
QED

Theorem letrecs_distinct_Lams:
  ∀l e. letrecs_distinct (Lams l e) ⇔ letrecs_distinct e
Proof
  Induct \\ gs [letrecs_distinct_def, Lams_def]
QED

Theorem ignore_FDIFF:
  DISJOINT f (FDOM m) ⇒ FDIFF m f = m
Proof
  fs [fmap_eq_flookup,FLOOKUP_DEF,FDIFF_def,DRESTRICT_DEF,IN_DISJOINT]
  \\ metis_tac []
QED

val _ = export_theory();
