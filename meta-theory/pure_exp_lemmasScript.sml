
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
  rw[closed_def, freevars_def] >>
  gvs[FLAT_EQ_NIL, FILTER_EQ_NIL, EVERY_MAP, EVERY_FLAT, EVERY_MEM]
  >- (gvs[EVERY_MEM, closed_def, SUBSET_DEF])
  >- (
    gvs[EVERY_MEM, closed_def, SUBSET_DEF] >>
    eq_tac >> rw[] >> gvs[MEM_EL, PULL_EXISTS]
    ) >>
  eq_tac >> rw[SUBSET_DEF] >>
  first_x_assum irule >>
  goal_assum (drule_at Any) >>
  Cases_on `x` >> gvs[]
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

Theorem subst_single_def:
  (∀n v s. subst n v (Var s) = (if n = s then v else Var s)) ∧
  (∀n v op xs. subst n v (Prim op xs) = Prim op (MAP (subst n v) xs)) ∧
  (∀n v x y. subst n v (App x y) = App (subst n v x) (subst n v y)) ∧
  (∀n v s x. subst n v (Lam s x) = Lam s (if s = n then x else subst n v x)) ∧
  (∀n v f x. subst n v (Letrec f x) =
    (if MEM n (MAP FST f) then Letrec f x else
      Letrec (MAP (λ(g,z). (g, subst n v z )) f) (subst n v x)))
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

Theorem subst_ignore_single:
  ∀ n v e. ¬MEM n (freevars e) ⇒ subst n v e = e
Proof
  rw[] >>
  irule subst_ignore >>
  gvs[pred_setTheory.EXTENSION, finite_mapTheory.FDOM_FUPDATE]
QED

Theorem subst_subst_single:
  ∀m n x y.
    closed x ∧ closed y ∧ m ≠ n ⇒
    subst n x (subst m y e) = subst m y (subst n x e)
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

Theorem subst_subst_single_UPDATE:
  ∀m e n v.
    closed v ⇒
    subst (m |+ (n,v)) e = subst m (subst n v e)
Proof
  rw[] >>
  simp[Once FUPDATE_EQ_FUNION] >>
  irule (GSYM subst_subst_FUNION) >>
  fs[FRANGE_FLOOKUP, FLOOKUP_UPDATE, PULL_EXISTS]
QED

Theorem bind_single_def:
  ∀n v e. bind n v e = if closed v then subst n v e else Fail
Proof
  rw[bind_def] >> gvs[FLOOKUP_UPDATE]
QED

Theorem bind_bind_single:
  ∀m n x y.
    closed x ∧ m ≠ n ⇒
    bind n x (bind m y e) = bind m y (bind n x e)
Proof
  rw[] >> fs[bind_def] >>
  IF_CASES_TAC >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  irule subst_subst_single >> fs[] >>
  gvs[FLOOKUP_UPDATE]
QED

Theorem bind_bind_single_UPDATE:
  ∀m e n v.
    closed v ∧ n ∉ FDOM m ⇒
    bind (m |+ (n,v)) e = bind m (bind n v e)
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
  fs[Once subst_subst_single_UPDATE]
QED

(******************* freevars ********************)

Theorem freevars_expandLets:
  ∀y i cn nm vs cs.
    MEM y (freevars (expandLets i cn nm vs cs)) ∧ y ≠nm ⇒
    MEM y (FILTER (λn. ¬MEM n vs) (freevars cs))
Proof
  strip_tac >>
  Induct_on ‘vs’ >>
  rw[expandLets_def,MEM_FILTER] >>
  gvs[] >>
  gvs[MEM_FILTER] >> metis_tac[]
QED

Theorem freevars_expandRows:
  ∀y nm css.
    MEM y (freevars (expandRows nm css)) ∧ y ≠ nm ⇒
      ∃cn vs cs. MEM (cn,vs,cs) css ∧ MEM y (FILTER (λn. ¬MEM n vs) (freevars cs))
Proof
  strip_tac >>
  ho_match_mp_tac expandRows_ind >>
  rw[freevars_def,expandRows_def,freevars_expandLets] >>
  gvs[MEM_FILTER] >>
  imp_res_tac freevars_expandLets >>
  gvs[MEM_FILTER] >>
  metis_tac[]
QED

Theorem freevars_expandCases:
  ∀y x nm css.
    MEM y (freevars (expandCases x nm css)) ⇒
      (nm ≠ y ∧
       ∃cn vs cs. MEM (cn,vs,cs) css ∧ MEM y (FILTER (λn. ¬MEM n vs) (freevars cs))) ∨
      MEM y (freevars x)
Proof
  rw[expandCases_def,MEM_FILTER] >> simp[] >>
  disj1_tac >>
  drule freevars_expandRows >>
  impl_tac >- simp[] >>
  rw[MEM_FILTER]
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

Theorem freevars_subst_single:
  ∀n v e.
    closed v ⇒
    freevars (subst n v e) = freevars e DELETE n
Proof
  rw[] >>
  qspec_then `FEMPTY |+ (n,v)` assume_tac freevars_subst >> fs[DELETE_DEF]
QED

Theorem subst_subst_eq:
  closed y ⇒ subst v x (subst v y e) = subst v y e
Proof
  rw [] \\ match_mp_tac subst_ignore_single
  \\ fs [freevars_subst]
QED

Theorem freevars_subst_single_iff:
  ∀ n e x y.
    closed x ∧ closed y
  ⇒ (closed (subst n x e) ⇔ closed (subst n y e))
Proof
  rw[] >> fs[closed_def] >>
  qspec_then `FEMPTY |+ (n,x)` assume_tac freevars_subst >>
  qspec_then `FEMPTY |+ (n,y)` assume_tac freevars_subst >>
  gvs[FRANGE_FLOOKUP, FLOOKUP_UPDATE, closed_def, EXTENSION] >>
  fs[NIL_iff_NOT_MEM]
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

Theorem freevars_bind_single:
  ∀ n v e.
    set (freevars (bind n v e)) =
    if closed v then freevars e DELETE n else {}
Proof
  rw[bind_def] >> gvs[FLOOKUP_UPDATE] >>
  irule freevars_subst_single >> simp[]
QED

Theorem IMP_closed_subst:
  (∀v. v ∈ FRANGE m ⇒ closed v) ∧ freevars e SUBSET FDOM m ⇒
  closed (subst m e)
Proof
  rw [] \\ drule freevars_subst
  \\ disch_then (qspec_then ‘e’ mp_tac)
  \\ fs [EXTENSION,SUBSET_DEF,closed_def]
  \\ Cases_on ‘freevars (subst m e) : string list’ \\ fs []
  \\ qexists_tac ‘h’ \\ fs []
  \\ CCONTR_TAC \\ fs [] \\ res_tac
QED

Theorem subst_fdomsub:
  ∀f e x. x ∉ freevars e ⇒ subst f e = subst (f \\ x) e
Proof
  ho_match_mp_tac subst_ind >>
  rw[subst_def,DOMSUB_FLOOKUP_THM,MAP_EQ_f,DOMSUB_IDEM]
  >- (first_x_assum(match_mp_tac o MP_CANON) >>
      gvs[MEM_MAP] >> metis_tac[])
  >- metis_tac[DOMSUB_COMMUTES,DOMSUB_IDEM]
  >- metis_tac[DOMSUB_COMMUTES,DOMSUB_IDEM]
  >- (pairarg_tac >> gvs[] >>
      simp[fdiff_fdomsub_commute] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR])
  >- (simp[fdiff_fdomsub_commute] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR])
  >- (pairarg_tac >> gvs[] >>
      simp[fdiff_fdomsub_INSERT,ABSORPTION_RWT])
  >- (simp[fdiff_fdomsub_INSERT,ABSORPTION_RWT])
QED

Theorem subst_FDIFF':
  ∀p f x. FINITE p ∧ (∀n. n ∈ p ⇒ n ∉ freevars x) ⇒ subst f x = subst (FDIFF f p) x
Proof
  Induct_on ‘FINITE’ >>
  rpt strip_tac
  >- simp[FDIFF_def,DRESTRICT_UNIV]
  >- (qpat_x_assum ‘∀f x. _ ⇒ subst _ _ = _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single o MP_CANON) >>
      conj_tac >- rw[] >>
      simp[GSYM fdiff_fdomsub_INSERT,fdiff_fdomsub_commute] >>
      match_mp_tac subst_fdomsub >>
      rw[])
QED

Theorem subst_FDIFF'':
  ∀p f x. (∀n. n ∈ p ⇒ n ∉ freevars x) ⇒ subst f x = subst (FDIFF f p) x
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[fdiff_bound] >>
  match_mp_tac subst_FDIFF' >>
  rw[FINITE_INTER]
QED

Theorem subst_FDIFF:
  ∀f x. subst f x = subst (DRESTRICT f (freevars x)) x
Proof
  rw[] >>
  SIMP_TAC std_ss [SimpR “$=”,Once(GSYM COMPL_COMPL)] >>
  SIMP_TAC std_ss [GSYM FDIFF_def] >>
  match_mp_tac subst_FDIFF'' >>
  rw[]
QED

Theorem closed_subst_freevars:
  ∀s x y.
    closed x ∧ closed(subst s x y) ⇒
    set(freevars y) ⊆ {s}
Proof
  rw[] >> pop_assum mp_tac >> drule freevars_subst_single >>
  disch_then(qspecl_then [‘s’,‘y’] mp_tac) >> rw[] >>
  gvs[closed_def, DELETE_DEF, SUBSET_DIFF_EMPTY]
QED

Theorem closed_subst_all_freevars:
  ∀m e.
    (∀v. v ∈ FRANGE m ⇒ closed v) ∧
    closed (subst m e)
  ⇒ freevars e ⊆ FDOM m
Proof
  rw[] >> imp_res_tac freevars_subst >>
  gvs[closed_def, EXTENSION, NIL_iff_NOT_MEM, SUBSET_DEF, DISJ_EQ_IMP]
QED

Theorem closed_freevars_subst:
  ∀s x y.
    closed x ∧ set(freevars y) ⊆ {s} ⇒
    closed(subst s x y)
Proof
  rw[] >>
  drule freevars_subst_single >> disch_then (qspecl_then [‘s’,‘y’] mp_tac) >>
  gvs[DELETE_DEF, closed_def] >> rw[] >>
  `freevars (subst s x y) = {}` suffices_by gvs[] >>
  pop_assum SUBST_ALL_TAC >>
  rw[SUBSET_DIFF_EMPTY]
QED

val _ = export_theory();
