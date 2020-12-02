
open HolKernel Parse boolLib bossLib term_tactic;
open stringTheory optionTheory configTheory expTheory pure_langTheory
     listTheory pairTheory pred_setTheory alistTheory dep_rewrite
     finite_mapTheory;

val _ = new_theory "pure_langProps";

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

Theorem freevars_bind:
  ∀m y.
    set (freevars (bind m y)) =
      if (∀v. v ∈ FRANGE m ⇒ closed v) then
        freevars y DIFF FDOM m
      else {}
Proof
  rw[bind_def] >> fs[]
  >- (drule freevars_subst >> fs[]) >>
  gvs[FRANGE_FLOOKUP] >> res_tac
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
    fs[subst_def]
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

val _ = export_theory ();
