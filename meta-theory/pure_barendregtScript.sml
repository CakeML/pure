(*
  Barendregt convention for PureLang
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory listTheory rich_listTheory pred_setTheory;
open pure_expTheory pure_exp_lemmasTheory pure_miscTheory pure_beta_equivTheory;

val _ = new_theory "pure_barendregt";


(********** Preliminaries: lists of pairwise-disjoint sets *)

Definition list_disjoint_def:
  list_disjoint l ⇔
    ∀left mid right.
      l = left ++ [mid] ++ right
    ⇒ DISJOINT mid (BIGUNION (set (left ++ right)))
End

Theorem list_disjoint_alt_def:
  list_disjoint l ⇔
    ∀left right. l = left ++ right ⇒
      DISJOINT (BIGUNION (set left)) (BIGUNION (set right))
Proof
  rw[list_disjoint_def] >> eq_tac >> rw[]
  >- (
    first_x_assum irule >>
    qspecl_then [`left`,`s'`] assume_tac $ GEN_ALL MEM_SING_APPEND >> gvs[] >>
    qexists_tac `a` >> simp[]
    )
  >- (
    once_rewrite_tac[DISJOINT_SYM] >>
    first_x_assum irule >> qexists_tac `left` >> simp[]
    )
  >- (first_x_assum irule >> qexists_tac `left ++ [mid]` >> simp[])
QED

Theorem list_disjoint:
  list_disjoint l ⇔
    ∀left mid right. l = left ++ [mid] ++ right
    ⇒ DISJOINT mid (BIGUNION (set left))
Proof
  rw[list_disjoint_def] >> eq_tac >> rw[]
  >- metis_tac[]
  >- metis_tac[] >>
  drule_at Concl $ iffLR MEM_SING_APPEND >> strip_tac >> gvs[] >>
  first_x_assum $ qspec_then `left ++ [mid] ++ a` mp_tac >> rw[] >>
  gvs[SF DNF_ss] >> simp[Once DISJOINT_SYM]
QED

Theorem list_disjoint_cons:
  list_disjoint (x::xs) ⇔
    list_disjoint xs ∧ EVERY (DISJOINT x) xs
Proof
  rw[list_disjoint_alt_def] >> eq_tac >> rw[]
  >- (first_x_assum irule >> qexists `x::left` >> simp[])
  >- (
    first_x_assum $ qspec_then `[x]` assume_tac >> gvs[EVERY_MEM]
    ) >>
  gvs[APPEND_EQ_CONS, EVERY_MEM] >>
  first_x_assum irule >> rpt $ goal_assum $ drule_at Any >> simp[]
QED

Theorem list_disjoint_singleton[simp]:
  list_disjoint [a]
Proof
  rw[list_disjoint_alt_def] >> Cases_on `left` >> gvs[]
QED

Theorem list_disjoint_doubleton[simp]:
  list_disjoint [a;b] ⇔ DISJOINT a b
Proof
  rw[list_disjoint_def] >> eq_tac >> rw[]
  >- (first_x_assum irule >> qexistsl_tac [`[]`] >> simp[]) >>
  Cases_on `left` >> gvs[] >> Cases_on `t` >> gvs[] >> simp[DISJOINT_SYM]
QED

Theorem list_disjoint_append:
  ∀l1 l2. list_disjoint (l1 ++ l2) ⇔
    list_disjoint l1 ∧ list_disjoint l2 ∧
    DISJOINT (BIGUNION (set l1)) (BIGUNION (set l2))
Proof
  rw[list_disjoint_alt_def] >> eq_tac >> rw[]
  >- (first_x_assum irule >> qexists_tac `left` >> simp[])
  >- (first_x_assum irule >> qexists_tac `l1 ++ left` >> simp[])
  >- (first_x_assum irule >> qexists_tac `l1` >> simp[]) >>
  gvs[APPEND_EQ_APPEND]
  >- (last_x_assum irule >> ntac 2 $ goal_assum drule >> simp[])
  >- (
    last_x_assum kall_tac >> last_x_assum irule >>
    ntac 2 $ goal_assum drule >> simp[]
    )
QED

Theorem list_disjoint_ALL_DISTINCT:
  ∀l. EVERY FINITE l ⇒
    (list_disjoint l ⇔ ALL_DISTINCT (FLAT $ MAP SET_TO_LIST l))
Proof
  Induct >- rw[list_disjoint_def] >>
  rw[list_disjoint_cons, ALL_DISTINCT_APPEND] >> gvs[] >>
  irule AND_CONG >> rw[] >> eq_tac >> rw[]
  >- (
    CCONTR_TAC >> gvs[] >>
    gvs[MEM_FLAT, MEM_MAP, EVERY_MEM, MEM_SET_TO_LIST, DISJOINT_ALT]
    )
  >- (
    gvs[Once MONO_NOT_EQ] >>
    gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS, EVERY_MEM] >> rw[] >>
    first_x_assum drule >> gvs[MEM_SET_TO_LIST, DISJOINT_ALT] >> metis_tac[]
    )
QED


(********** Unique bound variables **********)

Definition unique_boundvars_def:
  unique_boundvars (Var x) = T ∧
  unique_boundvars (Prim op es) =
    (EVERY unique_boundvars es ∧ list_disjoint (MAP boundvars es)) ∧
  unique_boundvars (App e1 e2) = (
    unique_boundvars e1 ∧ unique_boundvars e2 ∧
    DISJOINT (boundvars e1) (boundvars e2)) ∧
  unique_boundvars (Lam x e) = (x ∉ boundvars e ∧ unique_boundvars e) ∧
  unique_boundvars (Letrec fns e) = (
    ALL_DISTINCT (MAP FST fns) ∧
    list_disjoint (set (MAP FST fns) :: MAP boundvars (e::MAP SND fns)) ∧
    EVERY unique_boundvars (e :: MAP SND fns))
Termination
  WF_REL_TAC `measure exp_size` >>
  Induct >> rw[] >> gvs[SF DNF_ss] >>
  PairCases_on `h` >> gvs[pure_expTheory.exp_size_def] >>
  first_x_assum drule >> disch_then $ qspec_then `e` assume_tac >> gvs[]
End

Theorem unique_boundvars_Letrec:
  unique_boundvars (Letrec fns e) ⇔
    ALL_DISTINCT (MAP FST fns) ∧
    let names = set $ MAP FST fns in
      EVERY (λ(f,body).
        DISJOINT names (boundvars body) ∧
        DISJOINT (boundvars e) (boundvars body) ∧
        unique_boundvars body) fns ∧
      list_disjoint (MAP boundvars (MAP SND fns)) ∧
      DISJOINT names (boundvars e) ∧
      unique_boundvars e
Proof
  rw[unique_boundvars_def] >> irule_at Any AND_CONG >> rw[] >>
  simp[list_disjoint_cons] >> eq_tac >> rw[] >>
  gvs[EVERY_MEM, MEM_MAP, EXISTS_PROD] >> gvs[PULL_EXISTS] >> rw[]
  >- (pairarg_tac >> gvs[] >> rpt $ last_assum $ irule_at Any) >>
  first_x_assum drule >> gvs[]
QED

Theorem unique_boundvars_thm:
  ∀e. unique_boundvars e ⇔ ALL_DISTINCT (boundvars_l e)
Proof
  Induct using unique_boundvars_ind >>
  rw[unique_boundvars_Letrec, unique_boundvars_def] >>
  gvs[ALL_DISTINCT_APPEND]
  >- (
    Induct_on `es` >> rw[] >> gvs[] >- simp[list_disjoint_def] >>
    gvs[list_disjoint_cons, ALL_DISTINCT_APPEND] >>
    gvs[EVERY_MEM, MEM_MAP, MEM_FLAT, DISJOINT_ALT, boundvars_equiv, PULL_EXISTS] >>
    metis_tac[]
    )
  >- gvs[DISJOINT_ALT, boundvars_equiv]
  >- gvs[boundvars_equiv] >>
  eq_tac >> strip_tac
  >- (
    gvs[SF DNF_ss, EVERY_MEM, DISJOINT_ALT, boundvars_equiv,
        MEM_FLAT, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
    reverse $ rw[] >- metis_tac[] >- metis_tac[] >- metis_tac[] >>
    `∀f body. MEM (f,body) fns ⇒ ALL_DISTINCT (boundvars_l body)` by metis_tac[] >>
    pop_assum mp_tac >> qpat_x_assum `list_disjoint _` mp_tac >>
    rpt $ pop_assum kall_tac >> Induct_on `fns` >> rw[] >> gvs[SF DNF_ss] >>
    pairarg_tac >> gvs[ALL_DISTINCT_APPEND, list_disjoint_cons] >>
    first_x_assum $ irule_at Any >> conj_tac >> gvs[] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    gvs[MEM_FLAT, MEM_MAP, EVERY_MEM, DISJOINT_ALT,
        EXISTS_PROD, FORALL_PROD, boundvars_equiv] >>
    metis_tac[]
    )
  >- (
    gvs[SF DNF_ss, EVERY_MEM, DISJOINT_ALT, boundvars_equiv,
        MEM_FLAT, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
    rw[] >- metis_tac[] >- metis_tac[]
    >~ [`¬MEM x (boundvars_l e)`] >- metis_tac[]
    >- (
      drule ALL_DISTINCT_FLAT_IMP >> simp[MEM_MAP, PULL_EXISTS] >>
      disch_then drule >> simp[] >> metis_tac[]
      ) >>
    DEP_REWRITE_TAC[list_disjoint_ALL_DISTINCT] >> simp[EVERY_MAP] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    qpat_x_assum `ALL_DISTINCT (FLAT _)` mp_tac >> rpt $ pop_assum kall_tac >>
    Induct_on `fns` >> rw[] >> gvs[] >> pairarg_tac >> gvs[] >>
    gvs[ALL_DISTINCT_APPEND, boundvars_equiv] >> rw[] >>
    first_x_assum drule >> simp[MEM_FLAT, MEM_MAP, FORALL_PROD] >>
    rw[DISJ_EQ_IMP, PULL_FORALL, PULL_EXISTS] >> res_tac
    )
QED


(********** Barendregt convention **********)

Definition barendregt_def:
  barendregt e ⇔ unique_boundvars e ∧ DISJOINT (boundvars e) (freevars e)
End

Theorem barendregt_alt_def:
  barendregt (Var x) = T ∧
  barendregt (Prim op es) =
    (EVERY barendregt es ∧
     ∀l mid r. es = l ++ [mid] ++ r ⇒
      DISJOINT (boundvars mid) (BIGUNION $ set $ MAP allvars (l ++ r))) ∧
  barendregt (App e1 e2) = (
    barendregt e1 ∧ barendregt e2 ∧
    DISJOINT (boundvars e1) (allvars e2) ∧
    DISJOINT (boundvars e2) (allvars e1)) ∧
  barendregt (Lam x e) = (x ∉ boundvars e ∧ barendregt e) ∧
  barendregt (Letrec fns e) = (
    EVERY barendregt (e :: MAP SND fns) ∧
    ALL_DISTINCT (MAP FST fns) ∧
    DISJOINT (boundvars e)
      (set (MAP FST fns) ∪ BIGUNION (set $ MAP (allvars o SND) fns)) ∧
    ∀l mid r. fns = l ++ [mid] ++ r ⇒
      DISJOINT (boundvars (SND mid))
        (set (MAP FST fns) ∪ allvars e ∪
         BIGUNION (set $ MAP (allvars o SND) (l ++ r))))
Proof
  rw[barendregt_def, unique_boundvars_def, SF ETA_ss] >>
  gvs[MEM_MAP, PULL_EXISTS, AC CONJ_ASSOC CONJ_COMM, SF DNF_ss]
  >- (
    eq_tac >> strip_tac
    >- (
      rw[]
      >- gvs[EVERY_MEM, barendregt_def] >>
      gvs[SF DNF_ss, list_disjoint_append, MEM_MAP, PULL_EXISTS] >>
      gvs[allvars_thm] >> metis_tac[DISJOINT_SYM]
      ) >>
    rw[] >> gvs[allvars_thm]
    >- gvs[EVERY_MEM, barendregt_def]
    >- (
      rw[list_disjoint, MAP_EQ_APPEND] >> gvs[MEM_MAP] >> metis_tac[DISJOINT_SYM]
      ) >>
    dxrule_at Concl $ iffLR MEM_SING_APPEND >> strip_tac >> gvs[barendregt_def]
    >- (
      dxrule_at Concl $ iffLR MEM_SING_APPEND >> strip_tac >> gvs[] >>
      rename1 `a ++ [x] ++ b ++ [x'] ++ c` >>
      last_x_assum $ qspec_then `a` mp_tac >> simp[] >> metis_tac[DISJOINT_SYM]
      )
    >- (
      dxrule_at Concl $ iffLR MEM_SING_APPEND >> strip_tac >> gvs[] >>
      rename1 `a ++ [x] ++ b ++ [x'] ++ c` >>
      first_x_assum $ qspec_then `a ++ [x] ++ b` mp_tac >> simp[] >>
      metis_tac[DISJOINT_SYM]
      )
    )
  >- (simp[allvars_thm] >> metis_tac[DISJOINT_SYM])
  >- (eq_tac >> rw[] >> gvs[DISJOINT_ALT] >> metis_tac[])
  >- (
    gvs[list_disjoint_cons] >> eq_tac >> strip_tac
    >- (
      `DISJOINT (boundvars e)
        (freevars e ∪ BIGUNION (set $ MAP (freevars o SND) fns)) ∧
       ∀y. MEM y fns ⇒
        DISJOINT (boundvars (SND y))
        (freevars e ∪ BIGUNION (set $ MAP (freevars o SND) fns))` by (
          gvs[UNCURRY, DISJOINT_ALT, MEM_MAP, PULL_EXISTS, PULL_FORALL,
              EVERY_MAP, EVERY_MEM] >> metis_tac[]) >>
      qpat_x_assum `∀y. _ ⇒ DISJOINT (UNCURRY _ _) _` kall_tac >>
      ntac 2 $ qpat_x_assum `DISJOINT _ (_ DIFF _)` kall_tac >>
      rw[] >> gvs[list_disjoint_append, MEM_MAP, PULL_EXISTS, EVERY_MAP]
      >- simp[Once DISJOINT_SYM]
      >- (gvs[EVERY_MEM, barendregt_def] >> metis_tac[DISJOINT_SYM])
      >- (gvs[allvars_thm, EVERY_MEM] >> metis_tac[DISJOINT_SYM]) >>
      gvs[SF DNF_ss, allvars_thm] >> metis_tac[DISJOINT_SYM]
      ) >>
    gvs[AC CONJ_ASSOC CONJ_COMM, EVERY_MAP, MAP_MAP_o, ELIM_UNCURRY] >> rw[]
    >- (gvs[EVERY_MEM, barendregt_def])
    >- (
      rw[list_disjoint] >> gvs[MAP_EQ_APPEND, MEM_MAP] >> rename1 `l ++ [m] ++ r` >>
      first_x_assum $ drule_at Any >> rw[allvars_thm] >> simp[Once DISJOINT_SYM]
      )
    >- (
      rw[EVERY_MEM] >> last_x_assum drule >> rw[allvars_thm] >>
      simp[Once DISJOINT_SYM]
      )
    >- (
      rw[EVERY_MEM] >>
      dxrule_at Concl $ iffLR MEM_SING_APPEND >> strip_tac >> gvs[] >>
      rpt $ last_x_assum $ qspec_then `a` mp_tac >> simp[]
      )
    >- (gvs[DISJOINT_ALT, MEM_MAP, PULL_EXISTS, allvars_thm] >> metis_tac[])
    >- (gvs[DISJOINT_ALT, MEM_MAP, PULL_EXISTS, allvars_thm] >> metis_tac[])
    >- (
      irule DISJOINT_SUBSET >> irule_at Any pred_setTheory.DIFF_SUBSET >> simp[] >>
      dxrule_at Concl $ iffLR MEM_SING_APPEND >> strip_tac >> gvs[] >>
      rw[] >> gvs[MEM_MAP, barendregt_def]
      >- (gvs[allvars_thm] >> metis_tac[])
      >- (first_x_assum $ drule_at Any >> simp[allvars_thm])
      >- simp[Once DISJOINT_SYM] >>
      dxrule_at Concl $ iffLR MEM_SING_APPEND >> strip_tac >> gvs[] >>
      rpt $ first_x_assum $ qspec_then `a` mp_tac >> simp[allvars_thm]
      )
    )
QED

Theorem barendregt_beta_equivalence:
  barendregt (App (Lam x body) arg) ⇒
    App (Lam x body) arg ≅ subst1 x arg body
Proof
  rw[barendregt_def] >> irule disjoint_vars_beta_equivalence >> simp[]
QED

Theorem barendregt_beta_equivalence_Letrec:
  barendregt (Letrec fns e) ⇒
    Letrec fns e ≅ subst (FEMPTY |++ (MAP (λ(f,body). f, Letrec fns body) fns)) e
Proof
  rw[barendregt_def] >>
  irule disjoint_vars_beta_equivalence_Letrec >> rw[EVERY_MEM] >>
  pairarg_tac >> gvs[] >> simp[Once DISJOINT_SYM] >> gvs[DISJOINT_ALT] >> rw[] >>
  last_x_assum drule >> strip_tac >>
  gvs[DISJ_EQ_IMP, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> metis_tac[]
QED


(**********)

val _ = export_theory();
