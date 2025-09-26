Theory acyclic_termination
Ancestors
  arithmetic list relation set_relation pred_set finite_map
  misc[qualified]  (* for list_max *)
Libs
  BasicProvers dep_rewrite

Definition acyclic_rec_def:
  acyclic_rec r f err x =
    if acyclic r ∧ ∃s. FINITE s ∧ domain r ⊆ s ∧ range r ⊆ s
    then
      let children = SET_TO_LIST {y | r (y,x)} in
        f x children (MAP (acyclic_rec r f err) children)
    else err
Termination
  WF_REL_TAC `λx y.
    FST x = FST y ∧
    acyclic (FST y) ∧ ∃s. FINITE s ∧ domain (FST y) ⊆ s ∧ range (FST y) ⊆ s ∧
    (FST y) (SND $ SND $ SND x, SND $ SND $ SND y)`
  >- (
    qspecl_then [
      `\r. acyclic r ∧ ∃s. FINITE s ∧ domain r ⊆ s ∧ range r ⊆ s`,
      `FST`,
      `λr x y. r(x,y)`,
      `SND o SND o SND`
    ] irule WF_PULL >>
    reverse $ rw[]
    >- (
      drule_all acyclic_WF >>
      simp[reln_to_rel_def,IN_DEF]
    ) >>
    metis_tac[]
  ) >>
  rw[] >>
  pop_assum mp_tac >>
  DEP_REWRITE_TAC[MEM_SET_TO_LIST] >>
  reverse $ rw[]
  >- metis_tac[] >>
  drule_then irule SUBSET_FINITE >>
  gvs[domain_def] >>
  rev_drule_at_then Any irule SUBSET_TRANS >>
  rw[SUBSET_DEF,IN_DEF] >>
  metis_tac[]
End

Definition acyclic_depth_def:
  acyclic_depth r x = acyclic_rec r (λx xs ys. list_max ys + 1n) 0 x
End

Theorem list_max_MAX_SET_set:
  list_max l = MAX_SET (set l)
Proof
  Induct_on `l` >>
  rw[miscTheory.list_max_def,MAX_SET_THM,MAX_DEF]
QED

(* helper function for termination proof with acyclicity *)
Theorem acyclic_depth_alt:
  ∀r x.
    acyclic_depth r x =
      if acyclic r ∧ ∃s. FINITE s ∧ domain r ⊆ s ∧ range r ⊆ s
      then
        MAX_SET (IMAGE (acyclic_depth r) {y | r (y,x)}) + 1
      else 0
Proof
  simp[lambdify acyclic_depth_def] >>
  `∀r f e x.
     f = (λx xs ys. list_max ys + 1) ∧ e = 0 ⇒
     acyclic_rec r f e x =
     if acyclic r ∧ ∃s. FINITE s ∧ domain r ⊆ s ∧ range r ⊆ s then
       MAX_SET (IMAGE (λx. acyclic_rec r f e x) {y | r (y,x)}) + 1
     else 0` suffices_by rw[] >>
  ho_match_mp_tac acyclic_rec_ind >>
  reverse $ rw[]
  >- simp[acyclic_rec_def] >>
  simp[Once acyclic_rec_def] >>
  reverse $ IF_CASES_TAC
  >- metis_tac[] >>
  simp[list_max_MAX_SET_set,LIST_TO_SET_MAP] >>
  DEP_REWRITE_TAC[SET_TO_LIST_INV] >>
  gvs[domain_def,IN_DEF] >>
  drule_then irule SUBSET_FINITE >>
  rev_drule_at_then Any irule SUBSET_TRANS >>
  rw[SUBSET_DEF,IN_DEF] >>
  metis_tac[]
QED

Theorem acyclic_super_FINITE:
  ∃s.
    FINITE s ∧
    domain
      (λp. ∃s ts. FLOOKUP ce (SND p) = SOME (s,ts) ∧
        MEM (FST p) s) ⊆ s ∧
    range
      (λp. ∃s ts. FLOOKUP ce (SND p) = SOME (s,ts) ∧
        MEM (FST p) s) ⊆ s
Proof
  qexists `FDOM ce ∪
    BIGUNION (IMAGE (set o FST) $ FRANGE ce)` >>
  rw[]
  >- simp[FINITE_LIST_TO_SET]
  >- (
    irule SUBSET_TRANS >>
    irule_at (Pos last) $ cj 2 SUBSET_UNION >>
    rw[SUBSET_DEF,IN_DEF,domain_def,
         SRULE[IN_DEF] FRANGE_FLOOKUP] >>
    first_x_assum $ irule_at (Pos last) >>
    simp[]
  ) >>
  irule SUBSET_TRANS >>
  irule_at (Pos last) $ cj 1 SUBSET_UNION >>
  rw[SUBSET_DEF,range_def,flookup_thm]
QED
