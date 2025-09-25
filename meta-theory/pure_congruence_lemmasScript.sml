Theory pure_congruence_lemmas
Ancestors
  list pred_set finite_map pure_congruence pure_exp_lemmas

Theorem Apps_APPEND:
  ∀f xs ys. Apps f (xs ++ ys) = Apps (Apps f xs) ys
Proof
  Induct_on ‘xs’ >> simp[pure_expTheory.Apps_def]
QED

Theorem exp_eq_Apps_cong:
  ∀b f1 f2 es1 es2.
    (f1 ≅? f2) b ∧ LIST_REL (λe1 e2. (e1 ≅? e2) b) es1 es2 ⇒
    (Apps f1 es1 ≅? Apps f2 es2) b
Proof
  Induct_on ‘es1’ using SNOC_INDUCT >>
  simp[Apps_SNOC, LIST_REL_SNOC, PULL_EXISTS, Apps_APPEND,
       pure_expTheory.Apps_def] >> rpt strip_tac >>
  irule exp_eq_App_cong >> simp[]
QED

Theorem exp_eq_Lams_cong_noaconv:
  (e1 ≅? e2) b ⇒ (Lams vs e1 ≅? Lams vs e2) b
Proof
  Induct_on ‘vs’ >> simp[pure_expTheory.Lams_def, exp_eq_Lam_cong]
QED

Theorem exp_eq_Let_cong_noaconv:
  (e1 ≅? e2) b ∧ (bod1 ≅? bod2) b ⇒
  (Let v e1 bod1 ≅? Let v e2 bod2) b
Proof
  simp[exp_eq_App_cong, exp_eq_Lam_cong]
QED

Theorem exp_eq_If_cong:
  (g1 ≅? g2) b ∧ (t1 ≅? t2) b ∧ (e1 ≅? e2) b ⇒
  (If g1 t1 e1 ≅? If g2 t2 e2) b
Proof
  simp[exp_eq_Prim_cong]
QED

Theorem exp_eq_Seq_cong:
  (e11 ≅? e21) b ∧ (e12 ≅? e22) b ⇒ (Seq e11 e12 ≅? Seq e21 e22) b
Proof
  strip_tac >> irule exp_eq_Prim_cong >> simp[]
QED

Theorem exp_eq_IfT:
  (If (Cons "True" []) e1 e2 ≅? e1) b
Proof
  irule pure_exp_relTheory.eval_IMP_exp_eq >>
  simp[pure_expTheory.subst_def, pure_evalTheory.eval_thm]
QED

Theorem exp_eq_COND_cong:
  (P ⇒ e1 ≅ d1) ∧ (¬P ⇒ e2 ≅ d2) ⇒
  (if P then e1 else e2) ≅ (if P then d1 else d2)
Proof
  rw[]
QED

Theorem Let_Fail:
  (Let w e Fail ≅? Fail) b
Proof
  simp[Let_Prim_alt]
QED

Theorem Seq_Fail:
  (Seq Fail e ≅? Fail) b
Proof
  simp[pure_exp_relTheory.exp_eq_def, pure_expTheory.bind_def] >> rw[] >>
  irule pure_exp_relTheory.eval_IMP_app_bisimilarity >>
  simp[pure_expTheory.subst_def] >> conj_tac
  >- (irule IMP_closed_subst >> gs[FRANGE_DEF, PULL_EXISTS, FLOOKUP_DEF]) >>
  simp[pure_evalTheory.eval_thm]
QED

Theorem Let_Var':
  (Let v (Var v) M ≅? M) b
Proof
  simp[pure_exp_relTheory.exp_eq_def, pure_expTheory.bind_def] >> rw[] >>
  simp[pure_expTheory.subst_def] >>
  irule pure_exp_relTheory.eval_IMP_app_bisimilarity >>
  ‘(∀v. v ∈ FRANGE f ⇒ closed v) ∧ (∀w. w ∈ FRANGE (f \\ v) ⇒ closed w)’
    by gs[FRANGE_DEF, PULL_EXISTS, FLOOKUP_DEF, DOMSUB_FAPPLY_THM] >>
  rw[]
  >- (simp[freevars_subst] >> gs[SUBSET_DEF, SF CONJ_ss])
  >- gs[FLOOKUP_DEF]
  >- (irule IMP_closed_subst >> simp[]) >>
  gs[pure_evalTheory.eval_Let, pure_expTheory.bind_def, FLOOKUP_DEF] >>
  simp[subst_subst_FUNION] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[fmap_EXT] >> rw[]
  >- (simp[EXTENSION] >> metis_tac[])
  >- simp[FUNION_DEF, DOMSUB_FAPPLY_THM]
  >- simp[FUNION_DEF, DOMSUB_FAPPLY_THM]
QED

