open HolKernel Parse boolLib bossLib;

open listTheory pairTheory

open pure_nestedcaseTheory pureLangTheory pure_cexpTheory pure_congruenceTheory
     pure_exp_lemmasTheory

val _ = new_theory "pure_nestedcaseProof";

Theorem exp_eq_refl[simp] = exp_eq_refl

Theorem silly_cong_lemma[local]:
  ((∀a b. MEM (a,b) l2 ⇒ P a b) ⇔ (∀p. MEM p l2 ⇒ P (FST p) (SND p))) ∧
  ((∀a b c. MEM (a,b,c) l3 ⇒ Q a b c) ⇔
     (∀t. MEM t l3 ⇒ Q (FST t) (FST (SND t)) (SND (SND t))))
Proof
  simp[FORALL_PROD]
QED


Theorem MEM_updlast:
  ∀l rep x.
    l ≠ [] ⇒
    (MEM x (updlast l rep) ⇔ MEM x (FRONT l) ∨ MEM x rep)
Proof
  recInduct updlast_ind >> simp[] >> metis_tac[]
QED

Theorem updlast_SNOC:
  ∀l rep y. updlast (l ++ [y]) rep = l ++ rep
Proof
  Induct >> simp[] >> Cases_on ‘l’ >> gvs[]
QED

Definition nested_rows_term_def:
  nested_rows_term v t [] = t ∧
  nested_rows_term v t (pe::pes) =
  let (gd,binds) = patguards [(v, FST pe)]
  in
    If gd (FOLDR (λ(u,e) A. Let u e A) (SND pe) binds)
       (nested_rows_term v t pes)
End

Theorem nested_rows_to_termform:
  nested_rows v pes = nested_rows_term v Fail pes
Proof
  Induct_on ‘pes’ >> simp[nested_rows_def, nested_rows_term_def]
QED

Theorem nested_rows_term_APPEND:
  nested_rows_term v t (l1 ++ l2) =
  nested_rows_term v (nested_rows_term v t l2) l1
Proof
  Induct_on ‘l1’ >> simp[nested_rows_term_def]
QED

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

Theorem exp_eq_lets_for_cong:
  (e1 ≅? e2) b ⇒ (lets_for cn v l e1 ≅? lets_for cn v l e2) b
Proof
  Induct_on ‘l’ >> simp[lets_for_def, FORALL_PROD, exp_eq_Let_cong_noaconv]
QED

Theorem exp_eq_rows_of_cong:
  LIST_REL
    (λ(cnm1,vs1,e1) (cnm2,vs2,e2). cnm1 = cnm2 ∧ vs1 = vs2 ∧ (e1 ≅? e2) b)
    l1 l2 ⇒
  (rows_of s l1 ≅? rows_of s l2) b
Proof
  Induct_on ‘LIST_REL’ >> simp[rows_of_def, FORALL_PROD] >> rpt strip_tac >>
  irule exp_eq_If_cong >> simp[exp_eq_lets_for_cong]
QED

Theorem exp_eq_patguards_cong:
  ∀gps1 gps2 e1 binds1 e2 binds2.
    LIST_REL (λ(e1,p1) (e2, p2). p1 = p2 ∧ (e1 ≅? e2) b) gps1 gps2 ∧
    patguards gps1 = (e1,binds1) ∧ patguards gps2 = (e2, binds2) ⇒
    (e1 ≅? e2) b ∧
    LIST_REL (λ(v1,e1) (v2,e2). v1 = v2 ∧ (e1 ≅? e2) b) binds1 binds2
Proof
  recInduct patguards_ind >> simp[patguards_def, PULL_EXISTS, FORALL_PROD] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  rename [‘cepat_CASE pat’] >> Cases_on ‘pat’ >> gvs[] >~
  [‘(I ## CONS (v,pat1)) (patguards eps1) = (e1,binds1) ∧
    (I ## CONS (v,pat2)) (patguards eps2) = (e2,binds2)’]
  >- (map_every Cases_on [‘patguards eps1’, ‘patguards eps2’] >> simp[] >>
      strip_tac >> gvs[] >> metis_tac[]) >~
  [‘(pat1 ≅? pat2) b ∧ LIST_REL _ eps1 eps2’, ‘patguards (MAPi _ ps ++ _)’,
   ‘Proj cnm’]
  >- (map_every Cases_on [
         ‘patguards (MAPi (λi p. (Proj cnm i pat1, p)) ps ++ eps1)’,
         ‘patguards (MAPi (λi p. (Proj cnm i pat2, p)) ps ++ eps2)’
       ] >> gs[] >> strip_tac >> gvs[] >>
      qabbrev_tac ‘epR = (λ(e1,p1:cepat) (e2,p2). p1 = p2 ∧ (e1 ≅? e2) b) ’ >>
      ‘LIST_REL epR (MAPi (λi p. (Proj cnm i pat1, p)) ps)
                    (MAPi (λi p. (Proj cnm i pat2, p)) ps)’
        by (simp[LIST_REL_EL_EQN, Abbr‘epR’] >> rpt strip_tac >>
            irule exp_eq_Prim_cong >> simp[]) >>
      dxrule_then (drule_then assume_tac) LIST_REL_APPEND_suff >>
      first_x_assum $ drule_all_then strip_assume_tac >>
      simp[exp_eq_If_cong, exp_eq_Prim_cong])
  >- metis_tac[]
QED

Theorem exp_eq_FOLDR_Let_cong:
  (A1 ≅? A2) b ∧ LIST_REL (λ(v1,e1) (v2,e2). v1 = v2 ∧ (e1 ≅? e2) b) l1 l2 ⇒
  (FOLDR (λ(u,e) A. Let u e A) A1 l1 ≅? FOLDR (λ(u,e) A. Let u e A) A2 l2) b
Proof
  Induct_on ‘LIST_REL’>> simp[FORALL_PROD, exp_eq_Let_cong_noaconv]
QED

Theorem exp_eq_nested_row_terms_cong:
  (gd1 ≅? gd2) b ∧ (k1 ≅? k2) b ∧
  LIST_REL (λ(p1,e1) (p2,e2). p1 = p2 ∧ (e1 ≅? e2) b) pes1 pes2 ⇒
  (nested_rows_term gd1 k1 pes1 ≅? nested_rows_term gd2 k2 pes2) b
Proof
  Induct_on ‘LIST_REL’ >> simp[nested_rows_term_def, FORALL_PROD] >>
  rpt strip_tac >> gvs[] >>
  rename [‘patguards [(gd1,pat)]’, ‘(gd1 ≅? gd2) b’] >>
  ‘LIST_REL (λ(e1,p1) (e2,p2). p1 = p2 ∧ (e1 ≅? e2) b) [(gd1,pat)] [(gd2,pat)]’
    by simp[] >>
  drule_then assume_tac exp_eq_patguards_cong >>
  map_every Cases_on [‘patguards [(gd1,pat)]’, ‘patguards [(gd2,pat)]’] >>
  gs[] >> irule exp_eq_If_cong >> simp[] >>
  irule exp_eq_FOLDR_Let_cong >> simp[]
QED

Theorem exp_eq_IfT:
  (If (Cons "True" []) e1 e2 ≅? e1) b
Proof
  irule pure_exp_relTheory.eval_IMP_exp_eq >>
  simp[pure_expTheory.subst_def, pure_evalTheory.eval_thm]
QED

Theorem dest_nestedcase_EQ_SOME:
  dest_nestedcase e = SOME (texp,tv,pes) ⇔
  ∃i p0 e0 perest. e = NestedCase i texp tv p0 e0 perest ∧
                   pes = (p0,e0) :: perest
Proof
  Cases_on ‘e’ >> simp[] >> metis_tac[]
QED

Theorem dest_var_EQ_SOME:
  dest_var e = SOME vnm ⇔ ∃i. e = Var i vnm
Proof
  Cases_on ‘e’ >> simp[]
QED

Theorem lift_uscore_correct:
  ∀e. exp_of (lift_uscore e) ≅ exp_of e
Proof
  ho_match_mp_tac better_cexp_induction >>
  rpt conj_tac >>
  simp[lift_uscore_thm, exp_of_def, MAP_MAP_o, Cong MAP_CONG,
       combinTheory.o_ABS_L] >> simp[SF ETA_ss] >> rpt strip_tac >~
  [‘Prim _ _ ≅ Prim _ _’]
  >- (irule exp_eq_Prim_cong >>
      gvs[LIST_REL_EL_EQN, EL_MAP, MEM_EL, PULL_EXISTS]) >~
  [‘Apps _ _ ≅ Apps _ _’]
  >- (irule exp_eq_Apps_cong >>
      gvs[MEM_EL, LIST_REL_EL_EQN, EL_MAP, PULL_EXISTS]) >~
  [‘Lams _ _ ≅ Lams _ _’] >- simp[exp_eq_Lams_cong_noaconv] >~
  [‘Let _ _ _ ≅ Let _ _ _’] >- simp[exp_eq_Let_cong_noaconv] >~
  [‘Letrec _ _ ≅ Letrec _ _’]
  >- (irule exp_eq_Letrec_cong >>
      simp[MAP_MAP_o, combinTheory.o_ABS_R, ELIM_UNCURRY] >>
      gvs[MEM_EL, LIST_REL_EL_EQN, EL_MAP, PULL_EXISTS] >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[PAIR]) >~
  [‘MEM _ (FLAT _)’, ‘Seq Fail _’]
  >- (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> rw[] >~
      [‘Seq Fail _’]
      >- (irule exp_eq_Prim_cong >> simp[] >>
          irule exp_eq_Let_cong_noaconv >> simp[] >>
          irule exp_eq_rows_of_cong >>
          gvs[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY, MEM_EL, PULL_EXISTS] >>
          rpt strip_tac >> first_x_assum irule >> metis_tac[PAIR]) >>
      irule exp_eq_Let_cong_noaconv >> simp[] >>
      irule exp_eq_rows_of_cong >>
      gvs[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY, MEM_EL, PULL_EXISTS] >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[PAIR]) >~
  [‘LAST ((pat1, lift_uscore exp1) :: MAP _ pes)’]
  >- (qmatch_goalsub_abbrev_tac ‘LAST allpes’ >>
      ‘∃lpat lexp. LAST allpes = (lpat, lexp)’ by metis_tac[pair_CASES] >>
      simp[] >> reverse $ Cases_on ‘lpat = cepatUScore’ >> simp[]
      >- (simp[exp_of_def] >> cheat) >>
      cheat (* >>
      Cases_on ‘pes = []’ >> simp[exp_of_def, exp_eq_Let_cong_noaconv] >>
      qabbrev_tac ‘pes0 = FRONT pes’ >>
      qabbrev_tac ‘pe = LAST pes’ >>
      ‘pes = pes0 ++ [pe]’ by metis_tac[APPEND_FRONT_LAST] >>
      map_every Q.RM_ABBREV_TAC [‘pes0’, ‘pe’] >>
      ‘∃p e. pe = (p,e)’ by metis_tac[pair_CASES] >>
      gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
      reverse $ Cases_on ‘p = cepatUScore’ >> simp[]
      >- (simp[exp_of_def] >> irule exp_eq_Let_cong_noaconv >> simp[] >>
          simp[nested_rows_to_termform, nested_rows_term_APPEND,
               MAP_MAP_o, combinTheory.o_ABS_R, pairTheory.o_UNCURRY_R] >>
          irule exp_eq_nested_row_terms_cong >>
          simp[exp_eq_nested_row_terms_cong]>>
          gs[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY, MEM_EL, PULL_EXISTS] >>
          rpt strip_tac >> first_x_assum irule >> metis_tac[PAIR]) >>
      Cases_on ‘dest_nestedcase (lift_uscore e)’ >> simp[exp_of_def]
      >- (irule exp_eq_Let_cong_noaconv >> simp[] >>
          simp[nested_rows_to_termform] >>
          irule exp_eq_nested_row_terms_cong >> simp[] >>
          gs[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY, MEM_EL, PULL_EXISTS] >>
          rpt strip_tac >> first_x_assum irule >> metis_tac[PAIR]) >>
      rename [‘dest_nestedcase _ = SOME blob’] >>
      ‘∃texp v nested_pes. blob = (texp, v, nested_pes)’
        by metis_tac[pair_CASES] >>
      gvs[] >> Cases_on ‘dest_var texp’ >> simp[]
      >- (simp[exp_of_def] >>
          irule exp_eq_Let_cong_noaconv >> simp[] >>
          simp[nested_rows_to_termform] >>
          irule exp_eq_nested_row_terms_cong >> simp[] >>
          gs[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY, MEM_EL, PULL_EXISTS] >>
          rpt strip_tac >> first_x_assum irule >> metis_tac[PAIR]) >>
      rename [‘dest_var texp = SOME vnm’] >>
      reverse $ Cases_on ‘gdv = vnm’ >> simp[]
      >- (simp[exp_of_def] >>
          irule exp_eq_Let_cong_noaconv >> simp[] >>
          simp[nested_rows_to_termform] >>
          irule exp_eq_nested_row_terms_cong >> simp[] >>
          gs[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY, MEM_EL, PULL_EXISTS] >>
          rpt strip_tac >> first_x_assum irule >> metis_tac[PAIR]) >>
      gvs[] >> simp[exp_of_def] >>
      irule exp_eq_Let_cong_noaconv >> simp[] >>
      simp[nested_rows_to_termform, nested_rows_term_APPEND,
           nested_rows_term_def, patguards_def, updlast_SNOC, MAP_MAP_o,
           combinTheory.o_ABS_R, pairTheory.o_UNCURRY_R] >>
      irule exp_eq_nested_row_terms_cong >> simp[] >> conj_tac
      >- (gs[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY, MEM_EL, PULL_EXISTS] >>
          rpt strip_tac >> first_x_assum irule >> metis_tac[PAIR]) >>
      irule exp_eq_trans >>
      irule_at (Pat ‘(_ ≅? If _ _ _) b’) (iffLR exp_eq_sym) >>
      irule_at Any exp_eq_IfT >>
      irule exp_eq_trans >>
      first_assum $ irule_at (Pat ‘(_ ≅? exp_of _) b’) >>
      gs[dest_nestedcase_EQ_SOME, dest_var_EQ_SOME] >>
      simp[exp_of_def, nested_rows_to_termform] >>
      cheat *))
QED



val _ = export_theory();
