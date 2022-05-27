open HolKernel Parse boolLib bossLib;

open listTheory pairTheory finite_mapTheory pred_setTheory

open pure_nestedcaseTheory pureLangTheory pure_cexpTheory pure_congruenceTheory
     pure_exp_lemmasTheory pure_congruence_lemmasTheory exp_eqSimps

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

val _ = temp_delsimps ["nested_rows_def"]
Theorem lift_uscore_correct:
  ∀e. exp_of (lift_uscore e) ≅ exp_of e
Proof
  ho_match_mp_tac better_cexp_induction >>
  rpt conj_tac >>
  simp[lift_uscore_thm, exp_of_def, MAP_MAP_o, Cong MAP_CONG,
       combinTheory.o_ABS_L] >> simp[SF ETA_ss] >>
  rpt strip_tac >~
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
      simp[] >>
      qmatch_abbrev_tac ‘exp_of (if _ then _ else BASE) ≅ ORIG’ >>
      ‘exp_of BASE ≅ ORIG’
        by (simp[Abbr‘BASE’, Abbr‘ORIG’, exp_of_def,
                 MAP_MAP_o, pairTheory.o_UNCURRY_R, combinTheory.o_ABS_R,
                 SF EXPEQ_ss] >>
            simp[ELIM_UNCURRY] >>
            qmatch_abbrev_tac ‘(if P then _ else e2) ≅ (if P then _ else d2)’>>
            ‘e2 ≅ d2’ suffices_by simp[SF EXPEQ_ss] >>
            UNABBREV_ALL_TAC >> irule exp_eq_Let_cong_noaconv >>
            simp[] >> simp[nested_rows_to_termform] >>
            irule exp_eq_nested_row_terms_cong >> simp[] >>
            gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP] >>
            rpt strip_tac >> first_x_assum irule >> metis_tac[PAIR]) >>
      reverse $ Cases_on ‘lpat = cepatUScore’ >> simp[] >>
      Cases_on ‘dest_nestedcase lexp’ >> simp[] >>
      rename [‘dest_nestedcase _ = SOME blob’] >>
      ‘∃texp tv nested_pes. blob = (texp, tv, nested_pes)’
        by metis_tac[pair_CASES] >>
      gvs[] >> Cases_on ‘dest_var texp’ >> simp[] >>
      rename [‘dest_var texp = SOME vnm’] >>
      reverse $ Cases_on ‘s = tv ∧ vnm = tv’ >> simp[] >> gvs[] >>
      ‘allpes ≠ []’ by simp[Abbr‘allpes’] >>
      qabbrev_tac ‘pespfx = FRONT allpes’ >>
      ‘allpes = pespfx ++ [(cepatUScore, lexp)]’
        by metis_tac[APPEND_FRONT_LAST] >>
      Q.RM_ABBREV_TAC ‘pespfx’>> simp[updlast_SNOC] >>
      gs[dest_nestedcase_EQ_SOME] >>
      ‘pespfx = [] ∨ ∃p00 e00 pfxtl. pespfx = (p00,e00) :: pfxtl’
        by metis_tac[list_CASES, pair_CASES]
      >- (simp[] >> gvs[Abbr‘allpes’, dest_var_EQ_SOME, exp_of_def] >>
          dxrule_then assume_tac $ iffLR exp_eq_sym >>
          simp[SF EXPEQ_ss, Abbr‘BASE’, exp_of_def] >>
          qmatch_goalsub_abbrev_tac
            ‘Let s (Var s) (nested_rows (Var s) allpes)’ >>
          simp[nested_rows_def, patguards_def, SF EXPEQ_ss] >> rw[] >>
          simp[SF EXPEQ_ss]) >>
      pop_assum SUBST_ALL_TAC >> simp[] >>
      ‘p00 = pat1 ∧ e00 = lift_uscore exp1’ by (simp[Abbr‘allpes’] >> gs[]) >>
      ntac 2 (pop_assum SUBST_ALL_TAC) >>
      simp[exp_of_def] >> simp[combinTheory.o_DEF] >>
      simp[SF EXPEQ_ss, Abbr‘ORIG’] >>
      Cases_on ‘MEM s (cepat_vars_l pat1)’ >> simp[] >>
      qpat_x_assum ‘allpes = _’ mp_tac >>
      simp[Abbr‘allpes’] >>
      simp[MAP_EQ_APPEND, EXISTS_PROD, PULL_EXISTS] >> rpt strip_tac >>
      gvs[MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY] >>
      rename [‘MAP _ pesfront ++ [(cepatUScore, _)]’] >>
      Cases_on ‘MEM s (FLAT (MAP (λx. cepat_vars_l (FST x)) pesfront))’ >>
      simp[] >>
      Cases_on ‘MEM s (cepat_vars_l p0)’ >> simp[]
      >- (gs[] >> cheat) >>
      cheat ) (*
      Cases_on ‘MEM s (FLAT (MAP (λx. cepat_vars_l (FST x)) pfxtl)’
          irule exp_eq_Prim_cong >> simp[] >>
          simp[Abbr‘EE’]>>
          irule exp_eq_Let_cong_noaconv >> simp[] >>
          simp[nested_rows_to_termform, nested_rows_term_APPEND,
               Excl "APPEND", GSYM APPEND] >>
          simp[MAP_MAP_o, combinTheory.o_ABS_R, pairTheory.o_UNCURRY_R] >>
          rpt strip_tac >> irule exp_eq_nested_row_terms_cong >> simp[] >>
          conj_tac
          >- (simp[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY] >>
              rpt strip_tac >> first_x_assum irule >> simp[MEM_EL] >>
              metis_tac[PAIR]) >>
          gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
          simp[nested_rows_term_def, SimpR “exp_eq”, patguards_def] >>
          irule exp_eq_trans >>
          irule_at (Pat ‘_ ≅ If _ _ _’)
                   (MATCH_MP (iffLR exp_eq_sym) exp_eq_IfT) >>
          rename [‘exp_of (lift_uscore pp) ≅ exp_of pp’,
                  ‘NestedCase _ _ _ _ _ _ = lift_uscore pp’] >>
          irule exp_eq_trans >> first_assum $ irule_at Any >>
          qpat_x_assum ‘_ = lift_uscore pp’ (assume_tac o SYM) >>
          simp[exp_of_def]



          Cases_on ‘GD’ >> simp[nested_rows_def, patguards_def] >>
          simp[exp_of_def, Abbr‘ORIG’] >> simp[
          gs[nested_rows_def, patguards_def]

      cheat
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
      cheat ) *)
QED



val _ = export_theory();
