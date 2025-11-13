(*
   Verification of pure_letrec_cexp
*)
Theory pure_letrec_cexpProof
Ancestors
  list rich_list pair alist pred_set finite_map sptree
  topological_sort pure_misc pure_exp pure_cexp pureLang
  pure_letrec_cexp pure_letrec pure_letrecProof pure_letrec_lam
  pure_letrec_lamProof pure_vars pure_exp_lemmas pure_cexp_lemmas
  pure_congruence pure_typing pure_typingProps mlmap
Libs
  BasicProvers dep_rewrite

(********************)
val _ = temp_delsimps ["nested_rows_def"]
Theorem letrec_recurse_Lams[local]:
  ∀l f e. letrec_recurse f (Lams l e) = Lams l (letrec_recurse f e)
Proof
  Induct >> rw[letrec_recurse_def, Lams_def]
QED

Theorem letrec_recurse_Apps[local]:
  ∀l f e. letrec_recurse f (Apps e l) =
    Apps (letrec_recurse f e) (MAP (letrec_recurse f) l)
Proof
  Induct >> rw[letrec_recurse_def, Apps_def]
QED

Theorem letrec_recurse_rows_of[local]:
  ∀n k l f. letrec_recurse f (rows_of n k l) =
    rows_of n (letrec_recurse f k)
            (MAP (λ(c,vs,e). (c, vs, letrec_recurse f e)) l)
Proof
  recInduct rows_of_ind >> rw[rows_of_def, letrec_recurse_def] >>
  pop_assum kall_tac >> rename1 `lets_for _ _ l _` >>
  map_every qid_spec_tac [`b`,`l`,`v`,`cn`] >>
  recInduct lets_for_ind >> rw[lets_for_def, letrec_recurse_def]
QED

Theorem patguards_letrec_recurse_gd[local]:
  ∀eps gd binds.
    patguards eps = (gd, binds) ∧
    (∀e p. MEM (e,p) eps ⇒ letrec_recurse f e = e) ⇒
    letrec_recurse f gd = gd
Proof
  recInduct patguards_ind >> REWRITE_TAC [patguards_def] >>
  rpt strip_tac
  >- gvs[letrec_recurse_def] >>
  rename [‘MEM _ (ep::eps)’] >>
  Cases_on ‘ep’ >> gvs[] >> rename [‘p = cepatUScore’]  >>
  Cases_on ‘p’ >> gvs[] >~
  [‘cepatUScore’] >- metis_tac[] >~
  [‘patguards eps = (_,_)’]
  >- (Cases_on ‘patguards eps’ >> gvs[] >> metis_tac[]) >>
  pairarg_tac >>
  gvs[letrec_recurse_def, indexedListsTheory.MEM_MAPi, PULL_EXISTS,
      DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[]
QED

Theorem letrec_recurse_FOLDR_Let[local]:
  (∀vnm e. MEM (vnm,e) binds ⇒ letrec_recurse f e = e) ⇒
  letrec_recurse f (FOLDR (λ(u,e) A. Let (explode u) e A) body binds) =
  FOLDR (λ(u,e) A. Let (explode u) e A) (letrec_recurse f body) binds
Proof
  Induct_on ‘binds’ >>
  simp[letrec_recurse_def, DISJ_IMP_THM, FORALL_AND_THM, FORALL_PROD] >>
  metis_tac[]
QED

Theorem patguards_binds_letrec_recurse_fixpoints[local]:
  ∀eps gd binds vnm e.
    patguards eps = (gd, binds) ∧
    (∀e p. MEM (e,p) eps ⇒ letrec_recurse f e = e) ∧
    MEM (vnm, e) binds ⇒
    letrec_recurse f e = e
Proof
  recInduct patguards_ind >> simp[patguards_def, FORALL_PROD] >>
  rpt strip_tac >>
  rename [‘p = cepatUScore’] >>
  Cases_on ‘p’ >> gvs[] >~
  [‘patguards eps = (_,_)’]
  >- (Cases_on ‘patguards eps’ >> gvs[] >> metis_tac[]) >~
  [‘cepatUScore’] >- metis_tac[] >>
  pairarg_tac >>
  gvs[indexedListsTheory.MEM_MAPi, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS,
      letrec_recurse_def] >> metis_tac[]
QED

Theorem letrec_recurse_nested_rows[local]:
  letrec_recurse f (nested_rows (Var v) pes) =
  nested_rows (Var v) (MAP (λ(p,e). (p, letrec_recurse f e)) pes)
Proof
  Induct_on ‘pes’ >> simp[letrec_recurse_def, nested_rows_def, FORALL_PROD] >>
  qx_genl_tac [‘e0’, ‘body’] >> pairarg_tac >>
  simp[letrec_recurse_def] >> conj_tac >~
  [‘letrec_recurse f gd = gd’]
  >- (irule patguards_letrec_recurse_gd >> first_assum $ irule_at Any >>
      simp[letrec_recurse_def]) >>
  irule letrec_recurse_FOLDR_Let >> rpt strip_tac >>
  irule patguards_binds_letrec_recurse_fixpoints >>
  rpt $ first_assum $ irule_at Any >> simp[letrec_recurse_def]
QED

Theorem letrec_recurse_exp_of:
  ∀f ce g.
  (∀c fns e. exp_of (f c fns e) =
             g (MAP (λ(v,e). (explode v,exp_of e)) fns) (exp_of e))
  ⇒ exp_of (letrec_recurse_cexp f ce) = letrec_recurse g (exp_of ce)
Proof
  recInduct letrec_recurse_cexp_ind >>
  rw[exp_of_def, letrec_recurse_cexp_def, letrec_recurse_def,
     letrec_recurse_Lams, letrec_recurse_Apps, Excl "nested_rows_def"]
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    first_x_assum drule >> rw[] >> AP_THM_TAC >> AP_TERM_TAC >>
    rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
    last_x_assum irule >> simp[] >> goal_assum drule
    )
  (* >- (first_x_assum drule >> simp[]) *)
  >- (first_x_assum $ drule_at Any >> simp[MAP_MAP_o, Cong MAP_CONG])
  >- (pop_assum
      (fn th => rpt $ first_x_assum (fn ith => mp_then Any assume_tac ith th))>>
      simp[MAP_MAP_o, combinTheory.o_DEF] >> simp[Cong MAP_CONG]) >>~-
  ([‘rows_of’],
   pop_assum
     (fn th => rpt $ first_x_assum (fn ith => mp_then Any assume_tac ith th)) >>
   simp[letrec_recurse_rows_of, MAP_MAP_o, pairTheory.o_UNCURRY_R,
        combinTheory.o_ABS_R, letrec_recurse_def] >>
   match_mp_tac (METIS_PROVE [] “x = x1 ∧ y = y1 ⇒ f x y = f x1 y1”) >>
   conj_tac >-
    (every_case_tac >> fs [letrec_recurse_def,IfDisj_def] >>
     rename [‘Disj _ xs’] >> Induct_on ‘xs’ >> fs [] >>
     fs [Disj_def,letrec_recurse_def,FORALL_PROD]) >>
   rw[MAP_EQ_f] >> pairarg_tac >> gvs [] >> res_tac >> fs []) >>~-
  ([‘nested_rows’],
   qpat_x_assum ‘∀c fns e. exp_of (f c fns e) = _’
     (fn th => rpt $ first_x_assum (fn ith => mp_then Any assume_tac ith th)) >>
   simp[letrec_recurse_nested_rows, MAP_MAP_o, o_UNCURRY_R,
        combinTheory.o_ABS_R, letrec_recurse_def] >>
   AP_TERM_TAC >> rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >> metis_tac[]) >>
  gvs[MEM_FLAT, MEM_MAP, FORALL_PROD] >> TRY pairarg_tac >> gvs[] >~
  [‘MEM x (FST (SND y))’] >- (PairCases_on ‘y’ >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem letrec_recurse_cexp_cexp_wf:
  (∀c fns e. cexp_wf (Letrec c fns e) ⇒ cexp_wf (f c fns e)) ⇒
  cexp_wf ce ⇒
  cexp_wf (letrec_recurse_cexp f ce)
Proof
  strip_tac >>
  Induct_on `ce` using freevars_cexp_ind >>
  rw[letrec_recurse_cexp_def, cexp_wf_def] >>
  gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD]
  >- (
    last_x_assum irule >> simp[cexp_wf_def] >>
    gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> metis_tac[]
    )
  >- metis_tac[]
  >- metis_tac[]
  >- (
    Cases_on `eopt` >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
    metis_tac[]
    )
  >- gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss] >>
    Cases_on `eopt` >> gvs[] >> PairCases_on `x` >> gvs[]
    )
  >- gvs[MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss]
  >- metis_tac[]
  >- gvs[MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss]
QED

Theorem letrec_recurse_cexp_NestedCase_free:
  (∀c fns e. NestedCase_free (Letrec c fns e) ⇒ NestedCase_free (f c fns e)) ⇒
  NestedCase_free ce ⇒
  NestedCase_free (letrec_recurse_cexp f ce)
Proof
  strip_tac >>
  Induct_on `ce` using freevars_cexp_ind >>
  rw[letrec_recurse_cexp_def] >> gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD]
  >- (
    last_x_assum irule >> simp[MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
    metis_tac[]
    )
  >- metis_tac[]
  >- (
    Cases_on `eopt` >> gvs[] >> rpt (pairarg_tac >> gvs[])
    )
QED


(********************)

Definition fv_set_ok_def:
  fv_set_ok e ⇔
    map_ok (get_info e) ∧ cmp_of (get_info e) = var_cmp ∧
    (∀k. lookup (get_info e) k = SOME () ⇔ k ∈ freevars_cexp e)
End

Definition fvs_ok_def:
  fvs_ok (Var c v) = fv_set_ok (Var c v) ∧
  fvs_ok (Prim c op es) = (fv_set_ok (Prim c op es) ∧ EVERY fvs_ok es) ∧
  fvs_ok (App c e es) = (fv_set_ok (App c e es) ∧ EVERY fvs_ok (e::es)) ∧
  fvs_ok (Lam c vs e) = (fv_set_ok (Lam c vs e) ∧ fvs_ok e) ∧
  fvs_ok (Let c x e1 e2) = (fv_set_ok (Let c x e1 e2) ∧ fvs_ok e1 ∧ fvs_ok e2) ∧
  fvs_ok (Letrec c fns e) =
    (fv_set_ok (Letrec c fns e) ∧ fvs_ok e ∧ EVERY (λ(f,e). fvs_ok e) fns) ∧
  fvs_ok (Case c e v css eopt) =
    (fv_set_ok (Case c e v css eopt) ∧ fvs_ok e ∧
     EVERY (λ(cn,vs,e). fvs_ok e) css ∧
     OPTION_ALL (λ(_,e). fvs_ok e) eopt) ∧
  fvs_ok (NestedCase c g gv p e pes) =
    (fv_set_ok (NestedCase c g gv p e pes) ∧
     fvs_ok g ∧ fvs_ok e ∧ EVERY (λ(p,e). fvs_ok e) pes)
Termination
  WF_REL_TAC `measure $ cexp_size (K 0)` >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> rpt strip_tac >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[list_size_def]
End

Theorem fvs_ok_imp:
  ∀e. fvs_ok e ⇒ fv_set_ok e
Proof
  Cases >> rw[fvs_ok_def]
QED

Theorem neq_some_unit[local,simp]:
  x ≠ SOME () ⇔ x = NONE
Proof
  Cases_on ‘x’ >> simp[]
QED

val drwts = [
  map_ok_list_union |> SPEC_ALL |> REWRITE_RULE[IMP_CONJ_THM],
  map_ok_list_delete |> SPEC_ALL |> REWRITE_RULE[IMP_CONJ_THM],
  union_thm |> REWRITE_RULE[IMP_CONJ_THM],
  delete_thm |> REWRITE_RULE[IMP_CONJ_THM],
  insert_thm |> REWRITE_RULE[IMP_CONJ_THM],
  lookup_insert, lookup_union, lookup_delete,
  lookup_list_delete, lookup_list_union_var_set
  ];

Theorem fvs_ok_letrec_recurse_fvs:
  ∀f ce.
  (∀c fns e. fvs_ok (Letrec c fns e) ⇒ fvs_ok (f c fns e))
  ⇒ fvs_ok (letrec_recurse_fvs f ce)
Proof
  recInduct letrec_recurse_fvs_ind >> rw[letrec_recurse_fvs_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP, EVERY_MEM]
  >- (
    simp[LAMBDA_PROD, GSYM FST_THM] >>
    first_x_assum irule >> simp[fvs_ok_def, EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
    reverse conj_tac >- (rw[] >> res_tac) >> rw[fv_set_ok_def, get_info_def] >>
    DEP_REWRITE_TAC drwts >> csimp[EVERY_MAP, EVERY_MEM, FORALL_PROD]
    >- metis_tac[fvs_ok_imp, fv_set_ok_def]
    >- metis_tac[fvs_ok_imp, fv_set_ok_def] >>
    conj_tac >- metis_tac[fvs_ok_imp, fv_set_ok_def] >>
    simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    eq_tac >> rw[] >> gvs[] >>
    metis_tac[fvs_ok_imp, fv_set_ok_def]
    )
  >- (
    imp_res_tac fvs_ok_imp >> gvs[fv_set_ok_def] >>
    rw[fvs_ok_def, fv_set_ok_def, get_info_def] >>
    DEP_REWRITE_TAC drwts >> simp[] >> eq_tac >> rw[]
    )
  >- (
    imp_res_tac fvs_ok_imp >> gvs[fv_set_ok_def] >>
    rw[fvs_ok_def, fv_set_ok_def, get_info_def, EVERY_MAP, EVERY_MEM] >>
    DEP_REWRITE_TAC drwts >> simp[EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
    simp[MEM_MAP, PULL_EXISTS] >> metis_tac[fvs_ok_imp, fv_set_ok_def]
    )
  >- (
    imp_res_tac fvs_ok_imp >> gvs[fv_set_ok_def] >>
    rw[fvs_ok_def, fv_set_ok_def, get_info_def, EVERY_MAP, EVERY_MEM] >>
    DEP_REWRITE_TAC drwts >> simp[EVERY_MAP, EVERY_MEM] >>
    simp[MEM_MAP, PULL_EXISTS] >> metis_tac[fvs_ok_imp, fv_set_ok_def]
    )
  >- (
    rw[fvs_ok_def, fv_set_ok_def, get_info_def] >>
    DEP_REWRITE_TAC drwts >> simp[] >> eq_tac >> rw[]
    )
  >- (
    imp_res_tac fvs_ok_imp >> gvs[fv_set_ok_def] >>
    rw[fvs_ok_def, fv_set_ok_def, get_info_def] >>
    DEP_REWRITE_TAC drwts >> simp[] >>
    IF_CASES_TAC >> simp[] >>
    CASE_TAC >> gvs[] >> last_x_assum $ qspec_then `k` assume_tac >> gvs[]
    )
  >- (
    simp[LAMBDA_PROD] >>
    imp_res_tac fvs_ok_imp >> gvs[fv_set_ok_def] >>
    csimp[fvs_ok_def, fv_set_ok_def, get_info_def, EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
    reverse $ conj_tac
    >- (Cases_on ‘eopt’ >> TRY $ Cases_on ‘x’ >> gvs[] >> rw[] >> res_tac) >> rw[] >>
    DEP_REWRITE_TAC drwts >> csimp[EVERY_MAP, EVERY_MEM, FORALL_PROD]
    >- (Cases_on ‘eopt’ >> TRY $ Cases_on ‘x’ >> gvs[] >>
        rw[] >> DEP_REWRITE_TAC drwts >> simp[EVERY_MAP, EVERY_MEM, FORALL_PROD]
        >- metis_tac[fvs_ok_imp, fv_set_ok_def]
        >- metis_tac[fvs_ok_imp, fv_set_ok_def] >>
        rw[] >> DEP_REWRITE_TAC drwts >>
        simp[EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
        metis_tac[fvs_ok_imp, fv_set_ok_def]
      )
    >- (
      Cases_on ‘eopt’ >> TRY $ Cases_on ‘x’ >> gvs[] >>
      rw[] >> DEP_REWRITE_TAC drwts >> simp[EVERY_MAP, EVERY_MEM, FORALL_PROD]
      >- metis_tac[fvs_ok_imp, fv_set_ok_def]
      >- metis_tac[fvs_ok_imp, fv_set_ok_def] >>
      rw[] >> DEP_REWRITE_TAC drwts >>
      simp[EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
      metis_tac[fvs_ok_imp, fv_set_ok_def]
      ) >>
    conj_tac
    >- (
      Cases_on ‘eopt’ >> TRY $ Cases_on ‘x’ >> gvs[] >>
      reverse $ rw[] >>
      DEP_REWRITE_TAC drwts >> simp[EVERY_MAP, EVERY_MEM, FORALL_PROD]
      >- metis_tac[fvs_ok_imp, fv_set_ok_def]
      >- metis_tac[fvs_ok_imp, fv_set_ok_def] >>
      rw[] >> DEP_REWRITE_TAC drwts >> simp[EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
      metis_tac[fvs_ok_imp, fv_set_ok_def]
      ) >>
    Cases_on ‘eopt’ >> TRY $ Cases_on ‘x’ >> gvs[] >>
    simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    IF_CASES_TAC >> gvs[AllCaseEqs()] >> dsimp[] >>
    first_x_assum $ qspec_then `k` assume_tac >> gvs[] >>
    Cases_on ‘k ∈ freevars_cexp (letrec_recurse_fvs f e)’ >> gs[] >>
    eq_tac >> rw[]
    >- (pop_assum mp_tac >> DEP_REWRITE_TAC drwts >>
        simp[AllCaseEqs()] >> metis_tac[fvs_ok_imp, fv_set_ok_def])
    >- (goal_assum drule >> DEP_REWRITE_TAC drwts >> simp[] >>
        metis_tac[fvs_ok_imp, fv_set_ok_def])
    >- metis_tac[fvs_ok_imp, fv_set_ok_def]
    >- (pop_assum mp_tac >> DEP_REWRITE_TAC drwts >>
        simp[AllCaseEqs()] >> metis_tac[fvs_ok_imp, fv_set_ok_def])
    >- (disj2_tac >> goal_assum drule >> DEP_REWRITE_TAC drwts >> simp[] >>
        metis_tac[fvs_ok_imp, fv_set_ok_def])
    >- metis_tac[fvs_ok_imp, fv_set_ok_def]
    )
  >- (simp[fvs_ok_def, fv_set_ok_def, get_info_def, EVERY_MAP, LAMBDA_PROD,
           MEM_MAP, GSYM PEXISTS_THM, PULL_EXISTS, EVERY_MEM,
           GSYM PFORALL_THM] >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      rw[] >> DEP_REWRITE_TAC drwts
      >- (drule_then strip_assume_tac fvs_ok_imp >>
          last_x_assum (C (resolve_then Any strip_assume_tac) fvs_ok_imp) >>
          gvs[fv_set_ok_def, EVERY_MEM, PULL_EXISTS, MEM_MAP, FORALL_PROD] >>
          rw[] >> DEP_REWRITE_TAC drwts
          >- metis_tac[fv_set_ok_def, fvs_ok_imp]
          >- metis_tac[fv_set_ok_def, fvs_ok_imp]
          >- metis_tac[]
          >- metis_tac[] >>
          simp[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
          rw[] >> DEP_REWRITE_TAC drwts >> metis_tac[fv_set_ok_def, fvs_ok_imp])
      >- (drule_then strip_assume_tac fvs_ok_imp >>
          last_x_assum (C (resolve_then Any strip_assume_tac) fvs_ok_imp) >>
          gvs[fv_set_ok_def, EVERY_MEM, PULL_EXISTS, MEM_MAP, FORALL_PROD] >>
          rw[] >> DEP_REWRITE_TAC drwts >~
          [‘EVERY’]
          >- (simp[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
              rw[] >> DEP_REWRITE_TAC drwts >>
              metis_tac[fv_set_ok_def, fvs_ok_imp]) >>
          metis_tac[fv_set_ok_def, fvs_ok_imp]) >>
      drule_then strip_assume_tac fvs_ok_imp >>
      rev_drule_then strip_assume_tac fvs_ok_imp >>
      last_x_assum (C (resolve_then Any strip_assume_tac) fvs_ok_imp) >>
      rw[AllCaseEqs()] >>
      gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD, fv_set_ok_def,
          EXISTS_PROD] >>
      rw[] >> DEP_REWRITE_TAC drwts >>
      gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD, fv_set_ok_def] >>
      rw[] >> DEP_REWRITE_TAC drwts >> simp[] >>
      TRY (first_x_assum $ drule_then strip_assume_tac >> simp[] >> NO_TAC) >>
      eq_tac >> rpt strip_tac >>
      TRY (rename [‘MEM (pat, exp) pes’] >>
           first_x_assum $ drule_then strip_assume_tac >> simp[]) >>
      gvs[lookup_list_delete]
      >- metis_tac[cepat_vars_l_correct]
      >- metis_tac[cepat_vars_l_correct] >>
      dsimp[lookup_list_delete] >>
      qmatch_abbrev_tac ‘_ ∨ k ∈ freevars_cexp (letrec_recurse_fvs f ee)’ >>
      qmatch_abbrev_tac ‘_ ∨ P’ >> Cases_on ‘P’ >> simp[] >>
      gvs[markerTheory.Abbrev_def] >>
      first_x_assum (pop_assum o mp_then Concl mp_tac o iffLR) >>
      simp[cepat_vars_l_correct] >>
      strip_tac >> disj2_tac >> first_assum $ irule_at Any >>
      simp[lookup_list_delete, cepat_vars_l_correct])
QED

Theorem letrec_recurse_IfDisj[local]:
  letrec_recurse g (IfDisj n p1 x) =
  IfDisj n p1 (letrec_recurse g x)
Proof
  fs [IfDisj_def,letrec_recurse_def]
  \\ rename [‘Disj _ xs’]
  \\ Induct_on ‘xs’ \\ fs [FORALL_PROD,Disj_def,letrec_recurse_def]
QED

Theorem letrec_recurse_fvs_exp_of:
  ∀f ce g.
    (∀c fns e.
       fvs_ok (Letrec c fns e) ⇒
       fvs_ok (f c fns e) ∧
       exp_of (f c fns e) =
       g (MAP (λ(v,e). (explode v,exp_of e)) fns) (exp_of e))
    ⇒
    exp_of (letrec_recurse_fvs f ce) = letrec_recurse g (exp_of ce)
Proof
  recInduct letrec_recurse_cexp_ind >>
  rw[exp_of_def, letrec_recurse_fvs_def, letrec_recurse_def]
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
    first_x_assum drule >> strip_tac >> simp[] >> rw[] >>
    last_x_assum $ drule_at Any >> strip_tac >>
    rgs[IMP_CONJ_THM, FORALL_AND_THM] >>
    last_x_assum $ DEP_REWRITE_TAC o single >> rw[]
    >- (
      simp[fvs_ok_def, EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
      reverse $ conj_asm2_tac >> gvs[]
      >- (rw[] >> irule_at Any fvs_ok_letrec_recurse_fvs >> simp[]) >>
      simp[fv_set_ok_def, get_info_def, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
      rw[] >> DEP_REWRITE_TAC drwts >> simp[EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
      simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
      metis_tac[fvs_ok_imp, fv_set_ok_def]
      ) >>
    AP_THM_TAC >> AP_TERM_TAC >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
    last_x_assum irule >> simp[] >> goal_assum drule
    )
  >- (rw[letrec_recurse_Lams] >> AP_TERM_TAC >> first_x_assum irule >> simp[])
  >- (simp[MAP_MAP_o, combinTheory.o_DEF] >> rw[MAP_EQ_f])
  >- (
    rw[letrec_recurse_Apps] >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
    first_x_assum drule >> rw[] >> AP_TERM_TAC >> rw[MAP_EQ_f]
    ) >>
  pop_assum (fn th => rpt $ first_x_assum $ C (mp_then Any assume_tac) th) >>
  gs [MEM_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, DISJ_EQ_IMP] >>
  rw[letrec_recurse_rows_of, letrec_recurse_nested_rows] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
  >~ [‘nested_rows’] >-
   (AP_TERM_TAC >> fs [] >>
    rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
    last_x_assum irule >> simp[] >> goal_assum drule) >>
  match_mp_tac $ METIS_PROVE [] “x = x1 ∧ y = y1 ⇒ f y x = f y1 x1” >>
  rpt strip_tac >>
  TRY (rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
       last_x_assum irule >> simp[] >> goal_assum drule \\ NO_TAC) >>
  Cases_on ‘eopt’ >> fs [letrec_recurse_def] >>
  pairarg_tac >> gvs [letrec_recurse_IfDisj]
QED

Theorem letrec_recurse_fvs_cexp_wf:
  (∀c fns e. cexp_wf (Letrec c fns e) ⇒ cexp_wf (f c fns e)) ⇒
  cexp_wf ce ⇒
  cexp_wf (letrec_recurse_fvs f ce)
Proof
  strip_tac >>
  Induct_on `ce` using freevars_cexp_ind >>
  rw[letrec_recurse_fvs_def, cexp_wf_def] >>
  gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD]
  >- (
    last_x_assum irule >> simp[cexp_wf_def] >>
    gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> metis_tac[]
    )
  >- metis_tac[]
  >- metis_tac[]
  >- (
    Cases_on `eopt` >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
    metis_tac[]
    )
  >- gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss] >>
    Cases_on `eopt` >> gvs[] >> PairCases_on `x` >> gvs[]
    )
  >- gvs[MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss]
  >- metis_tac[]
  >- gvs[MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss]
QED

Theorem letrec_recurse_fvs_NestedCase_free:
  (∀c fns e. NestedCase_free (Letrec c fns e) ⇒ NestedCase_free (f c fns e)) ⇒
  NestedCase_free ce ⇒
  NestedCase_free (letrec_recurse_fvs f ce)
Proof
  strip_tac >>
  Induct_on `ce` using freevars_cexp_ind >>
  rw[letrec_recurse_fvs_def] >>
  gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD]
  >- (
    last_x_assum irule >> simp[MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
    metis_tac[]
    )
  >- metis_tac[]
  >- (
    Cases_on `eopt` >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
    CASE_TAC >> gvs[]
    )
QED


(********** Distinctness **********)

Theorem distinct_cexp_correct:
  ∀ce. exp_of (distinct_cexp ce) = distinct (exp_of ce)
Proof
  rw[distinct_cexp_def, distinct_def] >>
  irule letrec_recurse_exp_of >> simp[exp_of_def] >>
  Induct >> simp[make_distinct_def, FORALL_PROD, MEM_MAP, EXISTS_PROD] >>
  rw[]
QED

Theorem distinct_cexp_exp_eq:
  ∀ce. exp_of ce ≅ exp_of (distinct_cexp ce)
Proof
  rw[distinct_cexp_correct, distinct_exp_eq]
QED

Theorem distinct_cexp_cexp_wf:
  ∀ce. cexp_wf ce ⇒ cexp_wf (distinct_cexp ce)
Proof
  rw[distinct_cexp_def] >> irule letrec_recurse_cexp_cexp_wf >>
  rw[] >> gvs[cexp_wf_def] >> rw[]
  >- (
    pop_assum kall_tac >> Induct_on `fns` >> rw[make_distinct_def] >>
    PairCases_on `h` >> rw[make_distinct_def] >> gvs[]
    )
  >- (
    Induct_on `fns` >> rw[make_distinct_def] >>
    PairCases_on `h` >> rw[make_distinct_def] >>
    Cases_on `fns` >> gvs[]
    )
QED

Theorem distinct_cexp_NestedCase_free:
  ∀ce. NestedCase_free ce ⇒ NestedCase_free (distinct_cexp ce)
Proof
  rw[distinct_cexp_def] >> irule letrec_recurse_cexp_NestedCase_free >> rw[] >>
  Induct_on `fns` >> rw[make_distinct_def] >>
  PairCases_on `h` >> rw[make_distinct_def] >> gvs[]
QED

Theorem distinct_cexp_freevars:
  ∀ce. freevars_cexp (distinct_cexp ce) ⊆ freevars_cexp ce
Proof
  gen_tac >> qspec_then `exp_of ce` mp_tac freevars_distinct >>
  simp[GSYM distinct_cexp_correct, freevars_exp_of] >>
  gvs[SUBSET_DEF, PULL_EXISTS]
QED


(********** Splitting **********)

Theorem exp_of_make_Letrecs_cexp[local]:
  ∀fns.
    exp_of (make_Letrecs_cexp fns e) =
      make_Letrecs (MAP (MAP (λ(fn,e). (explode fn,exp_of e))) fns) (exp_of e)
Proof
  Induct >> rw[make_Letrecs_def, make_Letrecs_cexp_def, exp_of_def]
QED

Theorem fvs_ok_make_Letrecs_cexp:
  ∀fns e.
    EVERY (EVERY (fvs_ok o SND)) fns ∧ fvs_ok e
  ⇒ fvs_ok (make_Letrecs_cexp fns e)
Proof
  Induct >> rw[make_Letrecs_cexp_def] >> gvs[] >>
  reverse $ rw[fvs_ok_def]
  >- (gvs[combinTheory.o_DEF, SND_THM, LAMBDA_PROD]) >>
  res_tac >> imp_res_tac fvs_ok_imp >> gvs[fv_set_ok_def] >>
  rw[get_info_def] >> DEP_REWRITE_TAC drwts >>
  gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
  rpt conj_tac >> metis_tac[fvs_ok_imp, fv_set_ok_def]
QED

(* TODO move some theorems to HOL *)
Theorem to_nums_correct:
  ∀xs b. domain (to_nums b xs) = {c | ∃d. MEM d xs ∧ ALOOKUP b d = SOME c}
Proof
  Induct >> rw[to_nums_def] >> CASE_TAC >> gvs[EXTENSION] >>
  rw[] >> eq_tac >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem wf_to_nums[simp]:
  ∀ns l. wf (to_nums l ns)
Proof
  Induct >> rw[to_nums_def] >>
  CASE_TAC >> gvs[wf_insert]
QED

Theorem to_nums_set_eq[local]:
  set l1 = set l2 ⇒ to_nums l l1 = to_nums l l2
Proof
  rw[] >> irule $ iffRL spt_eq_thm >> simp[] >>
  qspecl_then [`l1`,`l`] assume_tac to_nums_correct >>
  qspecl_then [`l2`,`l`] assume_tac to_nums_correct >>
  gvs[EXTENSION, domain_lookup] >> rw[] >>
  reverse $ Cases_on `lookup n (to_nums l l1)` >> gvs[]
  >- (goal_assum drule >> simp[]) >>
  Cases_on `lookup n (to_nums l l2)` >> gvs[] >> res_tac >> fs[]
QED

Theorem top_sort_set_eq[local]:
  ∀l1 l2.
    MAP FST l1 = MAP FST l2 ∧
    LIST_REL (λa b. set a = set b) (MAP SND l1) (MAP SND l2)
  ⇒ top_sort_any l1 = top_sort_any l2
Proof
  rw[top_sort_any_def]
  >- (Cases_on `l1` >> gvs[])
  >- (Cases_on `l2` >> gvs[]) >>
  AP_TERM_TAC >> AP_TERM_TAC >>
  imp_res_tac LIST_REL_LENGTH >> gvs[] >>
  irule $ iffLR MAPi_EQ_l >> rw[] >>
  qmatch_goalsub_abbrev_tac `_ a = _ b` >>
  PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
  irule to_nums_set_eq >> gvs[LIST_REL_EL_EQN, EL_MAP] >>
  first_x_assum drule >> simp[]
QED

Theorem top_sort_aux_sets[local]:
  ∀ns reach acc. ∃res.
    top_sort_aux ns reach acc = res ++ acc ∧
    set (FLAT res) = set ns
Proof
  recInduct top_sort_aux_ind >> rw[top_sort_aux_def] >>
  qpat_abbrev_tac `parts = partition _ _ _ _` >>
  PairCases_on `parts` >> gvs[] >>
  drule partition_thm >> strip_tac >> gvs[] >>
  gvs[EXTENSION] >> metis_tac[]
QED

Theorem top_sort_sets[local]:
  ∀l. set (FLAT (top_sort l)) = set (MAP FST l)
Proof
  rw[top_sort_def] >>
  qmatch_goalsub_abbrev_tac `top_sort_aux ns reach acc` >>
  qspecl_then [`ns`,`reach`,`acc`] assume_tac top_sort_aux_sets >>
  unabbrev_all_tac >> gvs[]
QED

Theorem top_sort_any_sets:
  ∀l. set (FLAT (top_sort_any l)) = set (MAP FST l)
Proof
  gen_tac >> once_rewrite_tac[top_sort_any_def] >> LET_ELIM_TAC >>
  IF_CASES_TAC >- gvs[NULL_EQ] >>
  simp[GSYM MAP_FLAT, LIST_TO_SET_MAP, Abbr `nesting`] >>
  simp[top_sort_sets, combinTheory.o_DEF, LAMBDA_PROD] >>
  rw[EXTENSION, indexedListsTheory.MEM_MAPi, PULL_EXISTS, UNCURRY] >>
  simp[Abbr `from_num`, lookup_fromAList] >>
  `∀l k. ALOOKUP (MAPi (λi n. (i,n)) l) k =
      if k < LENGTH l then SOME (EL k l) else NONE` by (
      Induct using SNOC_INDUCT >> gvs[SNOC_APPEND] >>
      gvs[ALOOKUP_APPEND, EL_APPEND_EQN, indexedListsTheory.MAPi_APPEND] >> rw[]) >>
  rw[Abbr `names`] >> csimp[EL_MAP] >>
  simp[MEM_MAP, MEM_EL, PULL_EXISTS]
QED

Theorem MAPi_MAP:
  ∀f g. MAPi f (MAP g l) = MAPi (flip ($o $o f) g) l
Proof
  Induct_on ‘l’ >> simp[combinTheory.o_DEF, combinTheory.C_DEF]
QED

Theorem ALOOKUP_MAPi_inj0[local]:
  (∀x y. f x = f y ⇔ x = y) ⇒
  ALOOKUP (MAPi (λi (x,y). (f x, i + c)) l) (f e) =
  ALOOKUP (MAPi (λi (x,y). (x, i + c)) l) e
Proof
  strip_tac >> qid_spec_tac ‘c’ >>
  Induct_on ‘l’ >>
  simp[FORALL_PROD, combinTheory.o_DEF, arithmeticTheory.ADD1] >>
  rw[] >> ONCE_REWRITE_TAC [DECIDE “x + (y + 1) = y + (x + 1n)”] >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem ALOOKUP_MAPi_inj = ALOOKUP_MAPi_inj0 |> Q.INST [‘c’ |-> ‘0’] |> SRULE[]

Theorem to_nums_MAP2:
  (∀x y. f x = f y ⇔ x = y) ⇒
  to_nums (MAPi (λi (x,y). (f x, i)) l) (MAP f v) =
  to_nums (MAPi (λi (x,y). (x, i)) l) v
Proof
  strip_tac >> Induct_on ‘v’ >> simp[to_nums_def] >> qx_gen_tac ‘h’ >>
  irule combeq3 >> simp[ALOOKUP_MAPi_inj]
QED

Theorem MAPi_SNOC:
  MAPi f (SNOC h t) = SNOC (f (LENGTH t) h) (MAPi f t)
Proof
  simp[indexedListsTheory.MAPi_APPEND, SNOC_APPEND]
QED

Theorem ALOOKUP_MAPi:
  ∀n. ALOOKUP (MAPi (λi (x,y). (i, f i x y)) l) n =
      if n < LENGTH l then SOME (f n (FST (EL n l)) (SND (EL n l)))
      else NONE
Proof
  Induct_on ‘l’ using SNOC_INDUCT >>
  simp[arithmeticTheory.LT_SUC, FORALL_PROD, MAPi_SNOC] >>
  simp[SNOC_APPEND, ALOOKUP_APPEND] >> rw[] >>
  gvs[EL_APPEND_EQN] >>
  Cases_on ‘l’ >> gvs[] >> Cases_on ‘n’ >> gvs[]
QED

Theorem top_sort_through_inj:
  (∀x y. f x = f y ⇔ x = y) ⇒
  top_sort_any (MAP (f ## MAP f) l) = MAP (MAP f) (top_sort_any l)
Proof
  strip_tac >>
  simp[top_sort_any_def] >> Cases_on ‘l = []’ >> simp[] >>
  simp[NULL_EQ, MAP_MAP_o, MAPi_MAP, combinTheory.o_ABS_R] >>
  simp[combinTheory.o_DEF, combinTheory.C_DEF] >>
  simp[ELIM_UNCURRY, MAP_MAP_o, combinTheory.o_ABS_R] >>
  simp[LAMBDA_PROD] >> simp[to_nums_MAP2] >>
  rw[MAP_EQ_f] >>
  simp[lookup_fromAList, ALOOKUP_MAPi] >> rw[] >>
  Cases_on ‘l’ >> gvs[] >> Cases_on ‘h’ >> simp[]
QED

Theorem ALOOKUP_MAP_injected_keys:
  (∀x y. f x = f y ⇔ x = y) ⇒
  ALOOKUP (MAP (λ(k,v). (f k, g v)) inputs) (f x) =
  OPTION_MAP g (ALOOKUP inputs x)
Proof
  strip_tac >> Induct_on ‘inputs’ >> simp[FORALL_PROD] >> rw[]
QED

Theorem split_all_cexp_correct:
  ∀ce. exp_of (split_all_cexp ce) = split_all (exp_of ce)
Proof
  rw[split_all_cexp_def, split_all_def] >>
  irule letrec_recurse_fvs_exp_of >>
  simp[exp_of_def, exp_of_make_Letrecs_cexp] >> rw[]
  >- (
    irule fvs_ok_make_Letrecs_cexp >> gvs[fvs_ok_def] >>
    gvs[EVERY_MEM, SND_THM, FORALL_PROD] >> rw[] >>
    gvs[split_one_cexp_def, MEM_MAP] >>
    qmatch_asmsub_abbrev_tac `MEM _ (top_sort_any ll)` >>
    qspec_then `ll` assume_tac top_sort_any_sets >>
    gvs[EXTENSION] >> pop_assum $ assume_tac o iffLR >>
    gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    pop_assum $ drule_all >> rw[] >>
    unabbrev_all_tac >> gvs[MEM_MAP, EXISTS_PROD] >> rename1 `MEM (a,b) fns` >>
    Cases_on `ALOOKUP fns a` >> gvs[ALOOKUP_NONE, MEM_MAP] >>
    imp_res_tac ALOOKUP_MEM >> res_tac
    ) >>
  rw[] >> AP_THM_TAC >> AP_TERM_TAC >>
  rw[split_one_def, split_one_cexp_def] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  ‘top_sort_any (MAP (λ(p1,p2). (explode p1, freevars_l (exp_of p2))) fns) =
   top_sort_any (MAP (explode ## MAP explode) (MAP (I ## freevars_cexp_l) fns))’
    by (irule top_sort_set_eq >>
        simp[MAP_MAP_o, pairTheory.o_UNCURRY_R, combinTheory.o_ABS_R] >>
        simp[combinTheory.o_DEF, ELIM_UNCURRY] >>
        simp[LIST_REL_EL_EQN, GSYM freevars_cexp_equiv, EL_MAP, LIST_TO_SET_MAP,
             GSYM freevars_equiv, freevars_exp_of]) >>
  simp[top_sort_through_inj] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, ALOOKUP_MAP_injected_keys] >>
  ‘top_sort_any (MAP (λ(fn,e). (fn, MAP FST (toAscList (get_info e)))) fns) =
   top_sort_any (MAP (I ## freevars_cexp_l) fns)’
    by (irule top_sort_set_eq >>
        simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        simp[ELIM_UNCURRY, SF ETA_ss] >>
        simp[LIST_REL_EL_EQN, EL_MAP, LIST_TO_SET_MAP] >>
        gvs[fvs_ok_def, EVERY_MEM, MEM_EL, PULL_EXISTS, ELIM_UNCURRY] >>
        rpt strip_tac >> rename [‘n < LENGTH fns’] >>
        ‘fvs_ok (SND (EL n fns))’ by simp[] >>
        drule fvs_ok_imp >> simp[fv_set_ok_def, GSYM freevars_cexp_equiv] >>
        simp[GSYM LIST_TO_SET_MAP, GSYM MAP_FST_toAscList] >>
        strip_tac >> simp[EXTENSION] >>
        simp[miscTheory.FDOM_FLOOKUP, GSYM lookup_thm]) >>
  simp[] >>
  rw[MAP_EQ_f] >>
  rename [‘MEM component (top_sort_any _)’, ‘MEM e component’] >>
  ‘∃res. ALOOKUP fns e = SOME res’ suffices_by simp[PULL_EXISTS]>>
  ‘MEM e (FLAT (top_sort_any (MAP (I ## freevars_cexp_l) fns)))’
    by (simp[MEM_FLAT] >> metis_tac[]) >>
  gs[top_sort_any_sets, MEM_MAP, EXISTS_PROD, miscTheory.ALOOKUP_EXISTS_IFF,
     SF SFY_ss]
QED

Theorem split_all_cexp_exp_eq:
  ∀ce. letrecs_distinct (exp_of ce) ⇒
    exp_of ce ≅ exp_of (split_all_cexp ce)
Proof
  rw[split_all_cexp_correct, split_all_correct]
QED

Theorem cexp_wf_make_Letrecs_cexp:
  cexp_wf (make_Letrecs_cexp l e) ⇔
    EVERY ($<> []) l ∧
    EVERY (EVERY (cexp_wf o SND)) l ∧
    cexp_wf e
Proof
  Induct_on `l` >> rw[make_Letrecs_cexp_def, cexp_wf_def] >>
  eq_tac >> rw[] >>
  gvs[EVERY_MAP, combinTheory.o_DEF]
QED

Theorem top_sort_aux_non_null:
  ∀l r acc.
  l ≠ [] ∧ ¬MEM [] acc ⇒
  ¬MEM [] (top_sort_aux l r acc)
Proof
  recInduct top_sort_aux_ind >> rw[top_sort_aux_def] >>
  pairarg_tac >> gvs[] >>
  Cases_on `xs` >> gvs[top_sort_aux_def] >>
  Cases_on `zs` >> gvs[top_sort_aux_def]
QED

Theorem top_sort_non_null:
  l ≠ [] ⇒ ¬MEM [] (top_sort l)
Proof
  rw[top_sort_def] >>
  qspec_then `MAP FST l` mp_tac top_sort_aux_non_null >> simp[]
QED

Theorem split_one_sets:
  set (FLAT (split_one_cexp fns)) ⊆ set fns
Proof
  rw[split_one_cexp_def, SUBSET_DEF] >> gvs[MEM_FLAT, MEM_MAP] >>
  qmatch_asmsub_abbrev_tac `top_sort_any ll` >>
  qspec_then `ll` mp_tac top_sort_any_sets >>
  `MAP FST ll = MAP FST fns` by (
    unabbrev_all_tac >> simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]) >>
  rw[] >> gvs[EXTENSION, EQ_IMP_THM, FORALL_AND_THM] >>
  gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  first_x_assum drule >> disch_then drule >> rw[] >>
  PairCases_on `y` >> gvs[] >>
  Cases_on `ALOOKUP fns y0` >> gvs[ALOOKUP_NONE, MEM_MAP] >>
  imp_res_tac ALOOKUP_MEM
QED

Theorem split_all_cexp_cexp_wf:
  ∀ce. cexp_wf ce ⇒ cexp_wf (split_all_cexp ce)
Proof
  rw[split_all_cexp_def] >> irule letrec_recurse_fvs_cexp_wf >>
  rw[] >> gvs[cexp_wf_def] >> rw[cexp_wf_make_Letrecs_cexp]
  >- (
    rw[split_one_cexp_def] >>
    simp[EVERY_MAP, top_sort_any_def, NULL_EQ] >>
    simp[EVERY_MEM] >> irule top_sort_non_null >>
    Cases_on `fns` >> gvs[]
    )
  >- (
    simp[GSYM EVERY_FLAT] >> rw[EVERY_MEM] >>
    drule $ SRULE [SUBSET_DEF] split_one_sets >>
    gvs[EVERY_MAP, EVERY_MEM]
    )
QED

Theorem NestedCase_free_make_Letrecs_cexp:
  NestedCase_free (make_Letrecs_cexp l e) ⇔
    EVERY (NestedCase_free o SND) (FLAT l) ∧ NestedCase_free e
Proof
  Induct_on `l` >> rw[make_Letrecs_cexp_def, SF ETA_ss] >>
  eq_tac >> rw[] >>
  gvs[EVERY_MAP, combinTheory.o_DEF]
QED

Theorem split_all_cexp_NestedCase_free:
  ∀ce. NestedCase_free ce ⇒ NestedCase_free (split_all_cexp ce)
Proof
  rw[split_all_cexp_def] >> irule letrec_recurse_fvs_NestedCase_free >>
  rw[NestedCase_free_make_Letrecs_cexp] >>
  gvs[EVERY_MEM, EVERY_MAP] >> rw[] >>
  drule $ SRULE [SUBSET_DEF] split_one_sets >> gvs[]
QED

Theorem split_all_cexp_freevars:
  ∀ce. letrecs_distinct (exp_of ce) ⇒
    freevars_cexp (split_all_cexp ce) = freevars_cexp ce
Proof
  rw[] >> qspec_then `exp_of ce` mp_tac split_all_freevars >>
  simp[GSYM split_all_cexp_correct, freevars_exp_of] >>
  gvs[EXTENSION, PULL_EXISTS, EQ_IMP_THM]
QED


(********** Cleaning up **********)

Theorem clean_one_fvs_ok:
  ∀c fns e. fvs_ok (Letrec c fns e) ⇒ fvs_ok (clean_one_cexp c fns e)
Proof
  rw[] >> gvs[fvs_ok_def] >> rw[clean_one_cexp_def] >>
  EVERY_CASE_TAC >> gvs[fvs_ok_def] >>
  imp_res_tac fvs_ok_imp >> gvs[fv_set_ok_def, get_info_def] >>
  rw[] >> eq_tac >> rw[] >> gvs[] >>
  CCONTR_TAC >> gvs[] >>
  qpat_x_assum `∀k. _ ⇔ k ∈ _ r` $ qspec_then `k` assume_tac >> gvs[]
QED

Theorem clean_all_cexp_correct:
  ∀ce. exp_of (clean_all_cexp ce) = clean_all (exp_of ce)
Proof
  rw[clean_all_cexp_def, clean_all_def] >>
  irule letrec_recurse_fvs_exp_of >>
  rpt gen_tac >> strip_tac >> rw[]
  >- gvs[clean_one_fvs_ok] >>
  rw[clean_one_def, clean_one_cexp_def, exp_of_def] >> gvs[]
  >- (irule FALSITY >>
      gvs[DISJOINT_ALT, MAP_MAP_o, combinTheory.o_DEF,
          LAMBDA_PROD, GSYM FST_THM, fvs_ok_def] >>
      imp_res_tac fvs_ok_imp >> gvs[fv_set_ok_def] >>
      gvs[MEM_MAP, PULL_EXISTS, EXISTS_PROD, get_info_def] >>
      gvs[EVERY_MAP, EVERY_MEM] >>
      first_x_assum drule >> simp[] >>
      rename [‘lookup (get_info e) x ≠ NONE’] >>
      first_x_assum $ qspec_then `x` assume_tac >> gvs[freevars_exp_of])
  >- (irule FALSITY >>
      gvs[DISJOINT_ALT, MAP_MAP_o, combinTheory.o_DEF, MEM_MAP, PULL_EXISTS,
          fvs_ok_def, EXISTS_MEM, FORALL_PROD, EXISTS_PROD] >>
      pop_assum drule >> simp[] >>
      imp_res_tac fvs_ok_imp >> gvs[fv_set_ok_def, freevars_exp_of] >>
      first_x_assum $ irule o iffLR >>
      rename [‘lookup (get_info e1) e2 = SOME ()’] >>
      Cases_on `lookup (get_info e1) e2` >> gvs[]) >>
  Cases_on `fns` >- gvs[] >>
  simp[] >> PairCases_on `h` >> simp[] >> ntac 2 $ pop_assum kall_tac >>
  reverse $ Cases_on `t` >> rgs[exp_of_def, fvs_ok_def] >>
  imp_res_tac fvs_ok_imp >> pop_assum mp_tac >> simp[fv_set_ok_def] >>
  strip_tac >>
  Cases_on `lookup (get_info h1) h0` >> rgs[freevars_exp_of, exp_of_def] >>
  simp[AllCaseEqs()] >> strip_tac >>
  first_x_assum (drule o iffRL) >> simp[]
QED

Theorem clean_all_cexp_exp_eq:
  ∀ce. exp_of ce ≅ exp_of (clean_all_cexp ce)
Proof
  rw[clean_all_cexp_correct, clean_all_correct]
QED

Theorem clean_all_preserves_typing:
  ∀ns ce db st env t.
    type_tcexp ns db st env (tcexp_of ce) t
  ⇒ type_tcexp ns db st env (tcexp_of (clean_all_cexp ce)) t
Proof
  strip_tac >> recInduct freevars_cexp_ind >> rpt conj_tac >>
  simp[clean_all_cexp_def, letrec_recurse_fvs_def, pure_tcexpTheory.tcexp_of_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF] >> rpt gen_tac >> strip_tac >> rpt gen_tac
  >- (
    once_rewrite_tac[type_tcexp_cases] >> rw[]
    >>~- ([`LIST_REL`], gvs[LIST_REL_EL_EQN, MEM_EL, EL_MAP] >> metis_tac[]) >>
    gvs[MAP_EQ_CONS] >> metis_tac[]
    )
  >- (
    once_rewrite_tac[type_tcexp_cases] >> rw[] >>
    rpt $ first_x_assum $ irule_at Any >>
    gvs[LIST_REL_EL_EQN, MEM_EL, EL_MAP] >> metis_tac[]
    )
  >- (
    once_rewrite_tac[type_tcexp_cases] >> rw[] >>
    rpt $ first_x_assum $ irule_at Any >> simp[]
    )
  >- (
    once_rewrite_tac[type_tcexp_cases] >> rw[] >>
    rpt $ first_x_assum $ irule_at Any >> simp[]
    )
  >- (
    `∀e. fv_set_ok (letrec_recurse_fvs clean_one_cexp e)` by (
      rw[] >> qspecl_then [`clean_one_cexp`,`e'`] mp_tac fvs_ok_letrec_recurse_fvs >>
      impl_tac >- simp[clean_one_fvs_ok] >> rw[] >> imp_res_tac fvs_ok_imp) >>
    simp[clean_one_cexp_def] >> rw[Once type_tcexp_cases]
    >- (
      first_x_assum drule >> rw[] >>
      irule type_tcexp_env_extensional >> goal_assum $ drule_at Any >>
      rw[ALOOKUP_APPEND] >> CASE_TAC >> gvs[] >>
      irule FALSITY >> imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      drule ALOOKUP_SOME >> simp[MAP_REVERSE, MAP_ZIP] >>
      gvs[EVERY_MEM, MEM_MAP, PULL_FORALL, PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
      CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[] >> gvs[fv_set_ok_def] >>
      `NestedCase_free $ letrec_recurse_fvs clean_one_cexp e` by (
        irule type_tcexp_NestedCase_free >>
        rpt $ goal_assum $ drule_at Any >> simp[]) >>
      gvs[pure_tcexp_lemmasTheory.freevars_tcexp_of] >> res_tac >> simp[]
      ) >>
    rpt (TOP_CASE_TAC >> gvs[pure_tcexpTheory.tcexp_of_def]) >>
    rpt (pairarg_tac >> gvs[])
    >- (
      simp[Once type_tcexp_cases] >>
      rpt $ first_x_assum $ drule_then assume_tac >> goal_assum $ drule_at Any >>
      irule type_tcexp_env_extensional >> goal_assum $ drule_at Any >> rw[] >>
      irule FALSITY >> last_x_assum $ qspec_then `x` assume_tac >> gvs[fv_set_ok_def] >>
      `NestedCase_free $ letrec_recurse_fvs clean_one_cexp x` by (
        irule type_tcexp_NestedCase_free >>
        rpt $ goal_assum $ drule_at Any >> simp[]) >>
      gvs[pure_tcexp_lemmasTheory.freevars_tcexp_of] >> res_tac >> gvs[]
      )
    >- (
      simp[Once type_tcexp_cases, PULL_EXISTS, EXISTS_PROD] >>
      rpt $ first_x_assum $ irule_at Any
      )
    >- (
      qpat_x_assum `lookup _ _ = _ ⇒ _` kall_tac >>
      qsuff_tac
        `type_tcexp ns db st env
          (Letrec (MAP ( λ(n,x).(n,tcexp_of x)) $
            MAP (λ(n,x). (n, letrec_recurse_fvs clean_one_cexp x)) fns)
              (tcexp_of (letrec_recurse_fvs clean_one_cexp e))) t`
      >- simp[] >> pop_assum kall_tac >>
      simp[Once type_tcexp_cases] >> qexists `schemes` >>
      gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      gvs[LIST_REL_EL_EQN, MEM_EL, EL_MAP] >> rw[] >> rpt (pairarg_tac >> gvs[]) >>
      first_x_assum drule >> rw[] >> first_x_assum irule >> simp[] >>
      goal_assum drule >> simp[]
      )
    )
  >- (
    rw[Once type_tcexp_cases] >> gvs[]
    >- (
      simp[Once type_tcexp_cases] >> disj1_tac >>
      gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> metis_tac[]
      )
    >- (
      simp[Once type_tcexp_cases] >> disj1_tac >> rpt (pairarg_tac >> gvs[]) >>
      rpt $ first_x_assum $ irule_at Any >> simp[]
      )
    >- (
      simp[Once type_tcexp_cases] >> ntac 2 disj2_tac >> disj1_tac >>
      gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> metis_tac[]
      )
    >- (
      simp[Once type_tcexp_cases] >> rpt disj2_tac >>
      gvs[EXISTS_PROD, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      rpt $ first_x_assum $ irule_at Any >> simp[] >>
      Cases_on `eopt` >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
      gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> metis_tac[]
      )
    )
QED

Theorem clean_all_cexp_cexp_wf:
  ∀ce. cexp_wf ce ⇒ cexp_wf (clean_all_cexp ce)
Proof
  rw[clean_all_cexp_def] >> irule letrec_recurse_fvs_cexp_wf >>
  rw[clean_one_cexp_def] >> gvs[cexp_wf_def] >>
  rpt (TOP_CASE_TAC >> gvs[]) >> simp[cexp_wf_def]
QED

Theorem clean_all_cexp_NestedCase_free:
  ∀ce. NestedCase_free ce ⇒ NestedCase_free (clean_all_cexp ce)
Proof
  rw[clean_all_cexp_def] >> irule letrec_recurse_fvs_NestedCase_free >>
  rw[clean_one_cexp_def] >> gvs[] >>
  rpt (TOP_CASE_TAC >> gvs[]) >> simp[]
QED

Theorem clean_all_cexp_freevars:
  ∀ce. freevars_cexp (clean_all_cexp ce) ⊆ freevars_cexp ce
Proof
  rw[] >> qspec_then `exp_of ce` mp_tac freevars_clean_all >>
  simp[GSYM clean_all_cexp_correct, freevars_exp_of] >>
  gvs[SUBSET_DEF, PULL_EXISTS]
QED

(********************)

Theorem exp_of_init_sets:
  ∀e. exp_of (init_sets e) = exp_of e
Proof
  ho_match_mp_tac init_sets_ind \\ rw [exp_of_def,init_sets_def]
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f,FORALL_PROD, SF SFY_ss]
  \\ fs [LAMBDA_PROD] \\ every_case_tac
  \\ TRY AP_TERM_TAC
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f,FORALL_PROD, SF SFY_ss]
  \\ Cases_on ‘eopt’ \\ fs [LAMBDA_PROD] \\ gvs []
  \\ TRY (Cases_on ‘x’ \\ fs [])
  \\ last_x_assum kall_tac
  \\ Induct_on ‘ys’ \\ fs [SF DNF_ss,FORALL_PROD] \\ rw []
  \\ last_x_assum $ drule \\ fs [rows_of_def]
QED

Theorem cexp_wf_init_sets:
  ∀ce. cexp_wf (init_sets ce) ⇔ cexp_wf ce
Proof
  Induct using freevars_cexp_ind >> rw[init_sets_def, cexp_wf_def] >>
  gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD]
  >- metis_tac[]
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM] >>
    Cases_on `eopt` >> gvs[] >- metis_tac[] >>
    rpt (pairarg_tac >> gvs[]) >> metis_tac[]
    )
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> metis_tac[]
    )
QED

Theorem NestedCase_free_init_sets:
  ∀ce. NestedCase_free (init_sets ce) ⇔ NestedCase_free ce
Proof
  Induct using freevars_cexp_ind >> rw[init_sets_def] >>
  gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD]
  >- metis_tac[]
  >- (
    Cases_on `eopt` >> gvs[] >- metis_tac[] >>
    rpt (pairarg_tac >> gvs[]) >> metis_tac[]
    )
QED

Theorem init_sets_freevars:
  ∀ce. freevars_cexp (init_sets ce) = freevars_cexp ce
Proof
  rw[] >> qspec_then `ce` assume_tac exp_of_init_sets >>
  qspec_then `init_sets ce` assume_tac freevars_exp_of >>
  qspec_then `ce` assume_tac freevars_exp_of >>
  gvs[EXTENSION, EQ_IMP_THM, PULL_EXISTS]
QED

(********************)

Theorem clean_cexp_correct:
  ∀ce. exp_of ce ≅ exp_of (clean_cexp c ce)
Proof
  rw[clean_cexp_def, exp_eq_refl, clean_all_cexp_exp_eq]
QED

Theorem clean_cexp_letrecs_distinct:
  ∀ce. letrecs_distinct (exp_of ce) ⇒ letrecs_distinct (exp_of (clean_cexp c ce))
Proof
  rw[clean_cexp_def, clean_all_letrecs_distinct, clean_all_cexp_correct]
QED

Theorem clean_cexp_cexp_wf:
  ∀ce c. cexp_wf ce ⇒ cexp_wf (clean_cexp c ce)
Proof
  rw[clean_cexp_def] >> irule clean_all_cexp_cexp_wf >> simp[]
QED

Theorem clean_cexp_NestedCase_free:
  ∀ce c. NestedCase_free ce ⇒ NestedCase_free (clean_cexp c ce)
Proof
  rw[clean_cexp_def] >> irule clean_all_cexp_NestedCase_free >> simp[]
QED

Theorem clean_cexp_freevars:
  ∀ce. freevars_cexp (clean_cexp c ce) ⊆ freevars_cexp ce
Proof
  rw[clean_cexp_def] >> gvs[clean_all_cexp_freevars]
QED

(**********)

Theorem transform_cexp_correct:
  ∀ce. exp_of ce ≅ exp_of (transform_cexp c ce)
Proof
  simp[transform_cexp_def,exp_of_init_sets,exp_eq_refl] >> gen_tac >>
  irule exp_eq_trans >> irule_at (Pos last) clean_cexp_correct >> rw[]
  >- (
    simp[distinct_cexp_correct, distinct_letrecs_distinct, exp_of_init_sets] >>
    simp[distinct_exp_eq]
    ) >>
  irule exp_eq_trans >> irule_at (Pos last) split_all_cexp_exp_eq >>
  simp[distinct_cexp_correct, distinct_letrecs_distinct, exp_of_init_sets] >>
  simp[distinct_exp_eq]
QED

Theorem transform_cexp_letrecs_distinct:
  ∀ce. letrecs_distinct (exp_of (transform_cexp c ce))
Proof
  gen_tac >> simp[transform_cexp_def] >> irule clean_cexp_letrecs_distinct >> rw[] >>
  simp[transform_cexp_def, split_all_cexp_correct, clean_cexp_correct,
       distinct_cexp_correct, exp_of_init_sets] >>
  assume_tac simplify_letrecs_distinct >> gvs[simplify_def,distinct_letrecs_distinct]
QED

Theorem transform_cexp_cexp_wf:
  ∀ce. cexp_wf ce ⇒ cexp_wf (transform_cexp c ce)
Proof
  rw[transform_cexp_def] >>
  irule clean_cexp_cexp_wf >>
  rpt $ irule split_all_cexp_cexp_wf >>
  irule distinct_cexp_cexp_wf >>
  simp[cexp_wf_init_sets]
QED

Theorem transform_cexp_NestedCase_free:
  ∀ce. NestedCase_free ce ⇒ NestedCase_free (transform_cexp c ce)
Proof
  rw[transform_cexp_def] >>
  irule clean_cexp_NestedCase_free >>
  rpt $ irule split_all_cexp_NestedCase_free >>
  irule distinct_cexp_NestedCase_free >>
  simp[NestedCase_free_init_sets]
QED

Theorem transform_cexp_closed:
  ∀ce. closed (exp_of ce) ⇒ closed (exp_of (transform_cexp c ce))
Proof
  rw[closed_def, transform_cexp_def, freevars_exp_of, EXTENSION] >>
  CCONTR_TAC >> gvs[] >>
  dxrule $ SRULE [SUBSET_DEF] clean_cexp_freevars >> strip_tac >>
  gvs[split_all_cexp_freevars, distinct_cexp_correct, distinct_letrecs_distinct] >>
  dxrule $ SRULE [SUBSET_DEF] distinct_cexp_freevars >> strip_tac >>
  gvs[init_sets_freevars]
QED


(********************)

