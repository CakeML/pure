(*
   Verification of a compiler that ensures every Letrec bound name is a lambda (Lam).
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open arithmeticTheory listTheory alistTheory optionTheory pairTheory dep_rewrite
     pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_exp_lemmasTheory pure_exp_relTheory pure_evalTheory
     pure_congruenceTheory pure_miscTheory pure_eval_lemmasTheory
     pure_letrecTheory pure_letrecProofTheory;

val _ = new_theory "pure_letrec_lamProof";


Definition apps_ok_def:
  apps_ok (apps : string |-> exp) ⇔
    (* each substition replaces a ‘Var n’ by ‘App (Var n) arg’ *)
    ∀n v. FLOOKUP apps n = SOME v ⇒ ∃arg. v = App (Var n) arg ∧ closed arg
End

Definition lams_ok_def:
  lams_ok apps xs ys ⇔
    (* all the substitions in apps must be within set of defined names *)
    FDOM apps ⊆ set (MAP FST xs) ∧
    LIST_REL
      (λ(v1,x1) (v2,x2).
         (* bound names stay the same *)
         v1 = v2 ∧
         if v1 IN FDOM apps then
           (* if this is an updated binding, then add a Lam, and subst apps: *)
           ∃w. ~(MEM w (freevars x1)) ∧ ~(MEM w (MAP FST xs)) ∧
               x2 = Lam w (subst apps x1)
         else (* otherwise only subst apps: *) x2 = subst apps x1)
      xs ys
End

Inductive letrec_lam:
  (∀xs x apps ys.
     apps_ok apps ∧ lams_ok apps xs ys ∧ closed (Letrec xs x) ⇒
     letrec_lam
       (Letrec xs x)
       (Letrec ys (subst apps x)))
  ∧
  (∀xs x apps ys arg.
     apps_ok apps ∧ lams_ok apps xs ys ∧
     closed arg ∧ closed (Letrec xs x) ∧ w ∉ freevars (subst apps x) ⇒
     letrec_lam
       (Letrec xs x)
       (App (Letrec ys (Lam w (subst apps x))) arg))
End

(********************)

Theorem apps_ok_FRANGE_freevars:
  ∀apps. apps_ok apps ⇒ ∀v. v ∈ FRANGE apps ⇒ freevars v ⊆ FDOM apps
Proof
  rw[apps_ok_def, IN_FRANGE_FLOOKUP] >>
  last_x_assum drule >> strip_tac >> gvs[FLOOKUP_DEF, closed_def]
QED

Theorem apps_ok_freevars_subst:
  ∀apps x. apps_ok apps ⇒ freevars (subst apps x) = (freevars x : string list)
Proof
  recInduct subst_ind >> rw[] >> gvs[apps_ok_def, subst_def]
  >- (CASE_TAC >> simp[] >> first_x_assum drule >> rw[] >> gvs[closed_def])
  >- (simp[MAP_MAP_o, combinTheory.o_DEF] >> AP_TERM_TAC >> rw[MAP_EQ_f])
  >- gvs[DOMSUB_FLOOKUP_THM]
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    gvs[FDIFF_def, FLOOKUP_DRESTRICT] >>
    AP_TERM_TAC >> simp[] >> AP_TERM_TAC >> simp[] >>
    rw[MAP_EQ_f] >> PairCases_on `e` >> gvs[] >> res_tac
    )
QED

Triviality lams_ok_imps:
  ∀apps xs ys. lams_ok apps xs ys ⇒
  MAP FST xs = MAP FST ys ∧ LENGTH xs = LENGTH ys ∧ FDOM apps ⊆ set (MAP FST xs)
Proof
  rw[lams_ok_def] >> gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2] >> rw[] >>
  last_x_assum drule >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]
QED

Triviality lams_ok_imp_freevars:
  ∀apps xs ys.
    lams_ok apps xs ys ∧ apps_ok apps
  ⇒ MAP (λ(fn,e). freevars e) xs = MAP (λ(fn,e). freevars e) ys
Proof
  rw[MAP_EQ_EVERY2] >> gvs[lams_ok_def, LIST_REL_EL_EQN] >> rw[] >>
  last_x_assum drule >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  EVERY_CASE_TAC >> gvs[] >>
  drule apps_ok_freevars_subst >> simp[] >>
  gvs[EXTENSION] >> rw[] >> metis_tac[]
QED

Theorem letrec_lam_subst:
  ∀f x g y.  letrec_lam x y ⇒ letrec_lam (subst f x) (subst g y)
Proof
  simp[Once letrec_lam_cases] >> rw[] >> rename1 `Letrec xs x`
  >- (
    ntac 2 (DEP_ONCE_REWRITE_TAC[subst_ignore]) >>
    simp[letrec_lam_cases, PULL_EXISTS] >>
    irule_at Any EQ_REFL >> simp[] >>
    imp_res_tac apps_ok_freevars_subst >> simp[] >>
    drule_all lams_ok_imp_freevars >> strip_tac >> gvs[] >>
    imp_res_tac lams_ok_imps >> gvs[] >>
    qmatch_goalsub_abbrev_tac `DISJOINT s` >> qsuff_tac `s = {}` >> gvs[] >>
    unabbrev_all_tac >> gvs[SUBSET_DIFF_EMPTY, BIGUNION_SUBSET, EVERY_MEM] >>
    gvs[MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
    gvs[MEM_EL, PULL_EXISTS] >> Cases_on `EL n ys` >> gvs[] >>
    last_x_assum drule >> Cases_on `EL n xs` >> gvs[] >> rw[] >>
    gvs[lams_ok_def, LIST_REL_EL_EQN] >> last_x_assum drule >> simp[] >>
    strip_tac >> gvs[] >> EVERY_CASE_TAC >> gvs[] >>
    simp[GSYM SUBSET_INSERT_DELETE]
    )
  >- (
    ntac 2 (DEP_ONCE_REWRITE_TAC[subst_ignore]) >>
    simp[letrec_lam_cases, PULL_EXISTS] >>
    irule_at Any EQ_REFL >> simp[] >>
    imp_res_tac apps_ok_freevars_subst >> simp[] >>
    drule_all lams_ok_imp_freevars >> strip_tac >> gvs[] >>
    imp_res_tac lams_ok_imps >> gvs[closed_def] >> rw[] >>
    qmatch_goalsub_abbrev_tac `DISJOINT s` >> qsuff_tac `s = {}` >> gvs[] >>
    unabbrev_all_tac >> gvs[SUBSET_DIFF_EMPTY, BIGUNION_SUBSET, EVERY_MEM] >>
    simp[GSYM SUBSET_INSERT_DELETE] >>
    gvs[MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
    gvs[MEM_EL, PULL_EXISTS] >> Cases_on `EL n ys` >> gvs[] >>
    last_x_assum drule >> Cases_on `EL n xs` >> gvs[] >> rw[] >>
    gvs[lams_ok_def, LIST_REL_EL_EQN] >> last_x_assum drule >> simp[] >>
    strip_tac >> gvs[] >> EVERY_CASE_TAC >> gvs[] >>
    simp[GSYM SUBSET_INSERT_DELETE]
    )
QED

Theorem letrec_rel_lam_subst:
  ∀x y.
    letrec_rel letrec_lam x y ⇒
    ∀f g. fmap_rel (letrec_rel letrec_lam) f g ⇒
          letrec_rel letrec_lam (subst f x) (subst g y)
Proof
  ho_match_mp_tac letrec_rel_ind >> rw[] >>
  simp[subst_def, Once letrec_rel_cases]
  >- (
    gvs[fmap_rel_OPTREL_FLOOKUP] >>
    last_x_assum (qspec_then `n` mp_tac) >>
    CASE_TAC >> CASE_TAC >> gvs[] >> simp[Once letrec_rel_cases]
    )
  >- (
    last_x_assum irule >>
    gvs[fmap_rel_OPTREL_FLOOKUP, DOMSUB_FLOOKUP_THM] >> rw[]
    )
  >- (gvs[LIST_REL_EL_EQN] >> rw[EL_MAP]) >>
  (
    qexists_tac
      `MAP (λ(p1,p2). (p1, subst (FDIFF g (set (MAP FST xs1))) p2)) xs1` >>
    qexists_tac `subst (FDIFF g (set (MAP FST xs1))) y` >> simp[] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    first_x_assum (irule_at Any) >> gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[]
    >- (gvs[fmap_rel_OPTREL_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >> rw[])
    >- (
      last_x_assum drule >> Cases_on `EL n xs` >> Cases_on `EL n xs1` >> gvs[] >>
      disch_then irule >>
      gvs[fmap_rel_OPTREL_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >> rw[]
      ) >>
    disj1_tac >> drule letrec_lam_subst >> simp[subst_def]
  )
QED

Triviality letrec_rel_lam_subst_single:
  letrec_rel letrec_lam x y ∧
  letrec_rel letrec_lam a b ⇒
  letrec_rel letrec_lam (subst s a x) (subst s b y)
Proof
  rw[] >> irule letrec_rel_lam_subst >>
  simp[fmap_rel_OPTREL_FLOOKUP, FLOOKUP_UPDATE] >> rw[]
QED

Theorem letrec_lam_correct:
  letrec_rel letrec_lam x y ∧ closed x ∧ closed y ⇒ x ≃ y
Proof
  rw [] \\ irule eval_to_sim_thm \\ fs []
  \\ qexists_tac ‘letrec_rel letrec_lam’ \\ fs []
  \\ simp [eval_to_sim_def]
  \\ rpt (pop_assum kall_tac)
  \\ qabbrev_tac ‘c = letrec_lam’
  \\ gen_tac \\ gen_tac
  \\ qid_spec_tac ‘e1’
  \\ qid_spec_tac ‘k’
  \\ ho_match_mp_tac eval_wh_to_ind \\ rw []
  THEN1
   (rename [‘Lam s x’]
    \\ qpat_x_assum ‘letrec_rel c _ _’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ rw []
    \\ fs [eval_wh_to_def]
    \\ unabbrev_all_tac \\ rw[]
    \\ irule letrec_rel_lam_subst_single
    \\ simp[letrec_rel_refl])
  THEN1
   (rename [‘App x1 x2’]
    \\ qpat_x_assum ‘letrec_rel c _ _’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ rw [] \\ fs []
    \\ fs [eval_wh_to_def]
    \\ Cases_on ‘eval_wh_to k x1 = wh_Diverge’
    THEN1 (fs [] \\ res_tac \\ qexists_tac ‘ck’ \\ fs [])
    \\ fs []
    \\ first_x_assum drule \\ fs [] \\ rw []
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k x1)’ \\ fs []
    THEN1
     (fs [AllCaseEqs()] \\ qexists_tac ‘ck’ \\ fs []
      \\ Cases_on ‘eval_wh_to k x1’ \\ fs [])
    \\ Cases_on ‘eval_wh_to k x1’ \\ gvs []
    \\ rename [‘eval_wh_to (ck + k) g = wh_Closure _ e1’]
    \\ ‘letrec_rel c (bind s x2 e) (bind s y e1)’ by (
      rw[bind_single_def] >> unabbrev_all_tac >>
      irule letrec_rel_lam_subst >> simp[] >>
      simp[fmap_rel_OPTREL_FLOOKUP, FLOOKUP_UPDATE] >> rw[])
    \\ Cases_on ‘k’ \\ fs []
    THEN1 (qexists_tac ‘0’ \\ fs [] >>
           IF_CASES_TAC >> simp[] >>
           drule eval_wh_inc >> disch_then (qspec_then `ck` (assume_tac o GSYM)) >>
           gvs[])
    \\ fs [ADD1]
    \\ last_x_assum drule \\ fs []
    \\ impl_tac THEN1 (
         simp[bind_single_def] >>
         imp_res_tac eval_wh_to_Closure_freevars_SUBSET >> simp[closed_def] >>
         once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
         dep_rewrite.DEP_REWRITE_TAC[freevars_subst_single] >> simp[] >>
         rw[EXTENSION, DISJ_EQ_IMP] >>
         first_x_assum drule >> rw[] >> gvs[closed_def])
    \\ strip_tac
    \\ Cases_on ‘eval_wh_to n (bind s x2 e) = wh_Diverge’ \\ fs []
    THEN1
     (qexists_tac ‘ck'’ \\ fs [] \\ IF_CASES_TAC \\ fs [] >>
      drule eval_wh_to_agree >>
      disch_then (qspec_then `ck + (n + 1)` (assume_tac o GSYM)) >>
      gvs[])
    \\ qexists_tac ‘ck+ck'’
    \\ ‘eval_wh_to (ck + (n + 1) + ck') g = wh_Closure s e1’ by (
      qspecl_then [`ck + (n + 1) + ck'`,`g`,`ck + (n + 1)`]
      assume_tac eval_wh_inc >>
      gvs[])
    \\ fs [] \\ Cases_on ‘eval_wh_to n (bind s x2 e)’ \\ fs []
    \\ ‘eval_wh_to (ck + (ck' + n)) (bind s y e1) =
        eval_wh_to (ck' + n) (bind s y e1)’ by (
      irule eval_wh_inc >> simp[]) >>
    fs[])
  THEN1
   (rename [‘Letrec f y’]
    \\ qpat_x_assum ‘letrec_rel c _ _’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ reverse (rw []) \\ fs []
    THEN1
     (Cases_on ‘k’ \\ fs [eval_wh_to_def]
      THEN1 (qexists_tac ‘0’ \\ fs []) \\ fs [ADD1]
      \\ ‘letrec_rel c (subst_funs f y) (subst_funs xs1 y1)’ by (
        dep_rewrite.DEP_REWRITE_TAC[subst_funs_eq_subst] >> gvs[] >>
        unabbrev_all_tac >>
        irule letrec_rel_lam_subst >> simp[] >>
        irule fmap_rel_FUPDATE_LIST_same >>
        simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        simp[GSYM FST_THM] >>
        gvs[LIST_REL_EL_EQN] >> rw[] >> gvs[EL_MAP] >>
        last_assum drule >> rename1 `EL foo f` >>
        qabbrev_tac `a = EL foo f` >> qabbrev_tac `b = EL foo xs1` >>
        PairCases_on `a` >> PairCases_on `b` >> gvs[] >> rw[] >>
        simp[Once letrec_rel_cases] >>
        goal_assum (drule_at Any) >> qexists_tac `xs1` >> simp[] >>
        gvs[LIST_REL_EL_EQN, EL_MAP])
      \\ first_x_assum drule \\ fs []
      \\ reverse impl_tac >- rw[] >>
         rw[subst_funs_def, bind_def] >> simp[closed_def] >>
         once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
         dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >>
         simp[IN_FRANGE_FLOOKUP, PULL_EXISTS, FDOM_FUPDATE_LIST] >>
         simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
         simp[GSYM FST_THM] >> gvs[SUBSET_DEF, EXTENSION] >>
         metis_tac[])
    \\ unabbrev_all_tac
    \\ pop_assum mp_tac
    \\ simp [Once letrec_lam_cases] \\ rw []
    \\ ‘closed (subst_funs ys (subst apps y1)) ∧ closed (subst_funs f y)’ by (
        rw[subst_funs_def, bind_def, closed_def] >>
        once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
        DEP_ONCE_REWRITE_TAC[freevars_subst] >>
        drule apps_ok_freevars_subst >> simp[] >> strip_tac >>
        simp[FDOM_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        simp[GSYM FST_THM, SUBSET_DIFF_EMPTY] >>
        imp_res_tac lams_ok_imps >> gvs[] >>
        ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> simp[] >>
        simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
        metis_tac[])
    \\ ‘letrec_rel letrec_lam (subst_funs f y) (subst_funs ys (subst apps y1))’ by (
      DEP_REWRITE_TAC[subst_funs_eq_subst] >> simp[] >>
      imp_res_tac lams_ok_imps >> gvs[] >>
      cheat (* TODO *)
      )
    THEN1 (* case 1 of letrec_lam *)
     (rewrite_tac [eval_wh_to_def]
      \\ IF_CASES_TAC THEN1 (gvs [] \\ qexists_tac ‘0’ \\ fs [])
      \\ gvs [] \\ last_x_assum irule \\ fs [])
    (* case 2 of letrec_lam *)
    \\ rewrite_tac [eval_wh_to_def]
    \\ IF_CASES_TAC THEN1 (gvs [] \\ qexists_tac ‘0’ \\ fs [])
    \\ gvs []
    \\ ‘subst_funs ys (Lam w (subst apps y1)) =
        Lam w (subst_funs ys (subst apps y1))’ by (
          simp[subst_funs_def, bind_def] >>
          reverse IF_CASES_TAC >> gvs[]
          >- (
            gvs[flookup_fupdate_list] >>
            pop_assum mp_tac >> CASE_TAC >> strip_tac >> gvs[] >>
            imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM, MEM_MAP, EXISTS_PROD] >>
            metis_tac[]
            ) >>
          simp[subst_def] >> irule (GSYM subst_fdomsub) >> simp[])
    \\ fs [eval_wh_to_def] \\ fs [bind_single_def])
  >- (
    rename [‘Prim p xs’] >>
    qpat_x_assum `letrec_rel c _ _` mp_tac >>
    simp[Once letrec_rel_cases] >> rw[] >>
    Cases_on `p` >> gvs[eval_wh_to_def]
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> gvs[]) >>
      IF_CASES_TAC >> gvs[LIST_REL_EL_EQN] >>
      `∃x1 x2 x3. xs = [x1;x2;x3]` by (
        Cases_on `xs` >> gvs[] >> Cases_on `t` >> gvs[] >>
        Cases_on `t'` >> gvs[] >> Cases_on `t` >> gvs[]
        ) >>
      `∃y1 y2 y3. ys = [y1;y2;y3]` by (
        Cases_on `ys` >> gvs[] >> Cases_on `t` >> gvs[] >>
        Cases_on `t'` >> gvs[] >> Cases_on `t` >> gvs[]
        ) >>
      gvs[] >>
      first_assum (qspec_then `0` assume_tac) >>
      first_assum (qspec_then `1` assume_tac) >>
      first_x_assum (qspec_then `2` assume_tac) >> gvs[] >>
      gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      reverse (Cases_on `eval_wh_to (k - 1) x1`) >> gvs[]
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[]) >>
      reverse (IF_CASES_TAC) >> gvs[]
      >- (
        reverse (IF_CASES_TAC) >> gvs[]
        >- (
          qexists_tac `ck` >> gvs[] >>
          Cases_on `l` >> gvs[] >> Cases_on `ys'` >> gvs[]
          ) >>
        last_x_assum drule_all >> strip_tac >> gvs[] >>
        reverse (Cases_on `eval_wh_to (k - 1) x3`) >> gvs[]
        >- (
          qexists_tac `ck'` >>
          Cases_on `eval_wh_to (ck' + k - 1) y1 = wh_Diverge` >> gvs[] >>
          drule eval_wh_to_agree >>
          disch_then (qspec_then `ck + k - 1` assume_tac) >> gvs[]
          ) >>
        qspecl_then [`ck + ck' + k - 1`,`y1`,`ck + k - 1`] mp_tac eval_wh_inc >>
        gvs[] >> strip_tac >>
        qspecl_then [`ck + ck' + k - 1`,`y3`,`ck' + k - 1`] mp_tac eval_wh_inc >>
        gvs[] >> strip_tac >>
        qexists_tac `ck + ck'` >> gvs[]
        )
      >- (
        first_x_assum drule_all >> strip_tac >> gvs[] >>
        reverse (Cases_on `eval_wh_to (k - 1) x2`) >> gvs[]
        >- (
          qexists_tac `ck'` >>
          Cases_on `eval_wh_to (ck' + k - 1) y1 = wh_Diverge` >> gvs[] >>
          drule eval_wh_to_agree >>
          disch_then (qspec_then `ck + k - 1` assume_tac) >> gvs[]
          ) >>
        qspecl_then [`ck + ck' + k - 1`,`y1`,`ck + k - 1`] mp_tac eval_wh_inc >>
        gvs[] >> strip_tac >>
        qspecl_then [`ck + ck' + k - 1`,`y2`,`ck' + k - 1`] mp_tac eval_wh_inc >>
        gvs[] >> strip_tac >>
        qexists_tac `ck + ck'` >> gvs[]
        )
      )
    >- (
      IF_CASES_TAC >> gvs[] >> qexists_tac `0` >> simp[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> simp[]) >>
      IF_CASES_TAC >> gvs[] >> gvs[LIST_REL_EL_EQN] >>
      `∃x. xs = [x]` by (
        Cases_on `xs` >> gvs[] >> Cases_on `t` >> gvs[]) >>
      `∃y. ys = [y]` by (
        Cases_on `ys` >> gvs[] >> Cases_on `t` >> gvs[]) >>
      gvs[] >>
      first_x_assum drule_all >> rw[] >>
      Cases_on `eval_wh_to (k - 1) x` >> gvs[] >>
      qexists_tac `ck` >> gvs[] >>
      IF_CASES_TAC >> gvs[] >>
      IF_CASES_TAC >> gvs[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> simp[]) >>
      IF_CASES_TAC >> gvs[] >> gvs[LIST_REL_EL_EQN] >>
      `∃x. xs = [x]` by (
        Cases_on `xs` >> gvs[] >> Cases_on `t` >> gvs[]) >>
      `∃y. ys = [y]` by (
        Cases_on `ys` >> gvs[] >> Cases_on `t` >> gvs[]) >>
      gvs[] >>
      first_x_assum drule_all >> rw[] >>
      reverse (Cases_on `eval_wh_to (k - 1) x`) >> gvs[]
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[]) >>
      reverse IF_CASES_TAC >> gvs[]
      >- (qexists_tac `ck` >> gvs[] >> EVERY_CASE_TAC >> gvs[]) >>
      first_x_assum drule >> rw[] >>
      last_x_assum drule >> impl_tac
      >- (
        gvs[closed_def, NIL_iff_NOT_MEM] >>
        CCONTR_TAC >> gvs[] >>
        imp_res_tac eval_wh_to_freevars_SUBSET >> gvs[MEM_MAP]
        >- (
          pop_assum kall_tac >> pop_assum mp_tac >> simp[PULL_EXISTS] >>
          goal_assum drule >> simp[EL_MEM]
          )
        >- (
          pop_assum mp_tac >> simp[PULL_EXISTS] >>
          goal_assum drule >> simp[EL_MEM]
          )
        ) >>
      rw[] >>
      reverse (Cases_on `eval_wh_to (k - 1) (EL n l)`) >> gvs[]
      >- (
        qexists_tac `ck'` >>
        Cases_on `eval_wh_to (ck' + k - 1) y = wh_Diverge` >> gvs[] >>
        drule eval_wh_to_agree >>
        disch_then (qspec_then `ck + k - 1` (assume_tac o GSYM)) >> gvs[]
        ) >>
      qspecl_then [`ck + ck' + k - 1`,`y`,`ck + k - 1`] mp_tac eval_wh_inc >>
      gvs[] >> strip_tac >>
      qspecl_then [`ck + ck' + k - 1`,`EL n ys'`,`ck' + k - 1`]
        mp_tac eval_wh_inc >>
      gvs[] >> strip_tac >>
      qexists_tac `ck + ck'` >> gvs[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> gvs[]) >>
      CASE_TAC >> gvs[]
      >- (
        qsuff_tac `get_atoms (MAP (λa. eval_wh_to (k − 1) a) ys) = NONE`
        >- (rw[] >> qexists_tac `0` >> simp[]) >>
        gvs[get_atoms_NONE_eq] >> imp_res_tac LIST_REL_LENGTH >> gvs[] >>
        csimp[EL_MAP] >> gvs[EL_MAP] >>
        map_every (fn pat => qpat_x_assum pat mp_tac)
          [`∀e1. MEM e1 _ ⇒ _`, `n < _`,`eval_wh_to _ _ = _`, `∀m. m < _ ⇒ _`,
           `EVERY _ _`, `EVERY _ _`, `LENGTH _ = _`] >>
        qid_spec_tac `n` >>
        qpat_x_assum `LIST_REL _ _ _` mp_tac >>
        map_every qid_spec_tac [`ys`,`xs`] >>
        ho_match_mp_tac LIST_REL_ind >> rw[] >>
        Cases_on `n` >> gvs[]
        >- (
          qexists_tac `0` >> gvs[] >>
          first_x_assum (qspec_then `h1` mp_tac) >> simp[] >>
          disch_then drule_all >> rw[] >>
          CCONTR_TAC >> drule eval_wh_inc >>
          disch_then (qspec_then `ck + k - 1` mp_tac) >> simp[]
          ) >>
        rename1 `n < _` >>
        Cases_on `eval_wh_to (k - 1) h2 = wh_Diverge`
        >- (qexists_tac `0` >> simp[]) >>
        last_x_assum (qspec_then `n` mp_tac) >> simp[IMP_CONJ_THM] >>
        impl_tac
        >- (rw[] >> last_x_assum (qspec_then `SUC m` mp_tac) >> simp[]) >>
        strip_tac >> rename1 `l < _` >>
        qexists_tac `SUC l` >> simp[] >> rw[] >>
        Cases_on `m` >> gvs[] >>
        last_x_assum (qspec_then `0` assume_tac) >> gvs[] >>
        first_x_assum (qspec_then `h1` mp_tac) >> simp[] >>
        disch_then drule_all >> strip_tac >>
        drule eval_wh_to_agree >>
        disch_then (qspec_then `ck + k - 1` mp_tac) >> rw[] >>
        metis_tac[]
        ) >>
      Cases_on `x` >> gvs[]
      >- (
        gvs[get_atoms_SOME_NONE_eq, EL_MAP] >>
        qsuff_tac
          `∃ck. get_atoms (MAP (λa. eval_wh_to (ck + k − 1) a) ys) = SOME NONE`
        >- (rw[] >> qexists_tac `ck` >> simp[]) >>
        simp[get_atoms_SOME_NONE_eq] >> csimp[EL_MAP] >>
        imp_res_tac LIST_REL_LENGTH >> gvs[] >> goal_assum drule >>
        map_every (fn pat => qpat_x_assum pat mp_tac)
          [`∀e1. MEM e1 _ ⇒ _`, `n < _`,` ∀a. eval_wh_to _ _ ≠ _`,
           `∀m. m ≤ _ ⇒ _`, `EVERY _ _`, `EVERY _ _`, `LENGTH _ = _`] >>
        qid_spec_tac `n` >>
        qpat_x_assum `LIST_REL _ _ _` mp_tac >>
        map_every qid_spec_tac [`ys`,`xs`] >>
        ho_match_mp_tac LIST_REL_ind >> rw[] >>
        Cases_on `n` >> gvs[]
        >- (
          pop_assum (qspec_then `h1` mp_tac) >> simp[] >>
          disch_then drule_all >> strip_tac >>
          qexists_tac `ck` >>
          Cases_on `eval_wh_to (k - 1) h1` >> gvs[]
          ) >>
        rename1 `SUC n` >>
        last_x_assum (qspec_then `n` mp_tac) >> simp[] >> impl_tac
        >- (rw[] >> last_x_assum (qspec_then `SUC m` mp_tac) >> simp[]) >>
        strip_tac >>
        first_x_assum (qspec_then `h1` mp_tac) >> simp[] >>
        disch_then drule_all >> strip_tac >>
        qexists_tac `ck + ck'` >> rw[]
        >- (
          qpat_x_assum `∀a. _ ≠ wh_Atom a` (qspec_then `a` mp_tac) >>
          first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
          drule eval_wh_inc >>
          disch_then (qspec_then `ck + (ck' + k) - 1` assume_tac) >> gvs[]
          ) >>
        Cases_on `m` >> gvs[]
        >- (
          qspecl_then [`ck + (ck' + k) - 1`,`h2`,`ck' + k - 1`]
            assume_tac eval_wh_inc >>
          gvs[] >>
          full_case_tac >> gvs[] >>
          last_x_assum (qspec_then `0` assume_tac) >> gvs[]
          )
        >- (
          rename1 `m ≤ _` >>
          first_x_assum drule >> strip_tac >>
          drule eval_wh_inc >>
          disch_then (qspec_then `ck + (ck' + k) - 1` assume_tac) >> gvs[]
          )
        ) >>
      rename1 `SOME (SOME as)` >>
      qsuff_tac
        `∃ck. get_atoms (MAP (λa. eval_wh_to (ck + k − 1) a) ys) = SOME (SOME as)`
      >- (rw[] >> qexists_tac `ck` >> simp[] >> CASE_TAC >> gvs[]) >>
      gvs[get_atoms_SOME_SOME_eq, EVERY2_MAP] >>
      map_every (fn pat => qpat_x_assum pat mp_tac)
        [`∀e1. MEM e1 _ ⇒ _`, `LIST_REL _ _ _`, `EVERY _ _`, `EVERY _ _`] >>
      qid_spec_tac `as` >>
      qpat_x_assum `LIST_REL _ _ _` mp_tac >>
      map_every qid_spec_tac [`ys`,`xs`] >>
      ho_match_mp_tac LIST_REL_strongind >> rw[] >>
      rename1 `LIST_REL _ _ as` >>
      qsuff_tac
        `∃ck. LIST_REL (λa a'. eval_wh_to (ck + k − 1) a = wh_Atom a') ys as`
      >- (
        pop_assum (qspec_then `h1` mp_tac) >> simp[] >>
        disch_then drule_all >> rw[] >>
        qexists_tac `ck + ck'` >>
        qspecl_then [`ck + ck' + k - 1`,`h2`,`ck + k - 1`]
          assume_tac eval_wh_inc >>
        gvs[LIST_REL_EL_EQN] >> rw[] >>
        qspecl_then [`ck + ck' + k - 1`,`EL n ys`,`ck' + k - 1`]
          assume_tac eval_wh_inc >>
        gvs[]
        ) >>
      last_x_assum irule >> simp[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> gvs[]) >>
      IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[]
      )
    )
QED

val _ = export_theory();
