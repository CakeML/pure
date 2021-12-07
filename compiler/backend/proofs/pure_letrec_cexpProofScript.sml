(*
   Verification of pure_letrec_cexp
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open listTheory pairTheory alistTheory pred_setTheory finite_mapTheory
     sptreeTheory topological_sortTheory;
open pure_miscTheory pure_expTheory pure_cexpTheory
     pure_letrec_cexpTheory pure_letrecTheory pure_letrecProofTheory
     pure_letrec_lamTheory pure_letrec_lamProofTheory pure_varsTheory
     pure_exp_lemmasTheory pure_cexp_lemmasTheory pure_congruenceTheory;
open mlmapTheory;

val _ = new_theory "pure_letrec_cexpProof";

(********************)

Triviality letrec_recurse_Lams:
  ∀l f e. letrec_recurse f (Lams l e) = Lams l (letrec_recurse f e)
Proof
  Induct >> rw[letrec_recurse_def, Lams_def]
QED

Triviality letrec_recurse_Apps:
  ∀l f e. letrec_recurse f (Apps e l) =
    Apps (letrec_recurse f e) (MAP (letrec_recurse f) l)
Proof
  Induct >> rw[letrec_recurse_def, Apps_def]
QED

Triviality letrec_recurse_rows_of:
  ∀n l f. letrec_recurse f (rows_of n l) =
    rows_of n (MAP (λ(c,vs,e). (c, vs, letrec_recurse f e)) l)
Proof
  recInduct rows_of_ind >> rw[rows_of_def, letrec_recurse_def] >>
  pop_assum kall_tac >> rename1 `lets_for _ _ l _` >>
  map_every qid_spec_tac [`b`,`l`,`v`,`cn`] >>
  recInduct lets_for_ind >> rw[lets_for_def, letrec_recurse_def]
QED

Theorem letrec_recurse_exp_of:
  ∀f ce g.
  (∀c fns e. exp_of (f c fns e) = g (MAP (λ(v,e). (v,exp_of e)) fns) (exp_of e))
  ⇒ exp_of (letrec_recurse_cexp f ce) = letrec_recurse g (exp_of ce)
Proof
  recInduct letrec_recurse_cexp_ind >>
  rw[exp_of_def, letrec_recurse_cexp_def, letrec_recurse_def]
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    first_x_assum drule >> rw[] >> AP_THM_TAC >> AP_TERM_TAC >>
    rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
    last_x_assum irule >> simp[] >> goal_assum drule
    )
  >- (rw[letrec_recurse_Lams] >> AP_TERM_TAC >> first_x_assum irule >> simp[])
  >- (simp[MAP_MAP_o, combinTheory.o_DEF] >> rw[MAP_EQ_f])
  >- (
    rw[letrec_recurse_Apps] >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
    first_x_assum drule >> rw[] >> AP_TERM_TAC >> rw[MAP_EQ_f]
    ) >>
  gs [MEM_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, DISJ_EQ_IMP] >>
  rw[letrec_recurse_rows_of] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> AP_TERM_TAC >>
  rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
  last_x_assum irule >> simp[] >> goal_assum drule
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
  fvs_ok (Case c e v css) =
    (fv_set_ok (Case c e v css) ∧ fvs_ok e ∧ EVERY (λ(cn,vs,e). fvs_ok e) css)
Termination
  WF_REL_TAC `measure $ cexp_size (K 0)` >> rw[] >> gvs[] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[cexp_size_def]
End

Theorem fvs_ok_imp:
  ∀e. fvs_ok e ⇒ fv_set_ok e
Proof
  Cases >> rw[fvs_ok_def]
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
    reverse $ conj_tac >- (rw[] >> res_tac) >> rw[] >>
    DEP_REWRITE_TAC drwts >> csimp[EVERY_MAP, EVERY_MEM, FORALL_PROD]
    >- (
      rw[] >> DEP_REWRITE_TAC drwts >> simp[EVERY_MAP, EVERY_MEM, FORALL_PROD]
      >- metis_tac[fvs_ok_imp, fv_set_ok_def]
      >- metis_tac[fvs_ok_imp, fv_set_ok_def] >>
      rw[] >> DEP_REWRITE_TAC drwts >> simp[EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
      metis_tac[fvs_ok_imp, fv_set_ok_def]
      )
    >- (
      rw[] >> DEP_REWRITE_TAC drwts >> simp[EVERY_MAP, EVERY_MEM, FORALL_PROD]
      >- metis_tac[fvs_ok_imp, fv_set_ok_def]
      >- metis_tac[fvs_ok_imp, fv_set_ok_def] >>
      rw[] >> DEP_REWRITE_TAC drwts >> simp[EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
      metis_tac[fvs_ok_imp, fv_set_ok_def]
      ) >>
    conj_tac
    >- (
      reverse $ rw[] >>
      DEP_REWRITE_TAC drwts >> simp[EVERY_MAP, EVERY_MEM, FORALL_PROD]
      >- metis_tac[fvs_ok_imp, fv_set_ok_def]
      >- metis_tac[fvs_ok_imp, fv_set_ok_def] >>
      rw[] >> DEP_REWRITE_TAC drwts >> simp[EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
      metis_tac[fvs_ok_imp, fv_set_ok_def]
      ) >>
    simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    IF_CASES_TAC >> gvs[]
    >- (CASE_TAC >> gvs[] >> first_x_assum $ qspec_then `k` assume_tac >> gvs[]) >>
    TOP_CASE_TAC >> gvs[] >> eq_tac >> rw[] >> gvs[]
    >- (
      pop_assum mp_tac >> DEP_REWRITE_TAC drwts >>
      metis_tac[fvs_ok_imp, fv_set_ok_def]
      )
    >- (first_x_assum $ qspec_then `k` assume_tac >> gvs[])
    >- (
      goal_assum drule >> DEP_REWRITE_TAC drwts >>
      metis_tac[fvs_ok_imp, fv_set_ok_def]
      )
    )
QED

Theorem letrec_recurse_fvs_exp_of:
  ∀f ce g.
  (∀c fns e.
    fvs_ok (Letrec c fns e)
   ⇒ fvs_ok (f c fns e) ∧
     exp_of (f c fns e) = g (MAP (λ(v,e). (v,exp_of e)) fns) (exp_of e))
  ⇒ exp_of (letrec_recurse_fvs f ce) = letrec_recurse g (exp_of ce)
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
  gs [MEM_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, DISJ_EQ_IMP] >>
  rw[letrec_recurse_rows_of] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> AP_TERM_TAC >>
  rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
  last_x_assum irule >> simp[] >> goal_assum drule
QED


(********** Distinctness **********)

Theorem distinct_cexp_correct:
  ∀ce. exp_of (distinct_cexp ce) = distinct (exp_of ce)
Proof
  rw[distinct_cexp_def, distinct_def] >>
  irule letrec_recurse_exp_of >> simp[exp_of_def] >>
  recInduct make_distinct_ind >> rw[make_distinct_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
QED

Theorem distinct_cexp_exp_eq:
  ∀ce. exp_of ce ≅ exp_of (distinct_cexp ce)
Proof
  rw[distinct_cexp_correct, distinct_exp_eq]
QED


(********** Splitting **********)

Triviality exp_of_make_Letrecs_cexp:
  ∀fns.
    exp_of (make_Letrecs_cexp fns e) =
      make_Letrecs (MAP (MAP (λ(fn,e). (fn,exp_of e))) fns) (exp_of e)
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

Triviality to_nums_set_eq:
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

Triviality top_sort_set_eq:
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

Triviality top_sort_aux_sets:
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

Triviality top_sort_sets:
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
  qmatch_goalsub_abbrev_tac `_ (top_sort_any a) = _ (top_sort_any b)` >>
  `top_sort_any a = top_sort_any b` by (
    irule top_sort_set_eq >> unabbrev_all_tac >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    rw[LIST_REL_EL_EQN, EL_MAP] >> Cases_on `EL n fns` >> simp[GSYM freevars_equiv] >>
    DEP_REWRITE_TAC[GSYM MAP_FST_toAscList |> REWRITE_RULE[IMP_CONJ_THM]] >>
    gvs[fvs_ok_def, EVERY_EL] >> last_x_assum drule >> strip_tac >> gvs[] >>
    imp_res_tac fvs_ok_imp >> gvs[fv_set_ok_def] >>
    rw[EXTENSION, miscTheory.FDOM_FLOOKUP] >>
    DEP_REWRITE_TAC[GSYM lookup_thm] >> simp[freevars_exp_of]
    ) >>
  simp[] >> rw[MAP_EQ_f, ALOOKUP_MAP] >>
  qsuff_tac `∃res. ALOOKUP fns s = SOME res` >> rw[] >> simp[] >>
  simp[miscTheory.ALOOKUP_EXISTS_IFF] >>
  qspec_then `b` assume_tac top_sort_any_sets >>
  gvs[EXTENSION, MEM_FLAT, MEM_MAP, EXISTS_PROD] >>
  pop_assum $ qspec_then `s` $ assume_tac o iffLR >> gvs[PULL_EXISTS] >>
  pop_assum drule_all >> strip_tac >> unabbrev_all_tac >>
  gvs[MEM_MAP] >> pairarg_tac >> gvs[] >> goal_assum drule
QED

Theorem split_all_cexp_exp_eq:
  ∀ce. letrecs_distinct (exp_of ce) ⇒
    exp_of ce ≅ exp_of (split_all_cexp ce)
Proof
  rw[split_all_cexp_correct, split_all_correct]
QED


(********** Cleaning up **********)

Theorem clean_all_cexp_correct:
  ∀ce. exp_of (clean_all_cexp ce) = clean_all (exp_of ce)
Proof
  rw[clean_all_cexp_def, clean_all_def] >>
  irule letrec_recurse_fvs_exp_of >>
  rpt gen_tac >> strip_tac >> rw[]
  >- (
    gvs[fvs_ok_def] >> rw[clean_one_cexp_def] >>
    EVERY_CASE_TAC >> gvs[fvs_ok_def] >>
    imp_res_tac fvs_ok_imp >> gvs[fv_set_ok_def, get_info_def] >>
    rw[] >> eq_tac >> rw[] >> gvs[] >>
    CCONTR_TAC >> gvs[] >>
    qpat_x_assum `∀k. _ ⇔ k ∈ _ r` $ qspec_then `k` assume_tac >> gvs[]
    ) >>
  rw[clean_one_def, clean_one_cexp_def, exp_of_def] >> gvs[]
  >- (
    irule FALSITY >>
    gvs[DISJOINT_ALT, MAP_MAP_o, combinTheory.o_DEF,
        LAMBDA_PROD, GSYM FST_THM, fvs_ok_def] >>
    imp_res_tac fvs_ok_imp >> gvs[fv_set_ok_def] >>
    gvs[MEM_MAP, PULL_EXISTS, EXISTS_PROD, get_info_def] >>
    gvs[EVERY_MAP, EVERY_MEM] >>
    first_x_assum drule >> simp[] >>
    first_x_assum $ qspec_then `x` assume_tac >> gvs[freevars_exp_of]
    )
  >- (
    irule FALSITY >>
    gvs[DISJOINT_ALT, MAP_MAP_o, combinTheory.o_DEF,
        LAMBDA_PROD, GSYM FST_THM, fvs_ok_def, EXISTS_MEM] >>
    pop_assum drule >> simp[] >>
    imp_res_tac fvs_ok_imp >> gvs[fv_set_ok_def, GSYM freevars_exp_of] >>
    first_x_assum $ irule o iffLR >>
    Cases_on `lookup (get_info e) e'` >> gvs[]
    ) >>
  Cases_on `fns` >- gvs[] >>
  simp[] >> PairCases_on `h` >> simp[] >> ntac 2 $ pop_assum kall_tac >>
  reverse $ Cases_on `t` >> rgs[exp_of_def, fvs_ok_def] >>
  imp_res_tac fvs_ok_imp >> pop_assum mp_tac >> simp[fv_set_ok_def] >> strip_tac >>
  Cases_on `lookup (get_info h1) h0` >> rgs[freevars_exp_of, exp_of_def] >>
  IF_CASES_TAC >> gvs[] >>
  first_x_assum $ qspec_then `h0` assume_tac >> gvs[]
QED

Theorem clean_all_cexp_exp_eq:
  ∀ce. exp_of ce ≅ exp_of (clean_all_cexp ce)
Proof
  rw[clean_all_cexp_correct, clean_all_correct]
QED

(********************)

Theorem transform_cexp_correct:
  ∀c ce. exp_of ce ≅ exp_of (transform_cexp c ce)
Proof
  rw[transform_cexp_def] >>
  irule exp_eq_trans >> irule_at (Pos last) clean_all_cexp_exp_eq >>
  irule exp_eq_trans >> irule_at (Pos last) split_all_cexp_exp_eq >>
  simp[distinct_cexp_correct, distinct_letrecs_distinct, distinct_exp_eq]
QED

(********************)

val _ = export_theory();

