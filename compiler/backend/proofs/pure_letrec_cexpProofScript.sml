(*
   Verification of pure_letrec_cexp
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open listTheory pairTheory alistTheory pred_setTheory
     sptreeTheory topological_sortTheory;
open pure_miscTheory pure_expTheory pure_cexpTheory
     pure_letrec_cexpTheory pure_letrecTheory pure_letrecProofTheory
     pure_exp_lemmasTheory pure_cexp_lemmasTheory pure_congruenceTheory;

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
    )
  >- (
    rw[letrec_recurse_rows_of] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> AP_TERM_TAC >>
    rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
    last_x_assum irule >> simp[] >> goal_assum drule
    )
QED

(********************)

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

Triviality exp_of_makeLetrecs_cexp:
  ∀fns.
    exp_of (make_Letrecs_cexp c fns e) =
      make_Letrecs (MAP (MAP (λ(fn,e). (fn,exp_of e))) fns) (exp_of e)
Proof
  Induct >> rw[make_Letrecs_def, make_Letrecs_cexp_def, exp_of_def]
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

Theorem MAPi_EQ_l:
  ∀l1 l2 f.
    LENGTH l1 = LENGTH l2 ∧
    (∀n. n < LENGTH l1 ⇒ f n (EL n l1) = f n (EL n l2))
  ⇒ MAPi f l1 = MAPi f l2
Proof
  Induct >> rw[] >> Cases_on `l2` >> gvs[] >> rw[]
  >- (first_x_assum $ qspec_then `0` mp_tac >> simp[]) >>
  first_x_assum irule >> simp[] >> rw[] >>
  first_x_assum $ qspec_then `SUC n` mp_tac >> simp[]
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
  irule MAPi_EQ_l >> rw[] >>
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

Triviality top_sort_any_sets:
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
  irule letrec_recurse_exp_of >> simp[exp_of_def, exp_of_makeLetrecs_cexp] >>
  rw[] >> AP_THM_TAC >> AP_TERM_TAC >>
  rw[split_one_def, split_one_cexp_def] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  qmatch_goalsub_abbrev_tac `_ (top_sort_any a) = _ (top_sort_any b)` >>
  `top_sort_any a = top_sort_any b` by (
    irule top_sort_set_eq >> unabbrev_all_tac >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    rw[LIST_REL_EL_EQN, EL_MAP] >> Cases_on `EL n fns` >> simp[] >>
    simp[GSYM freevars_equiv, GSYM freevars_cexp_equiv, freevars_exp_of]) >>
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

Theorem clean_all_cexp_correct:
  ∀ce. exp_of (clean_all_cexp ce) = clean_all (exp_of ce)
Proof
  rw[clean_all_cexp_def, clean_all_def] >>
  irule letrec_recurse_exp_of >>
  rw[clean_one_def, clean_one_cexp_def, exp_of_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, freevars_exp_of] >>
  Cases_on `fns` >- gvs[] >>
  simp[] >> PairCases_on `h` >> simp[freevars_exp_of] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `t` >> simp[exp_of_def] >> pairarg_tac >> simp[exp_of_def]
QED

Theorem clean_all_cexp_exp_eq:
  ∀ce. exp_of ce ≅ exp_of (clean_all_cexp ce)
Proof
  rw[clean_all_cexp_correct, clean_all_correct]
QED

Theorem simplify_cexp_correct:
  ∀ce. exp_of ce ≅ exp_of (simplify_cexp ce)
Proof
  rw[simplify_cexp_def] >>
  irule exp_eq_trans >> irule_at (Pos last) clean_all_cexp_exp_eq >>
  irule exp_eq_trans >> irule_at (Pos last) split_all_cexp_exp_eq >>
  simp[distinct_cexp_correct, distinct_letrecs_distinct, distinct_exp_eq]
QED

(********************)

val _ = export_theory();

