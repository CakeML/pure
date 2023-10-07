(*
  Proof for elimination of dead let-bindings
*)
open HolKernel Parse boolLib bossLib dep_rewrite;
open pairTheory listTheory pred_setTheory finite_mapTheory;
open pure_expTheory pure_exp_lemmasTheory pure_evalTheory
     pure_exp_relTheory pure_congruenceTheory
     pure_typingTheory pure_typingPropsTheory;
open pure_dead_letTheory pure_cexpTheory pureLangTheory
     pure_letrecProofTheory pure_letrec_cexpProofTheory
     mlmapTheory pure_varsTheory;

val _ = new_theory "pure_dead_letProof";


(********* exp-level **********)

Inductive dead_let_rel:
[~DeadLet:]
  (dead_let_rel e2 e2' ∧ x ∉ freevars e2'
    ⇒ dead_let_rel (Let x e1 e2) e2') ∧

(* Boilerplate: *)
[~Var:]
  dead_let_rel (Var x) (Var x) ∧
[~App:]
  (dead_let_rel e1 e1' ∧ dead_let_rel e2 e2'
    ⇒ dead_let_rel (App e1 e2) (App e1' e2')) ∧
[~Lam:]
  (dead_let_rel e e'
    ⇒ dead_let_rel (Lam x e) (Lam x e')) ∧
[~Prim:]
  (LIST_REL dead_let_rel es es'
    ⇒ dead_let_rel (Prim op es) (Prim op es')) ∧
[~Letrec:]
  (LIST_REL (λ(f,body) (f',body'). f = f' ∧ dead_let_rel body body') fns fns' ∧
   dead_let_rel e e'
    ⇒ dead_let_rel (Letrec fns e) (Letrec fns' e'))
End

Theorem dead_let_rel_freevars:
  ∀e1 e2. dead_let_rel e1 e2 ⇒ freevars e2 ⊆ freevars e1
Proof
  Induct_on `dead_let_rel` >> rw[] >> gvs[SUBSET_DEF] >>
  gvs[MEM_MAP, MEM_EL, LIST_REL_EL_EQN, PULL_EXISTS, UNCURRY] >> metis_tac[]
QED

Theorem dead_let_rel_refl[simp]:
  ∀e. dead_let_rel e e
Proof
  Induct using freevars_ind >> rw[] >>
  simp[Once dead_let_rel_cases] >>
  gvs[MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN] >>
  rw[] >> rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem dead_let_rel_exp_eq:
  ∀e1 e2. dead_let_rel e1 e2 ⇒ e1 ≅ e2
Proof
  Induct_on `dead_let_rel` >> reverse $ rw[]
  >- (
    irule exp_eq_Letrec_cong >> gvs[LIST_REL_EL_EQN] >>
    simp[Once LIST_EQ_REWRITE, EL_MAP] >>
    rw[] >> first_x_assum drule >> simp[UNCURRY]
    )
  >- (irule exp_eq_Prim_cong >> gvs[LIST_REL_EL_EQN])
  >- (irule exp_eq_Lam_cong >> simp[])
  >- (irule exp_eq_App_cong >> simp[])
  >- simp[exp_eq_refl] >>
  irule exp_eq_trans >> qexists `Let x e1 e2` >> conj_tac
  >- (irule exp_eq_App_cong >> irule_at Any exp_eq_Lam_cong >> simp[exp_eq_refl]) >>
  ntac 2 $ last_x_assum kall_tac >>
  rw[exp_eq_def, bind_def, subst_def] >> IF_CASES_TAC >> gvs[] >>
  irule eval_wh_IMP_app_bisimilarity >> simp[eval_wh_thm] >>
  simp[bind_def, FLOOKUP_SIMP, SF CONJ_ss] >>
  DEP_REWRITE_TAC[subst1_ignore] >>
  drule subst_fdomsub >> disch_then $ qspec_then `f` assume_tac >> gvs[] >>
  qsuff_tac `closed (subst (f \\ x) e2) ∧ closed (subst f e1)` >- gvs[closed_def] >>
  rw[] >> irule IMP_closed_subst >>
  simp[IN_FRANGE_FLOOKUP, PULL_EXISTS, DOMSUB_FLOOKUP_THM] >>
  rw[] >> gvs[SUBSET_DEF] >> res_tac
QED


(********* cexp-level **********)

Theorem get_info_def[simp] = get_info_def;

Theorem neq_some_unit[local]:
  x ≠ SOME () ⇔ x = NONE
Proof
  Cases_on ‘x’ >> simp[]
QED

(* Helper for mlmap theorems *)
fun cjs th =
  let fun generate_list f seed =
          if not (can f seed) then []
          else let val (e, seed') = f seed
               in e :: (generate_list f seed') end
  in generate_list (fn i => (cj i th, i + 1)) 1 end;

Theorem dead_let_imp_rel:
  ∀ce1 ce2. dead_let ce1 = ce2 ⇒
    dead_let_rel (exp_of ce1) (exp_of ce2) ∧
    fvs_ok ce2
Proof
  recInduct dead_let_ind >> rw[dead_let_def] >> gvs[exp_of_def]
  >- ( (* Let *)
    reverse CASE_TAC >> gvs[exp_of_def]
    >- (irule dead_let_rel_App >> irule_at Any dead_let_rel_Lam >> simp[]) >>
    irule dead_let_rel_DeadLet >> simp[] >>
    dxrule fvs_ok_imp >> simp[fv_set_ok_def] >> strip_tac >> gvs[] >>
    first_x_assum $ qspec_then `x` assume_tac >>
    gvs[pure_cexp_lemmasTheory.freevars_exp_of]
    )
  >- ( (* Let fvs_ok *)
    CASE_TAC >> gvs[exp_of_def] >> simp[fvs_ok_def, fv_set_ok_def] >>
    simp[PULL_FORALL] >> gen_tac >>
    DEP_REWRITE_TAC $ lookup_union::lookup_delete::cjs union_thm @ cjs delete_thm >>
    imp_res_tac fvs_ok_imp >> gvs[fv_set_ok_def] >>
    gvs[AllCaseEqs()] >> Cases_on `x = k` >> gvs[] >>
    last_x_assum $ qspec_then `k` assume_tac >> CCONTR_TAC >> gvs[] >>
    metis_tac[neq_some_unit]
    )
  >- ( (* Var fvs_ok *)
    simp[fvs_ok_def, fv_set_ok_def, insert_thm, lookup_insert, EQ_IMP_THM]
    )
  >- ( (* Prim *)
    irule dead_let_rel_Prim >>
    gvs[LIST_REL_EL_EQN, MEM_EL, EL_MAP, PULL_EXISTS]
    )
  >- ( (* Prim fvs_ok *)
    simp[fvs_ok_def, fv_set_ok_def, EVERY_MAP, EVERY_MEM] >>
    simp[PULL_FORALL] >> gen_tac >>
    DEP_REWRITE_TAC $ lookup_list_union_var_set :: cjs map_ok_list_union >>
    simp[EVERY_MAP, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    metis_tac[fvs_ok_imp, fv_set_ok_def]
    )
  >- ( (* App *)
    Induct_on `ces` using SNOC_INDUCT >> rw[] >>
    gvs[MAP_SNOC, Apps_SNOC, SF DNF_ss] >>
    irule dead_let_rel_App >> simp[]
    )
  >- ( (* App fvs_ok *)
    simp[fvs_ok_def, fv_set_ok_def, EVERY_MAP, EVERY_MEM] >>
    simp[PULL_FORALL] >> gen_tac >>
    DEP_REWRITE_TAC $ lookup_list_union_var_set :: cjs map_ok_list_union >>
    simp[EVERY_MAP, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    metis_tac[fvs_ok_imp, fv_set_ok_def]
    )
  >- ( (* Lams *)
    Induct_on `xs` >> rw[Lams_def] >> irule dead_let_rel_Lam >> simp[]
    )
  >- ( (* Lams fvs_ok *)
    simp[fvs_ok_def, fv_set_ok_def] >>
    simp[PULL_FORALL] >> gen_tac >>
    DEP_REWRITE_TAC $ lookup_list_delete :: cjs map_ok_list_delete >>
    gvs[AllCaseEqs()] >> metis_tac[fvs_ok_imp, fv_set_ok_def]
    )
  >- ( (* Letrec *)
    irule dead_let_rel_Letrec >> simp[] >>
    gvs[LIST_REL_EL_EQN, EL_MAP, MEM_EL, PULL_EXISTS] >>
    rw[] >> rpt (pairarg_tac >> gvs[]) >> first_x_assum drule >> simp[]
    )
  >- ( (* Letrec fvs_ok *)
    simp[fvs_ok_def, fv_set_ok_def, EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
    reverse conj_tac >- (rw[] >> first_x_assum drule >> simp[]) >>
    simp[PULL_FORALL] >> gen_tac >>
    DEP_REWRITE_TAC $ lookup_list_delete :: cjs map_ok_list_delete >>
    DEP_REWRITE_TAC $ lookup_list_union_var_set :: cjs map_ok_list_union >>
    simp[MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD, EVERY_MAP, EVERY_MEM] >>
    metis_tac[fvs_ok_imp, fv_set_ok_def]
    )
  >- ( (* Case *)
    qmatch_goalsub_abbrev_tac `(_ $ Seq Fail e1)` >>
    qmatch_goalsub_abbrev_tac `_ _ (_ (Seq Fail e2) _)` >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    qsuff_tac `dead_let_rel e1 e2`
    >- (rw[] >> rpt (irule dead_let_rel_Prim >> simp[])) >>
    unabbrev_all_tac >>
    irule dead_let_rel_App >> irule_at Any dead_let_rel_Lam >> simp[] >>
    Induct_on `css` >> rw[rows_of_def]
    >- (
      CASE_TAC >> gvs[] >> CASE_TAC >> gvs[] >>
      simp[IfDisj_def] >> irule dead_let_rel_Prim >> simp[]
      )
    >- (
      PairCases_on `h` >> rw[rows_of_def] >>
      rpt (irule_at Any dead_let_rel_Prim >> simp[]) >>
      first_x_assum $ irule_at Any >> conj_tac
      >- (rpt gen_tac >> strip_tac >> first_x_assum irule >> metis_tac[]) >>
      rename1 `lets_for _ _ l1` >>
      Induct_on `l1` >> rw[lets_for_def] >>
      PairCases_on `h` >> rw[lets_for_def] >>
      irule dead_let_rel_App >> irule_at Any dead_let_rel_Lam >> simp[]
      )
    )
  >- ( (* Case fvs_ok *)
    simp[fvs_ok_def, fv_set_ok_def, EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
    reverse conj_tac
    >- (
      Cases_on `us` >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
      rw[] >> first_x_assum drule >> gvs[]
      ) >>
    simp[PULL_FORALL] >> gen_tac >>
    DEP_REWRITE_TAC $ lookup_union :: cjs union_thm >>
    DEP_REWRITE_TAC $ lookup_delete :: cjs delete_thm >> gvs[cmp_of_delete] >>
    DEP_REWRITE_TAC $ lookup_list_union_var_set :: cjs map_ok_list_union >>
    simp[MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD, EVERY_MAP, EVERY_MEM] >>
    simp[AC CONJ_ASSOC CONJ_COMM] >>
    assume_tac fvs_ok_imp >> gvs[fv_set_ok_def] >> rpt conj_tac
    >- (Cases_on `us` >> gvs[] >> pairarg_tac >> gvs[])
    >- (Cases_on `us` >> gvs[] >> pairarg_tac >> gvs[])
    >- (
      rpt gen_tac >> strip_tac >>
      DEP_REWRITE_TAC $ lookup_list_delete :: cjs map_ok_list_delete >> metis_tac[]
      ) >>
    Cases_on `x = k` >> gvs[AllCaseEqs(), PULL_EXISTS, EXISTS_PROD, SF DNF_ss] >>
    eq_tac >> rw[] >> gvs[AC DISJ_ASSOC DISJ_COMM]
    >- (
      qpat_x_assum `lookup (list_delete _ _) _ = _` mp_tac >>
      DEP_REWRITE_TAC $ lookup_list_delete :: cjs map_ok_list_delete >> metis_tac[]
      )
    >- (
      rw[DISJ_EQ_IMP] >> goal_assum $ drule_at Any >>
      DEP_REWRITE_TAC $ lookup_list_delete :: cjs map_ok_list_delete >> gvs[] >>
      metis_tac[neq_some_unit]
      )
    >- (
      Cases_on `us` >> gvs[] >> pairarg_tac >> gvs[] >>
      metis_tac[neq_some_unit]
      )
    )
  >- ( (* NestedCase *)
    irule dead_let_rel_App >> irule_at Any dead_let_rel_Lam >> simp[] >>
    pairarg_tac >> gvs[] >> irule dead_let_rel_Prim >> rw[]
    >- (
      pop_assum kall_tac >> Induct_on `binds` >> rw[] >> pairarg_tac >> gvs[] >>
      irule dead_let_rel_App >> irule_at Any dead_let_rel_Lam >> simp[]
      ) >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    Induct_on `pces` >> rw[] >> rpt (pairarg_tac >> gvs[]) >>
    irule dead_let_rel_Prim >> simp[] >> first_x_assum $ irule_at Any >> simp[] >>
    conj_tac >- metis_tac[] >>
    pop_assum kall_tac >> Induct_on `binds'` >> rw[] >> pairarg_tac >> gvs[] >>
    irule dead_let_rel_App >> irule_at Any dead_let_rel_Lam >> simp[]
    )
  >- ( (* NestedCase fvs_ok *)
    simp[fvs_ok_def, fv_set_ok_def, EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
    reverse conj_tac >- (rw[] >> first_x_assum drule >> simp[]) >>
    simp[PULL_FORALL] >> gen_tac >>
    DEP_REWRITE_TAC $ lookup_union :: cjs union_thm >>
    DEP_REWRITE_TAC $ lookup_delete :: cjs delete_thm >> gvs[cmp_of_delete] >>
    DEP_REWRITE_TAC $ lookup_list_union_var_set :: cjs map_ok_list_union >>
    simp[MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD, EVERY_MAP, EVERY_MEM] >>
    DEP_REWRITE_TAC $ lookup_list_delete :: cjs map_ok_list_delete >>
    simp[AC CONJ_ASSOC CONJ_COMM] >>
    assume_tac fvs_ok_imp >> gvs[fv_set_ok_def] >> conj_tac
    >- (
      rw[] >> last_x_assum drule >> rw[] >>
      DEP_REWRITE_TAC $ lookup_list_delete :: cjs map_ok_list_delete >> simp[]
      ) >>
    Cases_on `x = k` >> gvs[AllCaseEqs(), PULL_EXISTS, EXISTS_PROD, SF DNF_ss] >>
    eq_tac >> rw[] >> gvs[AC DISJ_ASSOC DISJ_COMM]
    >- (
      qpat_x_assum `lookup (list_delete _ _) _ = _` mp_tac >>
      DEP_REWRITE_TAC $ lookup_list_delete :: cjs map_ok_list_delete >>
      gvs[AllCaseEqs(), cepat_vars_l_correct]
      )
    >- (
      qpat_x_assum `lookup (list_delete _ _) _ = _` mp_tac >>
      DEP_REWRITE_TAC $ lookup_list_delete :: cjs map_ok_list_delete >>
      gvs[AllCaseEqs(), cepat_vars_l_correct] >> metis_tac[]
      )
    >- (
      rw[DISJ_EQ_IMP] >> pop_assum mp_tac >>
      DEP_REWRITE_TAC $ lookup_list_delete :: cjs map_ok_list_delete >>
      gvs[AllCaseEqs(), cepat_vars_l_correct] >>
      metis_tac[neq_some_unit]
      )
    >- (
      rw[DISJ_EQ_IMP] >> goal_assum $ drule_at Any >>
      DEP_REWRITE_TAC $ lookup_list_delete :: cjs map_ok_list_delete >> gvs[] >>
      gvs[cepat_vars_l_correct] >> metis_tac[neq_some_unit]
      )
    )
QED

Theorem dead_let_cns_arities:
  ∀ce1 ce2. dead_let ce1 = ce2 ⇒ cns_arities ce2 ⊆ cns_arities ce1
Proof
  recInduct dead_let_ind >> rw[dead_let_def] >> gvs[cns_arities_def] >>
  gvs[SUBSET_DEF, MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD]
  >- (CASE_TAC >> gvs[cns_arities_def] >> metis_tac[])
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  Cases_on `us` >> gvs[] >- metis_tac[] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem dead_let_cexp_wf:
  ∀ce1 ce2. dead_let ce1 = ce2 ∧ cexp_wf ce1 ⇒ cexp_wf ce2
Proof
  recInduct dead_let_ind >> rw[dead_let_def] >> gvs[cexp_wf_def] >>
  gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD]
  >- (CASE_TAC >> gvs[cexp_wf_def])
  >- metis_tac[] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, pure_miscTheory.FST_THM] >>
  gvs[rich_listTheory.MAP_FST_funs]
  >- (
    Cases_on `us` >> gvs[] >- metis_tac[] >>
    rpt (pairarg_tac >> gvs[]) >> metis_tac[]
    )
  >- metis_tac[]
QED

Theorem dead_let_NestedCase_free:
  ∀ce1 ce2. dead_let ce1 = ce2 ∧ NestedCase_free ce1 ⇒ NestedCase_free ce2
Proof
  recInduct dead_let_ind >> rw[dead_let_def] >> gvs[] >>
  gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD]
  >- (rpt CASE_TAC >> gvs[])
  >- metis_tac[]
  >- metis_tac[]
  >- (Cases_on `us` >> gvs[] >> Cases_on `x` >> gvs[])
QED

Theorem dead_let_letrecs_distinct:
  ∀ce1 ce2. dead_let ce1 = ce2 ∧ letrecs_distinct (exp_of ce1)
  ⇒ letrecs_distinct (exp_of ce2)
Proof
  recInduct dead_let_ind >> rw[dead_let_def] >>
  gvs[exp_of_def, letrecs_distinct_def, letrecs_distinct_Apps, letrecs_distinct_Lams] >>
  gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD]
  >- (rpt CASE_TAC >> gvs[exp_of_def, letrecs_distinct_def])
  >- (gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> metis_tac[])
  >- (
    gvs[COND_RAND, letrecs_distinct_def] >> gvs[letrecs_distinct_rows_of] >>
    gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
    reverse $ conj_tac >- metis_tac[] >>
    Cases_on `us` >> gvs[] >> pairarg_tac >> gvs[] >>
    last_x_assum mp_tac >> qpat_x_assum `letrecs_distinct (IfDisj _ _ _)` mp_tac >>
    rpt $ pop_assum kall_tac >>
    Induct_on `cn_ars` >> rw[IfDisj_def, Disj_def, letrecs_distinct_def]
    )
  >- (
    pairarg_tac >> gvs[letrecs_distinct_def] >> rw[]
    >- (
      qpat_x_assum `letrecs_distinct _ ⇒ letrecs_distinct _` mp_tac >>
      qpat_x_assum `letrecs_distinct (FOLDR _ _ _)` mp_tac >>
      rpt $ pop_assum kall_tac >>
      Induct_on `binds` >> rw[] >> pairarg_tac >> gvs[letrecs_distinct_def]
      ) >>
    last_x_assum mp_tac >>
    qpat_x_assum `letrecs_distinct (nested_rows _ _)` mp_tac >>
    rpt $ pop_assum kall_tac >>
    Induct_on `pces` >> rw[nested_rows_def] >>
    rpt (pairarg_tac >> gvs[]) >> gvs[letrecs_distinct_def, SF DNF_ss] >>
    last_x_assum drule >> simp[] >> strip_tac >>
    qpat_x_assum `letrecs_distinct _ ⇒ letrecs_distinct _` mp_tac >>
    qpat_x_assum `letrecs_distinct (FOLDR _ _ _)` mp_tac >>
    rpt $ pop_assum kall_tac >>
    Induct_on `binds` >> rw[] >> pairarg_tac >> gvs[letrecs_distinct_def]
    )
QED


(********** typing **********)

Theorem dead_let_preserves_typing:
  ∀ns ce db st env t.
    type_tcexp ns db st env (tcexp_of ce) t
  ⇒ type_tcexp ns db st env (tcexp_of (dead_let ce)) t
Proof
  gen_tac >> recInduct freevars_cexp_ind >> rpt conj_tac >>
  simp[dead_let_def, pure_tcexpTheory.tcexp_of_def] >>
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
    reverse CASE_TAC >> gvs[pure_tcexpTheory.tcexp_of_def]
    >- (
      once_rewrite_tac[type_tcexp_cases] >> rw[] >>
      rpt $ first_x_assum $ irule_at Any >> simp[]
      ) >>
    rw[Once type_tcexp_cases] >> first_x_assum $ dxrule_then assume_tac >>
    irule type_tcexp_env_extensional >> goal_assum $ drule_at Any >> rw[] >>
    irule FALSITY >>
    imp_res_tac $ SRULE [] type_tcexp_NestedCase_free >>
    gvs[pure_tcexp_lemmasTheory.freevars_tcexp_of] >>
    qspec_then `e2` assume_tac $ cj 2 dead_let_imp_rel >> gvs[] >>
    dxrule_then assume_tac fvs_ok_imp >> gvs[fv_set_ok_def] >>
    pop_assum $ drule o iffRL >> simp[]
    )
  >- (
    simp[LAMBDA_PROD] >> once_rewrite_tac[type_tcexp_cases] >> rw[] >>
    qexists `schemes` >> rw[] >> gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    gvs[LIST_REL_EL_EQN, EL_MAP,  MEM_EL, PULL_EXISTS] >> rw[] >>
    rpt (pairarg_tac >> gvs[]) >>
    first_x_assum drule >> simp[] >> strip_tac >>
    last_x_assum drule >> simp[]
    )
  >- (
    simp[LAMBDA_PROD, optionTheory.OPTION_MAP_COMPOSE, combinTheory.o_DEF] >>
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


(********* top-level **********)

Theorem dead_let_correct:
  ∀ce. exp_of ce ≅ exp_of (dead_let ce) ∧
       (closed $ exp_of ce ⇒ closed $ exp_of (dead_let ce)) ∧
       cns_arities (dead_let ce) ⊆ cns_arities ce ∧
       (cexp_wf ce ⇒ cexp_wf (dead_let ce)) ∧
       (letrecs_distinct (exp_of ce) ⇒ letrecs_distinct (exp_of (dead_let ce))) ∧
       (NestedCase_free ce ⇒ NestedCase_free (dead_let ce))
Proof
  gen_tac >>
  qspec_then `ce` assume_tac dead_let_imp_rel >> gvs[] >>
  qspec_then `ce` assume_tac dead_let_cns_arities >> gvs[] >>
  qspec_then `ce` assume_tac dead_let_cexp_wf >> gvs[] >>
  qspec_then `ce` assume_tac dead_let_NestedCase_free >> gvs[] >>
  qspec_then `ce` assume_tac dead_let_letrecs_distinct >> gvs[] >>
  drule dead_let_rel_exp_eq >> rw[] >>
  drule dead_let_rel_freevars >> gvs[closed_def, SUBSET_DEF, EXTENSION]
QED


(**********)

val _ = export_theory();
