(* Relating the itree- and FFI state-based CakeML semantics *)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open optionTheory relationTheory pairTheory listTheory arithmeticTheory;
open lem_pervasives_extraTheory libTheory namespaceTheory astTheory
     ffiTheory semanticPrimitivesTheory smallStepTheory evaluatePropsTheory;
open io_treeTheory pure_miscTheory
     cakeml_semanticsTheory cakeml_semanticsPropsTheory;

val _ = new_theory "cakeml_semanticsProof";


(******************** Useful simplifications ********************)

(* Deliberately no `application_def` here *)
val smallstep_ss = simpLib.named_rewrites "smallstep_ss" [
    smallStepTheory.continue_def,
    smallStepTheory.return_def,
    smallStepTheory.push_def,
    smallStepTheory.e_step_def
    ];

val itree_ss = simpLib.named_rewrites "itree_ss" [
    cakeml_semanticsTheory.continue_def,
    cakeml_semanticsTheory.return_def,
    cakeml_semanticsTheory.push_def,
    cakeml_semanticsTheory.estep_def,
    get_ffi_def
    ];


(******************** Simpler lemmas ********************)

(* Takes 30s *)
Theorem do_app_rel:
  (∀s. op ≠ FFI s) ⇒
  OPTREL (λ(a,b) (c,d). a = c ∧ result_rel b d)
    (do_app st op vs)
    (OPTION_MAP (λ(a,b). (FST a, b)) (do_app (st, ffi) op vs))
Proof
  rw[semanticPrimitivesTheory.do_app_def] >>
  rpt (
    TOP_CASE_TAC >>
    gvs[do_app_def, result_rel_cases, store_alloc_def]
    )
QED

(* Takes 20s *)
Theorem application_rel:
  (∀s. op ≠ FFI s) ∧
  ctxt_rel cs1 cs2 ⇒
  step_result_rel
    (application op env st vs cs1)
    (application op env (st,ffi) vs cs2)
Proof
  rw[] >>
  drule do_app_rel >> disch_then $ qspecl_then [`vs`,`st`,`ffi`] assume_tac >>
  rw[application_def, cml_application_thm]
  >- (CASE_TAC >> gvs[step_result_rel_cases] >> CASE_TAC >> gvs[]) >>
  Cases_on `do_app (st,ffi) op vs` >> gvs[] >>
  Cases_on `do_app st op vs` >> gvs[]
  >- (rpt (TOP_CASE_TAC >> gvs[step_result_rel_cases])) >>
  gvs[FST_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[result_rel_cases] >>
  rpt (
    TOP_CASE_TAC >>
    gvs[step_result_rel_cases, SF smallstep_ss, SF itree_ss,
        ctxt_rel_def, ctxt_frame_rel_cases]
    )
QED

Theorem application_rel_FFI_type_error:
  application (FFI s) env st vs cs1 = Etype_error ⇔
  application (FFI s) env (st, ffi) vs cs2 = Eabort Rtype_error
Proof
  rw[application_def, cml_application_thm] >>
  simp[semanticPrimitivesTheory.do_app_def] >>
  every_case_tac >> gvs[SF smallstep_ss] >>
  gvs[store_lookup_def, store_assign_def, store_v_same_type_def]
QED

Theorem application_rel_FFI_step:
  application (FFI s) env st vs cs1 = Estep (env, st, Val v, cs1) ⇔
  application (FFI s) env (st, ffi) vs cs2 = Estep (env, (st,ffi), Val v, cs2)
Proof
  rw[application_def, cml_application_thm] >>
  simp[semanticPrimitivesTheory.do_app_def] >>
  every_case_tac >> gvs[SF smallstep_ss] >>
  gvs[call_FFI_def, store_lookup_def, store_assign_def, store_v_same_type_def]
  >- (eq_tac >> rw[] >> metis_tac[LUPDATE_SAME]) >>
  every_case_tac >> gvs[] >> rw[] >> gvs[ffi_state_component_equality]
QED


(******************** Relating non-FFI steps ********************)

Theorem step_result_rel_single:
  ∀ea eb.
    step_result_rel (Estep ea) (Estep eb) ∧
    ¬ is_Effi (estep ea)
  ⇒ step_result_rel (estep ea) (e_step eb) ∧
    ∀ffi. get_ffi (e_step eb) = SOME ffi ⇒ get_ffi (Estep eb) = SOME ffi
Proof
  rpt PairCases >> rename1 `_ (_ (env,st,ev,cs1)) (_ (env',(st',ffi),ev',cs2))` >>
  gvs[e_step_def] >>
  every_case_tac >> gvs[estep_def, step_result_rel_cases] >> strip_tac >>
  gvs[SF smallstep_ss, SF itree_ss, ctxt_rel_def, ctxt_frame_rel_cases, get_ffi_def] >>
  gvs[GSYM ctxt_frame_rel_cases, GSYM step_result_rel_cases]
  >- (
    rename1 `application op _ _ _ _` >>
    reverse $ Cases_on `∃s. op = FFI s` >> gvs[]
    >- (
      reverse $ rw[]
      >- (
        drule application_ffi_unchanged >>
        Cases_on `application op env (st,ffi) [] cs2` >> gvs[get_ffi_def] >>
        PairCases_on `p` >> disch_then drule >> gvs[get_ffi_def]
        )
      >- (
        drule application_rel >> gvs[ctxt_rel_def] >> disch_then drule >>
        disch_then $ qspecl_then [`[]`,`st`,`ffi`,`env`] assume_tac >>
        gvs[step_result_rel_cases, ctxt_rel_def]
        )
      ) >>
    qspecl_then [`[]`,`st`,`s`,`env`,`cs1`]
      assume_tac $ GEN_ALL application_FFI_results >> gvs[] >>
    csimp[] >> gvs[is_Effi_def, get_ffi_def]
    >- metis_tac[application_rel_FFI_type_error] >>
    imp_res_tac application_rel_FFI_step >> simp[get_ffi_def]
    )
  >- gvs[FST_THM, LAMBDA_PROD]
  >- gvs[FST_THM, LAMBDA_PROD] >>
  CASE_TAC >- gvs[continue_def, get_ffi_def] >>
  PairCases_on `h` >> gvs[] >> PairCases_on `x` >> gvs[] >>
  rename1 `ctxt_frame_rel c1 c2` >> rename1 `(c1,env)` >>
  rename1 `LIST_REL _ rest1 rest2` >>
  Cases_on `c1` >> gvs[SF itree_ss, ctxt_frame_rel_cases] >>
  gvs[GSYM ctxt_frame_rel_cases, get_ffi_def]
  >- (EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases])
  >- (
    reverse CASE_TAC >>
    gvs[PULL_EXISTS, EXISTS_PROD, get_ffi_def, SF itree_ss]
    >- simp[ctxt_frame_rel_cases] >>
    rename1 `application op _ _ vs _` >>
    reverse $ Cases_on `∃s. op = FFI s` >> gvs[]
    >- (
      reverse $ rw[]
      >- (
        drule application_ffi_unchanged >>
        Cases_on `application op env (st,ffi) vs rest2` >> gvs[get_ffi_def] >>
        PairCases_on `p` >> disch_then drule >> gvs[get_ffi_def]
        )
      >- (
        drule application_rel >> gvs[ctxt_rel_def] >> disch_then drule >>
        disch_then $ qspecl_then [`vs`,`st`,`ffi`,`env`] assume_tac >>
        gvs[step_result_rel_cases, ctxt_rel_def]
        )
      ) >>
    qspecl_then [`vs`,`st`,`s`,`env`,`rest1`]
      assume_tac $ GEN_ALL application_FFI_results >> gvs[] >>
    csimp[] >> gvs[is_Effi_def, get_ffi_def]
    >- metis_tac[application_rel_FFI_type_error] >>
    imp_res_tac application_rel_FFI_step >> gvs[get_ffi_def]
    )
  >- (EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases])
  >- (EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases])
  >- (EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases])
  >- (
    CASE_TAC >> gvs[PULL_EXISTS, EXISTS_PROD, get_ffi_def, SF itree_ss]
    >- simp[ctxt_frame_rel_cases] >>
    CASE_TAC >>  gvs[SF itree_ss] >>
    EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases]
    )
  >- (
    TOP_CASE_TAC >> gvs[SF itree_ss] >>
    EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases]
    )
QED

Theorem step_result_rel_n:
  ∀n ea eb.
    step_result_rel ea eb ∧
    ¬ is_Effi (step_n n ea)
  ⇒ step_result_rel (step_n n ea) (step_n_cml n eb) ∧
    ∀ffi. get_ffi (step_n_cml n eb) = SOME ffi ⇒ get_ffi eb = SOME ffi
Proof
  Induct >- simp[step_n_def, step_n_cml_def] >>
  simp[step_n_alt_def, step_n_cml_alt_def] >>
  rpt gen_tac >> strip_tac >>
  last_x_assum drule >> impl_keep_tac
  >- (CCONTR_TAC >> gvs[is_Effi_def]) >>
  strip_tac >>
  Cases_on `step_n n ea` >> imp_res_tac step_result_rel_cases >> gvs[get_ffi_def] >>
  simp[GSYM step_result_rel_cases] >>
  qmatch_goalsub_abbrev_tac `step_result_rel (estep ea) (e_step eb)` >>
  qspecl_then [`ea`,`eb`] assume_tac step_result_rel_single >> gvs[] >>
  unabbrev_all_tac >> gvs[get_ffi_def]
QED


(******************** Relating FFI steps ********************)

Theorem application_rel_FFI:
  application (FFI s) env st vs cs1 = Effi s conf ws lnum env st cs1 ⇒
    store_lookup lnum st = SOME $ W8array ws ∧
    application (FFI s) env (st, ffi) vs cs2 =
      case ffi.oracle s ffi.ffi_state conf ws of
      | Oracle_return ffi' ws' =>
          if LENGTH ws' ≠ LENGTH ws then
            Eabort $ Rffi_error $ Final_event s conf ws FFI_failed
          else
            Estep (env,
              (LUPDATE (W8array ws') lnum st,
               ffi with <|
                  ffi_state := ffi';
                  io_events := ffi.io_events ++ [IO_event s conf (ZIP (ws,ws'))]
                  |>),
              Val $ Conv NONE [], cs2)
      | Oracle_final outcome =>
          Eabort $ Rffi_error $ Final_event s conf ws outcome
Proof
  simp[application_def] >>
  ntac 6 (TOP_CASE_TAC >> gvs[]) >>
  gvs[store_lookup_def] >>
  ntac 2 (TOP_CASE_TAC >> gvs[]) >> rw[] >> gvs[] >>
  simp[smallStepTheory.application_def, semanticPrimitivesTheory.do_app_def] >>
  simp[store_lookup_def, call_FFI_def] >>
  qmatch_goalsub_abbrev_tac `foo l` >>
  reverse $ Cases_on `foo l` >> gvs[] >>
  IF_CASES_TAC >> gvs[store_assign_def, store_v_same_type_def, SF smallstep_ss]
QED

Theorem application_rel_FFI':
  application (FFI s) env (st, ffi) vs cs2 ≠ Eabort Rtype_error ⇒
  (∃conf lnum ws.
    vs = [Litv $ StrLit conf; Loc lnum] ∧
    store_lookup lnum st = SOME $ W8array ws ∧
    application (FFI s) env st vs cs1 =
      Effi s (MAP (λc. n2w $ ORD c) (EXPLODE conf)) ws lnum env st cs1) ∨
  (s = "" ∧
  application (FFI s) env st vs cs1 = Estep (env, st, Val $ Conv NONE [], cs1))
Proof
  rw[smallStepTheory.application_def, semanticPrimitivesTheory.do_app_def] >>
  every_case_tac >> gvs[application_def] >>
  IF_CASES_TAC >> gvs[]
QED

Theorem e_step_ffi_changed:
  e_step (env, (st, ffi), ev, cs2) = Estep (env', (st', ffi'), ev', cs2') ∧
  ffi ≠ ffi' ∧
  ctxt_rel cs1 cs2 ⇒
  ∃ s conf lnum ccs ws.
    ev = Val (Litv (StrLit conf)) ∧
    cs1 = (Capp (FFI s) [Loc lnum] [], env') :: ccs ∧
    store_lookup lnum st = SOME (W8array ws) ∧
    estep (env, st, ev, cs1) =
      Effi s (MAP (λc. n2w $ ORD c) (EXPLODE conf)) ws lnum env' st ccs
Proof
  rw[] >> drule_all e_step_ffi_changed >> rw[] >>
  gvs[ctxt_rel_def] >> pairarg_tac >> gvs[ctxt_frame_rel_cases] >>
  simp[estep_def, SF itree_ss, application_thm]
QED

Theorem step_result_rel_single_FFI:
  ∀ea eb.
    step_result_rel (Estep ea) (Estep eb) ∧
    estep ea = Effi s ws1 ws2 lnum env' st' cs1'
  ⇒ ∃ffi.
      get_ffi (Estep eb) = SOME ffi ∧
      ((∃ffi'. get_ffi (e_step eb) = SOME ffi' ∧ ffi' ≠ ffi)  ∨
       (∃outcome. e_step eb = Eabort (Rffi_error (Final_event s ws1 ws2 outcome))))
Proof
  rpt PairCases >> gvs[step_result_rel_cases, e_step_def] >> rw[] >>
  rename1 `estep (env,st,ev,cs1)` >> rename1 `Estep ((env,(st,ffi),ev,cs2))` >>
  gvs[get_ffi_def] >>
  every_case_tac >> gvs[estep_def, step_result_rel_cases, FST_THM, LAMBDA_PROD] >>
  gvs[SF smallstep_ss, SF itree_ss, ctxt_rel_def, ctxt_frame_rel_cases, get_ffi_def]
  >- (imp_res_tac application_eq_Effi_fields >> gvs[application_def, SF itree_ss]) >>
  TOP_CASE_TAC >> gvs[SF itree_ss] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[get_ffi_def, SF itree_ss]
  >- (EVERY_CASE_TAC >> gvs[])
  >- (
    CASE_TAC >> gvs[SF itree_ss, GSYM ctxt_frame_rel_cases] >>
    imp_res_tac application_eq_Effi_fields >> gvs[] >>
    rename [`LIST_REL _ cs1 cs2`, `application _ env`] >>
    drule application_rel_FFI >>
    disch_then $ qspecl_then [`ffi`,`cs2`] assume_tac >> gvs[] >>
    every_case_tac >> gvs[get_ffi_def] >>
    gvs[ffi_state_component_equality]
    )
  >- (EVERY_CASE_TAC >> gvs[])
  >- (EVERY_CASE_TAC >> gvs[])
  >- (EVERY_CASE_TAC >> gvs[])
  >- (rpt (CASE_TAC >> gvs[SF itree_ss]))
  >- (rpt (CASE_TAC >> gvs[SF itree_ss]))
QED

Theorem step_result_rel_single_FFI':
  (∀ffi. get_ffi (e_step e2) = SOME ffi ⇒ get_ffi (Estep e2) = SOME ffi) ∧
  (∀a. e_step e2 ≠ Eabort $ Rffi_error a) ∧
  step_result_rel (Estep e1) (Estep e2)
  ⇒ step_result_rel (estep e1) (e_step e2)
Proof
  rw[] >> drule step_result_rel_single >> rw[] >>
  pop_assum irule >>
  CCONTR_TAC >> gvs[is_Effi_def] >>
  drule_all step_result_rel_single_FFI >>
  rw[] >> gvs[]
QED

Theorem step_result_rel_n':
  ∀n e1 e2.
    get_ffi (step_n_cml n (Estep e2)) = get_ffi (Estep e2) ∧
    step_result_rel (Estep e1) (Estep e2)
  ⇒ step_result_rel (step_n n (Estep e1)) (step_n_cml n (Estep e2))
Proof
  Induct >- rw[step_n_def, step_n_cml_def] >> rw[] >>
  `step_result_rel (step_n n (Estep e1)) (step_n_cml n (Estep e2))` by (
    last_x_assum irule >> simp[] >>
    qspecl_then [`SUC n`,`Estep e2`] mp_tac step_n_cml_preserved_FFI >>
    Cases_on `step_n_cml (SUC n) (Estep e2)` >> gvs[get_ffi_def] >>
    PairCases_on `e2` >> gvs[get_ffi_def]) >>
  simp[step_n_alt_def, step_n_cml_alt_def] >>
  gvs[step_result_rel_cases] >>
  gvs[GSYM step_result_rel_cases] >>
  qspecl_then [`SUC n`,`Estep (env',(st',ffi'),ev',cs2')`]
    mp_tac step_n_cml_preserved_FFI >>
  gvs[step_n_cml_alt_def] >>
  Cases_on `e_step (env,(st,ffi),ev,cs2)` >> gvs[get_ffi_def] >>
  disch_then $ qspec_then `n` mp_tac >> simp[get_ffi_def] >> rw[] >> gvs[] >>
  first_assum $ once_rewrite_tac o single o GSYM >>
  irule step_result_rel_single_FFI' >>
  simp[get_ffi_def, step_result_rel_cases]
QED


(******************** interp ********************)

Theorem interp_Ret_Termination:
  ctxt_rel cs1 cs2 ⇒
  (
    interp (Estep (env, st, Exp e, cs1)) = Ret Termination ⇔
    (∃v st'. small_eval env (st, ffi) e cs2 ((st', ffi), Rval v)) ∨
    (∃v st'. small_eval env (st, ffi) e cs2 ((st', ffi), Rerr $ Rraise v))
  )
Proof
  rw[Once interp] >> eq_tac >> rw[]
  >- (
    every_case_tac >> gvs[io_distinct, step_until_halt_def] >>
    pop_assum mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >> gvs[] >>
    reverse every_case_tac >> gvs[is_halt_def] >>
    Induct_on `x` >> gvs[step_n_alt_def] >>
    reverse every_case_tac >> gvs[] >- metis_tac[] >- metis_tac[] >>
    rw[] >> PairCases_on `p` >> gvs[estep_to_Edone]
    >- (
      disj1_tac >>
      rw[small_eval_eq_step_to_halt_cml, step_to_halt_cml_def] >>
      qspecl_then [`x`,`Estep (env,st,Exp e,cs1)`,`Estep (env,(st,ffi),Exp e,cs2)`]
        assume_tac step_result_rel_n >>
      gvs[step_result_rel_cases, is_Effi_def, ctxt_rel_def, get_ffi_def] >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[] >> gvs[]
      >- (qexists_tac `x` >> simp[is_halt_cml_def]) >>
      qspecl_then [`x`,`x'`] assume_tac is_halt_cml_step_n_cml_eq >>
      pop_assum $ drule_at Any >> gvs[is_halt_cml_def] >>
      disch_then $ assume_tac o GSYM >> gvs[]
      )
    >- (
      disj2_tac >>
      rw[small_eval_eq_step_to_halt_cml, step_to_halt_cml_def] >>
      qspecl_then [`x`,`Estep (env,st,Exp e,cs1)`,`Estep (env,(st,ffi),Exp e,cs2)`]
        assume_tac step_result_rel_n >>
      gvs[step_result_rel_cases, is_Effi_def, ctxt_rel_def, get_ffi_def] >>
      pairarg_tac >> gvs[ctxt_frame_rel_cases] >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[] >> gvs[]
      >- (qexists_tac `x` >> simp[is_halt_cml_def]) >>
      qspecl_then [`x`,`x'`] assume_tac is_halt_cml_step_n_cml_eq >>
      pop_assum $ drule_at Any >> gvs[is_halt_cml_def] >>
      disch_then $ assume_tac o GSYM >> gvs[]
      )
    )
  >- (
    gvs[small_eval_eq_step_to_halt_cml, step_to_halt_cml_def] >>
    pop_assum mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >> gvs[] >>
    qspecl_then [`x`,`Estep (env,st,Exp e,cs1)`,`Estep (env,(st,ffi),Exp e,cs2)`]
      assume_tac step_result_rel_n >>
    gvs[step_result_rel_cases, get_ffi_def, ctxt_rel_def] >>
    pop_assum mp_tac >> impl_tac
    >- (
      irule step_result_rel_not_Effi >>
      irule_at Any step_result_rel_n' >>
      qexists_tac `(env,(st,ffi),Exp e,cs2)` >>
      simp[get_ffi_def, step_result_rel_cases, ctxt_rel_def]
      ) >>
    rw[Once cml_io_unfold_err, step_until_halt_def] >>
    DEEP_INTRO_TAC some_intro >> reverse $ rw[] >> gvs[]
    >- (
      qexists_tac `SUC x` >>
      simp[step_n_alt_def, estep_def, SF itree_ss, is_halt_def]
      ) >>
    rename1 `step_n y` >>
    `step_n y (Estep (env,st,Exp e,cs1)) =
      step_n (SUC x) (Estep (env,st,Exp e,cs1))` by (
      irule is_halt_step_n_eq >>
      simp[step_n_alt_def, estep_def, SF itree_ss, is_halt_def]) >>
    simp[step_n_alt_def, estep_def, SF itree_ss, is_halt_def]
    )
  >- (
    gvs[small_eval_eq_step_to_halt_cml, step_to_halt_cml_def] >>
    pop_assum mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >> gvs[] >>
    qspecl_then [`x`,`Estep (env,st,Exp e,cs1)`,`Estep (env,(st,ffi),Exp e,cs2)`]
      assume_tac step_result_rel_n >>
    gvs[step_result_rel_cases, get_ffi_def, ctxt_rel_def] >>
    gvs[PULL_EXISTS, EXISTS_PROD, ctxt_frame_rel_cases] >>
    gvs[GSYM ctxt_frame_rel_cases] >>
    pop_assum mp_tac >> impl_tac
    >- (
      irule step_result_rel_not_Effi >>
      irule_at Any step_result_rel_n' >>
      qexists_tac `(env,(st,ffi),Exp e,cs2)` >>
      simp[get_ffi_def, step_result_rel_cases, ctxt_rel_def]
      ) >>
    rw[Once cml_io_unfold_err, step_until_halt_def] >>
    DEEP_INTRO_TAC some_intro >> reverse $ rw[] >> gvs[]
    >- (
      qexists_tac `SUC x` >>
      simp[step_n_alt_def, estep_def, SF itree_ss, is_halt_def]
      ) >>
    rename1 `step_n y` >>
    `step_n y (Estep (env,st,Exp e,cs1)) =
      step_n (SUC x) (Estep (env,st,Exp e,cs1))` by (
      irule is_halt_step_n_eq >>
      simp[step_n_alt_def, estep_def, SF itree_ss, is_halt_def]) >>
    simp[step_n_alt_def, estep_def, SF itree_ss, is_halt_def]
    )
QED

Theorem interp_Ret_Error:
  ctxt_rel cs1 cs2 ⇒
  (
    interp (Estep (env, st, Exp e, cs1)) = Ret Error ⇔
    ∃st'. small_eval env (st, ffi) e cs2 ((st', ffi), Rerr $ Rabort Rtype_error)
  )
Proof
  rw[Once interp] >> eq_tac >> rw[]
  >- (
    every_case_tac >> gvs[io_distinct, step_until_halt_def] >>
    pop_assum mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >> gvs[] >>
    every_case_tac >> gvs[is_halt_def] >>
    rw[small_eval_def, e_step_reln_eq_step_n_cml, PULL_EXISTS] >>
    ntac 2 $ pop_assum mp_tac >>
    map_every qid_spec_tac [`cs1`,`cs2`,`env`,`st`,`e`,`ffi`,`x`] >>
    Induct >> rw[step_n_alt_def] >>
    reverse every_case_tac >> gvs[]
    >- (last_x_assum irule >> goal_assum drule >> simp[]) >>
    last_x_assum kall_tac >>
    qspecl_then [`x`,`Estep (env,st,Exp e,cs1)`] mp_tac step_result_rel_n >>
    simp[step_result_rel_cases, PULL_EXISTS, is_Effi_def] >>
    disch_then drule >>
    disch_then $ qspec_then `ffi` assume_tac >> gvs[get_ffi_def] >>
    goal_assum drule >>
    qspec_then `(env',st',ev,cs1')` mp_tac step_result_rel_single >>
    gvs[step_result_rel_cases, is_Effi_def]
    )
  >- (
    gvs[small_eval_def, e_step_reln_eq_step_n_cml] >>
    qspecl_then [`n`,`Estep (env,st,Exp e,cs1)`,`Estep (env,(st,ffi),Exp e,cs2)`]
      assume_tac step_result_rel_n >>
    gvs[step_result_rel_cases, get_ffi_def, ctxt_rel_def] >>
    pop_assum mp_tac >> impl_tac
    >- (
      irule step_result_rel_not_Effi >>
      irule_at Any step_result_rel_n' >>
      qexists_tac `(env,(st,ffi),Exp e,cs2)` >>
      simp[get_ffi_def, step_result_rel_cases, ctxt_rel_def]
      ) >>
    rw[Once cml_io_unfold_err, step_until_halt_def] >>
    `estep (env',st',e',cs1') = Etype_error` by (
      qspec_then `(env',st',e',cs1')` mp_tac step_result_rel_single >>
      gvs[step_result_rel_cases, is_Effi_def, PULL_EXISTS, ctxt_rel_def] >>
      disch_then drule >> disch_then $ qspec_then `ffi` assume_tac >>
      gvs[get_ffi_def] >> pop_assum mp_tac >> impl_tac >> rw[] >> gvs[is_halt_def] >>
      qsuff_tac `¬is_Effi (estep (env',st',e',cs1'))` >- gvs[is_Effi_def] >>
      irule step_result_rel_not_Effi >>
      irule_at Any step_result_rel_single_FFI' >>
      simp[step_result_rel_cases, PULL_EXISTS, ctxt_rel_def] >>
      goal_assum $ drule_at Any >> qexists_tac `ffi` >> simp[get_ffi_def]) >>
    DEEP_INTRO_TAC some_intro >> reverse $ rw[] >> gvs[]
    >- (
      qexists_tac `SUC n` >> simp[step_n_alt_def, is_halt_def]
      ) >>
    rename1 `step_n y` >>
    `step_n y (Estep (env,st,Exp e,cs1)) =
      step_n (SUC n) (Estep (env,st,Exp e,cs1))` by (
      irule is_halt_step_n_eq >> simp[step_n_alt_def, is_halt_def]) >>
    simp[step_n_alt_def]
    )
QED

Theorem interp_Ret_SilentDivergence:
  ctxt_rel cs1 cs2 ⇒
  (
    interp (Estep (env, st, Exp e, cs1)) = Ret SilentDivergence ⇔
    ∀n. ∃st2.
      step_n_cml n (Estep (env, (st, ffi), Exp e, cs2)) = Estep st2 ∧
      ¬ is_halt_cml (Estep st2) ∧
      get_ffi (Estep st2) = SOME ffi
  )
Proof
  rw[Once interp] >> eq_tac >> rw[]
  >- (
    every_case_tac >> gvs[io_distinct, step_until_halt_def] >>
    every_case_tac >> gvs[] >>
    pop_assum mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >> gvs[] >>
    qspecl_then [`n`,`Estep (env,st,Exp e,cs1)`] mp_tac step_result_rel_n >>
    simp[step_result_rel_cases, PULL_EXISTS] >> disch_then drule >>
    disch_then $ qspec_then `ffi` mp_tac >>
    impl_tac >> gvs[]
    >- (
      pop_assum $ qspec_then `n` assume_tac >>
      gvs[is_Effi_def] >> CCONTR_TAC >> gvs[is_halt_def]
      ) >>
    reverse $ strip_tac >> gvs[get_ffi_def]
    >- metis_tac[is_halt_def] >- metis_tac[is_halt_def] >>
    Cases_on `ev` >> simp[is_halt_cml_def] >>
    Cases_on `cs2''` >> gvs[is_halt_cml_def, ctxt_rel_def]
    >- (
      first_x_assum $ qspec_then `SUC n` mp_tac >>
      simp[step_n_alt_def, estep_def, SF itree_ss, is_halt_def]
      ) >>
    PairCases_on `h` >> Cases_on `h0` >> gvs[is_halt_cml_def] >>
    Cases_on `t` >> gvs[is_halt_cml_def] >>
    pairarg_tac >> gvs[ctxt_frame_rel_cases] >>
    first_x_assum $ qspec_then `SUC n` mp_tac >>
    simp[step_n_alt_def, estep_def, SF itree_ss, is_halt_def]
    )
  >- (
    rw[step_until_halt_def] >>
    DEEP_INTRO_TAC some_intro >> rw[] >> gvs[] >>
    irule FALSITY >> pop_assum mp_tac >> simp[] >>
    pop_assum $ qspec_then `x` assume_tac >> gvs[] >>
    PairCases_on `st2` >> gvs[get_ffi_def] >>
    rename1 `¬is_halt_cml (Estep (env',(st',_),ev,cs2'))` >>
    qspecl_then [`x`,`(env,st,Exp e,cs1)`,`(env,(st,ffi),Exp e,cs2)`]
      assume_tac step_result_rel_n' >>
    gvs[step_result_rel_cases, get_ffi_def] >>
    simp[is_halt_def]
    )
QED

val _ = export_theory();

