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
    store_lookup lnum st = SOME $ W8array ws ∧ s ≠ "" ∧
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

Theorem e_step_ffi_changed_estep_to_Effi:
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

Theorem step_result_rel_single_FFI_strong:
  ∀ea eb.
    step_result_rel (Estep ea) (Estep eb) ∧
    estep ea = Effi s conf ws lnum env st cs1
  ⇒ ∃env' ffi conf'.
      conf = MAP (λc. n2w (ORD c)) (EXPLODE conf') ∧
      ea = (env',st, Val (Litv $ StrLit conf'),
            (Capp (FFI s) [Loc lnum] [], env)::cs1) ∧
      store_lookup lnum st = SOME (W8array ws) ∧ s ≠ "" ∧
      get_ffi (Estep eb) = SOME ffi ∧
      e_step eb =
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
                Val $ Conv NONE [], (TL $ SND $ SND $ SND eb))
        | Oracle_final outcome =>
            Eabort $ Rffi_error $ Final_event s conf ws outcome
Proof
  rpt PairCases >> gvs[step_result_rel_cases] >> rw[] >>
  rename1 `estep (env0,st0,ev0,cs10)` >>
  Cases_on `ev0` >> gvs[estep_def]
  >- (
    Cases_on `e` >> gvs[estep_def, SF itree_ss] >>
    every_case_tac >> gvs[] >>
    imp_res_tac application_eq_Effi_fields >> gvs[]
    ) >>
  Cases_on `cs10` >> gvs[SF itree_ss] >>
  PairCases_on `h` >> Cases_on `h0` >> gvs[SF itree_ss]
  >- (every_case_tac >> gvs[])
  >- (
    rename1 `Capp _ _ es` >> Cases_on `es` >> gvs[SF itree_ss] >>
    imp_res_tac application_eq_Effi_fields >> gvs[] >>
    drule application_rel_FFI >>
    disch_then $ qspecl_then [`eb2`,`TL eb4`] assume_tac >> gvs[] >>
    gvs[ctxt_rel_def] >> pairarg_tac >> gvs[ctxt_frame_rel_cases] >>
    simp[e_step_def, SF smallstep_ss]
    )
  >- (every_case_tac >> gvs[])
  >- (every_case_tac >> gvs[])
  >- (every_case_tac >> gvs[])
  >- (
    rename1 `Cmat l` >> Cases_on `l` >> gvs[SF itree_ss] >>
    PairCases_on `h` >> gvs[SF itree_ss] >>
    every_case_tac >> gvs[]
    )
  >- (
    rename1 `Ccon _ _ ls` >> Cases_on `ls` >> gvs[SF itree_ss] >>
    every_case_tac >> gvs[]
    )
QED

Theorem step_result_rel_single_FFI_error:
  ∀ea eb.
    step_result_rel (Estep ea) (Estep eb) ∧
    e_step eb = Eabort (Rffi_error (Final_event s conf ws outcome))
  ⇒ ∃lnum env. estep ea =
    Effi s conf ws lnum env (FST $ SND ea) (TL $ SND $ SND $ SND ea)
Proof
  rpt $ PairCases >> rw[e_step_def] >>
  every_case_tac >> gvs[SF smallstep_ss]
  >- (
    gvs[cml_application_thm] >>
    every_case_tac >> gvs[SF smallstep_ss] >>
    gvs[semanticPrimitivesTheory.do_app_def]
    ) >>
  FULL_CASE_TAC >> gvs[] >>
  every_case_tac >> gvs[cml_application_thm] >>
  every_case_tac >> gvs[SF smallstep_ss] >>
  gvs[semanticPrimitivesPropsTheory.do_app_cases] >>
  gvs[step_result_rel_cases, ctxt_rel_def] >>
  pairarg_tac >> gvs[ctxt_frame_rel_cases] >>
  gvs[SF itree_ss, application_def, call_FFI_def] >>
  every_case_tac >> gvs[store_lookup_def]
QED

Theorem step_result_rel_single':
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
  irule step_result_rel_single' >>
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
      irule_at Any step_result_rel_single' >>
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

Theorem interp_Div:
  ctxt_rel cs1 cs2 ⇒
  (
    interp (Estep (env, st, Exp e, cs1)) = Div ⇔
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


(******************** trace_prefix ********************)

(*
  TODO the proofs below are quite messy and repetitive.
  This is partly because they focus on the "wrong" parts of the two traces
  which are being related - we case split on the first chunk of each trace,
  where actually we want to reuse the theorems above and think about the
  last bit of the trace.

  Perhaps modifying `trace_prefix` as follows might be useful - it now returns
  the remaining bit of itree left to process. Together with the lemma below,
  we might be able to "fast-forward" the proof on to the interesting part of
  the traces.

****************************************

Definition trace_prefix_def:
  trace_prefix 0 (oracle, ffi_st) itree = ([], NONE, SOME itree) ∧
  trace_prefix (SUC n) (oracle, ffi_st) (Ret r) = ([], SOME r, NONE) ∧
  trace_prefix (SUC n) (oracle, ffi_st)  Div = ([], NONE, NONE) ∧
  trace_prefix (SUC n) (oracle, ffi_st) (Vis (s, conf, ws) f) =
    case oracle s ffi_st conf ws of
    | Oracle_return ffi_st' ws' =>
        let (io, res, rest) = trace_prefix n (oracle, ffi_st') (f $ INR ws') in
        if LENGTH ws ≠ LENGTH ws' then (io, res, rest)
        else (IO_event s conf (ZIP (ws,ws'))::io, res, rest)
    | Oracle_final outcome => trace_prefix n (oracle, ffi_st) (f $ INL outcome)
End

Theorem trace_prefix_interp:
  trace_prefix 0 (oracle, ffi_st) (interp e) = ([], NONE, SOME $ interp e) ∧
  trace_prefix (SUC n) (oracle, ffi_st) (interp e) =
    case step_until_halt e of
    | Ret => ([], SOME Termination, NONE)
    | Err => ([], SOME Error, NONE)
    | Div => ([], NONE, NONE)
    | Act s conf ws lnum env st cs =>
        case oracle s ffi_st conf ws of
        | Oracle_return ffi_st' ws' =>
            if LENGTH ws ≠ LENGTH ws' ∧ n = 0 then
              ([], NONE, SOME $ Ret (FinalFFI (s,conf,ws) FFI_failed))
            else if LENGTH ws ≠ LENGTH ws' then
              ([], SOME $ FinalFFI (s, conf, ws) FFI_failed, NONE)
            else let (io, res, rest) =
              trace_prefix n (oracle, ffi_st')
                (interp $
                  Estep (env, LUPDATE (W8array ws') lnum st, Val $ Conv NONE [], cs))
            in ((IO_event s conf (ZIP (ws,ws')))::io, res, rest)
        | Oracle_final outcome =>
            if n = 0 then
              ([], NONE, SOME $ Ret (FinalFFI (s,conf,ws) outcome))
            else
              ([], SOME $ FinalFFI (s, conf, ws) outcome, NONE)
Proof
  rw[trace_prefix_def] >> rw[Once interp] >>
  CASE_TAC >> gvs[trace_prefix_def] >>
  reverse $ CASE_TAC >> gvs[]
  >- (Cases_on `n` >> gvs[trace_prefix_def]) >>
  IF_CASES_TAC >> gvs[] >>
  Cases_on `n` >> gvs[trace_prefix_def]
QED

Theorem trace_prefix_interp_SOME:
  ∀n oracle ffi_st e io r rest.
    trace_prefix (SUC n) (oracle,ffi_st) (interp e) = (io, SOME r, rest)
  ⇒ rest = NONE ∧
    ∃m rest'.
      m < SUC n ∧ trace_prefix m (oracle,ffi_st) (interp e) = (io, NONE, rest') ∧
      rest' = SOME $ Ret r
Proof
  Induct >> once_rewrite_tac[trace_prefix_interp] >> rw[] >>
  every_case_tac >> gvs[]
  >- gvs[trace_prefix_interp]
  >- gvs[trace_prefix_interp]
  >- (gvs[trace_prefix_interp] >> rw[Once interp])
  >- (gvs[trace_prefix_interp] >> rw[Once interp])
  >- (gvs[trace_prefix_interp] >> rw[Once interp])
  >- (pairarg_tac >> gvs[] >> last_x_assum drule >> simp[])
  >- (qexists_tac `SUC 0` >> rewrite_tac[trace_prefix_interp] >> simp[])
  >- (
    pairarg_tac >> gvs[] >>
    last_x_assum drule >> strip_tac >> gvs[] >>
    qexists_tac `SUC m` >> simp[trace_prefix_interp]
    )
  >- (qexists_tac `SUC 0` >> rewrite_tac[trace_prefix_interp] >> simp[])
  >- (qexists_tac `0` >> rw[Once trace_prefix_interp] >> rw[Once interp])
  >- (qexists_tac `0` >> rw[Once trace_prefix_interp] >> rw[Once interp])
  >- (qexists_tac `0` >> rw[Once trace_prefix_interp] >> rw[Once interp])
QED
*)


Theorem trace_prefix_Error:
  ctxt_rel cs1 cs2 ⇒
  ((∃n. trace_prefix n (oracle, ffi_st)
    (interp (Estep (env,st,ev,cs1))) = (io, SOME Error)) ⇔
  ∃est2 ffi'.
    RTC e_step_reln
      (env, (st, ffi with <| oracle := oracle; ffi_state := ffi_st |>), ev, cs2)
      est2 ∧
    get_ffi (Estep est2) = SOME ffi' ∧
    ffi'.io_events = ffi.io_events ++ io ∧
    e_step est2 = Eabort Rtype_error)
Proof
  rw[] >> eq_tac >> rw[] >> rpt $ pop_assum mp_tac
  >- (
    map_every qid_spec_tac
      [`ev`,`ffi`,`oracle`,`ffi_st`,`st`,`env`,`io`,`cs2`,`cs1`,`n`] >>
    Induct >> rw[trace_prefix_interp] >>
    gvs[step_until_halt_def] >> every_case_tac >> gvs[]
    >- (pairarg_tac >> gvs[trace_prefix_def])
    >- (
      pairarg_tac >> gvs[] >>
      rename1 `Effi _ _ _ lnum env' st' cs1'` >>
      rename1 `_ conf ws = Oracle_return ffi_st' ws'` >>
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      drule is_halt_step_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `step_n x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      `∃l. m = SUC l` by (Cases_on `m` >> gvs[step_n_def]) >> gvs[] >>
      pop_assum $ qspec_then `l` assume_tac >> gvs[] >>
      Cases_on `step_n l (Estep (env,st,ev,cs1))` >> gvs[is_halt_def] >>
      qmatch_goalsub_abbrev_tac `_,(_,ffi0),_,_` >>
      qspecl_then [`l`,`Estep (env,st,ev,cs1)`,`Estep (env,(st,ffi0),ev,cs2)`]
        mp_tac step_result_rel_n >>
      simp[step_result_rel_cases, is_Effi_def, get_ffi_def] >>
      strip_tac >> gvs[get_ffi_def] >>
      qpat_x_assum `step_n (SUC _) _ = _` mp_tac >> rw[step_n_alt_def] >>
      once_rewrite_tac[RTC_CASES_RTC_TWICE] >> simp[PULL_EXISTS] >>
      rw[Once RTC_CASES2] >> irule_at Any OR_INTRO_THM2 >>
      simp[PULL_EXISTS, GSYM CONJ_ASSOC] >>
      rw[Once e_step_reln_eq_step_n_cml, PULL_EXISTS] >>
      goal_assum drule >> rw[e_step_reln_def] >>
      drule_at Any step_result_rel_single_FFI_strong >>
      simp[step_result_rel_cases, PULL_EXISTS] >>
      disch_then drule >> simp[get_ffi_def] >>
      disch_then $ qspec_then `ffi'` assume_tac >> gvs[] >>
      unabbrev_all_tac >> gvs[] >>
      qmatch_goalsub_abbrev_tac `_,(_,ffi2),_,_` >>
      gvs[ctxt_rel_def] >> gvs[GSYM ctxt_rel_def] >>
      last_x_assum drule >> disch_then drule >>
      disch_then $ qspec_then `ffi2` assume_tac >> gvs[] >>
      unabbrev_all_tac >> gvs[] >>
      goal_assum drule >> goal_assum drule >> simp[]
      )
    >- (
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      drule is_halt_step_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `step_n x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      `∃l. m = SUC l` by (Cases_on `m` >> gvs[step_n_def]) >> gvs[] >>
      pop_assum $ qspec_then `l` assume_tac >> gvs[] >>
      Cases_on `step_n l (Estep (env,st,ev,cs1))` >> gvs[is_halt_def] >>
      qmatch_goalsub_abbrev_tac `_,(_,ffi0),_,_` >>
      qspecl_then [`l`,`Estep (env,st,ev,cs1)`,`Estep (env,(st,ffi0),ev,cs2)`]
        mp_tac step_result_rel_n >>
      simp[step_result_rel_cases, is_Effi_def, get_ffi_def] >>
      strip_tac >> gvs[get_ffi_def] >>
      qpat_x_assum `step_n (SUC _) _ = _` mp_tac >> rw[step_n_alt_def] >>
      rw[Once e_step_reln_eq_step_n_cml, PULL_EXISTS] >>
      goal_assum drule >> simp[get_ffi_def] >>
      qspec_then `(env',st',ev',cs1')` assume_tac step_result_rel_single >>
      gvs[step_result_rel_cases, is_Effi_def] >> unabbrev_all_tac >> gvs[]
      )
    )
  >- (
    simp[e_step_reln_eq_step_n_cml, PULL_EXISTS, AND_IMP_INTRO] >> gen_tac >>
    map_every qid_spec_tac
      [`est2`,`ev`,`ffi`,`oracle`,`ffi_st`,`st`,`env`,`io`,`cs2`,`cs1`,`n`] >>
    Induct >> rw[]
    >- (
      gvs[step_n_cml_def] >>
      qexists_tac `SUC 0` >> once_rewrite_tac[trace_prefix_interp] >>
      simp[step_until_halt_def] >>
      `estep (env,st,ev,cs1) = Etype_error` by (
        qmatch_asmsub_abbrev_tac `_,(_,ffi0),_,_` >>
        qspecl_then [`env,(st,ffi0),ev,cs2`,`env,st,ev,cs1`]
          assume_tac $ GEN_ALL step_result_rel_single' >>
        gvs[get_ffi_def, step_result_rel_cases]) >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[]
      >- (qexists_tac `SUC 0` >> rewrite_tac[step_n_def] >> simp[is_halt_def]) >>
      Cases_on `x` >> gvs[step_n_def, is_halt_def] >> gvs[get_ffi_def]
      ) >>
    gvs[step_n_cml_def] >>
    qmatch_asmsub_abbrev_tac `_,(_,ffi0),_,_` >>
    Cases_on `e_step (env,(st,ffi0),ev,cs2)` >> gvs[] >>
    Cases_on `get_ffi (Estep p) = SOME ffi0`
    >- (
      qspecl_then [`env,(st,ffi0),ev,cs2`,`env,st,ev,cs1`]
        assume_tac $ GEN_ALL step_result_rel_single' >>
      gvs[get_ffi_def, step_result_rel_cases] >>
      last_x_assum drule >>
      disch_then $ qspecl_then
        [`io`,`env'`,`st'`,`ffi_st`,`oracle`,`ffi`,`ev'`] mp_tac >>
      simp[] >> strip_tac >> rename1 `trace_prefix m _` >>
      qexists_tac `m` >> pop_assum mp_tac >>
      Cases_on `m` >> once_rewrite_tac[trace_prefix_interp] >> rw[] >>
      DEP_ONCE_REWRITE_TAC[step_until_halt_take_step] >> simp[is_halt_def]
      ) >>
    PairCases_on `p` >> gvs[get_ffi_def] >>
    rename1 `get_ffi _ = SOME ffi_new` >>
    rename1 `Estep (env',(st',ffi'),ev',cs2')` >>
    drule e_step_ffi_changed >> simp[] >>
    drule e_step_ffi_changed_estep_to_Effi >> simp[] >> disch_then drule >>
    strip_tac >> strip_tac >> gvs[ctxt_rel_def] >> gvs[GSYM ctxt_rel_def] >>
    Q.REFINE_EXISTS_TAC `SUC m` >> once_rewrite_tac[trace_prefix_interp] >>
    simp[step_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (
      qexists_tac `SUC 0` >> rewrite_tac[step_n_def] >>
      simp[estep_def, SF itree_ss, is_halt_def]
      ) >>
    Cases_on `x` >> gvs[step_n_def, is_halt_def] >>
    unabbrev_all_tac >> gvs[ctxt_frame_rel_cases] >>
    simp[UNCURRY] >> last_x_assum drule >> disch_then $ drule_at Any >>
    qmatch_asmsub_abbrev_tac `step_n_cml n (Estep (_,(st',_),vv,_))` >>
    qmatch_asmsub_abbrev_tac `_ ++ [new_event]` >>
    disch_then $ qspecl_then
      [`TL io`,`env'`,`st'`,`ffi'.ffi_state`, `ffi'.oracle`,`ffi'`,`vv`] mp_tac >>
    simp[] >> reverse $ impl_keep_tac >> gvs[] >> rw[]
    >- (qexists_tac `n'` >> simp[])
    >- (
      qpat_x_assum `step_n_cml n _ = _` $ SUBST_ALL_TAC o GSYM >>
      rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
      rw[ffi_state_component_equality]
      ) >>
    imp_res_tac io_events_mono_e_step >>
    imp_res_tac io_events_mono_step_n_cml >> gvs[io_events_mono_def] >>
    PairCases_on `est2` >> gvs[get_ffi_def] >>
    Cases_on `io` >> gvs[]
    )
QED

Theorem trace_prefix_Termination:
  ctxt_rel cs1 cs2 ⇒
  ((∃n. trace_prefix n (oracle, ffi_st)
    (interp (Estep (env,st,ev,cs1))) = (io, SOME Termination)) ⇔
  ∃est2 ffi'.
    RTC e_step_reln
      (env, (st, ffi with <| oracle := oracle; ffi_state := ffi_st |>), ev, cs2)
      est2 ∧
    is_halt_cml (Estep est2) ∧
    get_ffi (Estep est2) = SOME ffi' ∧
    ffi'.io_events = ffi.io_events ++ io)
Proof
  rw[] >> eq_tac >> rw[] >> rpt $ pop_assum mp_tac
  >- (
    map_every qid_spec_tac
      [`ev`,`ffi`,`oracle`,`ffi_st`,`st`,`env`,`io`,`cs2`,`cs1`,`n`] >>
    Induct >> rw[trace_prefix_interp] >>
    gvs[step_until_halt_def] >> every_case_tac >> gvs[]
    >- (
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >> gvs[is_halt_def]
      )
    >- (pairarg_tac >> gvs[trace_prefix_def])
    >- (
      pairarg_tac >> gvs[] >>
      rename1 `Effi _ conf ws lnum env' st' cs1'` >>
      rename1 `_ conf ws = Oracle_return ffi_st' ws'` >>
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      drule is_halt_step_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `step_n x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      `∃l. m = SUC l` by (Cases_on `m` >> gvs[step_n_def]) >> gvs[] >>
      pop_assum $ qspec_then `l` assume_tac >> gvs[] >>
      Cases_on `step_n l (Estep (env,st,ev,cs1))` >> gvs[is_halt_def] >>
      qmatch_goalsub_abbrev_tac `_,(_,ffi0),_,_` >>
      qspecl_then [`l`,`Estep (env,st,ev,cs1)`,`Estep (env,(st,ffi0),ev,cs2)`]
        mp_tac step_result_rel_n >>
      simp[step_result_rel_cases, is_Effi_def, get_ffi_def] >>
      strip_tac >> gvs[get_ffi_def] >>
      qpat_x_assum `step_n (SUC _) _ = _` mp_tac >> rw[step_n_alt_def] >>
      once_rewrite_tac[RTC_CASES_RTC_TWICE] >> simp[PULL_EXISTS] >>
      rw[Once RTC_CASES2] >> irule_at Any OR_INTRO_THM2 >>
      simp[PULL_EXISTS, GSYM CONJ_ASSOC] >>
      rw[Once e_step_reln_eq_step_n_cml, PULL_EXISTS] >>
      goal_assum drule >> rw[e_step_reln_def] >>
      drule_at Any step_result_rel_single_FFI_strong >>
      simp[step_result_rel_cases, PULL_EXISTS] >>
      disch_then drule >> simp[get_ffi_def] >>
      disch_then $ qspec_then `ffi'` assume_tac >> gvs[] >>
      unabbrev_all_tac >> gvs[] >>
      qmatch_goalsub_abbrev_tac `_,(_,ffi2),_,_` >>
      gvs[ctxt_rel_def] >> gvs[GSYM ctxt_rel_def] >>
      last_x_assum drule >> disch_then drule >>
      disch_then $ qspec_then `ffi2` assume_tac >> gvs[] >>
      unabbrev_all_tac >> gvs[] >> goal_assum drule >> gvs[]
      )
    >- (
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      drule is_halt_step_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `step_n x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      `∃l. m = SUC l` by (Cases_on `m` >> gvs[step_n_def]) >> gvs[] >>
      pop_assum $ qspec_then `l` assume_tac >> gvs[] >>
      Cases_on `step_n l (Estep (env,st,ev,cs1))` >> gvs[is_halt_def] >>
      qmatch_goalsub_abbrev_tac `_,(_,ffi0),_,_` >>
      qspecl_then [`l`,`Estep (env,st,ev,cs1)`,`Estep (env,(st,ffi0),ev,cs2)`]
        mp_tac step_result_rel_n >>
      simp[step_result_rel_cases, is_Effi_def, get_ffi_def] >>
      strip_tac >> gvs[get_ffi_def] >>
      qpat_x_assum `step_n (SUC _) _ = _` mp_tac >> rw[step_n_alt_def] >>
      rw[Once e_step_reln_eq_step_n_cml, PULL_EXISTS] >>
      goal_assum drule >>
      gvs[estep_to_Edone, ctxt_rel_def, is_halt_cml_def, get_ffi_def] >>
      unabbrev_all_tac >> gvs[] >>
      pairarg_tac >> gvs[is_halt_cml_def, ctxt_frame_rel_cases]
      )
    )
  >- (
    simp[e_step_reln_eq_step_n_cml, PULL_EXISTS, AND_IMP_INTRO] >> gen_tac >>
    map_every qid_spec_tac
      [`est2`,`ev`,`ffi`,`ffi'`,`oracle`,`ffi_st`,`st`,`env`,`io`,`cs2`,`cs1`,`n`] >>
    Induct >> rw[]
    >- (
      gvs[step_n_cml_def] >>
      qexists_tac `SUC 0` >> once_rewrite_tac[trace_prefix_interp] >>
      simp[step_until_halt_def] >>
      `estep (env,st,ev,cs1) = Edone` by (
        simp[estep_to_Edone] >>
        Cases_on `ev` >> gvs[is_halt_cml_def] >>
        Cases_on `cs2` >> gvs[is_halt_cml_def, ctxt_rel_def] >>
        pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
        Cases_on `c2` >> gvs[is_halt_cml_def, ctxt_frame_rel_cases] >>
        Cases_on `t` >> gvs[is_halt_cml_def]) >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[]
      >- (qexists_tac `SUC 0` >> rewrite_tac[step_n_def] >> simp[is_halt_def]) >>
      Cases_on `x` >> gvs[step_n_def, is_halt_def, get_ffi_def]
      ) >>
    gvs[step_n_cml_def] >>
    qmatch_asmsub_abbrev_tac `_,(_,ffi0),_,_` >>
    rename1 `get_ffi (Estep final_est) = SOME final_ffi` >>
    Cases_on `e_step (env,(st,ffi0),ev,cs2)` >> gvs[] >>
    Cases_on `get_ffi (Estep p) = SOME ffi0`
    >- (
      qspecl_then [`env,(st,ffi0),ev,cs2`,`env,st,ev,cs1`]
        assume_tac $ GEN_ALL step_result_rel_single' >>
      gvs[get_ffi_def, step_result_rel_cases] >>
      last_x_assum drule >>
      disch_then $ qspecl_then
        [`io`,`env'`,`st'`,`ffi_st`,`oracle`,`final_ffi`,`ffi`,`ev'`] mp_tac >>
      simp[] >> strip_tac >> rename1 `trace_prefix m _` >>
      qexists_tac `m` >> pop_assum mp_tac >>
      Cases_on `m` >> once_rewrite_tac[trace_prefix_interp] >> rw[] >>
      DEP_ONCE_REWRITE_TAC[step_until_halt_take_step] >> simp[is_halt_def]
      ) >>
    PairCases_on `p` >> gvs[get_ffi_def] >>
    rename1 `Estep (env',(st',ffi1),ev',cs2')` >>
    drule e_step_ffi_changed >> simp[] >>
    drule e_step_ffi_changed_estep_to_Effi >> simp[] >> disch_then drule >>
    strip_tac >> strip_tac >> gvs[ctxt_rel_def] >> gvs[GSYM ctxt_rel_def] >>
    Q.REFINE_EXISTS_TAC `SUC m` >> once_rewrite_tac[trace_prefix_interp] >>
    simp[step_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (
      qexists_tac `SUC 0` >> rewrite_tac[step_n_def] >>
      simp[estep_def, SF itree_ss, is_halt_def]
      ) >>
    Cases_on `x` >> gvs[step_n_def, is_halt_def] >>
    unabbrev_all_tac >> gvs[ctxt_frame_rel_cases] >>
    last_x_assum drule >>
    qmatch_asmsub_abbrev_tac `step_n_cml n (Estep (_,(st',_),vv,_))` >>
    qmatch_asmsub_abbrev_tac `_ ++ [new_event]` >>
    disch_then $ qspecl_then
      [`TL io`,`env'`,`st'`,`ffi1.ffi_state`,
       `ffi1.oracle`,`final_ffi`,`ffi1`,`vv`,`final_est`] mp_tac >>
    simp[] >> reverse $ impl_keep_tac >> gvs[] >> rw[]
    >- (qexists_tac `n'` >> simp[])
    >- (
      qpat_x_assum `step_n_cml n _ = _` $ SUBST_ALL_TAC o GSYM >>
      rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
      rw[ffi_state_component_equality]
      ) >>
    imp_res_tac io_events_mono_e_step >>
    imp_res_tac io_events_mono_step_n_cml >> gvs[io_events_mono_def] >>
    PairCases_on `final_est` >> gvs[get_ffi_def] >>
    Cases_on `io` >> gvs[]
    )
QED

Theorem trace_prefix_FinalFFI:
  ctxt_rel cs1 cs2 ⇒
  ((∃n. trace_prefix n (oracle, ffi_st)
    (interp (Estep (env,st,ev,cs1))) = (io, SOME $ FinalFFI (s,conf,ws) outcome)) ⇔
  ∃final_est final_ffi.
    RTC e_step_reln
      (env, (st, ffi with <| oracle := oracle; ffi_state := ffi_st |>), ev, cs2)
      final_est ∧
    get_ffi (Estep final_est) = SOME final_ffi ∧
    final_ffi.io_events = ffi.io_events ++ io ∧
    e_step final_est = Eabort (Rffi_error $ Final_event s conf ws outcome))
Proof
  rw[] >> eq_tac >> rw[] >> rpt $ pop_assum mp_tac
  >- (
    map_every qid_spec_tac
      [`ev`,`ffi`,`oracle`,`ffi_st`,`st`,`env`,`io`,`cs2`,`cs1`,
       `s`,`conf`,`ws`,`outcome`,`n`] >>
    Induct >> rw[trace_prefix_interp] >>
    gvs[step_until_halt_def] >> every_case_tac >> gvs[]
    >- (pairarg_tac >> gvs[trace_prefix_def])
    >- (
      rename1 `Effi _ conf ws lnum env' st' cs1'` >>
      rename1 `_ conf ws = Oracle_return ffi_st' ws'` >>
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      drule is_halt_step_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `step_n x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      `∃l. m = SUC l` by (Cases_on `m` >> gvs[step_n_def]) >> gvs[] >>
      pop_assum $ qspec_then `l` assume_tac >> gvs[] >>
      Cases_on `step_n l (Estep (env,st,ev,cs1))` >> gvs[is_halt_def] >>
      qmatch_goalsub_abbrev_tac `_,(_,ffi0),_,_` >>
      qspecl_then [`l`,`Estep (env,st,ev,cs1)`,`Estep (env,(st,ffi0),ev,cs2)`]
        mp_tac step_result_rel_n >>
      simp[step_result_rel_cases, is_Effi_def, get_ffi_def] >>
      strip_tac >> gvs[get_ffi_def] >>
      qpat_x_assum `step_n (SUC _) _ = _` mp_tac >> rw[step_n_alt_def] >>
      rw[e_step_reln_eq_step_n_cml, PULL_EXISTS] >>
      goal_assum drule >>
      drule_at Any step_result_rel_single_FFI_strong >>
      simp[step_result_rel_cases, PULL_EXISTS] >>
      disch_then drule >> simp[get_ffi_def] >>
      disch_then $ qspec_then `ffi'` assume_tac >> gvs[] >>
      unabbrev_all_tac >> gvs[]
      )
    >- (
      pairarg_tac >> gvs[] >>
      rename1 `Effi s1 conf1 ws1 lnum env' st' cs1'` >>
      rename1 `_ conf1 ws1 = Oracle_return ffi_st' ws'` >>
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      drule is_halt_step_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `step_n x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      `∃l. m = SUC l` by (Cases_on `m` >> gvs[step_n_def]) >> gvs[] >>
      pop_assum $ qspec_then `l` assume_tac >> gvs[] >>
      Cases_on `step_n l (Estep (env,st,ev,cs1))` >> gvs[is_halt_def] >>
      qmatch_goalsub_abbrev_tac `_,(_,ffi0),_,_` >>
      qspecl_then [`l`,`Estep (env,st,ev,cs1)`,`Estep (env,(st,ffi0),ev,cs2)`]
        mp_tac step_result_rel_n >>
      simp[step_result_rel_cases, is_Effi_def, get_ffi_def] >>
      strip_tac >> gvs[get_ffi_def] >>
      qpat_x_assum `step_n (SUC _) _ = _` mp_tac >> rw[step_n_alt_def] >>
      drule_at Any step_result_rel_single_FFI_strong >>
      simp[step_result_rel_cases, PULL_EXISTS] >>
      disch_then drule >> simp[get_ffi_def] >>
      disch_then $ qspec_then `ffi'` assume_tac >> gvs[] >>
      unabbrev_all_tac >> gvs[] >>
      gvs[ctxt_rel_def] >> gvs[GSYM ctxt_rel_def] >>
      pairarg_tac >> gvs[] >>
      last_x_assum drule >>
      disch_then drule >>
      qmatch_asmsub_abbrev_tac `Estep (_,(_,ffi1),_,_)` >>
      disch_then $ qspec_then `ffi1` mp_tac >>
      strip_tac >> gvs[] >>
      rpt $ goal_assum $ drule_at Any >>
      gvs[e_step_reln_eq_step_n_cml, PULL_EXISTS] >>
      qexists_tac `SUC n' + l` >> simp[step_n_cml_add] >> simp[step_n_cml_def] >>
      unabbrev_all_tac >> gvs[]
      )
    >- (
      rename1 `Effi s1 conf1 ws1 lnum env' st' cs1'` >>
      rename1 `_ conf1 ws1 = Oracle_final final_event` >>
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      drule is_halt_step_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `step_n x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      `∃l. m = SUC l` by (Cases_on `m` >> gvs[step_n_def]) >> gvs[] >>
      pop_assum $ qspec_then `l` assume_tac >> gvs[] >>
      Cases_on `step_n l (Estep (env,st,ev,cs1))` >> gvs[is_halt_def] >>
      qmatch_goalsub_abbrev_tac `_,(_,ffi0),_,_` >>
      qspecl_then [`l`,`Estep (env,st,ev,cs1)`,`Estep (env,(st,ffi0),ev,cs2)`]
        mp_tac step_result_rel_n >>
      simp[step_result_rel_cases, is_Effi_def, get_ffi_def] >>
      strip_tac >> gvs[get_ffi_def] >>
      qpat_x_assum `step_n (SUC _) _ = _` mp_tac >> rw[step_n_alt_def] >>
      drule_at Any step_result_rel_single_FFI_strong >>
      simp[step_result_rel_cases, PULL_EXISTS] >>
      disch_then drule >> simp[get_ffi_def] >>
      disch_then $ qspec_then `ffi'` assume_tac >> gvs[] >>
      unabbrev_all_tac >> gvs[] >>
      gvs[ctxt_rel_def] >> gvs[GSYM ctxt_rel_def] >>
      pairarg_tac >> gvs[] >>
      goal_assum $ drule_at Any >> simp[get_ffi_def] >>
      rw[e_step_reln_eq_step_n_cml] >>
      qexists_tac `l` >> simp[step_n_cml_def]
      )
    )
  >- (
    simp[e_step_reln_eq_step_n_cml, PULL_EXISTS, AND_IMP_INTRO, GSYM CONJ_ASSOC] >>
    gen_tac >>
    map_every qid_spec_tac
      [`final_est`,`ev`,`ffi`,`final_ffi`,`oracle`,`ffi_st`,`st`,`env`,
       `io`,`cs2`,`cs1`,`s`,`conf`,`ws`,`outcome`,`n`] >>
    Induct >> rw[]
    >- (
      gvs[step_n_cml_def, get_ffi_def] >>
      qexists_tac `SUC $ SUC 0` >> once_rewrite_tac[trace_prefix_interp] >>
      simp[step_until_halt_def] >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[]
      >- (
        drule_at Any step_result_rel_single_FFI_error >>
        simp[step_result_rel_cases, PULL_EXISTS] >> disch_then drule >> rw[] >>
        qexists_tac `SUC 0` >> rewrite_tac[step_n_def] >> simp[is_halt_def]
        ) >>
      drule_at Any step_result_rel_single_FFI_error >>
      simp[step_result_rel_cases, PULL_EXISTS] >> disch_then drule >> rw[] >>
      Cases_on `x` >> gvs[step_n_def, is_halt_def, get_ffi_def] >>
      drule_at Any step_result_rel_single_FFI_strong >>
      simp[step_result_rel_cases, PULL_EXISTS] >> disch_then drule >>
      qmatch_asmsub_abbrev_tac `_,(_,ffi0),_,_` >>
      disch_then $ qspec_then `ffi0` mp_tac >> simp[get_ffi_def] >>
      unabbrev_all_tac >> gvs[] >> rw[] >>
      pop_assum $ assume_tac o GSYM >>
      (* TODO odd looping behaviour here without this irritating case split *)
      Cases_on `oracle s ffi_st (MAP (λc. n2w (ORD c)) (EXPLODE conf')) ws`
      >- (gvs[] >> IF_CASES_TAC >> gvs[])
      >- (simp[] >> gvs[])
      ) >>
    gvs[step_n_cml_def] >>
    qmatch_asmsub_abbrev_tac `_,(_,ffi0),_,_` >>
    Cases_on `e_step (env,(st,ffi0),ev,cs2)` >> gvs[] >>
    Cases_on `get_ffi (Estep p) = SOME ffi0`
    >- (
      qspecl_then [`env,(st,ffi0),ev,cs2`,`env,st,ev,cs1`]
        assume_tac $ GEN_ALL step_result_rel_single' >>
      gvs[get_ffi_def, step_result_rel_cases] >>
      last_x_assum drule >>
      disch_then $ qspecl_then
        [`outcome`,`ws`,`conf`,`s`,`io`, `env'`,`st'`,
         `ffi_st`,`oracle`,`final_ffi`,`ffi`,`ev'`,`final_est`] mp_tac >>
      simp[] >> strip_tac >> rename1 `trace_prefix m _` >>
      qexists_tac `m` >> pop_assum mp_tac >>
      Cases_on `m` >> once_rewrite_tac[trace_prefix_interp] >> rw[] >>
      DEP_ONCE_REWRITE_TAC[step_until_halt_take_step] >> simp[is_halt_def]
      ) >>
    PairCases_on `p` >> gvs[get_ffi_def] >>
    rename1 `Estep (env',(st',ffi1),ev',cs2')` >>
    drule e_step_ffi_changed >> simp[] >>
    drule e_step_ffi_changed_estep_to_Effi >> simp[] >> disch_then drule >>
    strip_tac >> strip_tac >> gvs[ctxt_rel_def] >> gvs[GSYM ctxt_rel_def] >>
    Q.REFINE_EXISTS_TAC `SUC m` >> once_rewrite_tac[trace_prefix_interp] >>
    simp[step_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (
      qexists_tac `SUC 0` >> rewrite_tac[step_n_def] >>
      simp[estep_def, SF itree_ss, is_halt_def]
      ) >>
    Cases_on `x` >> gvs[step_n_def, is_halt_def] >>
    unabbrev_all_tac >> gvs[ctxt_frame_rel_cases] >>
    last_x_assum drule >>
    qmatch_asmsub_abbrev_tac `step_n_cml n (Estep (_,(st',_),vv,_))` >>
    qmatch_asmsub_abbrev_tac `_ ++ [new_event]` >>
    disch_then $ qspecl_then
      [`outcome`,`ws`,`conf`,`s`,`TL io`,`env'`,`st'`,`ffi1.ffi_state`,
       `ffi1.oracle`,`final_ffi`,`ffi1`,`vv`,`final_est`] mp_tac >>
    simp[] >> reverse $ impl_keep_tac >> gvs[] >> rw[]
    >- (qexists_tac `n'` >> simp[])
    >- (
      qpat_x_assum `step_n_cml n _ = _` $ SUBST_ALL_TAC o GSYM >>
      rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
      rw[ffi_state_component_equality]
      ) >>
    imp_res_tac io_events_mono_e_step >>
    imp_res_tac io_events_mono_step_n_cml >> gvs[io_events_mono_def] >>
    PairCases_on `final_est` >> gvs[get_ffi_def] >>
    Cases_on `io` >> gvs[]
    )
QED

Theorem trace_prefix_divergence_RL:
  ffi0 = ffi with <| oracle := oracle; ffi_state := ffi_st |> ⇒
  ctxt_rel cs1 cs2 ∧
  (∀est1. RTC e_step_reln (env,(st,ffi0),ev,cs2) est1
    ⇒ ∃est2. e_step_reln est1 est2) ∧
  RTC e_step_reln (env,(st,ffi0),ev,cs2) final_est ∧
  get_ffi (Estep final_est) = SOME final_ffi ∧
  final_ffi.io_events = ffi0.io_events ++ io ⇒
  ∃n.
    trace_prefix n (oracle, ffi_st)
      (interp (Estep (env,st,ev,cs1))) = (io, NONE)
Proof
  strip_tac >> csimp[e_step_reln_eq_step_n_cml, PULL_EXISTS] >>
  gen_tac >> pop_assum kall_tac >>
  map_every qid_spec_tac
    [`ev`,`ffi`,`oracle`,`ffi_st`,`st`,`env`,`io`,`cs2`,`cs1`,
     `final_est`,`final_ffi`,`n`] >>
  Induct >> rw[step_n_cml_def]
  >- (gvs[get_ffi_def] >> qexists_tac `0` >> simp[trace_prefix_interp]) >>
  qmatch_asmsub_abbrev_tac `_,(_,ffi0),_,_` >>
  Cases_on `e_step (env,(st,ffi0),ev,cs2)` >> gvs[] >>
  Cases_on `get_ffi (Estep p) = SOME ffi0`
  >- (
    qspecl_then [`env,(st,ffi0),ev,cs2`,`env,st,ev,cs1`]
      assume_tac $ GEN_ALL step_result_rel_single' >>
    gvs[get_ffi_def, step_result_rel_cases] >>
    last_x_assum drule >>
    disch_then $ qspecl_then
      [`final_ffi`,`final_est`,`io`,`env'`,
       `st'`,`ffi_st`,`oracle`,`ffi`,`ev'`] mp_tac >>
    simp[] >> impl_tac >> rw[]
    >- (last_x_assum irule >> qexists_tac `SUC n'` >> simp[step_n_cml_def]) >>
    rename1 `trace_prefix m _` >> qexists_tac `m` >> pop_assum mp_tac >>
    Cases_on `m` >> once_rewrite_tac[trace_prefix_interp] >> rw[] >>
    DEP_ONCE_REWRITE_TAC[step_until_halt_take_step] >> simp[is_halt_def]
    ) >>
  PairCases_on `p` >> gvs[get_ffi_def] >>
  rename1 `Estep (env',(st',ffi1),ev',cs2')` >>
  drule e_step_ffi_changed >> simp[] >>
  drule e_step_ffi_changed_estep_to_Effi >> simp[] >> disch_then drule >>
  strip_tac >> strip_tac >> gvs[ctxt_rel_def] >> gvs[GSYM ctxt_rel_def] >>
  Q.REFINE_EXISTS_TAC `SUC m` >> once_rewrite_tac[trace_prefix_interp] >>
  simp[step_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
  >- (
    pop_assum $ qspec_then `SUC 0` mp_tac >> rewrite_tac[step_n_def] >>
    simp[SF itree_ss, is_halt_def]
    ) >>
  Cases_on `x` >> gvs[step_n_def, is_halt_def] >>
  unabbrev_all_tac >> gvs[ctxt_frame_rel_cases] >>
  last_x_assum drule >>
  qmatch_asmsub_abbrev_tac `step_n_cml n (Estep (_,(st',_),vv,_))` >>
  qmatch_asmsub_abbrev_tac `_ ++ [new_event]` >>
  disch_then $ qspecl_then
    [`final_ffi`,`final_est`,`TL io`,`env'`,`st'`,`ffi1.ffi_state`,
     `ffi1.oracle`,`ffi1`,`vv`] mp_tac >>
  simp[] >> reverse $ impl_keep_tac >> gvs[] >> rw[]
  >- (qexists_tac `n'` >> simp[])
  >- (
    last_x_assum irule >> qexists_tac `SUC n'` >> simp[step_n_cml_def] >>
    pop_assum $ SUBST_ALL_TAC o GSYM >>
    rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> rw[ffi_state_component_equality]
    )
  >- (
    qpat_x_assum `step_n_cml n _ = _` $ SUBST_ALL_TAC o GSYM >>
    rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
    rw[ffi_state_component_equality]
    ) >>
  imp_res_tac io_events_mono_e_step >>
  imp_res_tac io_events_mono_step_n_cml >> gvs[io_events_mono_def] >>
  PairCases_on `final_est` >> gvs[get_ffi_def] >>
  Cases_on `io` >> gvs[]
QED


(******************** Collected results for expressions ********************)

Theorem small_eval_trace_prefix_termination:
  (small_eval env (st,ffi) e [] ((st',ffi'), Rval v) ∨
   small_eval env (st,ffi) e [] ((st',ffi'), Rerr (Rraise v)))
  ⇒ ∃n io.
      trace_prefix n (ffi.oracle, ffi.ffi_state)
        (interp (Estep (env,st,Exp e,[]))) = (io, SOME Termination) ∧
      ffi'.io_events = ffi.io_events ++ io
Proof
  rpt strip_tac >>
  `ctxt_rel ([] : ctxt list) []` by gvs[ctxt_rel_def] >>
  drule $ iffRL trace_prefix_Termination >>
  gvs[small_eval_def, e_step_reln_eq_step_n_cml, PULL_EXISTS] >>
  imp_res_tac io_events_mono_step_n_cml >>
  gvs[io_events_mono_def, rich_listTheory.IS_PREFIX_APPEND] >>
  disch_then $ qspecl_then
    [`st`,`ffi.oracle`,`l`,`ffi.ffi_state`,`ffi`,`Exp e`,`env`] mp_tac
  >- (
    disch_then $ qspec_then `(env',(st',ffi'),Val v,[])` mp_tac >> simp[get_ffi_def] >>
    disch_then irule >> simp[is_halt_cml_def] >>
    qexists_tac `n` >>
    qpat_x_assum `step_n_cml n _ = _` $ SUBST_ALL_TAC o GSYM >>
    rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
    simp[ffi_state_component_equality]
    )
  >- (
    disch_then $ qspec_then `(env',(st',ffi'),Val v,[Craise (),env''])` mp_tac >>
    simp[get_ffi_def] >>
    disch_then irule >> simp[is_halt_cml_def] >>
    qexists_tac `n` >>
    qpat_x_assum `step_n_cml n _ = _` $ SUBST_ALL_TAC o GSYM >>
    rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
    simp[ffi_state_component_equality]
    )
QED

Theorem trace_prefix_small_eval_termination:
  trace_prefix n (oracle, ffi_st)
    (interp (Estep (env,st,Exp e,[]))) = (io, SOME Termination)
  ⇒ ∃st' ffi' v.
      (small_eval env (st, ffi with <| oracle := oracle; ffi_state := ffi_st |>)
        e [] ((st',ffi'), Rval v) ∨
      small_eval env (st, ffi with <| oracle := oracle; ffi_state := ffi_st |>)
        e [] ((st',ffi'), Rerr (Rraise v))) ∧
      ffi'.io_events = ffi.io_events ++ io
Proof
  rw[] >>
  `ctxt_rel ([] : ctxt list) []` by gvs[ctxt_rel_def] >>
  drule $ iffLR trace_prefix_Termination >> simp[PULL_EXISTS] >>
  disch_then drule >> disch_then $ qspec_then `ffi` assume_tac >> gvs[] >>
  PairCases_on `est2` >> Cases_on `est23` >> gvs[is_halt_cml_def] >>
  Cases_on `est24` >> gvs[is_halt_cml_def, get_ffi_def, small_eval_def]
  >- (
    irule_at Any OR_INTRO_THM1 >> simp[PULL_EXISTS] >>
    goal_assum drule >> simp[]
    )
  >- (
    PairCases_on `h` >> Cases_on `h0` >> Cases_on `t` >> gvs[is_halt_cml_def] >>
    irule_at Any OR_INTRO_THM2 >> simp[PULL_EXISTS] >>
    goal_assum drule >> simp[]
    )
QED

Theorem small_eval_trace_prefix_type_error:
  small_eval env (st,ffi) e [] ((st',ffi'), Rerr (Rabort Rtype_error))
  ⇒ ∃n io.
      trace_prefix n (ffi.oracle, ffi.ffi_state)
        (interp (Estep (env,st,Exp e,[]))) = (io, SOME Error) ∧
      ffi'.io_events = ffi.io_events ++ io
Proof
  rpt strip_tac >>
  `ctxt_rel ([] : ctxt list) []` by gvs[ctxt_rel_def] >>
  drule $ iffRL trace_prefix_Error >>
  gvs[small_eval_def, e_step_reln_eq_step_n_cml, PULL_EXISTS] >>
  imp_res_tac io_events_mono_step_n_cml >>
  gvs[io_events_mono_def, rich_listTheory.IS_PREFIX_APPEND] >>
  disch_then $ qspecl_then
    [`st`,`ffi.oracle`,`l`,`ffi.ffi_state`,`ffi`,`Exp e`,`env`] mp_tac >>
  qmatch_goalsub_abbrev_tac `(_,(_,ffi0),_)` >>
  `ffi0 = ffi` by (unabbrev_all_tac >> gvs[ffi_state_component_equality]) >>
  gvs[] >> pop_assum kall_tac >>
  disch_then drule >> simp[get_ffi_def]
QED

Theorem trace_prefix_small_eval_type_error:
  trace_prefix n (oracle, ffi_st)
    (interp (Estep (env,st,Exp e,[]))) = (io, SOME Error)
  ⇒ ∃st' ffi'.
      small_eval env (st,ffi with <| oracle := oracle; ffi_state := ffi_st|>)
        e [] ((st',ffi'), Rerr (Rabort Rtype_error)) ∧
      ffi'.io_events = ffi.io_events ++ io
Proof
  rw[] >>
  `ctxt_rel ([] : ctxt list) []` by gvs[ctxt_rel_def] >>
  drule $ iffLR trace_prefix_Error >> simp[PULL_EXISTS] >>
  disch_then drule >> disch_then $ qspec_then `ffi` assume_tac >> gvs[] >>
  simp[small_eval_def, PULL_EXISTS] >>
  PairCases_on `est2` >> goal_assum drule >> simp[] >> gvs[get_ffi_def]
QED

Theorem small_eval_trace_prefix_ffi_error:
  small_eval env (st,ffi) e []
        ((st',ffi'), Rerr (Rabort $ Rffi_error $ Final_event s conf ws outcome))
  ⇒ ∃n io.
      trace_prefix n (ffi.oracle, ffi.ffi_state)
        (interp (Estep (env,st,Exp e,[]))) = (io, SOME $ FinalFFI (s,conf,ws) outcome) ∧
      ffi'.io_events = ffi.io_events ++ io
Proof
  rpt strip_tac >> `ctxt_rel ([] : ctxt list) []` by gvs[ctxt_rel_def] >>
  drule $ iffRL trace_prefix_FinalFFI >>
  gvs[small_eval_def, e_step_reln_eq_step_n_cml, PULL_EXISTS] >>
  imp_res_tac io_events_mono_step_n_cml >>
  gvs[io_events_mono_def, rich_listTheory.IS_PREFIX_APPEND] >>
  disch_then $ qspecl_then
    [`ws`,`st`,`s`,`outcome`,`ffi.oracle`,`l`,`ffi.ffi_state`,`ffi`,
     `Exp e`,`env`,`conf`,`(env',(st',ffi'),e',c')`,`ffi'`,`n`] mp_tac >>
  simp[get_ffi_def] >> disch_then irule >>
  qpat_x_assum `step_n_cml n _ = _` $ SUBST_ALL_TAC o GSYM >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[ffi_state_component_equality]
QED

Theorem trace_prefix_small_eval_ffi_error:
  trace_prefix n (oracle, ffi_st)
    (interp (Estep (env,st,Exp e,[]))) = (io, SOME $ FinalFFI (s,conf,ws) outcome)
  ⇒ ∃st' ffi'.
      small_eval env (st,ffi with <| oracle := oracle; ffi_state := ffi_st|>)
        e [] ((st',ffi'), Rerr (Rabort $ Rffi_error $ Final_event s conf ws outcome)) ∧
      ffi'.io_events = ffi.io_events ++ io
Proof
  rw[] >>
  `ctxt_rel ([] : ctxt list) []` by gvs[ctxt_rel_def] >>
  drule $ iffLR trace_prefix_FinalFFI >> simp[PULL_EXISTS] >>
  disch_then drule >> disch_then $ qspec_then `ffi` assume_tac >> gvs[] >>
  simp[small_eval_def, PULL_EXISTS] >>
  PairCases_on `final_est` >> goal_assum drule >> simp[] >> gvs[get_ffi_def]
QED

Theorem e_diverges_trace_prefix:
  e_diverges env (st,ffi) e ∧
  RTC e_step_reln (env,(st,ffi),Exp e,[]) (env',(st',ffi'),e',c')
  ⇒ ∃n io.
      trace_prefix n (ffi.oracle, ffi.ffi_state)
        (interp (Estep (env,st,Exp e,[]))) = (io, NONE) ∧
      ffi'.io_events = ffi.io_events ++ io
Proof
  rpt strip_tac >> `ctxt_rel ([] : ctxt list) []` by gvs[ctxt_rel_def] >>
  drule_at Any trace_prefix_divergence_RL >> simp[] >>
  gvs[e_diverges_def, small_eval_def, e_step_reln_eq_step_n_cml, PULL_EXISTS] >>
  imp_res_tac io_events_mono_step_n_cml >>
  gvs[io_events_mono_def, rich_listTheory.IS_PREFIX_APPEND] >>
  disch_then $ qspecl_then
    [`st`,`ffi.oracle`,`l`,`ffi'`,`(env',(st',ffi'),e',c')`,
     `ffi.ffi_state`,`ffi`,`Exp e`,`env`,`n`] mp_tac >>
  disch_then irule >> simp[get_ffi_def] >>
  qpat_x_assum `step_n_cml n _ = _` $ SUBST_ALL_TAC o GSYM >> reverse $ rw[]
  >- (rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>  simp[ffi_state_component_equality])
  >- (
    PairCases_on `est1` >> rename1 `_ = Estep (a,(b,c),d,f)` >>
    last_x_assum $ qspecl_then [`a`,`(b,c)`,`d`,`f`,`n`] mp_tac >>
    reverse impl_tac >> rw[] >- goal_assum drule >>
    qpat_x_assum `step_n_cml n _ = _` $ SUBST_ALL_TAC o GSYM >>
    rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>  simp[ffi_state_component_equality]
    )
QED

(* TODO lift infinite behaviour relation to lprefix_lub *)

(******************** Declarations ********************)

(****************************************)

val _ = export_theory();

