(* Relating the itree- and FFI state-based CakeML semantics *)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open optionTheory relationTheory pairTheory listTheory arithmeticTheory;
open namespaceTheory astTheory ffiTheory semanticPrimitivesTheory
     evaluatePropsTheory smallStepTheory smallStepPropsTheory;
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

val dsmallstep_ss = simpLib.named_rewrites "dsmallstep_ss" [
    smallStepPropsTheory.collapse_env_def,
    smallStepTheory.decl_continue_def,
    smallStepTheory.decl_step_def
    ];

val itree_ss = simpLib.named_rewrites "itree_ss" [
    cakeml_semanticsTheory.continue_def,
    cakeml_semanticsTheory.return_def,
    cakeml_semanticsTheory.push_def,
    cakeml_semanticsTheory.estep_def,
    get_ffi_def
    ];

val ditree_ss = simpLib.named_rewrites "ditree_ss" [
    cakeml_semanticsTheory.dcontinue_def,
    cakeml_semanticsTheory.dreturn_def,
    cakeml_semanticsTheory.dpush_def,
    cakeml_semanticsTheory.dstep_def,
    dget_ffi_def
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

Theorem is_Dffi_eq_is_Effi_single:
  is_Dffi (dstep env dsta (ExpVal env' ev cs l p) dcs) ⇔
  is_Effi (estep (env',dsta.refs,ev,cs))
Proof
  Cases_on `ev` >> rw[SF ditree_ss, SF itree_ss]
  >- (every_case_tac >> gvs[is_Effi_def, is_Dffi_def]) >>
  Cases_on `cs` >> rw[SF ditree_ss, SF itree_ss, is_Effi_def, is_Dffi_def]
  >- (every_case_tac >> gvs[]) >>
  PairCases_on `h` >> Cases_on `h0` >> Cases_on `t` >>
  rw[SF ditree_ss, SF itree_ss, is_Effi_def, is_Dffi_def] >>
  every_case_tac >> gvs[]
QED

Theorem dstep_result_rel_single:
  ∀dsta deva dcsa db env.
    dstep_result_rel (Dstep dsta deva dcsa) (Dstep db) ∧
    ¬is_Dffi (dstep env dsta deva dcsa)
  ⇒ dstep_result_rel (dstep env dsta deva dcsa) (decl_step env db) ∧
    ∀ffi. dget_ffi (decl_step env db) = SOME ffi ⇒ dget_ffi (Dstep db) = SOME ffi
Proof
  ntac 3 gen_tac >> PairCases >> gen_tac >>
  simp[Once dstep_result_rel_cases] >> strip_tac >> gvs[deval_rel_cases]
  >- (
    Cases_on `d` >> gvs[decl_step_def, dstep_def] >>
    every_case_tac >> gvs[FST_THM, LAMBDA_PROD] >>
    simp[dstep_result_rel_cases, deval_rel_cases, ctxt_rel_def] >>
    gvs[dstate_rel_def, dget_ffi_def]
    )
  >- (
    Cases_on `db2` >> gvs[SF dsmallstep_ss, SF ditree_ss]
    >- simp[dstep_result_rel_cases] >>
    Cases_on `h` >> gvs[SF dsmallstep_ss, SF ditree_ss] >>
    Cases_on `l` >> gvs[SF dsmallstep_ss, SF ditree_ss] >>
    simp[dstep_result_rel_cases, deval_rel_cases, dget_ffi_def]
    ) >>
  Cases_on `ev` >> gvs[SF dsmallstep_ss, SF ditree_ss]
  >- (
    `¬is_Effi (estep (env',dsta.refs,Exp e,cs))` by (
      every_case_tac >> gvs[is_Effi_def, is_Dffi_def]) >>
    drule_at Any step_result_rel_single >>
    simp[Once step_result_rel_cases, PULL_EXISTS] >>
    disch_then drule >> disch_then $ qspec_then `db0.ffi` assume_tac >>
    rgs[dstate_rel_def, get_ffi_def] >>
    pop_assum mp_tac >> rw[step_result_rel_cases] >> gvs[dget_ffi_def, get_ffi_def] >>
    simp[dstep_result_rel_cases, deval_rel_cases, dstate_rel_def]
    ) >>
  Cases_on `cs` >> gvs[]
  >- (
    gvs[ctxt_rel_def, SF dsmallstep_ss, SF ditree_ss, dstate_rel_def] >>
    every_case_tac >> gvs[] >>
    gvs[dstep_result_rel_cases, deval_rel_cases, dstate_rel_def, dget_ffi_def]
    ) >>
  gvs[ctxt_rel_def] >> gvs[GSYM ctxt_rel_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  gvs[is_Dffi_eq_is_Effi_single] >>
  drule_at Any step_result_rel_single >> simp[FORALL_PROD] >>
  simp[step_result_rel_cases, ctxt_rel_def] >>
  simp[GSYM ctxt_rel_def, PULL_EXISTS, FORALL_PROD] >> disch_then drule_all >>
  disch_then $ qspec_then `db0.ffi` mp_tac >> rw[] >> gvs[] >>
  gvs[dstate_rel_def, dget_ffi_def, get_ffi_def] >>
  every_case_tac >> gvs[ctxt_frame_rel_cases, SF ditree_ss] >>
  Cases_on `t` >> gvs[ctxt_rel_def, SF ditree_ss] >>
  gvs[dstep_result_rel_cases, dstate_rel_def, deval_rel_cases, ctxt_rel_def]
QED

Theorem dstep_result_rel_n:
  ∀n dsta deva dcsa db env.
    dstep_result_rel (Dstep dsta deva dcsa) (Dstep db) ∧
    ¬ is_Dffi (dstep_n env n (Dstep dsta deva dcsa))
  ⇒ dstep_result_rel
      (dstep_n env n (Dstep dsta deva dcsa)) (dstep_n_cml env n (Dstep db))∧
    ∀ffi. dget_ffi (dstep_n_cml env n (Dstep db)) = SOME ffi
      ⇒ dget_ffi (Dstep db) = SOME ffi
Proof
  Induct >- simp[dstep_n_def, dstep_n_cml_def] >>
  simp[dstep_n_alt_def, dstep_n_cml_alt_def] >>
  rpt gen_tac >> strip_tac >>
  last_x_assum drule >> disch_then $ qspec_then `env` mp_tac >>
  impl_tac >- (every_case_tac >> gvs[is_Dffi_def]) >> strip_tac >>
  imp_res_tac dstep_result_rel_cases >> gvs[dget_ffi_def] >>
  drule dstep_result_rel_single >> disch_then $ qspec_then `env` mp_tac >>
  simp[] >> rw[] >> gvs[dget_ffi_def]
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

Theorem estep_to_Effi:
  estep ea = Effi s conf ws lnum env st cs ⇔
  ∃env' conf'.
    conf = MAP (λc. n2w (ORD c)) (EXPLODE conf') ∧
    ea = (env',st,Val (Litv (StrLit conf')),
            (Capp (FFI s) [Loc lnum] [],env)::cs) ∧
    store_lookup lnum st = SOME (W8array ws) ∧ s ≠ ""
Proof
  PairCases_on `ea` >> Cases_on `ea2` >> gvs[SF itree_ss]
  >- (
    Cases_on `e` >> gvs[SF itree_ss] >> every_case_tac >> gvs[] >>
    simp[application_thm] >> every_case_tac >> gvs[SF itree_ss]
    ) >>
  Cases_on `ea3` >> gvs[SF itree_ss] >>
  PairCases_on `h` >> reverse $ Cases_on `h0` >> gvs[SF itree_ss] >>
  every_case_tac >> gvs[]
  >- (Cases_on `l0` >> gvs[SF itree_ss] >> every_case_tac >> gvs[])
  >- (
    Cases_on `l` >> gvs[SF itree_ss] >>
    Cases_on `h` >> gvs[SF itree_ss] >> every_case_tac >> gvs[]
    ) >>
  Cases_on `l0` >> gvs[SF itree_ss] >> reverse eq_tac >> rw[]
  >- simp[application_thm] >>
  drule application_eq_Effi_fields >> rw[] >>
  gvs[application_thm] >> every_case_tac >> gvs[]
QED

Theorem dstep_to_Dffi:
  dstep env dst dev dcs = Dffi dst' (s,ws1,ws2,lnum,env',cs) locs pat dcs' ⇔
  ∃env'' conf.
    dst = dst' ∧ dcs = dcs' ∧
    dev = ExpVal env'' (Val (Litv (StrLit conf)))
            ((Capp (FFI s) [Loc lnum] [],env')::cs) locs pat ∧
    ws1 = MAP (λc. n2w (ORD c)) (EXPLODE conf) ∧
    store_lookup lnum dst.refs = SOME (W8array ws2) ∧ s ≠ ""
Proof
  Cases_on `∃d. dev = Decl d` >> gvs[dstep_def]
  >- (Cases_on `d` >> gvs[dstep_def] >> every_case_tac >> gvs[]) >>
  Cases_on `∃e. dev = Env e` >> gvs[dstep_def]
  >- (
    Cases_on `dcs` >> gvs[SF ditree_ss] >>
    Cases_on `h` >> Cases_on `l` >> gvs[SF ditree_ss]
    ) >>
  Cases_on `dev` >> gvs[SF ditree_ss] >> rw[] >> reverse eq_tac >> rw[]
  >- simp[SF ditree_ss, SF itree_ss, application_thm, dstate_component_equality] >>
  `is_Dffi (dstep env dst (ExpVal s' e l l0 p) dcs)` by gvs[is_Dffi_def] >>
  gvs[is_Dffi_eq_is_Effi_single, is_Effi_def, estep_to_Effi] >>
  rw[] >> gvs[SF ditree_ss, SF itree_ss, application_thm] >>
  simp[dstate_component_equality]
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
  rpt PairCases >> gvs[step_result_rel_cases] >> rw[estep_to_Effi] >> gvs[] >>
  gvs[get_ffi_def, ctxt_rel_def] >>
  gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> pairarg_tac >> gvs[] >>
  simp[SF smallstep_ss, cml_application_thm] >>
  simp[semanticPrimitivesTheory.do_app_def, ffiTheory.call_FFI_def] >>
  every_case_tac >> gvs[get_ffi_def]
  >- gvs[store_lookup_def, store_assign_def, store_v_same_type_def]
  >- rw[ffi_state_component_equality]
QED

Theorem decl_step_ffi_changed_dstep_to_Dffi:
  decl_step env (dst2, dev2, dcs) = Dstep (dst2', dev2', dcs') ∧
  dst2.ffi ≠ dst2'.ffi ∧
  dstate_rel dst1 dst2 ∧ deval_rel dev1 dev2 ⇒
  ∃env' env'' conf s lnum ccs locs pat ws.
    dev1 = ExpVal env' (Val $ Litv $ StrLit conf)
            ((Capp (FFI s) [Loc lnum] [], env'') :: ccs) locs pat ∧
    store_lookup lnum dst1.refs = SOME (W8array ws) ∧
    dstep env dst1 dev1 dcs = Dffi dst1
      (s,(MAP (λc. n2w $ ORD c) (EXPLODE conf)),ws,lnum,env'',ccs) locs pat dcs'
Proof
  rw[] >> drule_all decl_step_ffi_changed >> rw[] >>
  gvs[deval_rel_cases, ctxt_rel_def, dstate_rel_def] >>
  pairarg_tac >> gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >>
  gvs[SF ditree_ss, SF itree_ss] >>
  simp[application_thm, dstate_component_equality] >>
  gvs[SF dsmallstep_ss, SF smallstep_ss, cml_application_thm] >>
  gvs[semanticPrimitivesTheory.do_app_def, ffiTheory.call_FFI_def] >>
  gvs[store_assign_def, store_lookup_def, store_v_same_type_def]
QED

Theorem dstep_result_rel_single_FFI:
  ∀dsta deva dcsa db env dsta' s ws1 ws2 n env' cs ffi_call locs pat dcsa'.
    dstep_result_rel (Dstep dsta deva dcsa) (Dstep db) ∧
    dstep env dsta deva dcsa = Dffi dsta' (s,ws1,ws2,n,env',cs) locs pat dcsa'
  ⇒ ∃ffi.
      dget_ffi (Dstep db) = SOME ffi ∧
      ((∃ffi'. dget_ffi (decl_step env db) = SOME ffi' ∧ ffi' ≠ ffi) ∨
       (∃outcome.
          decl_step env db = Dabort (Rffi_error $ Final_event s ws1 ws2 outcome)))
Proof
  ntac 3 gen_tac >> PairCases >> rw[] >>
  gvs[dstep_result_rel_cases, dstep_to_Dffi, dget_ffi_def] >>
  gvs[deval_rel_cases, ctxt_rel_def] >>
  gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> pairarg_tac >> gvs[] >>
  simp[SF dsmallstep_ss, SF smallstep_ss, cml_application_thm] >>
  simp[semanticPrimitivesTheory.do_app_def, ffiTheory.call_FFI_def] >>
  every_case_tac >> gvs[dget_ffi_def] >>
  gvs[store_lookup_def, store_assign_def, store_v_same_type_def, dstate_rel_def] >>
  rw[ffi_state_component_equality]
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
  rpt PairCases >> gvs[step_result_rel_cases, estep_to_Effi] >> rw[get_ffi_def] >>
  gvs[ctxt_rel_def] >> gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >>
  pairarg_tac >> gvs[] >>
  simp[SF smallstep_ss, cml_application_thm] >>
  simp[semanticPrimitivesTheory.do_app_def, ffiTheory.call_FFI_def] >>
  every_case_tac >> gvs[store_assign_def, store_lookup_def, store_v_same_type_def]
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
  every_case_tac >> rgs[cml_application_thm] >>
  every_case_tac >> rgs[SF smallstep_ss] >> gvs[] >>
  rgs[semanticPrimitivesPropsTheory.do_app_cases] >> gvs[] >>
  rgs[step_result_rel_cases, ctxt_rel_def] >> gvs[] >>
  pairarg_tac >> rgs[ctxt_frame_rel_cases] >> gvs[] >>
  rgs[SF itree_ss, application_def, call_FFI_def] >> gvs[] >>
  every_case_tac >> rgs[store_lookup_def] >> gvs[]
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
  rgs[step_result_rel_cases] >> gvs[] >>
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

Theorem dstep_result_rel_single_FFI_strong:
  ∀dsta deva dcsa dstb devb dcsb env dsta' s conf ws lnum eenv cs1 locs pat dcsa'.
    dstep_result_rel (Dstep dsta deva dcsa) (Dstep (dstb, devb, dcsb)) ∧
    dstep env dsta deva dcsa = Dffi dsta' (s,conf,ws,lnum,eenv,cs1) locs pat dcsa'
  ⇒ ∃env' ffi conf' cs2.
      conf = MAP (λc. n2w (ORD c)) (EXPLODE conf') ∧
      deva = ExpVal env' (Val (Litv $ StrLit conf'))
              ((Capp (FFI s) [Loc lnum] [], eenv)::cs1) locs pat ∧
      devb = ExpVal env' (Val (Litv $ StrLit conf'))
              ((Capp (FFI s) [Loc lnum] () [], eenv)::cs2) locs pat ∧
      store_lookup lnum dsta.refs = SOME (W8array ws) ∧ s ≠ "" ∧
      dget_ffi (Dstep (dstb, devb, dcsb)) = SOME ffi ∧
      decl_step env (dstb, devb, dcsb) =
        case ffi.oracle s ffi.ffi_state conf ws of
        | Oracle_return ffi' ws' =>
            if LENGTH ws' ≠ LENGTH ws then
              Dabort $ Rffi_error $ Final_event s conf ws FFI_failed
            else
              Dstep (
                dstb with <|
                  refs := LUPDATE (W8array ws') lnum dstb.refs;
                  ffi := dstb.ffi with <|
                    ffi_state := ffi';
                    io_events := dstb.ffi.io_events ++ [IO_event s conf (ZIP (ws,ws'))]
                    |>
                  |>,
                ExpVal eenv (Val $ Conv NONE []) cs2 locs pat, dcsb)
        | Oracle_final outcome =>
            Dabort $ Rffi_error $ Final_event s conf ws outcome
Proof
  rw[] >> gvs[dstep_to_Dffi, dstep_result_rel_cases, deval_rel_cases, ctxt_rel_def] >>
  gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> pairarg_tac >> gvs[] >>
  simp[dget_ffi_def, SF dsmallstep_ss, SF smallstep_ss, cml_application_thm] >>
  simp[semanticPrimitivesTheory.do_app_def, ffiTheory.call_FFI_def] >>
  gvs[dstate_rel_def] >> every_case_tac >> gvs[] >>
  gvs[store_assign_def, store_lookup_def, store_v_same_type_def]
QED

Theorem dstep_result_rel_single_FFI_error:
  ∀dsta deva dcsa dstb devb dcsb.
    dstep_result_rel (Dstep dsta deva dcsa) (Dstep (dstb,devb,dcsb)) ∧
    decl_step env (dstb,devb,dcsb) = Dabort (Rffi_error (Final_event s conf ws outcome))
  ⇒ ∃lnum env' cs locs pat.
      dstep env dsta deva dcsa = Dffi dsta (s,conf,ws,lnum,env',cs) locs pat dcsa
Proof
  rw[] >> Cases_on `∃d. deva = Decl d` >> gvs[]
  >- (
    gvs[dstep_result_rel_cases, deval_rel_cases] >>
    Cases_on `d` >> gvs[SF dsmallstep_ss, SF ditree_ss] >>
    every_case_tac >> gvs[]
    ) >>
  Cases_on `∃e. deva = Env e` >> gvs[]
  >- (
    gvs[dstep_result_rel_cases, deval_rel_cases] >>
    Cases_on `e` >> gvs[SF dsmallstep_ss, SF ditree_ss] >>
    every_case_tac >> gvs[]
    ) >>
  Cases_on `deva` >> gvs[dstep_result_rel_cases, deval_rel_cases] >>
  gvs[SF dsmallstep_ss] >>
  qmatch_asmsub_abbrev_tac `e_step_result_CASE foo` >>
  qspec_then `(s',(dstb.refs,dstb.ffi),e,scs)` mp_tac $
    SIMP_RULE std_ss [Once SWAP_FORALL_THM] step_result_rel_single_FFI_error >>
  simp[step_result_rel_cases, PULL_EXISTS] >> disch_then drule >>
  simp[estep_to_Effi] >> strip_tac >> unabbrev_all_tac >>
  Cases_on `e` >> gvs[] >- (every_case_tac >> gvs[]) >>
  Cases_on `scs` >> gvs[ctxt_rel_def] >- (every_case_tac >> gvs[]) >>
  gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  every_case_tac >> gvs[] >>
  gvs[SF ditree_ss, SF itree_ss, application_thm, dstate_rel_def] >>
  simp[dstate_component_equality]
QED

Theorem dstep_result_rel_single':
  ∀dsta deva dcsa d2 env.
    (∀ffi. dget_ffi (decl_step env d2) = SOME ffi ⇒ dget_ffi (Dstep d2) = SOME ffi) ∧
    (∀a. decl_step env d2 ≠ Dabort $ Rffi_error a) ∧
    dstep_result_rel (Dstep dsta deva dcsa) (Dstep d2)
    ⇒ dstep_result_rel (dstep env dsta deva dcsa) (decl_step env d2)
Proof
  rw[] >> drule dstep_result_rel_single >> rw[] >>
  gvs[IMP_CONJ_THM, FORALL_AND_THM] >>
  first_x_assum irule >> CCONTR_TAC >> gvs[is_Dffi_def] >>
  PairCases_on `ev` >> drule_all dstep_result_rel_single_FFI >> rw[] >> gvs[]
QED

Theorem dstep_result_rel_n':
  ∀n dsta deva dcsa db env.
    dget_ffi (dstep_n_cml env n (Dstep db)) = dget_ffi (Dstep db) ∧
    dstep_result_rel (Dstep dsta deva dcsa) (Dstep db)
  ⇒ dstep_result_rel
      (dstep_n env n (Dstep dsta deva dcsa)) (dstep_n_cml env n (Dstep db))
Proof
  Induct >- rw[dstep_n_def, dstep_n_cml_def] >> rw[] >>
  `dstep_result_rel
    (dstep_n env n (Dstep dsta deva dcsa)) (dstep_n_cml env n (Dstep db))` by (
    last_x_assum irule >> simp[] >>
    qspecl_then [`SUC n`,`Dstep db`] mp_tac dstep_n_cml_preserved_FFI >>
    Cases_on `dstep_n_cml env (SUC n) (Dstep db)` >> gvs[dget_ffi_def] >>
    PairCases_on `db` >> gvs[dget_ffi_def]) >>
  simp[dstep_n_alt_def, dstep_n_cml_alt_def] >>
  rgs[dstep_result_rel_cases] >> gvs[] >>
  gvs[GSYM dstep_result_rel_cases, PULL_EXISTS, dget_ffi_def] >>
  qspecl_then [`SUC n`,`Dstep (st',dev2',dcsa)`]
    mp_tac dstep_n_cml_preserved_FFI >>
  gvs[dstep_n_cml_alt_def] >>
  Cases_on `decl_step env (st,dev2,dcs)` >> gvs[dget_ffi_def] >>
  disch_then $ qspecl_then [`p`,`env`] mp_tac >> simp[] >>
  disch_then $ qspec_then `n` mp_tac >> simp[dget_ffi_def] >> rw[] >> gvs[] >>
  qpat_assum `decl_step _ _ = _` $ once_rewrite_tac o single o GSYM >>
  irule dstep_result_rel_single' >>
  simp[dget_ffi_def, dstep_result_rel_cases]
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


(******************** dinterp ********************)

Theorem dinterp_Ret_Termination:
  dstate_rel dst st ∧ deval_rel deva devb ⇒
  (
    dinterp env (Dstep dst deva dcs) = Ret Termination ⇔
    (∃v st'. small_eval_dec env (st,devb,dcs) (st', Rval v) ∧ st.ffi = st'.ffi) ∨
    (∃v st'. small_eval_dec env (st,devb,dcs) (st', Rerr (Rraise v)) ∧ st.ffi = st'.ffi)
  )
Proof
  rw[Once dinterp] >> eq_tac >> rw[]
  >- (
    every_case_tac >> gvs[dstep_until_halt_def] >>
    pop_assum mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >> gvs[] >>
    every_case_tac >> gvs[dis_halt_def]
    >- (
      Induct_on `x` >> gvs[dstep_n_alt_def] >>
      reverse every_case_tac >> gvs[] >- metis_tac[] >- metis_tac[] >>
      rw[dstep_to_Ddone] >> disj1_tac >>
      rw[small_eval_dec_eq_dstep_n_cml, PULL_EXISTS] >>
      qspecl_then [`x`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
        assume_tac dstep_result_rel_n >>
      gvs[is_Dffi_def, dstep_result_rel_cases, deval_rel_cases] >>
      goal_assum drule >> gvs[dget_ffi_def]
      )
    >- (
      Induct_on `x` >> gvs[dstep_n_alt_def] >>
      every_case_tac >> gvs[] >> rw[] >>
      rw[small_eval_dec_eq_dstep_n_cml, PULL_EXISTS] >> disj2_tac >>
      qspecl_then [`x`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
        assume_tac dstep_result_rel_n >>
      gvs[is_Dffi_def, dstep_result_rel_cases] >> goal_assum drule >>
      qspecl_then [`d`,`d0`,`l`,`(st',dev2,l)`,`env`]
        assume_tac dstep_result_rel_single >>
      gvs[is_Dffi_def, dstep_result_rel_cases, dget_ffi_def]
      )
    )
  >- (
    gvs[small_eval_dec_eq_dstep_n_cml, dstep_until_halt_def] >>
    qspecl_then [`n`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
      assume_tac dstep_result_rel_n >>
    gvs[dstep_result_rel_cases, dget_ffi_def] >>
    pop_assum mp_tac >> impl_tac
    >- (
      irule dstep_result_rel_not_Dffi >> irule_at Any dstep_result_rel_n' >>
      qexists_tac `(st,devb,dcs)` >> simp[dget_ffi_def, dstep_result_rel_cases]
      ) >>
    strip_tac >> pop_assum mp_tac >> rw[deval_rel_cases] >>
    DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (qexists_tac `SUC n` >> simp[dstep_n_alt_def, SF ditree_ss, dis_halt_def]) >>
    `dstep_n env x (Dstep dst deva dcs) = dstep_n env (SUC n) (Dstep dst deva dcs)` by (
      irule dis_halt_dstep_n_eq >> simp[dstep_n_alt_def, SF ditree_ss, dis_halt_def]) >>
    gvs[dstep_n_alt_def, SF ditree_ss]
    )
  >- (
    gvs[small_eval_dec_eq_dstep_n_cml, dstep_until_halt_def] >>
    qspecl_then [`n`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
      assume_tac dstep_result_rel_n >>
    gvs[dstep_result_rel_cases, dget_ffi_def] >>
    pop_assum mp_tac >> impl_tac
    >- (
      irule dstep_result_rel_not_Dffi >> irule_at Any dstep_result_rel_n' >>
      qexists_tac `(st,devb,dcs)` >> simp[dget_ffi_def, dstep_result_rel_cases]
      ) >>
    strip_tac >>
    qspecl_then [`dst'`,`dev1`,`dcs'`,`(st',dev,dcs')`,`env`]
      assume_tac dstep_result_rel_single' >>
    gvs[dget_ffi_def, dstep_result_rel_cases] >>
    DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (qexists_tac `SUC n` >> simp[dstep_n_alt_def, SF ditree_ss, dis_halt_def]) >>
    `dstep_n env x (Dstep dst deva dcs) = dstep_n env (SUC n) (Dstep dst deva dcs)` by (
      irule dis_halt_dstep_n_eq >> simp[dstep_n_alt_def, SF ditree_ss, dis_halt_def]) >>
    gvs[dstep_n_alt_def, SF ditree_ss]
    )
QED

Theorem dinterp_Ret_Error:
  dstate_rel dst st ∧ deval_rel deva devb ⇒
  (
    dinterp env (Dstep dst deva dcs) = Ret Error ⇔
    ∃st'. small_eval_dec env (st,devb,dcs) (st',Rerr $ Rabort Rtype_error) ∧
          st.ffi = st'.ffi
  )
Proof
  rw[Once dinterp] >> eq_tac >> rw[]
  >- (
    every_case_tac >> gvs[dstep_until_halt_def] >>
    pop_assum mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >>
    every_case_tac >> gvs[dis_halt_def] >>
    simp[small_eval_dec_eq_dstep_n_cml, PULL_EXISTS] >>
    qspecl_then [`x`,`env`,`Dstep dst deva dcs`]
      assume_tac dis_halt_dstep_n_min >>
    gvs[dis_halt_def] >> qpat_x_assum `dstep_n _ x _ = _` kall_tac >>
    Cases_on `m` >> gvs[dstep_n_alt_def] >>
    reverse every_case_tac >> gvs[]
    >- (first_x_assum $ qspec_then `n` mp_tac >> simp[dis_halt_def]) >>
    qspecl_then [`n`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
      assume_tac dstep_result_rel_n >>
    gvs[dstep_result_rel_cases, is_Dffi_def] >> goal_assum drule >>
    qspecl_then [`d`,`d0`,`l`,`(st',dev2,l)`,`env`]
      assume_tac dstep_result_rel_single >>
    gvs[dstep_result_rel_cases, is_Dffi_def, dget_ffi_def]
    )
  >- (
    gvs[small_eval_dec_eq_dstep_n_cml] >>
    qspecl_then [`n`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
      assume_tac dstep_result_rel_n' >>
    gvs[dstep_result_rel_cases, is_Dffi_def, dget_ffi_def] >>
    qspecl_then [`dst'`,`dev1`,`dcs'`,`(st',dev,dcs')`,`env`]
      assume_tac dstep_result_rel_single' >>
    gvs[dstep_result_rel_cases, dget_ffi_def] >>
    simp[dstep_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (qexists_tac `SUC n` >> simp[dstep_n_alt_def, dis_halt_def]) >>
    `dstep_n env x (Dstep dst deva dcs) = dstep_n env (SUC n) (Dstep dst deva dcs)` by (
      irule dis_halt_dstep_n_eq >> simp[dstep_n_alt_def, dis_halt_def]) >>
    gvs[dstep_n_alt_def]
    )
QED

Theorem dinterp_Div:
  dstate_rel dst st ∧ deval_rel deva devb ⇒
  (
    dinterp env (Dstep dst deva dcs) = Div ⇔
    ∀n. ∃st2.
      dstep_n_cml env n (Dstep (st,devb,dcs)) = Dstep st2 ∧
      ¬dis_halt_cml (Dstep st2) ∧
      dget_ffi (Dstep st2) = SOME st.ffi
  )
Proof
  rw[Once dinterp] >> eq_tac >> rw[]
  >- (
    gvs[dstep_until_halt_def] >> every_case_tac >> gvs[] >>
    pop_assum mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >>
    pop_assum $ qspec_then `n` assume_tac >>
    Cases_on `dstep_n env n (Dstep dst deva dcs)` >> gvs[dis_halt_def] >>
    qspecl_then [`n`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
      assume_tac dstep_result_rel_n >>
    gvs[dstep_result_rel_cases, is_Dffi_def] >>
    gvs[dis_halt_cml_def, dget_ffi_def]
    )
  >- (
    simp[dstep_until_halt_def] >>
    DEEP_INTRO_TAC some_intro >> rw[] >>
    first_x_assum $ qspec_then `x` assume_tac >> gvs[dis_halt_cml_def] >>
    qspecl_then [`x`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
      assume_tac dstep_result_rel_n' >>
    gvs[dstep_result_rel_cases, dget_ffi_def, dis_halt_def]
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

Theorem trace_prefix_dec_Error:
  dstate_rel dsta st ∧ deval_rel deva devb ⇒

  ((∃n. trace_prefix n (oracle, ffi_st)
    (dinterp env (Dstep dsta deva dcs)) = (io, SOME Error)) ⇔

  ∃dst ffi'.
    (decl_step_reln env)^*
      (st with ffi := st.ffi with <| oracle := oracle; ffi_state := ffi_st |>,
       devb, dcs) dst ∧
    dget_ffi (Dstep dst) = SOME ffi' ∧
    ffi'.io_events = st.ffi.io_events ++ io ∧
    decl_step env dst = Dabort (Rtype_error))
Proof
  rw[] >> eq_tac >> rw[] >> rpt $ pop_assum mp_tac
  >- (
    map_every qid_spec_tac
      [`dsta`,`deva`,`dcs`,`oracle`,`ffi_st`,`st`,`devb`,`env`,`io`,`dcs`,`n`] >>
    Induct >> rw[trace_prefix_dinterp] >>
    gvs[dstep_until_halt_def] >> every_case_tac >> gvs[]
    >- (
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      drule dis_halt_dstep_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `dstep_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      `∃l. m = SUC l` by (Cases_on `m` >> gvs[dstep_n_def]) >> gvs[] >>
      pop_assum $ qspec_then `l` assume_tac >> gvs[] >>
      Cases_on `dstep_n env l (Dstep dsta deva dcs)` >> gvs[] >>
      gvs[dstep_n_alt_def, dis_halt_def] >>
      rename1 `_ = Dstep dsta' deva' dcs'` >>
      qmatch_goalsub_abbrev_tac `RTC _ (st',_)` >>
      qspecl_then [`l`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[dstep_result_rel_cases, is_Dffi_def] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> gvs[dget_ffi_def] >>
      rw[decl_step_reln_eq_dstep_n_cml, PULL_EXISTS] >> goal_assum drule >>
      simp[dget_ffi_def] >> unabbrev_all_tac >>
      gvs[state_component_equality, ffi_state_component_equality] >>
      qspecl_then [`dsta'`,`deva'`,`dcs'`,`(st'',dev2,dcs')`,`env`]
        mp_tac dstep_result_rel_single >>
      simp[dstep_result_rel_cases, is_Dffi_def]
      )
    >- (pairarg_tac >> gvs[trace_prefix_def])
    >- (
      pairarg_tac >> gvs[] >>
      rename1 `ExpVal env' _ cs locs pat` >>
      rename1 `Dffi dst (s,ws1,ws2,lnum,env'',_) _ _ dcs'` >>
      rename1 `_ conf ws = Oracle_return ffi_st' ws'` >>
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      drule dis_halt_dstep_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `dstep_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      `∃l. m = SUC l` by (Cases_on `m` >> gvs[dstep_n_def]) >> gvs[] >>
      pop_assum $ qspec_then `l` assume_tac >> gvs[] >>
      Cases_on `dstep_n env l (Dstep dsta deva dcs)` >> gvs[dis_halt_def] >>
      qmatch_goalsub_abbrev_tac `(st',_)` >>
      qspecl_then [`l`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[dstep_result_rel_cases, is_Dffi_def, dget_ffi_def] >>
      impl_tac >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> gvs[dget_ffi_def] >>
      gvs[dstep_n_alt_def] >>
      rw[Once RTC_CASES_RTC_TWICE, PULL_EXISTS] >>
      rw[Once RTC_CASES2] >> irule_at Any OR_INTRO_THM2 >>
      simp[PULL_EXISTS, GSYM CONJ_ASSOC] >>
      rw[decl_step_reln_eq_dstep_n_cml, PULL_EXISTS] >>
      goal_assum drule >> rw[decl_step_reln_def] >>
      drule_at Any dstep_result_rel_single_FFI_strong >>
      simp[dstep_result_rel_cases, PULL_EXISTS] >>
      disch_then drule_all >> strip_tac >> gvs[dget_ffi_def] >>
      unabbrev_all_tac >> gvs[ffi_state_component_equality] >>
      qmatch_goalsub_abbrev_tac `Dstep (st2,ev,ll)` >>
      last_x_assum $ drule_at $ Pos last >>
      qpat_x_assum `deval_rel _ _` mp_tac >>
      simp[deval_rel_cases, ctxt_rel_def, PULL_EXISTS] >>
      simp[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> strip_tac >>
      disch_then $ drule_at Any >>
      disch_then $ qspec_then `st2` mp_tac >>
      impl_tac >- (unabbrev_all_tac >> gvs[dstate_rel_def, dstep_to_Dffi]) >>
      simp[decl_step_reln_eq_dstep_n_cml] >> rw[] >> gvs[] >>
      qmatch_asmsub_abbrev_tac `dstep_n_cml _ _ (Dstep (st3,_))` >>
      `st3 = st2` by (unabbrev_all_tac >>
        gvs[state_component_equality, ffi_state_component_equality]) >>
      gvs[dstep_to_Dffi] >> goal_assum drule >> simp[] >>
      unabbrev_all_tac >> gvs[]
      )
    )
  >- (
    simp[decl_step_reln_eq_dstep_n_cml] >>
    simp[PULL_EXISTS, AND_IMP_INTRO, GSYM CONJ_ASSOC] >> gen_tac >>
    map_every qid_spec_tac
      [`dsta`,`deva`,`dcs`,`oracle`,`ffi_st`,`st`,`ffi'`,
        `dst`,`devb`,`env`,`io`,`dcs`,`n`] >>
    Induct >> rw[]
    >- (
      gvs[dstep_n_cml_def] >>
      qexists_tac `SUC 0` >> once_rewrite_tac[trace_prefix_dinterp] >>
      simp[dstep_until_halt_def] >>
      `dstep env dsta deva dcs = Dtype_error` by (
        qmatch_asmsub_abbrev_tac `Dstep (st',_)` >>
        qspecl_then [`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
          assume_tac dstep_result_rel_single' >>
        gvs[dget_ffi_def, dstep_result_rel_cases] >>
        pop_assum irule >> unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[]
      >- (qexists_tac `SUC 0` >> rewrite_tac[dstep_n_def] >> simp[dis_halt_def]) >>
      Cases_on `x` >> gvs[dstep_n_def, dis_halt_def] >> gvs[dget_ffi_def]
      ) >>
    gvs[dstep_n_cml_def] >>
    qmatch_asmsub_abbrev_tac `(st2,_)` >>
    Cases_on `decl_step env (st2,devb,dcs)` >> gvs[] >>
    Cases_on `dget_ffi (Dstep p) = SOME st2.ffi`
    >- (
      qspecl_then [`dsta`,`deva`,`dcs`,`(st2,devb,dcs)`,`env`]
        mp_tac dstep_result_rel_single' >>
      simp[dget_ffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> gvs[dget_ffi_def] >>
      unabbrev_all_tac >> gvs[] >>
      last_x_assum $ qspecl_then [
        `io`,`env`,`dev2`,`dst`,`ffi'`,
        `st'`,`ffi_st`,`oracle`,`dcs'`,`dev1`,`dst'`] mp_tac >>
      simp[] >> qpat_x_assum `_.ffi = _` $ assume_tac o GSYM >> simp[] >>
      `st' with ffi := st'.ffi = st'` by rw[state_component_equality] >> rw[] >>
      qexists_tac `n'` >> pop_assum mp_tac >>
      Cases_on `n'` >> once_rewrite_tac[trace_prefix_dinterp] >> rw[] >>
      DEP_ONCE_REWRITE_TAC[dstep_until_halt_take_step] >> simp[dis_halt_def]
      ) >>
    PairCases_on `p` >> gvs[dget_ffi_def] >>
    rename1 `dget_ffi _ = SOME ffi_new` >>
    rename1 `Dstep (st2',devb',dcs')` >>
    drule decl_step_ffi_changed >> simp[] >>
    drule decl_step_ffi_changed_dstep_to_Dffi >> simp[] >>
    disch_then $ qspecl_then [`dsta`,`deva`] mp_tac >> simp[] >> impl_tac
    >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
    strip_tac >> strip_tac >> gvs[] >>
    unabbrev_all_tac >>
    qpat_x_assum `dstate_rel _ _` mp_tac >> rw[dstate_rel_def] >> gvs[] >>
    gvs[ffi_state_component_equality] >>
    Q.REFINE_EXISTS_TAC `SUC m` >> once_rewrite_tac[trace_prefix_dinterp] >>
    simp[dstep_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (
      qexists_tac `SUC 0` >> rewrite_tac[dstep_n_def] >>
      simp[dstep_def, SF ditree_ss, dis_halt_def]
      ) >>
    Cases_on `x` >> gvs[dstep_n_def, dis_halt_def] >>
    qpat_x_assum `deval_rel _ _` mp_tac >> simp[deval_rel_cases, ctxt_rel_def] >>
    simp[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> rw[] >> gvs[] >>
    qmatch_asmsub_abbrev_tac `_ ++ [new_event]` >>
    qmatch_asmsub_abbrev_tac `dstep_n_cml _ _ (Dstep (st2,dev2,_))` >>
    last_x_assum $ qspecl_then [
      `TL io`,`env`,`dev2`,`dst`,`ffi_new`,`st2`,`ffi_st'`,`oracle`,`dcs`] mp_tac >>
    simp[Abbr `dev2`, deval_rel_cases, PULL_EXISTS] >> disch_then $ drule_at Any >>
    disch_then $
      qspec_then `dsta with refs := LUPDATE (W8array ws'') lnum dsta.refs` mp_tac >>
    qmatch_goalsub_abbrev_tac `Dstep (st3,_)` >>
    `st3 = st2` by (unabbrev_all_tac >> gvs[dstate_rel_def]) >> gvs[] >>
    simp[] >> reverse $ impl_keep_tac >> gvs[] >> rw[] >> unabbrev_all_tac >> gvs[]
    >- (qexists_tac `n'` >> simp[])
    >- gvs[dstate_rel_def] >>
    imp_res_tac io_events_mono_decl_step >>
    imp_res_tac io_events_mono_dstep_n_cml >> gvs[io_events_mono_def] >>
    PairCases_on `dst` >> gvs[dget_ffi_def] >>
    Cases_on `io` >> gvs[]
    )
QED

Theorem trace_prefix_dec_Termination:
  dstate_rel dsta st ∧ deval_rel deva devb ⇒

  ((∃n. trace_prefix n (oracle, ffi_st)
    (dinterp env (Dstep dsta deva dcs)) = (io, SOME Termination)) ⇔

  ∃dst ffi'.
    (decl_step_reln env)^*
      (st with ffi := st.ffi with <| oracle := oracle; ffi_state := ffi_st |>,
       devb, dcs) dst ∧
    dget_ffi (Dstep dst) = SOME ffi' ∧
    ffi'.io_events = st.ffi.io_events ++ io ∧
    (decl_step env dst = Ddone ∨ ∃v. decl_step env dst = Draise v))
Proof
  rw[] >> eq_tac >> rw[] >> rpt $ pop_assum mp_tac
  >- (
    map_every qid_spec_tac
      [`dsta`,`deva`,`dcs`,`oracle`,`ffi_st`,`st`,`devb`,`env`,`io`,`dcs`,`n`] >>
    Induct >> rw[trace_prefix_dinterp] >>
    gvs[dstep_until_halt_def] >> every_case_tac >> gvs[]
    >- (
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      Cases_on `x` >- gvs[dstep_n_def, dis_halt_def] >>
      gvs[dstep_n_alt_def] >> every_case_tac >> gvs[dis_halt_def]
      )
    >- (
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      qmatch_goalsub_abbrev_tac `(st',_)` >>
      drule dis_halt_dstep_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `dstep_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      Cases_on `m` >- gvs[dstep_n_def, dis_halt_def] >>
      gvs[dstep_n_alt_def] >> reverse every_case_tac >> gvs[] >> rename1 `SUC m`
      >- (first_x_assum $ qspec_then `m` assume_tac >> gvs[dis_halt_def]) >>
      qspecl_then [`m`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[is_Dffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> simp[decl_step_reln_eq_dstep_n_cml, PULL_EXISTS] >>
      goal_assum drule >> gvs[dget_ffi_def] >>
      unabbrev_all_tac >> gvs[ffi_state_component_equality] >>
      disj1_tac >> rgs[dstep_to_Ddone, Once deval_rel_cases, SF dsmallstep_ss]
      )
    >- (
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      qmatch_goalsub_abbrev_tac `(st',_)` >>
      drule dis_halt_dstep_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `dstep_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      Cases_on `m` >- gvs[dstep_n_def, dis_halt_def] >>
      gvs[dstep_n_alt_def] >> reverse every_case_tac >> gvs[] >> rename1 `SUC m`
      >- (first_x_assum $ qspec_then `m` assume_tac >> gvs[dis_halt_def]) >>
      qspecl_then [`m`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[is_Dffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> simp[decl_step_reln_eq_dstep_n_cml, PULL_EXISTS] >>
      goal_assum drule >> gvs[dget_ffi_def] >>
      unabbrev_all_tac >> gvs[ffi_state_component_equality] >>
      disj2_tac >>
      qspecl_then [`d`,`d0`,`l`,`(st'',dev2,l)`,`env`]
       mp_tac dstep_result_rel_single >>
      simp[is_Dffi_def, dstep_result_rel_cases]
      )
    >- gvs[trace_prefix_dinterp]
    >- (
      pairarg_tac >> gvs[] >>
      last_x_assum $ drule_at $ Pos last >> simp[deval_rel_cases, PULL_EXISTS] >>
      strip_tac >> qmatch_goalsub_abbrev_tac `(st',_)` >>
      qspecl_then [`x`,`env`,`Dstep dsta deva dcs`]
        assume_tac dis_halt_dstep_n_min >> gvs[dis_halt_def] >>
      qpat_x_assum `dstep_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      Cases_on `m` >- gvs[dstep_n_def, dis_halt_def] >>
      gvs[dstep_n_alt_def] >> reverse every_case_tac >> gvs[] >> rename1 `SUC m`
      >- (first_x_assum $ qspec_then `m` assume_tac >> gvs[dis_halt_def]) >>
      qspecl_then [`m`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[is_Dffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >>
      simp[Once RTC_CASES_RTC_TWICE, PULL_EXISTS, GSYM CONJ_ASSOC] >>
      simp[Once decl_step_reln_eq_dstep_n_cml, PULL_EXISTS] >>
      rename1 `Dffi dst (s,conf,ws,lnum,env',cs) locs pat` >>
      rename1 `_ = Dstep dsta' deva' dcs'` >>
      qmatch_goalsub_abbrev_tac `_ ++ [new_event]` >>
      goal_assum drule >> gvs[dget_ffi_def] >>
      drule_at Any dstep_result_rel_single_FFI_strong >>
      simp[dstep_result_rel_cases] >> disch_then drule_all >>
      strip_tac >> gvs[Abbr `st'`] >>
      gvs[dget_ffi_def, ffi_state_component_equality] >>
      rgs[Once deval_rel_cases, ctxt_rel_def] >> gvs[] >>
      gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >>
      first_x_assum $ drule_at Any >>
      disch_then $ qspec_then
        `st'' with <|
          refs := LUPDATE (W8array l') lnum st''.refs;
          ffi := st''.ffi with io_events := st''.ffi.io_events ++ [new_event]
          |>` mp_tac >>
      impl_tac >- (unabbrev_all_tac >> gvs[dstep_to_Dffi, dstate_rel_def]) >>
      strip_tac >> gvs[] >>
      simp[Once RTC_CASES1] >> irule_at Any OR_INTRO_THM2 >> simp[PULL_EXISTS] >>
      simp[decl_step_reln_def] >>
      qmatch_goalsub_abbrev_tac `(sta,_)` >>
      qmatch_asmsub_abbrev_tac `RTC _ (stb,_)` >>
      `sta = stb` by (
        unabbrev_all_tac >> gvs[dstep_to_Dffi] >>
        rw[state_component_equality, ffi_state_component_equality]) >>
      unabbrev_all_tac >> gvs[dstep_to_Dffi] >>
      goal_assum drule >> goal_assum drule >> simp[]
      )
    )
  >- (
    simp[decl_step_reln_eq_dstep_n_cml] >>
    simp[PULL_EXISTS, AND_IMP_INTRO, GSYM CONJ_ASSOC] >> gen_tac >>
    map_every qid_spec_tac
      [`dsta`,`deva`,`dcs`,`oracle`,`ffi_st`,`st`,`ffi'`,
        `dst`,`devb`,`env`,`io`,`dcs`,`n`] >>
    Induct >> rw[]
    >- (
      gvs[dstep_n_cml_def] >>
      qexists_tac `SUC 0` >> once_rewrite_tac[trace_prefix_dinterp] >>
      simp[dstep_until_halt_def] >>
      `dstep env dsta deva dcs = Ddone` by (
        qmatch_asmsub_abbrev_tac `Dstep (st',_)` >>
        qspecl_then [`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
          assume_tac dstep_result_rel_single' >>
        gvs[dget_ffi_def, dstep_result_rel_cases] >>
        pop_assum irule >> unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[]
      >- (qexists_tac `SUC 0` >> rewrite_tac[dstep_n_def] >> simp[dis_halt_def]) >>
      Cases_on `x` >> gvs[dstep_n_def, dis_halt_def] >> gvs[dget_ffi_def]
      ) >>
    gvs[dstep_n_cml_def] >>
    qmatch_asmsub_abbrev_tac `(st2,_)` >>
    Cases_on `decl_step env (st2,devb,dcs)` >> gvs[] >>
    Cases_on `dget_ffi (Dstep p) = SOME st2.ffi`
    >- (
      qspecl_then [`dsta`,`deva`,`dcs`,`(st2,devb,dcs)`,`env`]
        mp_tac dstep_result_rel_single' >>
      simp[dget_ffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> gvs[dget_ffi_def] >>
      unabbrev_all_tac >> gvs[] >>
      last_x_assum $ qspecl_then [
        `io`,`env`,`dev2`,`dst`,`ffi'`,
        `st'`,`ffi_st`,`oracle`,`dcs'`,`dev1`,`dst'`] mp_tac >>
      simp[] >> qpat_x_assum `_.ffi = _` $ assume_tac o GSYM >> simp[] >>
      `st' with ffi := st'.ffi = st'` by rw[state_component_equality] >> rw[] >>
      qexists_tac `n'` >> pop_assum mp_tac >>
      Cases_on `n'` >> once_rewrite_tac[trace_prefix_dinterp] >> rw[] >>
      DEP_ONCE_REWRITE_TAC[dstep_until_halt_take_step] >> simp[dis_halt_def]
      ) >>
    PairCases_on `p` >> gvs[dget_ffi_def] >>
    rename1 `dget_ffi _ = SOME ffi_new` >>
    rename1 `Dstep (st2',devb',dcs')` >>
    drule decl_step_ffi_changed >> simp[] >>
    drule decl_step_ffi_changed_dstep_to_Dffi >> simp[] >>
    disch_then $ qspecl_then [`dsta`,`deva`] mp_tac >> simp[] >> impl_tac
    >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
    strip_tac >> strip_tac >> gvs[] >>
    unabbrev_all_tac >>
    qpat_x_assum `dstate_rel _ _` mp_tac >> rw[dstate_rel_def] >> gvs[] >>
    gvs[ffi_state_component_equality] >>
    Q.REFINE_EXISTS_TAC `SUC m` >> once_rewrite_tac[trace_prefix_dinterp] >>
    simp[dstep_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (
      qexists_tac `SUC 0` >> rewrite_tac[dstep_n_def] >>
      simp[dstep_def, SF ditree_ss, dis_halt_def]
      ) >>
    Cases_on `x` >> gvs[dstep_n_def, dis_halt_def] >>
    qpat_x_assum `deval_rel _ _` mp_tac >> simp[deval_rel_cases, ctxt_rel_def] >>
    simp[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> rw[] >> gvs[] >>
    qmatch_asmsub_abbrev_tac `_ ++ [new_event]` >>
    qmatch_asmsub_abbrev_tac `dstep_n_cml _ _ (Dstep (st2,dev2,_))` >>
    last_x_assum $ qspecl_then [
      `TL io`,`env`,`dev2`,`dst`,`ffi_new`,`st2`,`ffi_st'`,`oracle`,`dcs`] mp_tac >>
    simp[Abbr `dev2`, deval_rel_cases, PULL_EXISTS] >> disch_then $ drule_at Any >>
    disch_then $
      qspec_then `dsta with refs := LUPDATE (W8array ws'') lnum dsta.refs` mp_tac >>
    qmatch_goalsub_abbrev_tac `Dstep (st3,_)` >>
    `st3 = st2` by (unabbrev_all_tac >> gvs[dstate_rel_def]) >> gvs[] >>
    simp[] >> reverse $ impl_keep_tac >> gvs[] >> rw[] >> unabbrev_all_tac >> gvs[]
    >- (qexists_tac `n'` >> simp[])
    >- gvs[dstate_rel_def] >>
    imp_res_tac io_events_mono_decl_step >>
    imp_res_tac io_events_mono_dstep_n_cml >> gvs[io_events_mono_def] >>
    PairCases_on `dst` >> gvs[dget_ffi_def] >>
    Cases_on `io` >> gvs[]
    )
  >- (
    simp[decl_step_reln_eq_dstep_n_cml] >>
    simp[PULL_EXISTS, AND_IMP_INTRO, GSYM CONJ_ASSOC] >> gen_tac >>
    map_every qid_spec_tac
      [`dsta`,`deva`,`dcs`,`oracle`,`ffi_st`,`st`,`ffi'`,
        `dst`,`devb`,`env`,`io`,`dcs`,`v`,`n`] >>
    Induct >> rw[]
    >- (
      gvs[dstep_n_cml_def] >>
      qexists_tac `SUC 0` >> once_rewrite_tac[trace_prefix_dinterp] >>
      simp[dstep_until_halt_def] >>
      `dstep env dsta deva dcs = Draise v` by (
        qmatch_asmsub_abbrev_tac `Dstep (st',_)` >>
        qspecl_then [`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
          assume_tac dstep_result_rel_single' >>
        gvs[dget_ffi_def, dstep_result_rel_cases] >>
        pop_assum irule >> unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[]
      >- (qexists_tac `SUC 0` >> rewrite_tac[dstep_n_def] >> simp[dis_halt_def]) >>
      Cases_on `x` >> gvs[dstep_n_def, dis_halt_def] >> gvs[dget_ffi_def]
      ) >>
    gvs[dstep_n_cml_def] >>
    qmatch_asmsub_abbrev_tac `(st2,_)` >>
    Cases_on `decl_step env (st2,devb,dcs)` >> gvs[] >>
    Cases_on `dget_ffi (Dstep p) = SOME st2.ffi`
    >- (
      qspecl_then [`dsta`,`deva`,`dcs`,`(st2,devb,dcs)`,`env`]
        mp_tac dstep_result_rel_single' >>
      simp[dget_ffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> gvs[dget_ffi_def] >>
      unabbrev_all_tac >> gvs[] >>
      last_x_assum $ qspecl_then [
        `v`,`io`,`env`,`dev2`,`dst`,`ffi'`,
        `st'`,`ffi_st`,`oracle`,`dcs'`,`dev1`,`dst'`] mp_tac >>
      simp[] >> qpat_x_assum `_.ffi = _` $ assume_tac o GSYM >> simp[] >>
      `st' with ffi := st'.ffi = st'` by rw[state_component_equality] >> rw[] >>
      qexists_tac `n'` >> pop_assum mp_tac >>
      Cases_on `n'` >> once_rewrite_tac[trace_prefix_dinterp] >> rw[] >>
      DEP_ONCE_REWRITE_TAC[dstep_until_halt_take_step] >> simp[dis_halt_def]
      ) >>
    PairCases_on `p` >> gvs[dget_ffi_def] >>
    rename1 `dget_ffi _ = SOME ffi_new` >>
    rename1 `Dstep (st2',devb',dcs')` >>
    drule decl_step_ffi_changed >> simp[] >>
    drule decl_step_ffi_changed_dstep_to_Dffi >> simp[] >>
    disch_then $ qspecl_then [`dsta`,`deva`] mp_tac >> simp[] >> impl_tac
    >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
    strip_tac >> strip_tac >> gvs[] >>
    unabbrev_all_tac >>
    qpat_x_assum `dstate_rel _ _` mp_tac >> rw[dstate_rel_def] >> gvs[] >>
    gvs[ffi_state_component_equality] >>
    Q.REFINE_EXISTS_TAC `SUC m` >> once_rewrite_tac[trace_prefix_dinterp] >>
    simp[dstep_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (
      qexists_tac `SUC 0` >> rewrite_tac[dstep_n_def] >>
      simp[dstep_def, SF ditree_ss, dis_halt_def]
      ) >>
    Cases_on `x` >> gvs[dstep_n_def, dis_halt_def] >>
    qpat_x_assum `deval_rel _ _` mp_tac >> simp[deval_rel_cases, ctxt_rel_def] >>
    simp[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> rw[] >> gvs[] >>
    qmatch_asmsub_abbrev_tac `_ ++ [new_event]` >>
    qmatch_asmsub_abbrev_tac `dstep_n_cml _ _ (Dstep (st2,dev2,_))` >>
    last_x_assum $ qspecl_then [
      `v`,`TL io`,`env`,`dev2`,`dst`,`ffi_new`,`st2`,`ffi_st'`,`oracle`,`dcs`] mp_tac >>
    simp[Abbr `dev2`, deval_rel_cases, PULL_EXISTS] >> disch_then $ drule_at Any >>
    disch_then $
      qspec_then `dsta with refs := LUPDATE (W8array ws'') lnum dsta.refs` mp_tac >>
    qmatch_goalsub_abbrev_tac `Dstep (st3,_)` >>
    `st3 = st2` by (unabbrev_all_tac >> gvs[dstate_rel_def]) >> gvs[] >>
    simp[] >> reverse $ impl_keep_tac >> gvs[] >> rw[] >> unabbrev_all_tac >> gvs[]
    >- (qexists_tac `n'` >> simp[])
    >- gvs[dstate_rel_def] >>
    imp_res_tac io_events_mono_decl_step >>
    imp_res_tac io_events_mono_dstep_n_cml >> gvs[io_events_mono_def] >>
    PairCases_on `dst` >> gvs[dget_ffi_def] >>
    Cases_on `io` >> gvs[]
    )
QED

Theorem trace_prefix_dec_FinalFFI:
  dstate_rel dsta st ∧ deval_rel deva devb ⇒

  ((∃n. trace_prefix n (oracle, ffi_st)
    (dinterp env (Dstep dsta deva dcs)) = (io, SOME $ FinalFFI (s,conf,ws) outcome)) ⇔

  ∃dst ffi'.
    (decl_step_reln env)^*
      (st with ffi := st.ffi with <| oracle := oracle; ffi_state := ffi_st |>,
       devb, dcs) dst ∧
    dget_ffi (Dstep dst) = SOME ffi' ∧
    ffi'.io_events = st.ffi.io_events ++ io ∧
    decl_step env dst = Dabort (Rffi_error $ Final_event s conf ws outcome))
Proof
  rw[] >> eq_tac >> rw[] >> rpt $ pop_assum mp_tac
  >- (
    map_every qid_spec_tac
      [`dsta`,`deva`,`dcs`,`oracle`,`ffi_st`,`st`,`devb`,`env`,`io`,`dcs`,`n`] >>
    Induct >> rw[trace_prefix_dinterp] >>
    gvs[dstep_until_halt_def] >> every_case_tac >> gvs[]
    >- gvs[trace_prefix_dinterp]
    >- (
      qspecl_then [`x`,`env`,`Dstep dsta deva dcs`]
        assume_tac dis_halt_dstep_n_min >> gvs[dis_halt_def] >>
      qpat_x_assum `dstep_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      Cases_on `m` >- gvs[dstep_n_def, dis_halt_def] >>
      gvs[dstep_n_alt_def] >> reverse every_case_tac >> gvs[] >> rename1 `SUC m`
      >- (first_x_assum $ qspec_then `m` assume_tac >> gvs[dis_halt_def]) >>
      qmatch_goalsub_abbrev_tac `(st',_)` >>
      qspecl_then [`m`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[is_Dffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >>
      simp[Once decl_step_reln_eq_dstep_n_cml, PULL_EXISTS] >>
      rename1 `Dffi dst (s,conf,ws,lnum,env',cs) locs pat dcs''` >>
      rename1 `_ = Dstep dsta' deva' dcs'` >>
      goal_assum drule >> gvs[dget_ffi_def] >>
      drule_at Any dstep_result_rel_single_FFI_strong >>
      simp[dstep_result_rel_cases] >> disch_then drule_all >>
      strip_tac >> gvs[Abbr `st'`] >>
      gvs[dget_ffi_def, ffi_state_component_equality]
      )
    >- (
      pairarg_tac >> gvs[] >>
      last_x_assum $ drule_at $ Pos last >>
      simp[deval_rel_cases, PULL_EXISTS] >> strip_tac >>
      qspecl_then [`x`,`env`,`Dstep dsta deva dcs`]
        assume_tac dis_halt_dstep_n_min >> gvs[dis_halt_def] >>
      qpat_x_assum `dstep_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      Cases_on `m` >- gvs[dstep_n_def, dis_halt_def] >>
      gvs[dstep_n_alt_def] >> reverse every_case_tac >> gvs[] >> rename1 `SUC m`
      >- (first_x_assum $ qspec_then `m` assume_tac >> gvs[dis_halt_def]) >>
      qmatch_goalsub_abbrev_tac `(st',_)` >>
      qspecl_then [`m`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[is_Dffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> simp[Once RTC_CASES_RTC_TWICE, PULL_EXISTS, GSYM CONJ_ASSOC] >>
      simp[Once decl_step_reln_eq_dstep_n_cml, PULL_EXISTS] >>
      rename1 `Dffi dst (s',conf',ws',lnum,env',cs) locs pat dcs''` >>
      rename1 `_ = Dstep dsta' deva' dcs'` >>
      goal_assum drule >> gvs[dget_ffi_def] >>
      drule_at Any dstep_result_rel_single_FFI_strong >>
      simp[dstep_result_rel_cases] >> disch_then drule_all >>
      strip_tac >> gvs[Abbr `st'`] >>
      gvs[dget_ffi_def, ffi_state_component_equality] >>
      rgs[Once deval_rel_cases, ctxt_rel_def] >> gvs[GSYM ctxt_rel_def] >>
      simp[Once RTC_CASES1] >> irule_at Any OR_INTRO_THM2 >> simp[PULL_EXISTS] >>
      simp[decl_step_reln_def] >>
      first_x_assum $ drule_at Any >> gvs[dstep_to_Dffi] >>
      qmatch_goalsub_abbrev_tac `RTC _ (st1,_)` >>
      disch_then $ qspec_then `st1` mp_tac >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >> strip_tac >> gvs[] >>
      qmatch_asmsub_abbrev_tac `RTC _ (st2,_)` >>
      `st1 = st2` by (
        unabbrev_all_tac >>
        rw[state_component_equality, ffi_state_component_equality]) >>
      gvs[] >> goal_assum drule >> simp[] >>
      unabbrev_all_tac >> gvs[]
      )
    >- (
      qspecl_then [`x`,`env`,`Dstep dsta deva dcs`]
        assume_tac dis_halt_dstep_n_min >> gvs[dis_halt_def] >>
      qpat_x_assum `dstep_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      Cases_on `m` >- gvs[dstep_n_def, dis_halt_def] >>
      gvs[dstep_n_alt_def] >> reverse every_case_tac >> gvs[] >> rename1 `SUC m`
      >- (first_x_assum $ qspec_then `m` assume_tac >> gvs[dis_halt_def]) >>
      qmatch_goalsub_abbrev_tac `(st',_)` >>
      qspecl_then [`m`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[is_Dffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >>
      simp[Once decl_step_reln_eq_dstep_n_cml, PULL_EXISTS] >>
      rename1 `Dffi dst (s',conf',ws',lnum,env',cs) locs pat dcs''` >>
      rename1 `_ = Dstep dsta' deva' dcs'` >>
      goal_assum drule >> gvs[dget_ffi_def] >>
      drule_at Any dstep_result_rel_single_FFI_strong >>
      simp[dstep_result_rel_cases] >> disch_then drule_all >>
      strip_tac >> gvs[Abbr `st'`] >>
      gvs[dget_ffi_def, ffi_state_component_equality]
      )
    )
  >- (
    simp[decl_step_reln_eq_dstep_n_cml] >>
    simp[PULL_EXISTS, AND_IMP_INTRO, GSYM CONJ_ASSOC] >> gen_tac >>
    map_every qid_spec_tac
      [`dsta`,`deva`,`dcs`,`oracle`,`ffi_st`,`st`,`ffi'`,
        `dst`,`devb`,`env`,`io`,`dcs`,`n`] >>
    Induct >> rw[]
    >- (
      gvs[dstep_n_cml_def] >>
      qexists_tac `SUC $ SUC 0` >> once_rewrite_tac[trace_prefix_dinterp] >>
      simp[dstep_until_halt_def] >>
      drule_at Any dstep_result_rel_single_FFI_error >>
      simp[dstep_result_rel_cases] >> disch_then $ drule_at Any >>
      disch_then $ qspec_then `dsta` mp_tac >>
      impl_tac >- gvs[dstate_rel_def] >> strip_tac >> gvs[] >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[]
      >- (qexists_tac `SUC 0` >> simp[dstep_n_def, dis_halt_def]) >>
      drule_at Any dis_halt_dstep_n_eq >>
      disch_then $ qspec_then `SUC 0` $ mp_tac >> simp[dstep_n_def, dis_halt_def] >>
      disch_then kall_tac >> pop_assum kall_tac >>
      drule_at Any dstep_result_rel_single_FFI_strong >>
      simp[dstep_result_rel_cases] >> disch_then $ drule_at Any >>
      qmatch_asmsub_abbrev_tac `Dstep (st1,_)` >>
      disch_then $ qspec_then `st1` mp_tac >>
      impl_tac >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> gvs[] >> unabbrev_all_tac >> gvs[dget_ffi_def] >>
      every_case_tac >> rgs[]
      ) >>
    gvs[dstep_n_cml_def] >>
    qmatch_asmsub_abbrev_tac `(st2,_)` >>
    Cases_on `decl_step env (st2,devb,dcs)` >> gvs[] >>
    Cases_on `dget_ffi (Dstep p) = SOME st2.ffi`
    >- (
      qspecl_then [`dsta`,`deva`,`dcs`,`(st2,devb,dcs)`,`env`]
        mp_tac dstep_result_rel_single' >>
      simp[dget_ffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> gvs[dget_ffi_def] >>
      unabbrev_all_tac >> gvs[] >>
      last_x_assum $ qspecl_then [
        `io`,`env`,`dev2`,`dst`,`ffi'`,
        `st'`,`ffi_st`,`oracle`,`dcs'`,`dev1`,`dst'`] mp_tac >>
      simp[] >> qpat_x_assum `_.ffi = _` $ assume_tac o GSYM >> simp[] >>
      `st' with ffi := st'.ffi = st'` by rw[state_component_equality] >> rw[] >>
      qexists_tac `n'` >> pop_assum mp_tac >>
      Cases_on `n'` >> once_rewrite_tac[trace_prefix_dinterp] >> rw[] >>
      DEP_ONCE_REWRITE_TAC[dstep_until_halt_take_step] >> simp[dis_halt_def]
      ) >>
    PairCases_on `p` >> gvs[dget_ffi_def] >>
    rename1 `dget_ffi _ = SOME ffi_new` >>
    rename1 `Dstep (st2',devb',dcs')` >>
    drule decl_step_ffi_changed >> simp[] >>
    drule decl_step_ffi_changed_dstep_to_Dffi >> simp[] >>
    disch_then $ qspecl_then [`dsta`,`deva`] mp_tac >> simp[] >> impl_tac
    >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
    strip_tac >> strip_tac >> gvs[] >>
    unabbrev_all_tac >>
    qpat_x_assum `dstate_rel _ _` mp_tac >> rw[dstate_rel_def] >> gvs[] >>
    gvs[ffi_state_component_equality] >>
    Q.REFINE_EXISTS_TAC `SUC m` >> once_rewrite_tac[trace_prefix_dinterp] >>
    simp[dstep_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (
      qexists_tac `SUC 0` >> rewrite_tac[dstep_n_def] >>
      simp[dstep_def, SF ditree_ss, dis_halt_def]
      ) >>
    Cases_on `x` >> gvs[dstep_n_def, dis_halt_def] >>
    qpat_x_assum `deval_rel _ _` mp_tac >> simp[deval_rel_cases, ctxt_rel_def] >>
    simp[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> rw[] >> gvs[] >>
    qmatch_asmsub_abbrev_tac `_ ++ [new_event]` >>
    qmatch_asmsub_abbrev_tac `dstep_n_cml _ _ (Dstep (st2,dev2,_))` >>
    rename1 `ZIP (ws1,ws2)` >>
    last_x_assum $ qspecl_then [
      `TL io`,`env`,`dev2`,`dst`,`ffi_new`,`st2`,`ffi_st'`,`oracle`,`dcs`] mp_tac >>
    simp[Abbr `dev2`, deval_rel_cases, PULL_EXISTS] >> disch_then $ drule_at Any >>
    disch_then $
      qspec_then `dsta with refs := LUPDATE (W8array ws2) lnum dsta.refs` mp_tac >>
    qmatch_goalsub_abbrev_tac `Dstep (st3,_)` >>
    `st3 = st2` by (unabbrev_all_tac >> gvs[dstate_rel_def]) >> gvs[] >>
    simp[] >> reverse $ impl_keep_tac >> gvs[] >> rw[] >> unabbrev_all_tac >> gvs[]
    >- (qexists_tac `n'` >> simp[])
    >- gvs[dstate_rel_def] >>
    imp_res_tac io_events_mono_decl_step >>
    imp_res_tac io_events_mono_dstep_n_cml >> gvs[io_events_mono_def] >>
    PairCases_on `dst` >> gvs[dget_ffi_def] >>
    Cases_on `io` >> gvs[]
    )
QED

Theorem trace_prefix_dec_divergence_RL:
  dstate_rel dsta st ∧ deval_rel deva devb ∧
  small_decl_diverges env (st, devb, dcs) ∧
  (decl_step_reln env)^* (st, devb, dcs) dst ∧
  (FST dst).ffi.io_events = st.ffi.io_events ++ io ⇒
  ∃n.
    trace_prefix n (st.ffi.oracle, st.ffi.ffi_state)
      (dinterp env (Dstep dsta deva dcs)) = (io, NONE)
Proof
  simp[decl_step_reln_eq_dstep_n_cml, PULL_EXISTS] >> gen_tac >>
  map_every qid_spec_tac
    [`dsta`,`deva`,`dcs`,`st`,`devb`,`env`,`io`,`dst`,`n`] >>
  Induct >> rw[dstep_n_cml_def] >> gvs[]
  >- (qexists_tac `0` >> simp[trace_prefix_dinterp]) >>
  Cases_on `decl_step env (st,devb,dcs)` >> gvs[] >>
  Cases_on `dget_ffi (Dstep p) = SOME st.ffi`
  >- (
    qspecl_then [`dsta`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
      mp_tac dstep_result_rel_single' >>
    simp[dget_ffi_def, dstep_result_rel_cases] >> strip_tac >> gvs[] >>
    last_x_assum drule >> disch_then drule >>
    disch_then $ drule_at Any >> gvs[dget_ffi_def] >>
    impl_tac >> rw[] >> gvs[]
    >- (
      gvs[small_decl_diverges_def] >> rw[] >>
      first_x_assum irule >> simp[Once RTC_CASES1, decl_step_reln_def]
      ) >>
    rename1 `trace_prefix m _` >> qexists_tac `m` >> pop_assum mp_tac >>
    Cases_on `m` >> once_rewrite_tac[trace_prefix_dinterp] >> rw[] >>
    DEP_ONCE_REWRITE_TAC[dstep_until_halt_take_step] >> simp[dis_halt_def]
    ) >>
  PairCases_on `p` >> gvs[dget_ffi_def] >>
  rename1 `Dstep (st',devb',dcs')` >>
  drule decl_step_ffi_changed >> simp[] >>
  drule decl_step_ffi_changed_dstep_to_Dffi >> simp[] >> disch_then $ drule_all >>
  strip_tac >> strip_tac >> gvs[] >>
  rgs[Once deval_rel_cases, ctxt_rel_def] >> gvs[] >>
  gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >>
  Q.REFINE_EXISTS_TAC `SUC m` >> once_rewrite_tac[trace_prefix_dinterp] >>
  simp[dstep_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
  >- (
    pop_assum $ qspec_then `SUC 0` mp_tac >> rewrite_tac[dstep_n_def] >>
    simp[SF ditree_ss, dis_halt_def]
    ) >>
  drule_at Any dis_halt_dstep_n_eq >>
  disch_then $ qspec_then `SUC 0` mp_tac >> simp[dstep_n_def, dis_halt_def] >>
  strip_tac >> rgs[dstep_to_Dffi, Once dstate_rel_def] >>
  qmatch_asmsub_abbrev_tac `dstep_n_cml _ _ (Dstep (st1,ev,dcs))` >>
  last_x_assum $ qspecl_then [
    `dst`,`TL io`,`env`,`ev`,`st1`,`dcs`] mp_tac >>
  simp[Abbr `ev`, deval_rel_cases, PULL_EXISTS] >>
  disch_then $ drule_at Any >>
  disch_then $ qspec_then
    `dsta with refs := LUPDATE (W8array ws'') lnum st.refs` mp_tac >>
  unabbrev_all_tac >> simp[dstate_rel_def] >> reverse impl_keep_tac >> gvs[] >> rw[]
  >- (qexists_tac `n'` >> simp[])
  >- (
    gvs[small_decl_diverges_def] >> rw[] >>
    last_x_assum irule >> simp[Once RTC_CASES1, decl_step_reln_def]
    )
  >- (
    imp_res_tac io_events_mono_decl_step >>
    imp_res_tac io_events_mono_dstep_n_cml >> gvs[io_events_mono_def] >>
    Cases_on `io` >> gvs[]
    )
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


(******************** Collected results for declarations ********************)

Theorem small_eval_dec_trace_prefix_termination:
  dstate_rel dst st ∧
  (small_eval_dec env (st,Decl d,[]) (st',Rval e) ∨
   small_eval_dec env (st,Decl d,[]) (st',Rerr (Rraise v)))
  ⇒ ∃n io.
      trace_prefix n (st.ffi.oracle, st.ffi.ffi_state)
        (dinterp env (Dstep dst (Decl d) [])) = (io, SOME Termination) ∧
      st'.ffi.io_events = st.ffi.io_events ++ io
Proof
  rw[small_eval_dec_def, decl_step_reln_eq_dstep_n_cml] >>
  imp_res_tac io_events_mono_dstep_n_cml >>
  gvs[io_events_mono_def, rich_listTheory.IS_PREFIX_APPEND] >>
  qpat_x_assum `_ ⇒ _` kall_tac >> rename1 `_ ++ io` >>
  drule $ iffRL trace_prefix_dec_Termination >>
  disch_then $ qspecl_then [
    `st.ffi.oracle`,`io`,`st.ffi.ffi_state`,`env`,`Decl d`,`Decl d`,`[]`] mp_tac >>
  simp[deval_rel_cases, decl_step_reln_eq_dstep_n_cml, PULL_EXISTS] >>
  qmatch_goalsub_abbrev_tac `(st1,_)` >>
  `st1 = st` by (
    unabbrev_all_tac >>
    rw[state_component_equality, ffi_state_component_equality]) >>
  unabbrev_all_tac >> gvs[] >>
  disch_then drule >> simp[dget_ffi_def, SF dsmallstep_ss] >>
  PairCases_on `dst'` >> simp[dget_ffi_def]
QED

Theorem trace_prefix_small_eval_dec_termination:
  trace_prefix n (st.ffi.oracle, st.ffi.ffi_state)
    (dinterp env (Dstep dst (Decl d) [])) = (io, SOME Termination) ∧
  dstate_rel dst st
  ⇒ ∃st' e v.
      (small_eval_dec env (st,Decl d,[]) (st', Rval e) ∨
       small_eval_dec env (st,Decl d,[]) (st', Rerr (Rraise v))) ∧
      st'.ffi.io_events = st.ffi.io_events ++ io
Proof
  rw[small_eval_dec_def] >>
  drule $ iffLR trace_prefix_dec_Termination >> simp[PULL_EXISTS] >>
  disch_then $ drule_at Any >> simp[deval_rel_cases, PULL_EXISTS] >>
  qmatch_goalsub_abbrev_tac `(st1,_)` >>
  `st1 = st` by (
    unabbrev_all_tac >>
    rw[state_component_equality, ffi_state_component_equality]) >>
  unabbrev_all_tac >> gvs[] >> rw[] >> gvs[] >>
  PairCases_on `dst'` >> gvs[decl_step_to_Ddone]
  >- (irule_at Any OR_INTRO_THM1 >> goal_assum drule >> gvs[dget_ffi_def])
  >- (
    irule_at Any OR_INTRO_THM2 >> simp[PULL_EXISTS, GSYM CONJ_ASSOC, EXISTS_PROD] >>
    goal_assum drule >> gvs[dget_ffi_def]
    )
QED

Theorem small_eval_dec_trace_prefix_type_error:
  dstate_rel dst st ∧
  small_eval_dec env (st,Decl d,[]) (st', Rerr (Rabort Rtype_error))
  ⇒ ∃n io.
      trace_prefix n (st.ffi.oracle, st.ffi.ffi_state)
        (dinterp env (Dstep dst (Decl d) [])) = (io, SOME Error) ∧
      st'.ffi.io_events = st.ffi.io_events ++ io
Proof
  rw[small_eval_dec_def, decl_step_reln_eq_dstep_n_cml] >>
  imp_res_tac io_events_mono_dstep_n_cml >>
  gvs[io_events_mono_def, rich_listTheory.IS_PREFIX_APPEND] >>
  qpat_x_assum `_ ⇒ _` kall_tac >> rename1 `_ ++ io` >>
  drule $ iffRL trace_prefix_dec_Error >>
  disch_then $ qspecl_then [
    `st.ffi.oracle`,`io`,`st.ffi.ffi_state`,`env`,`Decl d`,`Decl d`,`[]`] mp_tac >>
  simp[deval_rel_cases, PULL_EXISTS, decl_step_reln_eq_dstep_n_cml] >>
  qmatch_goalsub_abbrev_tac `(st1,_)` >>
  `st1 = st` by (
    unabbrev_all_tac >>
    rw[state_component_equality, ffi_state_component_equality]) >>
  unabbrev_all_tac >> gvs[] >>
  disch_then drule >> simp[dget_ffi_def]
QED

Theorem trace_prefix_small_eval_dec_type_error:
  trace_prefix n (st.ffi.oracle, st.ffi.ffi_state)
    (dinterp env (Dstep dst (Decl d) [])) = (io, SOME Error) ∧
  dstate_rel dst st
  ⇒ ∃st'.  small_eval_dec env (st,Decl d,[]) (st', Rerr (Rabort Rtype_error))
Proof
  rw[] >> drule $ iffLR trace_prefix_dec_Error >> simp[PULL_EXISTS] >>
  disch_then $ drule_at Any >> simp[deval_rel_cases] >>
  qmatch_goalsub_abbrev_tac `(st1,_)` >>
  `st1 = st` by (
    unabbrev_all_tac >>
    rw[state_component_equality, ffi_state_component_equality]) >>
  unabbrev_all_tac >> gvs[] >>
  simp[small_eval_dec_def, PULL_EXISTS, EXISTS_PROD] >> rw[] >> gvs[] >>
  PairCases_on `dst'` >> goal_assum drule >> simp[]
QED

Theorem small_eval_trace_prefix_ffi_error:
  small_eval_dec env (st,Decl d,[])
    (st', Rerr (Rabort $ Rffi_error $ Final_event s conf ws outcome)) ∧
  dstate_rel dst st
  ⇒ ∃n io.
      trace_prefix n (st.ffi.oracle, st.ffi.ffi_state)
        (dinterp env (Dstep dst (Decl d) [])) =
          (io, SOME $ FinalFFI (s,conf,ws) outcome) ∧
      st'.ffi.io_events = st.ffi.io_events ++ io
Proof
  rw[small_eval_dec_def, decl_step_reln_eq_dstep_n_cml] >>
  imp_res_tac io_events_mono_dstep_n_cml >>
  gvs[io_events_mono_def, rich_listTheory.IS_PREFIX_APPEND] >>
  qpat_x_assum `_ ⇒ _` kall_tac >> rename1 `_ ++ io` >>
  drule $ iffRL trace_prefix_dec_FinalFFI >>
  disch_then $ qspecl_then [`ws`,`s`,`outcome`,`st.ffi.oracle`,`io`,
    `st.ffi.ffi_state`,`env`,`Decl d`,`Decl d`,`[]`,`conf`] mp_tac >>
  simp[deval_rel_cases, PULL_EXISTS, decl_step_reln_eq_dstep_n_cml] >>
  qmatch_goalsub_abbrev_tac `(st1,_)` >>
  `st1 = st` by (
    unabbrev_all_tac >>
    rw[state_component_equality, ffi_state_component_equality]) >>
  unabbrev_all_tac >> gvs[] >>
  disch_then drule >> simp[dget_ffi_def]
QED

Theorem trace_prefix_small_eval_dec_type_error:
  trace_prefix n (st.ffi.oracle, st.ffi.ffi_state)
    (dinterp env (Dstep dst (Decl d) [])) =
      (io, SOME $ FinalFFI (s,conf,ws) outcome) ∧
  dstate_rel dst st
  ⇒ ∃st'. small_eval_dec env (st,Decl d,[])
            (st', Rerr (Rabort $ Rffi_error $ Final_event s conf ws outcome)) ∧
      st'.ffi.io_events = st.ffi.io_events ++ io
Proof
  rw[] >> drule $ iffLR trace_prefix_dec_FinalFFI >> simp[PULL_EXISTS] >>
  disch_then $ drule_at Any >> simp[deval_rel_cases] >>
  qmatch_goalsub_abbrev_tac `(st1,_)` >>
  `st1 = st` by (
    unabbrev_all_tac >>
    rw[state_component_equality, ffi_state_component_equality]) >>
  unabbrev_all_tac >> gvs[] >>
  simp[small_eval_dec_def, PULL_EXISTS, EXISTS_PROD] >> rw[] >> gvs[] >>
  PairCases_on `dst'` >> goal_assum drule >> gvs[dget_ffi_def]
QED

Theorem decl_diverges_trace_prefix:
  small_decl_diverges env (st,Decl d,[]) ∧
  (decl_step_reln env)^* (st,Decl d,[]) (st',dev,dcs) ∧
  dstate_rel dst st
  ⇒ ∃n io.
      trace_prefix n (st.ffi.oracle, st.ffi.ffi_state)
        (dinterp env (Dstep dst (Decl d) [])) = (io, NONE) ∧
      st'.ffi.io_events = st.ffi.io_events ++ io
Proof
  rw[] >> drule trace_prefix_dec_divergence_RL >>
  disch_then $ drule_at Any >> simp[deval_rel_cases] >> strip_tac >>
  gvs[decl_step_reln_eq_dstep_n_cml] >>
  imp_res_tac io_events_mono_dstep_n_cml >>
  gvs[io_events_mono_def, rich_listTheory.IS_PREFIX_APPEND] >>
  goal_assum drule
QED

(* TODO lift infinite behaviour relation to lprefix_lub *)


(****************************************)

val _ = export_theory();

