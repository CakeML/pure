(* Relating the itree- and FFI state-based CakeML semantics *)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open optionTheory relationTheory pairTheory listTheory;
open lem_pervasives_extraTheory libTheory namespaceTheory astTheory
     ffiTheory semanticPrimitivesTheory smallStepTheory;
open io_treeTheory cakeml_semanticsTheory;

val _ = new_theory "cakeml_semanticsProof";

(* TODO use evaluatePropsTheory and semanticPrimitivesPropsTheory *)

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
    cakeml_semanticsTheory.estep_def
    ];

(* Adapt CakeML's RTC definitions to our more functional definitions *)
Definition step_n_cml_def:
  step_n_cml 0 e = e ∧
  step_n_cml (SUC n) (Estep st) = step_n_cml n (e_step st) ∧
  step_n_cml _ e = e
End

Theorem step_n_cml_alt_def:
  step_n_cml 0 e = e ∧
  step_n_cml (SUC n) e = (
    case step_n_cml n e of
    | Estep st => e_step st
    | e => e)
Proof
  rw[step_n_cml_def] >>
  qid_spec_tac `e` >> qid_spec_tac `n` >>
  Induct >> Cases >> rewrite_tac[step_n_cml_def] >> simp[]
QED

Theorem e_step_reln_eq_step_n_cml:
  e_step_reln^* st1 st2 ⇔
  ∃n. step_n_cml n (Estep st1) = Estep st2
Proof
  reverse $ eq_tac >> rw[] >> pop_assum mp_tac
  >- (
    map_every qid_spec_tac [`st2`,`st1`,`n`] >>
    Induct >> rw[step_n_cml_alt_def] >>
    EVERY_CASE_TAC >> gvs[] >>
    rw[Once relationTheory.RTC_CASES2] >> disj2_tac >>
    last_x_assum $ irule_at Any >> gvs[e_step_reln_def]
    )
  >- (
    Induct_on `RTC e_step_reln` >> rw[]
    >- (qexists_tac `0` >> gvs[step_n_cml_def])
    >- (qexists_tac `SUC n` >> gvs[step_n_cml_def, e_step_reln_def])
    )
QED

Definition is_halt_cml_def:
  is_halt_cml (Estep (env, st_ffi, Val v, [])) = T ∧
  is_halt_cml (Estep (env, st_ffi, Val v, [Craise (), env'])) = T ∧
  is_halt_cml (Eabort a) = T ∧
  is_halt_cml _ = F
End

Definition step_to_halt_cml_def:
  step_to_halt_cml env st_ffi ev cs =
    case some n. is_halt_cml (step_n_cml n (Estep (env, st_ffi, ev, cs))) of
    | NONE => NONE
    | SOME n => SOME $ step_n_cml n (Estep (env, st_ffi, ev, cs))
End

Theorem small_eval_eq_step_to_halt_cml:
  (small_eval env st_ffi e cs (st_ffi', Rval v) ⇔
  ∃n env'.
    step_n_cml n (Estep (env, st_ffi, Exp e, cs)) =
      (Estep (env', st_ffi', Val v, []))) ∧
  (small_eval env st_ffi e cs (st_ffi', Rerr (Rraise v)) ⇔
  ∃n env' env''.
    step_n_cml n (Estep (env, st_ffi, Exp e, cs)) =
      (Estep (env', st_ffi', Val v, [(Craise (), env'')]))) ∧
  ((∃st_ffi'. small_eval env st_ffi e cs (st_ffi', Rerr (Rabort a))) ⇔
  ∃n env' env''.
    step_n_cml n (Estep (env, st_ffi, Exp e, cs)) = Eabort a)
Proof
  reverse $ rw[small_eval_def, e_step_reln_eq_step_n_cml]
  >- (
    eq_tac >> rw[]
    >- (qexists_tac `SUC n` >> gvs[step_n_cml_alt_def]) >>
    Induct_on `n` >> gvs[step_n_cml_alt_def] >>
    EVERY_CASE_TAC >> gvs[] >> rw[PULL_EXISTS] >>
    PairCases_on `p` >> goal_assum drule >> simp[]
    ) >>
  eq_tac >> rw[] >> ntac 2 $ goal_assum drule
QED

Triviality Estep_is_halt_imp_e_step_neq_Estep:
  is_halt_cml (Estep st) ⇒ ∀st'. e_step st ≠ Estep st'
Proof
  PairCases_on `st` >> rw[] >>
  Cases_on `st3` >> Cases_on `st4` >> gvs[is_halt_cml_def]
  >- simp[e_step_def, SF smallstep_ss] >>
  PairCases_on `h` >>
  Cases_on `h0` >> Cases_on `t` >> gvs[is_halt_cml_def] >>
  simp[e_step_def, SF smallstep_ss]
QED

Theorem application_not_Estuck:
  application op env st_ffi vs cs ≠ Estuck
Proof
  rw[smallStepTheory.application_def] >> EVERY_CASE_TAC >> gvs[SF smallstep_ss]
QED

Theorem e_step_to_Estuck:
  e_step (env, st_ffi, ev, cs) = Estuck ⇔
  (∃v. ev = Val v ∧ cs = []) ∨
  (∃v env'. ev = Val v ∧ cs = [Craise (), env'])
Proof
  reverse $ eq_tac
  >- (rw[] >> gvs[SF smallstep_ss]) >>
  gvs[e_step_def] >> CASE_TAC >> gvs[]
  >- (EVERY_CASE_TAC >> gvs[SF smallstep_ss, application_not_Estuck]) >>
  Cases_on `cs` >> gvs[SF smallstep_ss] >>
  EVERY_CASE_TAC >> gvs[application_not_Estuck]
QED

Theorem e_diverges_eq_step_to_halt_cml:
  e_diverges env st_ffi e ⇔ step_to_halt_cml env st_ffi (Exp e) [] = NONE
Proof
  rw[step_to_halt_cml_def, e_diverges_def, e_step_reln_eq_step_n_cml] >>
  simp[PULL_EXISTS] >>
  eq_tac >> rw[] >> gvs[e_step_reln_def]
  >- (
    DEEP_INTRO_TAC some_intro >> rw[] >>
    Induct_on `x` >> rw[] >> gvs[step_n_cml_alt_def, is_halt_cml_def] >>
    CASE_TAC >> gvs[is_halt_def] >>
    PairCases_on `p` >> rename1 `Estep (a, b, c, d)` >>
    last_assum drule >> strip_tac >> gvs[] >> rename1 `Estep (f, g, h, i)` >>
    last_x_assum $ qspecl_then [`f`,`g`,`h`,`i`,`SUC x`] assume_tac >>
    gvs[step_n_cml_alt_def] >>
    metis_tac[Estep_is_halt_imp_e_step_neq_Estep]
    )
  >- (
    last_x_assum mp_tac >>
    DEEP_INTRO_TAC some_intro >> rw[] >>
    first_assum $ qspec_then `n` assume_tac >>
    first_x_assum $ qspec_then `SUC n` assume_tac >> gvs[step_n_cml_alt_def] >>
    Cases_on `e_step (env', s', e', c')` >> gvs[is_halt_cml_def]
    >- (PairCases_on `p` >> simp[]) >>
    gvs[e_step_to_Estuck, is_halt_cml_def]
    )
QED


(****************************************)


Inductive result_rel:
  result_rel (Rval v) (Rval v) ∧
  result_rel (Rraise v) (Rerr $ Rraise v)
End

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

Inductive ctxt_frame_rel:
  ctxt_frame_rel Craise (Craise ()) ∧
  ctxt_frame_rel (Chandle pes) (Chandle () pes) ∧
  ctxt_frame_rel (Capp op vs es) (Capp op vs () es) ∧
  ctxt_frame_rel (Clog lop e) (Clog lop () e) ∧
  ctxt_frame_rel (Cif e1 e2) (Cif () e1 e2) ∧
  ctxt_frame_rel (Cmat_check pes v) (Cmat_check () pes v) ∧
  ctxt_frame_rel (Cmat pes v) (Cmat () pes v) ∧
  ctxt_frame_rel (Clet vopt e) (Clet vopt () e) ∧
  ctxt_frame_rel (Ccon idopt vs es) (Ccon idopt vs () es) ∧
  ctxt_frame_rel (Ctannot ty) (Ctannot () ty) ∧
  ctxt_frame_rel (Clannot ls) (Clannot () ls)
End

Definition ctxt_rel_def:
  ctxt_rel cs1 cs2 =
    LIST_REL (λ(c1,env1) (c2,env2). ctxt_frame_rel c1 c2 ∧ env1 = env2) cs1 cs2
End

Inductive step_result_rel:
  (ctxt_rel cs1 cs2 ⇒
    step_result_rel (Estep (env, st, ev, cs1)) (Estep (env, (st, ffi), ev, cs2))) ∧
  step_result_rel Edone Estuck ∧
  step_result_rel Etype_error (Eabort $ Rtype_error)
End

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
  rw[application_def, smallStepTheory.application_def] >>
  rpt (
    TOP_CASE_TAC >>
    gvs[step_result_rel_cases, result_rel_cases, ctxt_rel_def,
        ctxt_frame_rel_cases, SF smallstep_ss, SF itree_ss]
    ) >>
  metis_tac[PAIR]
QED

Triviality application_FFI_results:
  application (FFI s) env st vs cs = res ⇒
  res = Etype_error ∨ ∃conf ws lnum. res = Effi s conf ws lnum env st cs
Proof
  rw[application_def] >> EVERY_CASE_TAC >> gvs[]
QED

Theorem application_rel_FFI_type_error:
  application (FFI s) env st vs cs1 = Etype_error ⇔
  application (FFI s) env (st, ffi) vs cs2 = Eabort Rtype_error
Proof
  rw[application_def, smallStepTheory.application_def] >>
  simp[semanticPrimitivesTheory.do_app_def] >>
  EVERY_CASE_TAC >> gvs[SF smallstep_ss] >>
  gvs[store_lookup_def, store_assign_def, store_v_same_type_def]
QED

Theorem application_rel_FFI:
  application (FFI s) env st vs cs1 = Effi s conf ws lnum env st cs1 ⇒
  ∃ws.
    store_lookup lnum st = SOME $ W8array ws ∧
    application (FFI s) env (st, ffi) vs cs2 =
      if s = "" then Estep (env, (st, ffi), Val $ Conv NONE [], cs2) else
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
  ntac 2 (TOP_CASE_TAC >> gvs[]) >> rw[] >>
  goal_assum drule >>
  simp[smallStepTheory.application_def, semanticPrimitivesTheory.do_app_def] >>
  simp[store_lookup_def, call_FFI_def] >>
  reverse IF_CASES_TAC >> gvs[store_assign_def, store_v_same_type_def]
  >- (simp[SF smallstep_ss] >> drule LUPDATE_SAME >> gvs[]) >>
  qmatch_goalsub_abbrev_tac `foo l` >>
  reverse $ Cases_on `foo l` >> gvs[] >>
  IF_CASES_TAC >> gvs[SF smallstep_ss]
QED

Theorem application_rel_FFI':
  application (FFI s) env (st, ffi) vs cs2 ≠ Eabort Rtype_error ⇒
  ∃conf lnum ws.
    vs = [Litv $ StrLit conf; Loc lnum] ∧
    store_lookup lnum st = SOME $ W8array ws ∧
    application (FFI s) env st vs cs1 =
      Effi s (MAP (λc. n2w $ ORD c) (EXPLODE conf)) ws lnum env st cs1
Proof
  rw[smallStepTheory.application_def, semanticPrimitivesTheory.do_app_def] >>
  EVERY_CASE_TAC >> gvs[application_def]
QED

Theorem do_app_ffi_changed:
  do_app (st, ffi) op vs = SOME ((st', ffi'), res) ∧
  ffi ≠ ffi' ⇒
  ∃s conf lnum ws ffi_st ws'.
    op = FFI s ∧
    vs = [Litv (StrLit conf); Loc lnum] ∧
    store_lookup lnum st = SOME (W8array ws) ∧
    s ≠ "" ∧
    ffi.oracle s ffi.ffi_state (MAP (λc. n2w $ ORD c) (EXPLODE conf)) ws =
      Oracle_return ffi_st ws' ∧
    LENGTH ws = LENGTH ws'
Proof
  simp[semanticPrimitivesTheory.do_app_def] >>
  EVERY_CASE_TAC >> gvs[store_alloc_def, store_assign_def] >>
  strip_tac >> gvs[call_FFI_def] >>
  EVERY_CASE_TAC >> gvs[]
QED

Theorem do_app_ffi_unchanged:
  ∀st ffi op vs st' ffi' res.
    (∀s. op ≠ FFI s) ∧
    do_app (st, ffi) op vs = SOME ((st', ffi'), res)
  ⇒ ffi = ffi'
Proof
  rpt gen_tac >>
  simp[semanticPrimitivesTheory.do_app_def] >>
  EVERY_CASE_TAC >> gvs[store_alloc_def]
QED

Theorem application_ffi_unchanged:
  ∀op env st ffi vs cs env' st' ffi' ev cs'.
    (∀s. op ≠ FFI s) ∧
    application op env (st, ffi) vs cs = Estep (env', (st', ffi'), ev, cs')
  ⇒ ffi = ffi'
Proof
  rpt gen_tac >>
  rw[smallStepTheory.application_def, SF smallstep_ss] >>
  qspecl_then [`st`,`ffi`,`op`,`vs`] assume_tac do_app_ffi_unchanged >>
  EVERY_CASE_TAC >> gvs[]
QED

Theorem e_step_ffi_changed:
  e_step (env, (st, ffi), ev, cs) = Estep (env', (st', ffi'), ev', cs') ∧
  ffi ≠ ffi' ⇒
  ∃ s conf lnum env'' ccs ws ffi_st ws'.
    ev = Val (Litv (StrLit conf)) ∧
    cs = (Capp (FFI s) [Loc lnum] () [], env'') :: ccs ∧
    store_lookup lnum st = SOME (W8array ws) ∧
    s ≠ "" ∧
    ffi.oracle s ffi.ffi_state (MAP (λc. n2w $ ORD c) (EXPLODE conf)) ws =
      Oracle_return ffi_st ws' ∧
    LENGTH ws = LENGTH ws'
Proof
  simp[e_step_def] >>
  EVERY_CASE_TAC >> gvs[SF smallstep_ss]
  >- (
    strip_tac >> rename1 `application op _ _ _ _` >>
    Cases_on `∀s. op ≠ FFI s` >> gvs[]
    >- (irule application_ffi_unchanged >> rpt $ goal_assum drule) >>
    gvs[smallStepTheory.application_def, semanticPrimitivesTheory.do_app_def]
    ) >>
  EVERY_CASE_TAC >> gvs[] >>
  rename1 `application op _ _ _ _` >>
  (
    strip_tac >> Cases_on `∀s. op ≠ FFI s` >> gvs[]
    >- (drule_all application_ffi_unchanged >> gvs[]) >>
    gvs[smallStepTheory.application_def,
        semanticPrimitivesTheory.do_app_def, call_FFI_def] >>
    EVERY_CASE_TAC >> gvs[SF smallstep_ss]
  )
QED


(****************************************)


(* Play out a particular trace prefix from a given itree, modelling the
   environment as an FFI oracle with associated FFI state (as in CakeML) *)
Definition trace_prefix_def:
  trace_prefix 0 (oracle, st) itree = ([], NONE) ∧
  trace_prefix (SUC n) (oracle, st) (Ret r) = ([], SOME r) ∧
  trace_prefix (SUC n) (oracle, st) (Vis (s, conf, ws) f) =
    case oracle s st conf ws of
    | Oracle_return st' ws' =>
        let (io, res) = trace_prefix n (oracle, st) (f $ INR ws') in
        (IO_event s conf (ZIP (ws,ws'))::io, res)
    | Oracle_final outcome => trace_prefix n (oracle, st) (f $ INL outcome)
End


(****************************************)


val _ = export_theory();

