(* Properties about the itree- and FFI state-based CakeML semantics *)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open optionTheory relationTheory pairTheory listTheory arithmeticTheory;
open lem_pervasives_extraTheory libTheory namespaceTheory astTheory
     ffiTheory semanticPrimitivesTheory smallStepTheory evaluatePropsTheory;
open io_treeTheory cakeml_semanticsTheory pure_miscTheory;

val _ = new_theory "cakeml_semanticsProps";

(******************** Definitions ********************)


(***** Step-counting version of smallStep RTC definitions *****)

Definition step_n_cml_def:
  step_n_cml 0 e = e ∧
  step_n_cml (SUC n) (Estep st) = step_n_cml n (e_step st) ∧
  step_n_cml _ e = e
End

Definition is_halt_cml_def:
  is_halt_cml (Estep (env, st_ffi, Val v, [])) = T ∧
  is_halt_cml (Estep (env, st_ffi, Val v, [Craise (), env'])) = T ∧
  is_halt_cml (Eabort a) = T ∧
  is_halt_cml _ = F
End

Definition step_to_halt_cml_def:
  step_to_halt_cml e =
    case some n. is_halt_cml (step_n_cml n e) of
    | NONE => NONE
    | SOME n => SOME $ step_n_cml n e
End


(***** Relating smallStep and itree-based semantics *****)

Inductive result_rel:
  result_rel (Rval v) (Rval v) ∧
  result_rel (Rraise v) (Rerr $ Rraise v)
End

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

(* Play out a particular trace prefix from a given itree, modelling the
   environment as an FFI oracle with associated FFI state (as in CakeML) *)
Definition trace_prefix_def:
  trace_prefix 0 (oracle, ffi_st) itree = ([], NONE) ∧
  trace_prefix (SUC n) (oracle, ffi_st) (Ret r) = ([], SOME r) ∧
  trace_prefix (SUC n) (oracle, ffi_st) (Vis (s, conf, ws) f) =
    case oracle s ffi_st conf ws of
    | Oracle_return ffi_st' ws' =>
        let (io, res) = trace_prefix n (oracle, ffi_st') (f $ INR ws') in
        if LENGTH ws ≠ LENGTH ws' then (io, res)
        else (IO_event s conf (ZIP (ws,ws'))::io, res)
    | Oracle_final outcome => trace_prefix n (oracle, ffi_st) (f $ INL outcome)
End


(***** Misc definitions *****)

Definition is_Effi_def:
  is_Effi (Effi _ _ _ _ _ _ _) = T ∧
  is_Effi _ = F
End

Definition get_ffi_def:
  get_ffi (Estep (env, (st, ffi), ev, cs)) = SOME ffi ∧
  get_ffi _ = NONE
End


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

Theorem step_n_same[simp]:
  ∀n.
    step_n n Edone = Edone ∧
    step_n n Etype_error = Etype_error ∧
    step_n n (Effi s ws1 ws2 n env st cs) = (Effi s ws1 ws2 n env st cs) ∧
    step_n_cml n Estuck = Estuck ∧
    step_n_cml n (Eabort a) = Eabort a
Proof
  Cases >> rw[step_n_def, step_n_cml_def]
QED

Theorem is_Effi_def:
  is_Effi e ⇔ ∃ s ws1 ws2 n env st cs. e = Effi s ws1 ws2 n env st cs
Proof
  Cases_on `e` >> simp[is_Effi_def]
QED

Theorem step_result_rel_not_Effi:
  ∀e1 e2. step_result_rel e1 e2 ⇒ ¬ is_Effi e1
Proof
  rw[step_result_rel_cases, is_Effi_def]
QED


(******************** Relate smallStep RTC and step-counting ********************)

(***** Lemmas *****)

(* Copied from CakeML *)
Theorem cml_application_thm:
  ∀op env s vs c.
    application op env s vs c =
    if op = Opapp then
      case do_opapp vs of
      | NONE => Eabort Rtype_error
      | SOME (env,e) => Estep (env,s,Exp e,c)
    else
      case do_app s op vs of
      | NONE => Eabort Rtype_error
      | SOME (v1,Rval v') => return env v1 v' c
      | SOME (v1,Rerr (Rraise v)) => Estep (env,v1,Val v,(Craise (),env)::c)
      | SOME (v1,Rerr (Rabort a)) => Eabort a
Proof
  rw[smallStepTheory.application_def] >> every_case_tac >> gvs[]
QED

Theorem application_not_Estuck:
  application op env st_ffi vs cs ≠ Estuck
Proof
  rw[cml_application_thm] >>
  EVERY_CASE_TAC >> gvs[SF smallstep_ss]
QED

Theorem e_step_to_Estuck:
  e_step (env, st_ffi, ev, cs) = Estuck ⇔
  (∃v. ev = Val v ∧ cs = []) ∨
  (∃v env'. ev = Val v ∧ cs = [Craise (), env'])
Proof
  reverse $ eq_tac
  >- (rw[] >> gvs[SF smallstep_ss]) >>
  gvs[e_step_def] >> CASE_TAC >> gvs[]
  >- (every_case_tac >> gvs[SF smallstep_ss, application_not_Estuck]) >>
  Cases_on `cs` >> gvs[SF smallstep_ss] >>
  every_case_tac >> gvs[application_not_Estuck]
QED

Theorem step_n_cml_eq_Estep:
  ∀n e st.
    step_n_cml n e = Estep st
  ⇒ ∀m. m < n ⇒ ∃st'. step_n_cml m e = Estep st'
Proof
  Induct >> rw[step_n_cml_def] >>
  Cases_on `e` >> gvs[step_n_cml_def] >>
  Cases_on `m` >> gvs[step_n_cml_def]
QED

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

Theorem step_n_cml_add:
  ∀a b. step_n_cml (a + b) e = step_n_cml a (step_n_cml b e)
Proof
  Induct >> rw[step_n_cml_def] >>
  simp[ADD_CLAUSES, step_n_cml_alt_def]
QED

Theorem is_halt_cml_Estep_imp_steps_neq_Estep:
  is_halt_cml st ⇒ ∀st'. step_n_cml (SUC n) st ≠ Estep st'
Proof
  Cases_on `st` >> gvs[is_halt_cml_def] >>
  PairCases_on `p` >>
  Cases_on `p3` >> gvs[is_halt_cml_def] >>
  Cases_on `p4` >> gvs[is_halt_cml_def]
  >- (gvs[step_n_cml_def, e_step_def, SF smallstep_ss, is_halt_cml_def]) >>
  PairCases_on `h` >> Cases_on `h0` >> gvs[is_halt_cml_def] >>
  Cases_on `t` >> gvs[is_halt_cml_def] >>
  gvs[step_n_cml_def, e_step_def, SF smallstep_ss, is_halt_cml_def]
QED

Theorem is_halt_cml_Estep_imp_steps_not_halt:
  is_halt_cml (Estep st) ⇒ ¬ is_halt_cml (step_n_cml (SUC n) (Estep st))
Proof
  PairCases_on `st` >> gvs[is_halt_cml_def] >>
  Cases_on `st3` >> gvs[is_halt_cml_def] >>
  Cases_on `st4` >> gvs[is_halt_cml_def]
  >- (gvs[step_n_cml_def, e_step_def, SF smallstep_ss, is_halt_cml_def]) >>
  PairCases_on `h` >> Cases_on `h0` >> gvs[is_halt_cml_def] >>
  Cases_on `t` >> gvs[is_halt_cml_def] >>
  gvs[step_n_cml_def, e_step_def, SF smallstep_ss, is_halt_cml_def]
QED

Theorem is_halt_cml_step_n_cml_eq:
  ∀n m e.
    is_halt_cml (step_n_cml n e) ∧
    is_halt_cml (step_n_cml m e)
  ⇒ step_n_cml n e = step_n_cml m e
Proof
  rw[] >> wlog_tac `n < m` [`n`,`m`]
  >- (Cases_on `n = m` >> gvs[]) >>
  imp_res_tac LESS_STRONG_ADD >> gvs[] >>
  gvs[step_n_cml_add |> ONCE_REWRITE_RULE[ADD_COMM]] >>
  Cases_on `step_n_cml n e` >> gvs[] >>
  imp_res_tac is_halt_cml_Estep_imp_steps_not_halt
QED


(***** Results *****)

Theorem e_step_reln_eq_step_n_cml:
  e_step_reln^* st1 st2 ⇔
  ∃n. step_n_cml n (Estep st1) = Estep st2
Proof
  reverse $ eq_tac >> rw[] >> pop_assum mp_tac
  >- (
    map_every qid_spec_tac [`st2`,`st1`,`n`] >>
    Induct >> rw[step_n_cml_alt_def] >>
    every_case_tac >> gvs[] >>
    rw[Once relationTheory.RTC_CASES2] >> disj2_tac >>
    last_x_assum $ irule_at Any >> gvs[e_step_reln_def]
    )
  >- (
    Induct_on `RTC e_step_reln` >> rw[]
    >- (qexists_tac `0` >> gvs[step_n_cml_def])
    >- (qexists_tac `SUC n` >> gvs[step_n_cml_def, e_step_reln_def])
    )
QED

Theorem small_eval_eq_step_n_cml:
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
    every_case_tac >> gvs[] >> rw[PULL_EXISTS] >>
    PairCases_on `p` >> goal_assum drule >> simp[]
    ) >>
  eq_tac >> rw[] >> ntac 2 $ goal_assum drule
QED

Theorem small_eval_eq_step_to_halt_cml:
  (small_eval env st_ffi e cs (st_ffi', Rval v) ⇔
  ∃env'.
    step_to_halt_cml (Estep (env, st_ffi, Exp e, cs)) =
      SOME (Estep (env', st_ffi', Val v, []))) ∧
  (small_eval env st_ffi e cs (st_ffi', Rerr (Rraise v)) ⇔
  ∃env' env''.
    step_to_halt_cml (Estep (env, st_ffi, Exp e, cs)) =
      SOME (Estep (env', st_ffi', Val v, [(Craise (), env'')]))) ∧
  ((∃st_ffi'. small_eval env st_ffi e cs (st_ffi', Rerr (Rabort a))) ⇔
  ∃env' env''.
    step_to_halt_cml (Estep (env, st_ffi, Exp e, cs)) = SOME (Eabort a))
Proof
  rw[small_eval_eq_step_n_cml, step_to_halt_cml_def] >> eq_tac >>
  DEEP_INTRO_TAC some_intro >> rw[] >> gvs[]
  >- metis_tac[is_halt_cml_step_n_cml_eq, is_halt_cml_def]
  >- (
    pop_assum $ qspec_then `n` assume_tac >>
    CCONTR_TAC >> gvs[is_halt_cml_def]
    )
  >- goal_assum drule
  >- metis_tac[is_halt_cml_step_n_cml_eq, is_halt_cml_def]
  >- (
    pop_assum $ qspec_then `n` assume_tac >>
    CCONTR_TAC >> gvs[is_halt_cml_def]
    )
  >- goal_assum drule
  >- metis_tac[is_halt_cml_step_n_cml_eq, is_halt_cml_def]
  >- (
    pop_assum $ qspec_then `n` assume_tac >>
    CCONTR_TAC >> gvs[is_halt_cml_def]
    )
  >- goal_assum drule
QED

Theorem e_diverges_eq_step_to_halt_cml:
  e_diverges env st_ffi e ⇔ step_to_halt_cml (Estep (env, st_ffi, Exp e, [])) = NONE
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
    CCONTR_TAC >> gvs[] >>
    drule is_halt_cml_Estep_imp_steps_neq_Estep >>
    disch_then $ qspec_then `0` mp_tac >>
    rewrite_tac[step_n_cml_alt_def] >> simp[]
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


(******************** Lemmas ********************)

(***** smallStep FFI-state lemmas *****)

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
    LENGTH ws = LENGTH ws' ∧
    st' = LUPDATE (W8array ws') lnum st ∧
    ffi'.oracle = ffi.oracle ∧
    ffi'.ffi_state = ffi_st ∧
    ffi'.io_events =
      ffi.io_events ++
        [IO_event s (MAP (λc. n2w $ ORD c) (EXPLODE conf)) (ZIP (ws,ws'))]
Proof
  simp[semanticPrimitivesTheory.do_app_def] >>
  every_case_tac >> gvs[store_alloc_def, store_assign_def] >>
  strip_tac >> gvs[call_FFI_def] >>
  every_case_tac >> gvs[]
QED

Theorem do_app_ffi_unchanged:
  ∀st ffi op vs st' ffi' res.
    (∀s. op ≠ FFI s) ∧
    do_app (st, ffi) op vs = SOME ((st', ffi'), res)
  ⇒ ffi = ffi'
Proof
  rpt gen_tac >>
  simp[semanticPrimitivesTheory.do_app_def] >>
  every_case_tac >> gvs[store_alloc_def]
QED

Theorem application_ffi_unchanged:
  ∀op env st ffi vs cs env' st' ffi' ev cs'.
    (∀s. op ≠ FFI s) ∧
    application op env (st, ffi) vs cs = Estep (env', (st', ffi'), ev, cs')
  ⇒ ffi = ffi'
Proof
  rpt gen_tac >>
  rw[cml_application_thm, SF smallstep_ss]
  >- (every_case_tac >> gvs[]) >>
  qspecl_then [`st`,`ffi`,`op`,`vs`] assume_tac do_app_ffi_unchanged >>
  every_case_tac >> gvs[]
QED

Theorem e_step_ffi_changed:
  e_step (env, (st, ffi), ev, cs) = Estep (env', (st', ffi'), ev', cs') ∧
  ffi ≠ ffi' ⇒
  ∃ s conf lnum ccs ws ffi_st ws'.
    ev = Val (Litv (StrLit conf)) ∧
    cs = (Capp (FFI s) [Loc lnum] () [], env') :: ccs ∧
    store_lookup lnum st = SOME (W8array ws) ∧
    s ≠ "" ∧
    ffi.oracle s ffi.ffi_state (MAP (λc. n2w $ ORD c) (EXPLODE conf)) ws =
      Oracle_return ffi_st ws' ∧
    LENGTH ws = LENGTH ws' ∧
    ev' = Val (Conv NONE []) ∧
    cs' = ccs ∧
    st' = LUPDATE (W8array ws') lnum st ∧
    ffi'.oracle = ffi.oracle ∧
    ffi'.ffi_state = ffi_st ∧
    ffi'.io_events =
      ffi.io_events ++
        [IO_event s (MAP (λc. n2w $ ORD c) (EXPLODE conf)) (ZIP (ws,ws'))]
Proof
  simp[e_step_def] >>
  every_case_tac >> gvs[SF smallstep_ss]
  >- (
    strip_tac >> rename1 `application op _ _ _ _` >>
    Cases_on `∀s. op ≠ FFI s` >> gvs[]
    >- (irule application_ffi_unchanged >> rpt $ goal_assum drule) >>
    gvs[smallStepTheory.application_def, semanticPrimitivesTheory.do_app_def]
    ) >>
  every_case_tac >> gvs[] >>
  rename1 `application op _ _ _ _` >>
  (
    strip_tac >> Cases_on `∀s. op ≠ FFI s` >> gvs[]
    >- (drule_all application_ffi_unchanged >> gvs[]) >>
    gvs[smallStepTheory.application_def,
        semanticPrimitivesTheory.do_app_def, call_FFI_def] >>
    every_case_tac >> gvs[SF smallstep_ss, store_lookup_def, store_assign_def]
  )
QED

Theorem io_events_mono_e_step:
  e_step e1 = Estep e2 ⇒
  io_events_mono (SND $ FST $ SND e1) (SND $ FST $ SND e2)
Proof
  PairCases_on `e1` >> PairCases_on `e2` >> gvs[] >> rw[] >>
  rename1 `e_step (env1,(st1,ffi1),ev1,cs1) = _ (env2,(st2,ffi2),ev2,cs2)` >>
  Cases_on `ffi1 = ffi2` >- simp[io_events_mono_refl] >>
  drule_all e_step_ffi_changed >> rw[] >> gvs[] >>
  rw[io_events_mono_def]
QED

Theorem io_events_mono_step_n_cml:
  ∀n e1 e2.
    step_n_cml n (Estep e1) = Estep e2
  ⇒ io_events_mono (SND $ FST $ SND e1) (SND $ FST $ SND e2)
Proof
  Induct >> rw[step_n_cml_alt_def] >>
  irule io_events_mono_trans >>
  last_x_assum $ irule_at Any >>
  qspecl_then [`SUC n`,`Estep e1`,`e2`] mp_tac step_n_cml_eq_Estep >>
  gvs[step_n_cml_alt_def] >>
  disch_then $ qspec_then `n` mp_tac >> gvs[] >>
  strip_tac >> gvs[] >>
  irule io_events_mono_e_step >> simp[]
QED

Theorem step_n_cml_preserved_FFI:
  ∀n e e'.
    step_n_cml n e = Estep e' ∧ get_ffi (Estep e') = get_ffi e
  ⇒ ∀m. m < n ⇒ get_ffi (step_n_cml m e) = get_ffi (Estep e')
Proof
  rw[] >> imp_res_tac LESS_STRONG_ADD >>
  gvs[step_n_cml_add |> ONCE_REWRITE_RULE[ADD_COMM]] >> rename1 `SUC n` >>
  Cases_on `step_n_cml m e` >> gvs[] >>
  PairCases_on `p` >> rename1 `(env1,(st1,ffi1),ev1,cs1)` >>
  Cases_on `e` >> gvs[] >>
  PairCases_on `p` >> rename1 `_ = get_ffi $ _ (env,(st,ffi),ev,cs)` >>
  PairCases_on `e'` >>
  rename1 `step_n_cml (SUC _) _ = Estep (env2,(st2,ffi2),ev2,cs2)` >>
  imp_res_tac io_events_mono_step_n_cml >> gvs[get_ffi_def] >>
  imp_res_tac io_events_mono_antisym >> gvs[]
QED


(***** itree-based lemmas *****)

Theorem step_n_alt_def:
  step_n 0 e = e ∧
  step_n (SUC n) e = (
    case step_n n e of
    | Estep st => estep st
    | e => e)
Proof
  rw[step_n_def] >>
  qid_spec_tac `e` >> qid_spec_tac `n` >>
  Induct >> Cases >> rewrite_tac[step_n_def] >> simp[]
QED

Theorem step_n_add:
  ∀a b. step_n (a + b) e = step_n a (step_n b e)
Proof
  Induct >> rw[step_n_def] >>
  simp[ADD_CLAUSES, step_n_alt_def]
QED

Theorem is_halt_step_n_eq:
  ∀n m e.
    is_halt (step_n n e) ∧
    is_halt (step_n m e)
  ⇒ step_n n e = step_n m e
Proof
  rw[] >> wlog_tac `n < m` [`n`,`m`]
  >- (Cases_on `n = m` >> gvs[]) >>
  imp_res_tac LESS_STRONG_ADD >> gvs[] >>
  gvs[step_n_add |> ONCE_REWRITE_RULE[ADD_COMM]] >>
  Cases_on `step_n n e` >> gvs[is_halt_def, step_n_def]
QED

Theorem application_thm:
  ∀op env s vs c.
    application op env s vs c =
    if op = Opapp then
      case do_opapp vs of
      | NONE => Etype_error
      | SOME (env,e) => Estep (env,s,Exp e,c)
    else if ∃n. op = FFI n then (
      case op of FFI n => (
        case vs of
          [Litv (StrLit conf); Loc lnum] => (
            case store_lookup lnum s of
              SOME (W8array ws) =>
                if n = "" then Estep (env, s, Val $ Conv NONE [], c)
                else Effi n (MAP (λc. n2w $ ORD c) (EXPLODE conf)) ws lnum env s c
            | _ => Etype_error)
        | _ => Etype_error)
      | _ => ARB)
    else
      case do_app s op vs of
      | NONE => Etype_error
      | SOME (v1,Rval v') => return env v1 v' c
      | SOME (v1,Rraise v) => Estep (env,v1,Val v,(Craise,env)::c)
Proof
  reverse $ rw[application_def] >> gvs[SF itree_ss] >>
  TOP_CASE_TAC >> gvs[]
QED

Theorem application_FFI_results:
  (application (FFI s) env st vs cs = Etype_error) ∨
  (application (FFI s) env st vs cs = Estep (env, st, Val $ Conv NONE [], cs)) ∨
  ∃conf ws lnum.
    (application (FFI s) env st vs cs) = Effi s conf ws lnum env st cs
Proof
  rw[application_thm] >> every_case_tac >> gvs[]
QED

Theorem application_eq_Effi_fields:
  application op env st vs cs = Effi s conf ws lnum env' st' cs' ⇒
  op = FFI s ∧ env = env' ∧ st = st' ∧ cs' = cs ∧
  ∃conf'.
    vs = [Litv $ StrLit conf'; Loc lnum] ∧
    conf = MAP (λc. n2w $ ORD c) (EXPLODE conf')
Proof
  Cases_on `op` >> simp[application_def, SF itree_ss] >>
  every_case_tac >> gvs[] >> rw[]
QED

Theorem application_not_Edone:
  application op env st_ffi vs cs ≠ Edone
Proof
  rw[application_thm] >>
  every_case_tac >> gvs[SF itree_ss]
QED

Theorem estep_to_Edone:
  estep (env, st, ev, cs) = Edone ⇔
  (∃v. ev = Val v ∧ cs = []) ∨
  (∃v env'. ev = Val v ∧ cs = [Craise, env'])
Proof
  reverse $ eq_tac
  >- (rw[] >> gvs[SF itree_ss]) >>
  Cases_on `ev` >> gvs[estep_def]
  >- (
    Cases_on `e` >> gvs[estep_def, SF itree_ss] >>
    every_case_tac >> gvs[] >> rw[application_not_Edone]
    ) >>
  Cases_on `cs` >> gvs[SF itree_ss] >>
  PairCases_on `h` >> Cases_on `h0` >> gvs[SF itree_ss] >>
  every_case_tac >> gvs[]
  >- (
    rename1 `Capp _ _ es` >>
    Cases_on `es` >> gvs[SF itree_ss, application_not_Edone]
    )
  >- (
    rename1 `Cmat l _` >> Cases_on `l` >> gvs[SF itree_ss] >>
    PairCases_on `h` >> gvs[SF itree_ss] >> every_case_tac >> gvs[]
    )
  >- (
    rename1 `Ccon _ _ es` >> Cases_on `es` >> gvs[SF itree_ss] >>
    every_case_tac >> gvs[]
    )
QED

Theorem cml_io_unfold_err:
  cml_io_unfold_err f seed =
    case f seed of
    | Ret' r   => Ret r
    | Vis' (s, ws1, ws2) g =>
        Vis (s, ws1, ws2)
          (λa. case a of
                  INL x => Ret $ FinalFFI x
                | INR y =>
                    if LENGTH ws2 = LENGTH y then cml_io_unfold_err f (g y)
                    else Ret $ FinalFFI FFI_failed)
Proof
  CASE_TAC >> gvs[cml_io_unfold_err_def] >>
  simp[Once io_unfold_err] >>
  PairCases_on `e` >> gvs[]
QED

Theorem interp:
  interp e =
    case step_until_halt e of
    | Ret => Ret Termination
    | Err => Ret Error
    | Div => Ret SilentDivergence
    | Act s ws1 ws2 n env st cs =>
        Vis (s, ws1, ws2)
          (λa. case a of
                | INL x => Ret $ FinalFFI x
                | INR y =>
                    if LENGTH ws2 = LENGTH y then
                      interp $
                        Estep (env, LUPDATE (W8array y) n st,
                               Val $ Conv NONE [], cs)
                    else Ret $ FinalFFI FFI_failed)
Proof
  rw[interp_def] >> rw[Once cml_io_unfold_err] >> simp[] >>
  CASE_TAC >> gvs[] >> rw[FUN_EQ_THM]
QED

Theorem trace_prefix_interp:
  trace_prefix 0 (oracle, ffi_st) (interp e) = ([], NONE) ∧
  trace_prefix (SUC n) (oracle, ffi_st) (interp e) =
    case step_until_halt e of
    | Ret => ([], SOME Termination)
    | Err => ([], SOME Error)
    | Div => ([], SOME SilentDivergence)
    | Act s conf ws lnum env st cs =>
        case oracle s ffi_st conf ws of
        | Oracle_return ffi_st' ws' =>
            if LENGTH ws ≠ LENGTH ws' ∧ n = 0 then ([], NONE)
            else if LENGTH ws ≠ LENGTH ws' then ([], SOME $ FinalFFI FFI_failed)
            else let (io, res) =
              trace_prefix n (oracle, ffi_st')
                (interp $
                  Estep (env, LUPDATE (W8array ws') lnum st, Val $ Conv NONE [], cs))
            in ((IO_event s conf (ZIP (ws,ws')))::io, res)
        | Oracle_final outcome =>
            if n = 0 then ([], NONE) else
            ([], SOME $ FinalFFI outcome)
Proof
  rw[trace_prefix_def] >> rw[Once interp] >>
  CASE_TAC >> gvs[trace_prefix_def] >>
  reverse $ CASE_TAC >> gvs[]
  >- (Cases_on `n` >> gvs[trace_prefix_def]) >>
  IF_CASES_TAC >> gvs[] >>
  Cases_on `n` >> gvs[trace_prefix_def]
QED


(****************************************)

val _ = export_theory();

