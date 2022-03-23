(* Theorem expressing `machine_sem` in terms of target itree semantics *)
open preamble;
open semanticsPropsTheory evaluatePropsTheory ffiTheory
     targetSemTheory targetPropsTheory;
open target_semanticsTheory target_semanticsPropsTheory
     cakeml_semanticsTheory cakeml_semanticsPropsTheory cakeml_semanticsProofTheory;


val _ = new_theory "target_semanticsProof"


(*********** evaluate' **********)

Definition evaluate'_def:
  evaluate' mc (ffi:'ffi ffi_state) k (ms:'a) =
    if k = 0 then (TimeOut,mc,ms,ffi)
    else
      if mc.target.get_pc ms ∈ mc.prog_addresses then
        if encoded_bytes_in_mem
            mc.target.config (mc.target.get_pc ms)
            (mc.target.get_byte ms) mc.prog_addresses then
          let ms1 = mc.target.next ms in
          let (ms2,new_oracle) = apply_oracle mc.next_interfer ms1 in
          let mc = mc with next_interfer := new_oracle in
            if EVERY mc.target.state_ok [ms;ms1;ms2] ∧
               (∀x. x ∉ mc.prog_addresses ⇒
                   mc.target.get_byte ms1 x =
                   mc.target.get_byte ms x)
            then
              evaluate' mc ffi (k - 1) ms2
            else
              (Error,mc,ms,ffi)
        else (Error,mc,ms,ffi)
      else if mc.target.get_pc ms = mc.halt_pc then
        (if mc.target.get_reg ms mc.ptr_reg = 0w
         then Halt Success else Halt Resource_limit_hit,mc,ms,ffi)
      else if mc.target.get_pc ms = mc.ccache_pc then
        let (ms1,new_oracle) =
          apply_oracle mc.ccache_interfer
            (mc.target.get_reg ms mc.ptr_reg,
             mc.target.get_reg ms mc.len_reg,
             ms) in
        let mc = mc with ccache_interfer := new_oracle in
          evaluate' mc ffi (k-1) ms1
      else
        case find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 of
        | NONE => (Error,mc,ms,ffi)
        | SOME ffi_index =>
          case read_ffi_bytearrays mc ms of
          | SOME bytes, SOME bytes2 =>
            (case call_FFI ffi (EL ffi_index mc.ffi_names) bytes bytes2 of
             | FFI_final outcome => (Halt (FFI_outcome outcome),mc,ms,ffi)
             | FFI_return new_ffi new_bytes =>
                let (ms1,new_oracle) = apply_oracle mc.ffi_interfer
                  (ffi_index,new_bytes,ms) in
                let mc = mc with ffi_interfer := new_oracle in
                  evaluate' mc new_ffi (k - 1:num) ms1)
          | _ => (Error,mc,ms,ffi)
End

Theorem evaluate'_0[simp]:
  evaluate' mc ffi 0 ms = (TimeOut,mc,ms,ffi)
Proof
  rw[Once evaluate'_def]
QED

Theorem evaluate_evaluate':
  ∀mc ffi k ms. evaluate mc ffi k ms = (λ(a,b,c,d).(a,c,d)) (evaluate' mc ffi k ms)
Proof
  ho_match_mp_tac evaluate_ind >> rw[] >>
  simp[Once evaluate_def, Once evaluate'_def] >>
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[] >>
  IF_CASES_TAC >> gvs[apply_oracle_def] >> IF_CASES_TAC >> gvs[] >>
  rpt (TOP_CASE_TAC >> gvs[])
QED

Theorem evaluate'_step:
  evaluate' mc ffi 0 ms = (TimeOut,mc,ms,ffi) ∧
  evaluate' mc ffi (SUC n) ms =
    case evaluate' mc ffi 1 ms of
    | (TimeOut,mc',ms',ffi') => evaluate' mc' ffi' n ms'
    | res => res
Proof
  simp[] >> simp[Once evaluate'_def, SimpRHS] >> simp[Once evaluate'_def] >>
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[apply_oracle_def] >>
  IF_CASES_TAC >> gvs[] >> rpt (TOP_CASE_TAC >> gvs[])
QED

Theorem evaluate'_step_alt:
  evaluate' mc ffi 0 ms = (TimeOut,mc,ms,ffi) ∧
  evaluate' mc ffi (SUC n) ms =
    case evaluate' mc ffi n ms of
    | (TimeOut,mc',ms',ffi') => evaluate' mc' ffi' 1 ms'
    | res => res
Proof
  simp[] >> map_every qid_spec_tac [`ms`,`ffi`,`mc`,`n`] >>
  Induct >- rw[] >> rpt gen_tac >>
  rewrite_tac[evaluate'_step] >>
  qabbrev_tac `ev = evaluate' mc ffi 1 ms` >> PairCases_on `ev` >> gvs[] >>
  TOP_CASE_TAC >> simp[] >> simp[GSYM evaluate'_step]
QED

Theorem evaluate'_add:
  ∀a b.
    evaluate' mc ffi (a + b) ms =
    case evaluate' mc ffi b ms of
    | (TimeOut,mc',ms',ffi') => evaluate' mc' ffi' a ms'
    | res => res
Proof
  Induct >> rw[evaluate'_step, ADD_CLAUSES] >>
  qabbrev_tac `ev = evaluate' mc ffi b ms` >> PairCases_on `ev` >> gvs[] >>
  Cases_on `ev0` >> gvs[] >> simp[GSYM evaluate'_step] >> simp[evaluate'_step_alt]
QED

Theorem evaluate'_add_alt:
  ∀a b.
    evaluate' mc ffi (a + b) ms =
    case evaluate' mc ffi a ms of
    | (TimeOut,mc',ms',ffi') => evaluate' mc' ffi' b ms'
    | res => res
Proof
  once_rewrite_tac[ADD_COMM] >> simp[evaluate'_add]
QED

Theorem evaluate'_io_events_mono:
   ∀mc ffi k ms res mc' ms' ffi'.
    evaluate' mc ffi k ms = (res,mc',ms',ffi') ⇒ io_events_mono ffi ffi'
Proof
  ho_match_mp_tac evaluate'_ind >> rw[] >>
  pop_assum mp_tac >> simp[Once evaluate'_def] >>
  ntac 4 (IF_CASES_TAC >> gvs[apply_oracle_def]) >>
  ntac 5 (TOP_CASE_TAC >> gvs[]) >> rw[] >> gvs[] >>
  irule io_events_mono_trans >> goal_assum $ drule_at Any >>
  irule call_FFI_rel_io_events_mono >>
  irule RTC_SUBSET >> simp[call_FFI_rel_def, SF SFY_ss]
QED

Theorem evaluate'_add_clock:
  ∀mc ffi k ms res.
    evaluate' mc ffi k ms = res ∧ FST res ≠ TimeOut
  ⇒ ∀k'. k ≤ k' ⇒ evaluate' mc ffi k' ms = res
Proof
  recInduct evaluate'_ind >> rw[] >>
  qpat_x_assum `FST _ ≠ _` mp_tac >> once_rewrite_tac[evaluate'_def] >>
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[] >>
  IF_CASES_TAC >> gvs[apply_oracle_def] >> IF_CASES_TAC >> gvs[] >>
  rpt (TOP_CASE_TAC >> gvs[])
QED

Theorem evaluate'_agree:
  evaluate' mc ffi k1 ms = res1 ∧
  evaluate' mc ffi k2 ms = res2 ∧
  FST res1 ≠ TimeOut ∧ FST res2 ≠ TimeOut
  ⇒ res1 = res2
Proof
  rw[] >> wlog_tac `k1 < k2` [`k1`,`k2`] >- gvs[NOT_LESS, LESS_OR_EQ] >>
  Cases_on `evaluate' mc ffi k1 ms` >> Cases_on `evaluate' mc ffi k2 ms` >>
  gvs[] >> PairCases_on `r` >> PairCases_on `r'` >>
  rev_dxrule evaluate'_add_clock >> simp[] >>
  disch_then $ qspec_then `k2` assume_tac >> gvs[]
QED

Theorem evaluate'_remove_clock:
  evaluate' mc ffi k ms = res ∧ FST res = TimeOut ∧ k' ≤ k ⇒
  FST (evaluate' mc ffi k' ms) = TimeOut
Proof
  metis_tac[evaluate'_add_clock, PAIR]
QED

Theorem evaluate'_min:
  ∀k mc ffi ms res.
    evaluate' mc ffi k ms = res ∧ FST res ≠ TimeOut
  ⇒ ∃k'. k' ≤ k ∧ evaluate' mc ffi k' ms = res ∧
      ∀m. m < k' ⇒ ∃mc' ms' ffi'. evaluate' mc ffi m ms = (TimeOut,mc',ms',ffi')
Proof
  Induct >> rw[] >>
  qabbrev_tac `res = evaluate' mc ffi (SUC k) ms` >> PairCases_on `res` >> gvs[] >>

  gvs[evaluate'_step_alt] >>
  Cases_on `evaluate' mc ffi k ms` >> gvs[] >> Cases_on `q` >> gvs[]
  >- (
    first_x_assum $ qspecl_then [`mc`,`ffi`,`ms`] assume_tac >> gvs[] >>
    qexists_tac `k'` >> simp[]
    )
  >- (
    first_x_assum $ qspecl_then [`mc`,`ffi`,`ms`] assume_tac >> gvs[] >>
    qexists_tac `k'` >> simp[]
    ) >>
  PairCases_on `r` >> gvs[] >>
  qexists_tac `SUC k` >> simp[evaluate'_step_alt] >> rw[] >>
  drule evaluate'_remove_clock >> simp[] >>
  disch_then $ qspec_then `m` mp_tac >> simp[] >> metis_tac[PAIR]
QED

Theorem evaluate'_1_ffi_unchanged:
  evaluate' mc (ffi:'ffi ffi_state) 1 ms = (res,mc',ms',ffi') ∧ res ≠ TimeOut
  ⇒ ffi = ffi'
Proof
  simp[Once evaluate'_def] >>
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[apply_oracle_def] >>
  IF_CASES_TAC >> gvs[] >> rpt (TOP_CASE_TAC >> gvs[]) >> rw[] >> gvs[]
QED

Theorem evaluate'_1_ffi_changed:
  evaluate' mc (ffi:'ffi ffi_state) 1 ms = (res,mc',ms',ffi') ∧ ffi' ≠ ffi ⇔
    res = TimeOut ∧
    mc.target.get_pc ms ∉ mc.prog_addresses ∧
    mc.target.get_pc ms ≠ mc.halt_pc ∧
    mc.target.get_pc ms ≠ mc.ccache_pc ∧
    mc' = mc with ffi_interfer := shift_seq 1 mc.ffi_interfer ∧
    ∃n ws1 ws2 l.
      find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 = SOME n ∧
      EL n mc.ffi_names ≠ "" ∧
      read_ffi_bytearrays mc ms = (SOME ws1,SOME ws2) ∧
      call_FFI ffi (EL n mc.ffi_names) ws1 ws2 = FFI_return ffi' l ∧
      ms' = mc.ffi_interfer 0 (n,l,ms)
Proof
  simp[Once evaluate'_def] >>
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[apply_oracle_def] >>
  IF_CASES_TAC >> gvs[] >> rpt (TOP_CASE_TAC >> gvs[]) >>
  eq_tac >> rw[] >>
  gvs[call_FFI_def, AllCaseEqs(), ffi_state_component_equality] >>
  qpat_x_assum `_ = f.io_events` $ assume_tac o GSYM >> simp[]
QED

Theorem evaluate'_1_ffi_failed:
  evaluate' mc (ffi:'ffi ffi_state) 1 ms = (Halt (FFI_outcome outcome),mc',ms',ffi') ⇔
    mc.target.get_pc ms ∉ mc.prog_addresses ∧
    mc.target.get_pc ms ≠ mc.halt_pc ∧
    mc.target.get_pc ms ≠ mc.ccache_pc ∧
    ms = ms' ∧ mc = mc' ∧ ffi = ffi' ∧
    ∃n ws1 ws2 l.
      find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 = SOME n ∧
      EL n mc.ffi_names ≠ "" ∧
      read_ffi_bytearrays mc ms = (SOME ws1,SOME ws2) ∧
      call_FFI ffi (EL n mc.ffi_names) ws1 ws2 = FFI_final outcome
Proof
  simp[Once evaluate'_def] >>
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[apply_oracle_def] >>
  IF_CASES_TAC >> gvs[] >> rpt (TOP_CASE_TAC >> gvs[]) >>
  eq_tac >> rw[] >> gvs[call_FFI_def, AllCaseEqs()]
QED

Theorem machine_sem_unique:
  machine_sem mc ffi ms b1 ∧ machine_sem mc ffi ms b2 ⇒ b1 = b2
Proof
  rw[DefnBase.one_line_ify NONE machine_sem_def] >>
  Cases_on `b1` >> gvs[] >> Cases_on `b2` >> gvs[]
  >- imp_res_tac unique_lprefix_lub
  >- (last_x_assum $ qspec_then `k` assume_tac >> gvs[])
  >- (last_x_assum $ qspec_then `k` assume_tac >> gvs[])
  >- (last_x_assum $ qspec_then `k` assume_tac >> gvs[])
  >- (
    gvs[evaluate_evaluate'] >> rpt (pairarg_tac >> gvs[]) >>
    dxrule evaluate'_agree >> disch_then dxrule >> rw[]
    )
  >- (
    gvs[evaluate_evaluate'] >> rpt (pairarg_tac >> gvs[]) >>
    dxrule evaluate'_agree >> disch_then dxrule >> rw[]
    )
  >- (last_x_assum $ qspec_then `k` assume_tac >> gvs[])
  >- (
    gvs[evaluate_evaluate'] >> rpt (pairarg_tac >> gvs[]) >>
    dxrule evaluate'_agree >> disch_then dxrule >> rw[]
    )
QED

(**********)

val _ = export_theory();

