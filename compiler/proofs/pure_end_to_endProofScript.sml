(*
   End-to-end correctness for the PureCake compiler
*)
open HolKernel Parse boolLib bossLib;
open pure_compilerProofTheory backend_itreeProofTheory state_to_cakeProofTheory;

val _ = new_theory "pure_end_to_endProof";

Overload cake_compile = ``backend$compile``;

Overload target_configs_ok =
  ``λconf (mc,ms).  backend_config_ok conf ∧ mc_conf_ok mc ∧ mc_init_ok conf mc``

Overload code_in_memory =
  ``λconf (bytes,bitmaps,c') (mc,ms).
      ∃cbspace data_sp.
        installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
          (backendProof$heap_regs conf.stack_conf.reg_names) mc ms``

Overload prunes = ``λpt mt. ∃ct. itree_rel pt ct ∧ prune ffi_convention F ct mt``

Theorem end_to_end_correctness:
  compile_to_ast c s = SOME cake ∧
  cake_compile conf cake = SOME code ∧
  target_configs_ok conf m ∧
  code_in_memory conf code m
  ⇒ ∃ce ns. string_to_cexp s = SOME (ce,ns) ∧
            prunes (pure_semantics$itree_of (exp_of ce)) (machine_sem_itree m)
Proof
  rw[] >> drule pure_compilerProofTheory.compiler_correctness >>
  strip_tac >> simp[] >>
  PairCases_on `m` >> PairCases_on `code` >>
  gvs[ffi_convention_def] >> goal_assum drule >>
  irule itree_compile_correct >> gvs[PULL_EXISTS, GSYM ffi_convention_def] >>
  rpt $ goal_assum $ drule_at Any >> simp[]
QED

val _ = export_theory();

