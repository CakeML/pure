(* Theorem showing oracle-based semantic preservation implies
   io_tree-based semantic preservation *)
open preamble;
open semanticsPropsTheory
open cakeml_semanticsTheory target_semanticsTheory;

val _ = new_theory "cakeml_target_proof"

Definition same_up_to_oom_def:
  (same_up_to_oom exact a b [] = T) ∧
  (same_up_to_oom exact a b (x::xs) ⇔
     (a = Div ∧ b = Div) ∨
     (a = Ret Termination ∧ b = Ret Termination) ∨
     (a = Ret (Error:cakeml_semantics$result) ∧ b = Ret Error) ∨
     (~exact ∧ b = Ret OutOfMemory) ∨
     (∃x y. a = Ret (FinalFFI x y) ∧ b = Ret (FinalFFI x y)) ∨
     ∃d f g.
       a = Vis d f ∧ b = Vis d g ∧
       same_up_to_oom exact (f x) (g x) xs)
End

Definition bisimilar_up_to_oom_def:
  bisimilar_up_to_oom exact a b = ∀xs. same_up_to_oom exact a b xs
End

(* TODO: This is might be a bit off since the machine configuation mc
         contains two oracles: next_interfer (desciribing the
         interference from the OS between each instruction execution!)
         and ffi_interfer (describing how state changes at each FFI
         call, based on what the FFI f says are the new bytes). *)
Theorem oracle_imp_itree_preservation:
  (∀f.
    Fail ∉ semantics_prog (s with ffi := f) env prog ∧
    machine_sem (mc:(α,β,γ) machine_config) f ms ⊆
      extend_with_resource_limit' safe_for_space
        (semantics_prog (s with ffi := f) env prog))
  ⇒
  bisimilar_up_to_oom safe_for_space
    (ARB interp prog s env) (* TODO: need prog-level semantics for CakeML *)
    (machine_sem_itree mc ms)
Proof
  cheat
QED

val _ = export_theory();
