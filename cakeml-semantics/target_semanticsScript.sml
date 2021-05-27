(* An itree-based semantics for the target machine code *)
open preamble;
open targetSemTheory;
open io_treeTheory cakeml_semanticsTheory;

val _ = new_theory "target_semantics"

Datatype:
  next_res = Act string (word8 list) (word8 list)
                 (('a,'b,'c) machine_config) (word8 list -> 'b)
           | Exit_Success
           | Exit_OutOfMemory
           | Div
           | Err
End

Definition eval_to_def:
  eval_to k mc (ms:'a) =
    if k = 0n then Div
    else
      if mc.target.get_pc ms IN mc.prog_addresses then
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
              eval_to (k - 1) mc ms2
            else
              Err
        else Err
      else if mc.target.get_pc ms = mc.halt_pc then
        (if mc.target.get_reg ms mc.ptr_reg = 0w
         then Exit_Success else Exit_OutOfMemory)
      else if mc.target.get_pc ms = mc.ccache_pc then
        let (ms1,new_oracle) =
          apply_oracle mc.ccache_interfer
            (mc.target.get_reg ms mc.ptr_reg,
             mc.target.get_reg ms mc.len_reg,
             ms) in
        let mc = mc with ccache_interfer := new_oracle in
          eval_to (k-1) mc ms1
      else
        case find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 of
        | NONE => Err
        | SOME ffi_index =>
          case read_ffi_bytearrays mc ms of
          | SOME bytes, SOME bytes2 =>
             let mc1 = mc with ffi_interfer := shift_seq 1 mc.ffi_interfer in
               Act (EL ffi_index mc.ffi_names) bytes bytes2 mc1
                 (λnew_bytes. mc.ffi_interfer 0 (ffi_index,new_bytes,ms))
          | _ => Err
End

Definition eval_def:
  eval mc ms =
    case some k. eval_to k mc (ms:'a) ≠ Div of
      NONE => Div
    | SOME k => eval_to k mc (ms:'a)
End

Datatype:
  result = Termination
         | OutOfMemory
         | Error
         | FinalFFI (string # word8 list # word8 list) ffi_outcome
End

Definition cml_io_unfold_err_def:
  cml_io_unfold_err f =
    io_unfold_err f
      ((λ(_,_,ws) r. LENGTH ws = LENGTH r),
      FinalFFI, (λe. FinalFFI e FFI_failed))
End

Definition interp_def:
  interp mc ms =
    cml_io_unfold_err
      (λ(mc, ms).
        case eval mc ms of
        | Exit_Success           => Ret' Termination
        | Exit_OutOfMemory       => Ret' OutOfMemory
        | Err                    => Ret' Error
        | Div                    => Div'
        | Act s ws1 ws2 mc1 cont => Vis' (s, ws1, ws2) (λr. (mc1, cont r)))
      (mc, ms)
End

val _ = export_theory();
