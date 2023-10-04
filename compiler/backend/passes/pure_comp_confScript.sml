(*
  Configuration what to optimise.
 *)

open HolKernel Parse boolLib bossLib mlstringTheory;

val _ = new_theory "pure_comp_conf";

Datatype:
  inline_opts = <|
    depth           : num ;
    heuristic       : num ;
  |>
End

Datatype:
  compiler_opts = <|
      do_pure_sort  : bool ;        (* pure-to-pure binding group analysis *)
      do_pure_clean : bool ;        (* pure-to-pure cleaning / deadcode elimination *)
      do_demands    : bool ;        (* demand analysis *)
      inlining      : inline_opts ; (* inlining *)
      do_mk_delay   : bool ;        (* thunk-to-thunk smart mk_delay constructor *)
      do_let_force  : bool ;        (* thunk-to-thunk simplify let force *)
      do_split_dlam : bool ;        (* thunk-to-thunk split delayed lambdas *)
      do_app_unit   : bool ;        (* state-to-state *)
      do_final_gc   : bool ;        (* invoke GC at end of CakeML program *)
      do_explore    : bool          (* print explorer output *)
    |>
End

Overload pure_sort_flag[local]  = “strlit "-sort"”
Overload pure_clean_flag[local] = “strlit "-clean"”
Overload demands_flag[local]    = “strlit "-demands"”
Overload inline_off_flag[local] = “strlit "-inline"”
Overload inline_max_flag[local] = “strlit "-inline_max"”
Overload mk_delay_flag[local]   = “strlit "-mk_delay"”
Overload let_force_flag[local]  = “strlit "-let_force"”
Overload dlam_flag[local]       = “strlit "-dlam"”
Overload unit_flag[local]       = “strlit "-unit"”
Overload final_gc_flag[local]   = “strlit "-final_gc"”
Overload explore_flag[local]    = “strlit "-explore"”

Overload inline_off_opts[local] = “<| depth := 0 ; heuristic := 0 |>”
Overload inline_default_opts[local] = “<| depth := 50 ; heuristic := 100 |>”
Overload inline_max_opts[local] = “<| depth := 5000 ; heuristic := 10000 |>”

Definition all_flags_def:
  all_flags = [pure_sort_flag;
               pure_clean_flag;
               demands_flag;
               inline_off_flag;
               inline_max_flag;
               mk_delay_flag;
               let_force_flag;
               dlam_flag;
               unit_flag;
               final_gc_flag;
               explore_flag]
End

Definition read_cline_args_def:
  read_cline_args (cl:mlstring list) ⇔
    case FILTER (λa. ~MEM a all_flags) cl of
    | (a::_) => INR (concat [strlit "ERROR: unknown flag "; a; strlit "\n"])
    | [] => INL <| do_pure_sort  := ¬ MEM pure_sort_flag cl  ;
                   do_pure_clean := ¬ MEM pure_clean_flag cl ;
                   do_demands    := ¬ MEM demands_flag cl    ;
                   inlining      := if MEM inline_off_flag cl then
                                      inline_off_opts
                                    else if MEM inline_max_flag cl then
                                      inline_max_opts
                                    else inline_default_opts ;
                   do_mk_delay   := ¬ MEM mk_delay_flag cl   ;
                   do_let_force  := ¬ MEM let_force_flag cl  ;
                   do_split_dlam := ¬ MEM dlam_flag cl       ;
                   do_app_unit   := ¬ MEM unit_flag cl       ;
                   do_final_gc   := MEM final_gc_flag cl     ; (* NB final GC only if flag is present *)
                   do_explore    := MEM explore_flag cl      |>
End

val default = EVAL “read_cline_args []” |> concl |> rand |> rand

Definition default_conf_def:
  default_conf = ^default
End

val _ = export_theory ();
