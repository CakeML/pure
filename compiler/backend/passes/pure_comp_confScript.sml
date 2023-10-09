(*
  Configuration what to optimise.
 *)

open HolKernel Parse boolLib bossLib intLib
     mlstringTheory mlintTheory mloptionTheory;

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
Overload inline_depth_flag[local] = “strlit "-inline_depth="”
Overload inline_size_flag[local] = “strlit "-inline_size="”
Overload mk_delay_flag[local]   = “strlit "-mk_delay"”
Overload let_force_flag[local]  = “strlit "-let_force"”
Overload dlam_flag[local]       = “strlit "-dlam"”
Overload unit_flag[local]       = “strlit "-unit"”
Overload final_gc_flag[local]   = “strlit "-final_gc"”
Overload explore_flag[local]    = “strlit "-explore"”

Definition get_num_flag_def:
  get_num_flag flag (cl : mlstring list) =
    case FILTER (λs. isPrefix flag s) cl of
    | [] => NONE
    | (s::_) =>
        let num_str = extract s (strlen flag) NONE in
        fromNatString num_str
End

Definition bool_flags_def:
  bool_flags = [pure_sort_flag;
               pure_clean_flag;
               demands_flag;
               mk_delay_flag;
               let_force_flag;
               dlam_flag;
               unit_flag;
               final_gc_flag;
               explore_flag]
End

Definition num_flags_def:
  num_flags = [inline_depth_flag; inline_size_flag]
End

Definition num_flag_ok_def:
  num_flag_ok s =
    EXISTS
      (λf. isPrefix f s ∧ IS_SOME (fromNatString $ extract s (strlen f) NONE))
      num_flags
End

Definition check_flags_def:
  check_flags (cl : mlstring list) =
    FILTER (λs. ¬MEM s bool_flags ∧ ¬num_flag_ok s) cl
End

Definition read_cline_args_def:
  read_cline_args (cl:mlstring list) ⇔
    case check_flags cl of
    | x::xs => INR (concat [strlit "ERROR: unknown flag(s) ";
                            concatWith (strlit ", ") (x::xs); strlit "\n"])
    | _ =>
      let inlining_opts =
        <| depth := getOpt (get_num_flag inline_depth_flag cl) 5000 ;
           heuristic := getOpt (get_num_flag inline_size_flag cl) 10000 |> in
      INL <| do_pure_sort  := ¬ MEM pure_sort_flag cl  ;
             do_pure_clean := ¬ MEM pure_clean_flag cl ;
             do_demands    := ¬ MEM demands_flag cl    ;
             inlining      := inlining_opts            ;
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
