(*
  A CakeML program that reads from stdio, applies a pure function, and
  prints to stdout.
 *)
open basis pure_printTheory lispProgTheory
     pure_letrec_cexpTheory pure_cexp_lemmasTheory pure_letrec_cexpProofTheory;

val _ = new_theory "ioProg";

val _ = set_grammar_ancestry[
          "pure_print",
          "basisProg",
          "basis_ffi"
        ];

val _ = translation_extends "lispProg";

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

(* -- parser -- *)

val res = translate source_valuesTheory.el1_def;
val res = translate source_valuesTheory.el2_def;
val res = translate num_to_str_aux_def;
val res = translate num_to_str_def;
val res = translate num_of_def;
val res = translate name_of_def;
val res = translate names_of_def;
val res = translate cop_of_def;
val res = translate cexp_of_def;
val res = translate bindings_of_def;
val res = translate parse_prog_def;

(* -- backend -- *)

(* topological_sortTheory *)

val res = translate sptreeTheory.spt_center_def;
val res = translate sptreeTheory.spt_left_def;
val res = translate sptreeTheory.spt_right_def;
val res = translate sptreeTheory.mk_BN_def;
val res = translate sptreeTheory.mk_BS_def;
val res = translate sptreeTheory.inter_def;
val res = translate sptreeTheory.union_def;
val res = translate sptreeTheory.subspt_eq;
val res = translate sptreeTheory.spt_fold_def;
val res = translate sptreeTheory.map_def;
val res = translate insert_def;
val res = translate fromAList_def;
val res = translate sptreeTheory.lookup_def;

val res = translate spt_closureTheory.closure_spt_def;
val res = translate topological_sortTheory.trans_clos_def;
val res = translate topological_sortTheory.needs_def;
val res = translate topological_sortTheory.partition_def;
val res = translate topological_sortTheory.top_sort_aux_def;
val res = translate topological_sortTheory.top_sort_def;
val res = translate topological_sortTheory.to_nums_def;
val res = translate topological_sortTheory.top_sort_any_def
val _ = Q.prove (
  `∀v. top_sort_any_side v`,
  rw[fetch "-" "top_sort_any_side_def"] >>
  Cases_on `v` >> gvs[]) |>
  update_precondition;


(* pure_varsTheory *)
val res = translate pure_varsTheory.var_cmp_def;
val res = translate pure_varsTheory.empty_def;

val res = translate (pure_varsTheory.list_union_def |>
                      SIMP_RULE std_ss [mllistTheory.foldl_intro]);
val res = translate (pure_varsTheory.list_delete_def |>
                      SIMP_RULE std_ss [mllistTheory.foldl_intro]);

(* pure_letrec_cexpTheory *)

val res = translate pure_cexpTheory.get_info_def;

val res = translate letrec_recurse_cexp_def;
val res = translate letrec_recurse_fvs_def;
val res =
  translate $
    REWRITE_RULE [ml_translatorTheory.MEMBER_INTRO]
      pure_letrecTheory.make_distinct_def
val res = translate distinct_cexp_def;
val res = translate make_Letrecs_cexp_def;
val res = translate split_one_cexp_def;
val _ = Q.prove (
  `∀v. split_one_cexp_side v`,
  rw[fetch "-" "split_one_cexp_side_def"] >> gvs[LAMBDA_PROD] >>
  qmatch_asmsub_abbrev_tac `topological_sort$top_sort_any l` >>
  qspec_then `l` assume_tac top_sort_any_sets >>
  gvs[EXTENSION, MEM_FLAT] >> pop_assum $ assume_tac o iffLR >>
  gvs[PULL_EXISTS] >> pop_assum drule_all >> rw[] >>
  unabbrev_all_tac >> gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  CCONTR_TAC >> gvs[ALOOKUP_NONE, pure_miscTheory.FST_THM]) |>
  update_precondition;
val res = translate split_all_cexp_def;
val res = translate clean_one_cexp_def;
val res = translate clean_all_cexp_def;

val res = translate transform_cexp_def;

(* -- printer -- *)

val res = translate sexp_of_op_def;

val _ = Q.prove(
  ‘∀n. sexp_of_op_side n’,
  fs [fetch "-" "sexp_of_op_side_def"]
  \\ gvs [] \\ intLib.COOPER_TAC)
  |> update_precondition;

val res = translate sexp_of_def;
val res = translate str_of_def;

Definition compile_def:
  compile (s:mlstring) =
    implode (str_of (parse_prog (explode s)))
End

val compile_v_thm = translate compile_def;

(*
  Read prints reads all input from stdin, applies f (any function from
  string to string), and then prints the result to stdout.
 *)

val read_print = process_topdecs ‘
  fun read_print f =
    TextIO.print (f (TextIO.inputAll TextIO.stdIn));
  ’;

val _ = append_prog read_print;
val read_print_v_tm = fetch_v "read_print" (get_ml_prog_state ());

(*
  'map_stdin' is the specification of what read_print does to the
  file system model. It is parametrized on the file system and the function
  applied to process the input.
 *)

Definition map_stdin_def:
  map_stdin f fs =
    add_stdout (fastForwardFD fs 0)
               (f (implode (THE (ALOOKUP fs.inode_tbl (UStream «stdin»)))))
End

(*
  This is the CF specification for read_print.
 *)

Theorem read_print_spec:
  (∃inp. stdin fs inp 0) ⇒
  (STRING_TYPE --> STRING_TYPE) f fv ⇒
    app (p: 'ffi ffi_proj) ^read_print_v_tm [fv]
      (COMMANDLINE cl * STDIO fs)
      (POSTv uv.
         &UNIT_TYPE () uv *
         STDIO (map_stdin f fs))
Proof
  xcf_with_def "read_print" (fetch "-" "read_print_v_def")
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [STDIO_def] \\ xpull)
  \\ assume_tac INSTREAM_stdin
  \\ drule_then assume_tac stdin_get_file_content
  \\ drule_then strip_assume_tac STD_streams_get_mode
  \\ xlet_auto
  >- (
    xsimpl)
  \\ xlet_auto
  >- (
    xsimpl)
  \\ xapp
  \\ xsimpl
  \\ first_assum (irule_at Any) \\ fs []
  \\ qexists_tac ‘fastForwardFD fs 0’
  \\ xsimpl
  \\ fs [map_stdin_def, stdin_def]
  \\ xsimpl
QED

(*
  This is the main function. You should apply read_print to some pure function
  that has been translated using the translator. Use the name of this function
  in place of 'id' and 'I' in the definitions and specs below.
 *)

val main = process_topdecs ‘
  fun main u = read_print compile;
’;

val _ = append_prog main;
val main_v = fetch_v "main" (get_ml_prog_state ());

Theorem main_spec:
  (∃inp. stdin fs inp 0) ⇒
    app (p: 'ffi ffi_proj) ^main_v [Conv NONE []]
      (COMMANDLINE cl * STDIO fs)
      (POSTv uv.
        &UNIT_TYPE () uv *
        STDIO (map_stdin compile fs))
Proof
  xcf_with_def "main" (fetch "-" "main_v_def")
  \\ xapp
  \\ irule_at Any compile_v_thm \\ fs []
  \\ first_assum (irule_at Any)
QED

Theorem main_whole_prog_spec:
  (∃inp. stdin fs inp 0) ⇒
    whole_prog_spec ^main_v cl fs NONE ((=) (map_stdin compile fs))
Proof
  rw [whole_prog_spec_def, SEP_CLAUSES]
  \\ irule_at Any main_spec
  \\ first_assum (irule_at Any)
  \\ rw [map_stdin_def, GSYM add_stdo_with_numchars,
         GSYM fastForwardFD_with_numchars, with_same_numchars]
QED

val (semantics_thm, prog_tm) =
  whole_prog_thm (get_ml_prog_state ()) "main" (UNDISCH main_whole_prog_spec);

Definition io_prog_def:
  io_prog = ^prog_tm
End

Theorem io_prog_semantics_thm =
  semantics_thm
  |> ONCE_REWRITE_RULE [GSYM io_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO, GSYM CONJ_ASSOC];

val _ = export_theory ();
