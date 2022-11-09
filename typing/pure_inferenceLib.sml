(* Computation library for inference. Unification parts ported from CakeML *)
structure pure_inferenceLib = struct

local
  open HolKernel boolLib bossLib
  open computeLib reduceLib optionLib pairLib listSimps stringLib sptreeLib
       combinLib finite_mapLib pred_setLib
  open basisComputeLib
  open pure_unificationTheory pure_inferenceTheory pure_printTheory pure_printLib

  val pure_wfs_FEMPTY = Q.prove(`pure_wfs FEMPTY`, rw[pure_wfs_def]);

  val funs = [pure_walk, pure_ext_s_check, pure_unifyl_def];

  val init_db =
    Net.insert (rand $ concl $ pure_wfs_FEMPTY, pure_wfs_FEMPTY) Net.empty;

  fun theory_computes thy =
    ThmSetData.theory_data {settype = "compute", thy = thy} |>
      ThmSetData.added_thms

in
  val toMLstring = stringLib.fromMLstring o dest_QUOTE;

  fun add_unify_compset compset = let

    val db = ref init_db

    fun get_wfs s =
      case Net.index s (!db) of
        (th::_) => th
      | _ => raise mk_HOL_ERR "pure_unificationLib" "get_wfs" (term_to_string s)


    fun wfs_thms () = Net.listItems (!db)

    fun pure_unify_conv eval tm = let
      val (_, [s,t1,t2]) = strip_comb tm
      val wfs_s = get_wfs s
      val th1 = SPECL [t1,t2] (MATCH_MP pure_unify wfs_s)
      val th2 = eval (rhs (concl th1))
      val th3 = TRANS th1 th2
      val res = rhs (concl th2)
      val _ = if optionSyntax.is_some res then
              let val key = rand res in
                if null (Net.index key (!db)) then
                  db := Net.insert
                    (key, PROVE[wfs_s,pure_unify_wfs,th3]
                          (mk_comb (rator (concl wfs_s), key)))
                    (!db)
                else ()
              end
              else ()
      in th3 end

    fun pure_vwalk_conv eval tm = let
      val (_,[s,t]) = strip_comb tm
      val wfs_s = get_wfs s
      val th1 = SPEC t (MATCH_MP pure_vwalk wfs_s)
      val th2 = eval (rhs (concl th1))
      in TRANS th1 th2 end

    fun pure_oc_conv eval tm = let
      val (_,[s,t1,t2]) = strip_comb tm
      val wfs_s = get_wfs s
      val th1 = SPECL [t1,t2] (MATCH_MP pure_oc wfs_s)
      val th2 = eval (rhs (concl th1))
      in TRANS th1 th2 end

    fun pure_walkstar_conv eval tm = let
      val (_,[s,t]) = strip_comb tm
      val wfs_s = get_wfs s
      val th1 = SPEC t (MATCH_MP pure_walkstar wfs_s)
      val th2 = eval (rhs (concl th1))
      in TRANS th1 th2 end

    fun convs eval = [
      (``pure_unify``, 3, pure_unify_conv eval),
      (``pure_vwalk``, 2, pure_vwalk_conv eval),
      (``pure_walkstar``, 2, pure_walkstar_conv eval),
      (``pure_oc``, 3, pure_oc_conv eval)
    ]

    val _ = computeLib.add_thms funs compset
    val _ = List.app (Lib.C computeLib.add_conv compset)
              (convs (computeLib.CBV_CONV compset))
    val _ = computeLib.extend_compset [computeLib.Tys [``:utype``]] compset
    in
      ()
    end

  fun pure_infer_compset () = let
    val cmp = reduceLib.num_compset ()
    val _ = Lib.C computeLib.extend_compset cmp (
              computeLib.Extenders [
                optionLib.OPTION_rws,
                pairLib.add_pair_compset,
                listLib.list_rws,
                alistLib.add_alist_compset,
                listLib.add_rich_list_compset,
                stringLib.add_string_compset,
                sptreeLib.add_sptree_compset,
                combinLib.add_combin_compset,
                basisComputeLib.add_basis_compset,
                finite_mapLib.add_finite_map_compset,
                pred_setLib.add_pred_set_compset,
                add_unify_compset
                ] ::
              computeLib.Tys [``:ordering``,``:itype``,``:'a constraint``] ::
              computeLib.Defs [pure_walk] ::
              map (computeLib.Defs o theory_computes) [
                "pure_inference", "pure_inference_common",
                "mlmap", "mlstring", "balanced_map", "pure_vars"
                ]
          )
    in cmp end

  val pure_infer_eval = CBV_CONV (pure_infer_compset ())

  fun pure_parse_infer_compset () = let
    val cmp = pure_infer_compset ()
    val _ = Lib.C computeLib.extend_compset cmp (
              computeLib.Extenders [pred_setLib.add_pred_set_compset] ::
              computeLib.Tys [``:source_values$v``] ::
              map (computeLib.Defs o theory_computes) [
                "pure_print", "parsing", "source_values"
                ]
              )
    in cmp end

  val pure_parse_infer_eval = CBV_CONV (pure_parse_infer_compset ())

end

end
