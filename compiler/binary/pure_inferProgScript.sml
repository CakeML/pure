(*
  Translation of PureLang type inferencer
 *)
open basis
     pure_inferenceTheory
     pure_parseProgTheory;

val _ = new_theory "pure_inferProg";

val _ = set_grammar_ancestry ["pure_parseProg", "pure_inference"];

val _ = translation_extends "pure_parseProg";

val _ = (max_print_depth := 1000);

(*-----------------------------------------------------------------------*
   code for fetching definitions automatically
 *-----------------------------------------------------------------------*)

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng
val mk_fun_type = curry op -->;
fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

val _ = add_preferred_thy "-";

Theorem NOT_NIL_AND_LEMMA:
   (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

Theorem monad_unitbind_assert:
  !b x. OPTION_IGNORE_BIND (OPTION_GUARD b) x = if b then x else NONE
Proof
  Cases THEN EVAL_TAC THEN SIMP_TAC std_ss []
QED

Theorem OPTION_BIND_THM:
   !x y. OPTION_BIND x y = case x of NONE => NONE | SOME i => y i
Proof
  Cases THEN SRW_TAC [] []
QED

val _ = (extra_preprocessing :=
  [MEMBER_INTRO,MAP,OPTION_BIND_THM,monad_unitbind_assert]);

(*-----------------------------------------------------------------------*
   infer
 *-----------------------------------------------------------------------*)

Theorem LLOOKUP_INTRO:
  ∀ts v d. (if v < LENGTH ts then EL v ts else d) =
           case LLOOKUP ts v of SOME x => x | NONE => d
Proof
  Induct \\ fs [LLOOKUP_def]
  \\ rw [] \\ fs []
  \\ Cases_on ‘v’ \\ fs []
  \\ metis_tac []
QED

val r = translate (def_of_const “isubst” |> RW [LLOOKUP_INTRO]);

val isubst_side = Q.prove (
  ‘∀b a. isubst_side a b ⇔ T’,
  Induct using pure_inference_commonTheory.itype_ind >> rw[] >>
  simp[Once $ fetch "-" "isubst_side_def"] >> gvs[oEL_THM])
  |> update_precondition;

val r = translate (pure_inferenceTheory.get_typedef_def
                     |> DefnBase.one_line_ify NONE |> RW [ADD1]);

val r = translate sptreeTheory.insert_def;
val r = translate sptreeTheory.union_def;
val r = translate sptreeTheory.lrnext_def;
val r = translate sptreeTheory.foldi_def;
val r = translate pure_inferenceTheory.infer_cons_def;
val r = translate pure_inference_commonTheory.itype_of_def;
val r = translate pure_inference_commonTheory.iFunctions_def;
val r = translate FOLDL;
val r = translate list_insert_def;
val r = translate pure_varsTheory.list_delete_def;

Theorem infer_bind_eq:
  infer_bind g f =
    λs. case g s of Err e => Err e | OK (x,s') => f x s'
Proof
  fs [FUN_EQ_THM,infer_bind_def]
QED

Theorem infer_ignore_bind_eq:
  infer_ignore_bind g f =
    λs. case g s of Err e => Err e | OK (x,s') => f s'
Proof
  fs [FUN_EQ_THM,infer_bind_def,infer_ignore_bind_def]
QED

val r = translate
  (apply_foldr_def
   |> SIMP_RULE std_ss [infer_bind_eq,infer_ignore_bind_eq]);

val r = translate
  (pure_inferenceTheory.infer'_prim_def
   |> SIMP_RULE std_ss [infer_bind_eq,infer_ignore_bind_eq]);

val r = translate
  (pure_inferenceTheory.infer'_def
   |> SIMP_RULE std_ss [infer_bind_eq,infer_ignore_bind_eq]);

val r = translate pure_inferencePropsTheory.infer'_infer;

val _ = (length (hyp r) = 0) orelse fail (); (* no side conditions *)

(*-----------------------------------------------------------------------*
   pure_unify
 *-----------------------------------------------------------------------*)

val _ = add_preferred_thy "-";

Triviality PRECONDITION_INTRO:
  (b ==> (x = y)) ==> (x = if PRECONDITION b then y else x)
Proof
  Cases_on `b` \\ SIMP_TAC std_ss [PRECONDITION_def]
QED

Triviality EXISTS_eq:
  ∀xs. EXISTS P xs ⇔ MEMBER T (MAP P xs)
Proof
  fs [GSYM MEMBER_INTRO]
  \\ Induct \\ fs []
QED

Theorem pure_vwalk_ind:
   !P.
      (!s v.
        (!v1 u. FLOOKUP s v = SOME v1 /\ v1 = CVar u ==> P s u) ==>
        P s v) ==>
      (!s v. pure_wfs s ==> P s v)
Proof
  NTAC 3 STRIP_TAC
  \\ Cases_on `pure_wfs s` \\ FULL_SIMP_TAC std_ss []
  \\ HO_MATCH_MP_TAC
     (pure_unificationTheory.pure_vwalk_ind
       |> SPEC_ALL |> UNDISCH
       |> Q.SPEC `P (s:num |-> itype)`
       |> DISCH_ALL |> RW [AND_IMP_INTRO] |> GEN_ALL)
  \\ fs []
QED

val r = translate
 (pure_unificationTheory.pure_vwalk
  |> SIMP_RULE std_ss [PULL_FORALL] |> SPEC_ALL
  |> MATCH_MP PRECONDITION_INTRO)

Theorem pure_vwalk_side_def[allow_rebind]:
  ∀s v. pure_vwalk_side s v ⇔ pure_wfs s
Proof
  strip_tac \\ reverse $ Cases_on ‘pure_wfs s’ \\ fs []
  >- simp [Once $ fetch "-" "pure_vwalk_side_def"]
  \\ strip_tac
  \\ first_assum mp_tac
  \\ first_x_assum mp_tac
  \\ qid_spec_tac ‘v’
  \\ qid_spec_tac ‘s’
  \\ ho_match_mp_tac pure_vwalk_ind
  \\ rw [] \\ fs []
  \\ simp [Once $ fetch "-" "pure_vwalk_side_def"]
QED

val _ = pure_vwalk_side_def |> update_precondition;

val r = translate pure_unificationTheory.pure_walk;

Theorem pure_walk_side[simp]:
  ∀s t. pure_wfs s ⇒ pure_walk_side s t
Proof
  simp [Once $ fetch "-" "pure_walk_side_def"]
QED

Theorem pure_oc_ind:
  ∀P. (∀v13 v14 v15.
         (∀x9 x8 x7 x6 x5 x4 x3.
            (pure_walk v13 v14 = TypeCons x9 x8 ⇒
             ∀x1. MEM x1 x8 ⇒ P v13 x1 v15) ∧
            (pure_walk v13 v14 = Tuple x7 ⇒ ∀x2. MEM x2 x7 ⇒ P v13 x2 v15) ∧
            (pure_walk v13 v14 = Function x6 x5 ⇒
             P v13 x6 v15 ∧ (¬pure_oc v13 x6 v15 ⇒ P v13 x5 v15)) ∧
            (pure_walk v13 v14 = Array x4 ⇒ P v13 x4 v15) ∧
            (pure_walk v13 v14 = M x3 ⇒ P v13 x3 v15)) ⇒
         P v13 v14 v15) ⇒
      ∀s t v. pure_wfs s ⇒ P s t v
Proof
  rpt strip_tac
  \\ drule pure_unificationTheory.pure_walkstar_ind
  \\ disch_then $ qspec_then ‘λx. ∀v. P s x v’ mp_tac
  \\ simp []
QED

val r = translate
 (pure_unificationTheory.pure_oc
  |> SIMP_RULE std_ss [PULL_FORALL,EXISTS_eq,MAP,MEMBER_def]
  |> SPEC_ALL
  |> MATCH_MP PRECONDITION_INTRO)

Triviality pure_oc_side:
  pure_oc_side s t v = pure_wfs s
Proof
  reverse $ Cases_on ‘pure_wfs s’ \\ simp []
  >- simp [Once $ fetch "-" "pure_oc_side_def"]
  \\ first_assum mp_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘v’
  \\ qid_spec_tac ‘t’
  \\ qid_spec_tac ‘s’
  \\ ho_match_mp_tac pure_oc_ind
  \\ rw []
  \\ simp [Once $ fetch "-" "pure_oc_side_def"]
QED

val _ = pure_oc_side |> update_precondition;

val r = translate pure_unificationTheory.pure_ext_s_check;

Triviality pure_ext_s_check_side:
  pure_ext_s_check_side s t v = pure_wfs s
Proof
  rewrite_tac [fetch "-" "pure_ext_s_check_side_def"]
QED

val _ = pure_ext_s_check_side |> update_precondition;

Triviality pure_unify_lemma:
  (pure_unify s t1 t2 =
     if PRECONDITION (pure_wfs s) then
      (case (pure_walk s t1,pure_walk s t2) of
         (DBVar db1,DBVar db2) => if db1 = db2 then SOME s else NONE
       | (DBVar db1,CVar v53) => pure_ext_s_check s v53 (DBVar db1)
       | (PrimTy pty1,PrimTy pty2) => if pty1 = pty2 then SOME s else NONE
       | (PrimTy pty1,CVar v73) => pure_ext_s_check s v73 (PrimTy pty1)
       | (Exception,Exception) => SOME s
       | (Exception,CVar v93) => pure_ext_s_check s v93 Exception
       | (TypeCons c1 ts1,TypeCons c2 ts2) =>
         if c1 = c2 then pure_unifyl s ts1 ts2 else NONE
       | (TypeCons c1 ts1,CVar v113) =>
         pure_ext_s_check s v113 (TypeCons c1 ts1)
       | (Tuple ts1',Tuple ts2') => pure_unifyl s ts1' ts2'
       | (Tuple ts1',CVar v133) => pure_ext_s_check s v133 (Tuple ts1')
       | (Function t11 t12,Function t21 t22) =>
         pure_unifyl s [t11; t12] [t21; t22]
       | (Function t11 t12,CVar v153) =>
         pure_ext_s_check s v153 (Function t11 t12)
       | (Array t1,Array t2) => pure_unify s t1 t2
       | (Array t1,CVar v173) => pure_ext_s_check s v173 (Array t1)
       | (M t1',M t2') => pure_unify s t1' t2'
       | (M t1',CVar v193) => pure_ext_s_check s v193 (M t1')
       | (CVar v1,DBVar v214) => pure_ext_s_check s v1 (DBVar v214)
       | (CVar v1,PrimTy v215) => pure_ext_s_check s v1 (PrimTy v215)
       | (CVar v1,Exception) => pure_ext_s_check s v1 Exception
       | (CVar v1,TypeCons v216 v217) =>
         pure_ext_s_check s v1 (TypeCons v216 v217)
       | (CVar v1,Tuple v218) => pure_ext_s_check s v1 (Tuple v218)
       | (CVar v1,Function v219 v220) =>
         pure_ext_s_check s v1 (Function v219 v220)
       | (CVar v1,Array v221) => pure_ext_s_check s v1 (Array v221)
       | (CVar v1,M v222) => pure_ext_s_check s v1 (M v222)
       | (CVar v1,CVar v2) => SOME (if v1 = v2 then s else s |+ (v1,CVar v2))
       | _ => NONE)
     else pure_unify s t1 t2) ∧
  (pure_unifyl s ts1 ts2 =
     if PRECONDITION (pure_wfs s) then
       case (ts1,ts2) of
       | ([],[]) => SOME s
       | (t1::ts1,t2::ts2) => (case pure_unify s t1 t2 of
                               | NONE => NONE
                               | SOME s' => pure_unifyl s' ts1 ts2)
       | _ => NONE
     else pure_unifyl s ts1 ts2)
Proof
  Cases_on ‘pure_wfs s’ \\ fs [PRECONDITION_def] \\ conj_tac
  >- (drule_then (qspecl_then [‘t1’,‘t2’] mp_tac) pure_unificationTheory.pure_unify
      \\ strip_tac \\ gvs [AllCaseEqs()])
  \\ Cases_on ‘ts1’ \\ Cases_on ‘ts2’ \\ fs []
  \\ fs [pure_unificationTheory.pure_unifyl_def]
QED

val r = translate_no_ind pure_unify_lemma;

Triviality pure_unify_ind:
  pure_unify_ind
Proof
  rewrite_tac [fetch "-" "pure_unify_ind_def"]
  \\ rpt gen_tac \\ strip_tac
  \\ ho_match_mp_tac pure_unificationTheory.pure_unify_ind
  \\ conj_tac
  >-
   (rpt strip_tac
    \\ last_x_assum irule
    \\ last_x_assum kall_tac
    \\ fs [])
  \\ last_x_assum kall_tac
  \\ rw []
  \\ Cases_on ‘ts1’ \\ fs []
  \\ Cases_on ‘ts2’ \\ fs []
QED

val _ = pure_unify_ind |> update_precondition;

val pure_unify_ind_lemma =
  pure_unify_ind |> REWRITE_RULE [fetch "-" "pure_unify_ind_def"];

Triviality pure_unify_side:
  (∀s t1 t2. pure_unify_side s t1 t2 ⇔ pure_wfs s) ∧
  (∀s ts1 ts2. pure_unifyl_side s ts1 ts2 ⇔ pure_wfs s)
Proof
  qsuff_tac ‘
    (∀s t1 t2. pure_wfs s ⇒ pure_wfs s ⇒ pure_unify_side s t1 t2) ∧
    (∀s ts1 ts2. pure_wfs s ⇒ pure_wfs s ⇒ pure_unifyl_side s ts1 ts2)’
  >-
   (rw [] \\ Cases_on ‘pure_wfs s’ \\ fs []
    \\ simp [Once $ fetch "-" "pure_unify_side_def"])
  \\ ho_match_mp_tac pure_unify_ind_lemma
  \\ rw []
  \\ simp [Once $ fetch "-" "pure_unify_side_def"]
  \\ rw [] \\ fs [SF SFY_ss]
  \\ res_tac \\ fs []
  \\ imp_res_tac pure_unificationTheory.pure_unify_wfs \\ fs []
QED

val _ = pure_unify_side |> update_precondition;

Definition pure_unify_empty_def:
  pure_unify_empty x y = pure_unify FEMPTY x y
End

val r = translate pure_unify_empty_def;

Theorem pure_walkstar_ind:
  ∀P. (∀v13 v14.
         (∀x9 x8 x7 x6 x5 x4 x3.
            (pure_walk v13 v14 = TypeCons x9 x8 ⇒ ∀x1. MEM x1 x8 ⇒ P v13 x1) ∧
            (pure_walk v13 v14 = Tuple x7 ⇒ ∀x2. MEM x2 x7 ⇒ P v13 x2) ∧
            (pure_walk v13 v14 = Function x6 x5 ⇒ P v13 x6 ∧ P v13 x5) ∧
            (pure_walk v13 v14 = Array x4 ⇒ P v13 x4) ∧
            (pure_walk v13 v14 = M x3 ⇒ P v13 x3)) ⇒
         P v13 v14) ⇒
      ∀s t. pure_wfs s ⇒ P s t
Proof
  rpt strip_tac
  \\ drule pure_unificationTheory.pure_walkstar_ind
  \\ disch_then $ qspec_then ‘λx. P s x’ mp_tac
  \\ simp []
QED

Triviality pure_walkstar_eta:
  MAP (pure_walkstar s) = MAP $ λx. pure_walkstar s x
Proof
  AP_TERM_TAC \\ fs [FUN_EQ_THM]
QED

val r = translate
 (pure_unificationTheory.pure_walkstar
  |> SIMP_RULE std_ss [PULL_FORALL,EXISTS_eq,MAP,MEMBER_def]
  |> SPEC_ALL
  |> MATCH_MP PRECONDITION_INTRO
  |> ONCE_REWRITE_RULE [pure_walkstar_eta]);

Theorem pure_walkstar_side:
  pure_walkstar_side s t = pure_wfs s
Proof
  reverse $ Cases_on ‘pure_wfs s’ \\ simp []
  >- simp [Once $ fetch "-" "pure_walkstar_side_def"]
  \\ first_assum mp_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘t’
  \\ qid_spec_tac ‘s’
  \\ ho_match_mp_tac pure_walkstar_ind
  \\ rw []
  \\ simp [Once $ fetch "-" "pure_walkstar_side_def"]
QED

val _ = pure_walkstar_side |> update_precondition;

(*-----------------------------------------------------------------------*
   solve
 *-----------------------------------------------------------------------*)

val r = translate is_solveable_def;
val r = translate get_solveable_def;
val r = translate activevars_def;
val r = translate oreturn_def;
val r = translate generalise_def;
val r = translate monomorphise_implicit_def;
val r = translate subst_constraint_def;

Theorem subst_constraint_side:
  ∀s t. subst_constraint_side s t = pure_wfs s
Proof
  ho_match_mp_tac subst_constraint_ind \\ rw []
  \\ simp [Once $ fetch "-" "subst_constraint_side_def"]
  \\ fs [fetch "-" "subst_vars_side_def"]
QED

val _ = subst_constraint_side |> update_precondition;

Triviality infer_bind:
  infer_bind (g : ('a,'e) inferM) f = λs.
    case g s of
    | Err e => Err e
    | OK (x, s') => (f x : ('b,'e) inferM) s'
Proof
  fs [infer_bind_def,FUN_EQ_THM]
QED

val r = translate
  (solve_def |> RW [GSYM pure_unify_empty_def]
   |> SIMP_RULE std_ss [infer_bind]);

Theorem solve_side:
  ∀s. solve_side s
Proof
  ho_match_mp_tac solve_ind \\ rw []
  \\ simp [Once $ fetch "-" "solve_side_def"]
  \\ rw [] \\ gvs []
  \\ Cases_on ‘pure_unify_empty x29 x28’
  \\ gvs [oreturn_def,fail_def,return_def]
  \\ fs [pure_unify_empty_def]
  \\ imp_res_tac pure_unificationTheory.pure_unify_wfs
  \\ fs []
QED

val r = solve_side |> update_precondition;

(*-----------------------------------------------------------------------*
   top-level entry point
 *-----------------------------------------------------------------------*)

val r = translate pure_inferenceTheory.infer_top_level_def;

val r = translate pure_typingTheory.freetyvars_ok_def;

Triviality type_wf_eq:
  type_wf typedefs v ⇔
     case v of
       TypeVar n => T
     | PrimTy pty => T
     | Exception => T
     | TypeCons id tyargs =>
       (EVERY I (MAP (λa. type_wf typedefs a) tyargs) ∧
        case LLOOKUP typedefs id of
        | NONE => F
        | SOME (arity,constructors) => LENGTH tyargs = arity)
     | Tuple ts => EVERY I (MAP (λa. type_wf typedefs a) ts)
     | Function tf t => type_wf typedefs t ∧ type_wf typedefs tf
     | Array t => type_wf typedefs t
     | M t => type_wf typedefs t
Proof
  Cases_on ‘v’ \\ fs [pure_typingTheory.type_wf_def]
  \\ fs [EVERY_MAP]
  \\ rpt (CASE_TAC \\ fs []) \\ eq_tac \\ rw []
QED

val r = translate type_wf_eq;

Definition every_pair_def:
  every_pair P [] = T ∧
  (every_pair P ((x,y)::xs) ⇔ P x y ∧ every_pair P xs)
End

Triviality intro_every_pair:
  EVERY P xs ⇔ every_pair (λx y. P (x,y)) xs
Proof
  Induct_on ‘xs’ \\ fs [FORALL_PROD,every_pair_def]
QED

val r = translate (pure_inferenceTheory.typedefs_ok_impl_def
          |> SIMP_RULE std_ss [intro_every_pair]);

val r = translate pure_inferenceTheory.infer_types_def;

val _ = export_theory ();
