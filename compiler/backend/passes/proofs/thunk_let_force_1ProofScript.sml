(*
  This transformation allows rewriting

     Force (Var n)    into    Var m

  inside ‘body’ in expressions such as

     Let (SOME m) (Force (Var n)) body

*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax BasicProvers;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory arithmeticTheory;
open pure_miscTheory thunkLangPropsTheory thunk_cexpTheory
     thunk_let_forceProofTheory thunk_exp_ofTheory thunk_let_forceTheory;

val _ = new_theory "thunk_let_force_1Proof";

val _ = set_grammar_ancestry ["thunk_let_force", "thunk_let_forceProof","thunk_cexp",
                              "finite_map", "pred_set", "rich_list",
                              "thunkLang", "wellorder",
                              "thunkLangProps", "thunk_exp_of"];

Overload safe_itree = “pure_semantics$safe_itree”

val _ = numLib.prefer_num ();

Definition dest_Var_def[simp]:
  dest_Var (Var n:lhs) = n
End

Triviality MAP_filter_clash_NONE:
  ∀m. MAP (filter_clash NONE) m = m
Proof
  Induct \\ fs [filter_clash_def,name_clash_def]
QED

Theorem LIST_REL_MAP_same:
  ∀xs. LIST_REL R (MAP f xs) (MAP g xs) = EVERY (λx. R (f x) (g x)) xs
Proof
  Induct \\ fs []
QED

Theorem e_rel_Lams:
  ∀vs x y m.
    e_rel (MAP (λm. if name_clashes vs m then NONE else m) m) x y ⇒
    e_rel m (Lams vs x) (Lams vs y)
Proof
  Induct \\ fs []
  >-
   (rpt gen_tac
    \\ match_mp_tac EQ_IMPLIES
    \\ rpt AP_THM_TAC \\ AP_TERM_TAC
    \\ Induct_on ‘m’ \\ fs []
    \\ Cases \\ fs []
    \\ Cases_on ‘x’ \\ fs []
    \\ Cases_on ‘q’ \\ fs [name_clashes_def])
  \\ rpt strip_tac
  \\ irule e_rel_Lam
  \\ last_x_assum irule
  \\ pop_assum mp_tac
  \\ match_mp_tac EQ_IMPLIES
  \\ rpt AP_THM_TAC \\ AP_TERM_TAC
  \\ Induct_on ‘m’ \\ fs []
  \\ Cases \\ fs []
  \\ Cases_on ‘x’ \\ fs []
  \\ Cases_on ‘q’ \\ fs [name_clashes_def] \\ rw []
  \\ gvs [name_clashes_def,name_clash_def]
QED

Theorem let_force_thm:
  ∀m x.
    EVERY (λm. ∀n x. m = SOME (n,x) ⇒ ∃v. n = Var v) m ⇒
    e_rel m (exp_of x)
            (exp_of (let_force (MAP (λ(x,n). (implode (dest_Var x),implode n))
                        (MAP THE (FILTER IS_SOME m))) x))
Proof
  rpt gen_tac \\ qid_spec_tac ‘m’ \\ qid_spec_tac ‘x’
  \\ ho_match_mp_tac (cns_arities_ind |> SIMP_RULE std_ss [])
  \\ rpt conj_tac \\ rpt gen_tac
  >~ [‘Var’] >-
   (fs [let_force_def,e_rel_Var])
  >~ [‘Delay’] >-
   (fs [let_force_def] \\ rw [] \\ irule e_rel_Delay
    \\ first_x_assum irule \\ fs [])
  >~ [‘Box’] >-
   (fs [let_force_def] \\ rw [] \\ irule e_rel_Box
    \\ first_x_assum irule \\ fs [])
  >~ [‘Force’] >-
   (rw [] \\ fs [let_force_def]
    \\ CASE_TAC \\ gvs []
    >- (irule e_rel_Force \\ res_tac \\ fs [])
    \\ CASE_TAC \\ gvs []
    >- (irule e_rel_Force \\ res_tac \\ fs [])
    \\ gvs [d_Var_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
    \\ imp_res_tac ALOOKUP_MEM
    \\ gvs [MEM_MAP,MEM_FILTER]
    \\ gvs [IS_SOME_EXISTS,UNCURRY]
    \\ gvs [EVERY_MEM] \\ res_tac \\ fs []
    \\ PairCases_on ‘x’ \\ gvs []
    \\ irule e_rel_Force_Var \\ fs [])
  >~ [‘Let opt’] >-
   (Cases_on ‘opt’ \\ fs []
    >-
     (rw [] \\ simp [let_force_def]
      \\ irule e_rel_Let \\ res_tac \\ fs [MAP_filter_clash_NONE])
    \\ rw [] \\ simp [let_force_def]
    \\ CASE_TAC \\ fs []
    >- (irule e_rel_Let \\ res_tac \\ fs []
        \\ first_x_assum $ qspec_then ‘MAP (filter_clash (SOME (explode x))) m’ mp_tac
        \\ impl_tac >-
         (qpat_x_assum ‘EVERY _ _’ mp_tac
          \\ qid_spec_tac ‘m’ \\ Induct
          \\ fs [filter_clash_def])
        \\ match_mp_tac (METIS_PROVE [] “b = c ⇒ (b ⇒ c)”)
        \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
        \\ qpat_x_assum ‘EVERY _ _’ mp_tac
        \\ qid_spec_tac ‘m’ \\ Induct
        \\ fs []
        \\ Cases \\ fs [filter_clash_def]
        \\ rename [‘name_clash _ (SOME t)’] \\ PairCases_on ‘t’ \\ gvs []
        \\ strip_tac
        \\ gvs [name_clash_def,can_keep_def]
        \\ rpt (IF_CASES_TAC \\ gvs []))
    \\ rename [‘d_Force_Var _ xx’] \\ Cases_on ‘xx’ \\ fs [d_Force_Var_def]
    \\ gvs [d_Var_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
    \\ CASE_TAC \\ fs []
    >- (irule e_rel_Let_Force_Var \\ res_tac \\ fs []
        \\ rename [‘let_force ((a,b)::_)’]
        \\ first_x_assum $ qspec_then ‘SOME (Var (explode a), explode b) ::
                                       MAP (filter_clash (SOME (explode b))) m’ mp_tac
        \\ impl_tac >-
         (qpat_x_assum ‘EVERY _ _’ mp_tac
          \\ qid_spec_tac ‘m’ \\ Induct
          \\ fs [filter_clash_def])
        \\ match_mp_tac (METIS_PROVE [] “b = c ⇒ (b ⇒ c)”)
        \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
        \\ fs []
        \\ qpat_x_assum ‘EVERY _ _’ mp_tac
        \\ qid_spec_tac ‘m’ \\ Induct
        \\ gvs [name_clash_def,can_keep_def]
        \\ Cases \\ fs [filter_clash_def]
        \\ rename [‘name_clash _ (SOME t)’] \\ PairCases_on ‘t’ \\ gvs []
        \\ strip_tac
        \\ gvs [name_clash_def,can_keep_def]
        \\ rpt (IF_CASES_TAC \\ gvs []))
    \\ irule e_rel_Let \\ res_tac \\ fs []
    \\ conj_tac
    >-
     (irule e_rel_Force_Var
      \\ imp_res_tac ALOOKUP_MEM \\ gvs [MEM_MAP,MEM_FILTER]
      \\ gvs [IS_SOME_EXISTS]
      \\ rename [‘(_,_) = _ aa’] \\ PairCases_on ‘aa’ \\ gvs [EVERY_MEM]
      \\ res_tac \\ gvs [])
    \\ first_x_assum $ qspec_then ‘MAP (filter_clash (SOME (explode x))) m’ mp_tac
    \\ impl_tac >-
     (qpat_x_assum ‘EVERY _ _’ mp_tac
      \\ qid_spec_tac ‘m’ \\ Induct
      \\ fs [filter_clash_def])
    \\ match_mp_tac (METIS_PROVE [] “b = c ⇒ (b ⇒ c)”)
    \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ qpat_x_assum ‘EVERY _ _’ mp_tac
    \\ qid_spec_tac ‘m’ \\ Induct
    \\ fs []
    \\ Cases \\ fs [filter_clash_def]
    \\ rename [‘name_clash _ (SOME t)’] \\ PairCases_on ‘t’ \\ gvs []
    \\ strip_tac
    \\ gvs [name_clash_def,can_keep_def]
    \\ rpt (IF_CASES_TAC \\ gvs []))
  >~ [‘Prim’] >-
   (rw [] \\ fs []
    \\ last_x_assum $ drule_at $ Pos $ el 2
    \\ strip_tac
    \\ fs [let_force_def]
    \\ irule e_rel_Prim
    \\ fs [MAP_MAP_o,LIST_REL_MAP_same]
    \\ fs [EVERY_MEM])
  >~ [`Monad`] >-
   (rw [] \\ fs []
    \\ last_x_assum $ drule_at $ Pos $ el 2
    \\ strip_tac
    \\ fs [let_force_def]
    \\ irule e_rel_Monad
    \\ fs [MAP_MAP_o,LIST_REL_MAP_same]
    \\ fs [EVERY_MEM])
  >~ [‘App’] >-
   (fs [exp_of_def,let_force_def]
    \\ rw [] \\ fs []
    \\ last_x_assum $ drule_at $ Pos $ el 2
    \\ first_x_assum dxrule
    \\ qid_spec_tac ‘es’
    \\ ho_match_mp_tac SNOC_INDUCT \\ rw []
    \\ gvs [FOLDL_SNOC,MAP_SNOC]
    \\ irule e_rel_App
    \\ fs [])
  >~ [‘Lam vs x’] >-
   (fs [let_force_def] \\ rw []
    \\ irule e_rel_Lams
    \\ last_x_assum $ qspec_then
         ‘(MAP (λm. if name_clashes (MAP explode vs) m then NONE else m) m)’ mp_tac
    \\ impl_tac
    >- (fs [EVERY_MEM,MEM_MAP,PULL_EXISTS] \\ rw [] \\ res_tac \\ fs [])
    \\ match_mp_tac EQ_IMPLIES
    \\ rpt AP_TERM_TAC \\ AP_THM_TAC \\ rpt AP_TERM_TAC
    \\ Induct_on ‘m’ \\ gvs [] \\ rpt strip_tac
    \\ Cases_on ‘h’ \\ fs []
    \\ Cases_on ‘x’ \\ gvs [can_keep_list_def,name_clashes_def]
    \\ rw [] \\ fs []
    \\ gvs [MEM_MAP])
  >~ [‘Letrec’] >-
   (fs [let_force_def] \\ rw []
    \\ irule e_rel_Letrec
    \\ qpat_abbrev_tac ‘m1 = MAP _ m’
    \\ qpat_abbrev_tac ‘f1 = FILTER _ _’
    \\ ‘EVERY (λm. ∀n x. m = SOME (n,x) ⇒ ∃v. n = Var v) m1’ by
      (fs [Abbr‘m1’,EVERY_MEM,MEM_MAP] \\ rw [] \\ gvs [] \\ res_tac \\ fs [])
    \\ first_x_assum drule
    \\ first_x_assum $ drule_at Any
    \\ qsuff_tac ‘(MAP (λ(x,n). (implode (dest_Var x),implode n))
                   (MAP THE (FILTER IS_SOME m1))) = f1’ >-
     (simp [MAP_MAP_o]
      \\ fs [LIST_REL_MAP_MAP,EVERY2_refl_EQ,FORALL_PROD]
      \\ rw [] \\ res_tac \\ fs [])
    \\ unabbrev_all_tac
    \\ pop_assum kall_tac
    \\ fs [FILTER_MAP,FILTER_FILTER]
    \\ fs [MAP_MAP_o,combinTheory.o_DEF]
    \\ Induct_on ‘m’ \\ fs []
    \\ Cases \\ fs []
    \\ Cases_on ‘x’ \\ fs []
    \\ strip_tac \\ gvs []
    \\ qmatch_goalsub_abbrev_tac ‘COND b1’
    \\ qpat_abbrev_tac ‘b2 = can_keep_list _ _’
    \\ qsuff_tac ‘b1 = b2’
    >- (fs [] \\ IF_CASES_TAC \\ fs []
        \\ unabbrev_all_tac \\ fs [IS_SOME_EXISTS])
    \\ unabbrev_all_tac
    \\ fs [name_clashes_def,can_keep_list_def,MEM_MAP,EXISTS_PROD,FORALL_PROD]
    \\ fs [IS_SOME_EXISTS,AllCaseEqs()]
    \\ eq_tac \\ rw [] \\ gvs [])
  \\ rename [‘Case’]
  \\ fs [let_force_def]
  \\ Induct_on ‘css’ \\ fs []
  >-
   (fs [rows_of_def] \\ Cases_on ‘d’ \\ fs []
    \\ rw [] >- simp [Once e_rel_cases]
    \\ rename [‘x = (_,_)’] \\ PairCases_on ‘x’ \\ fs []
    \\ rw [] \\ last_x_assum drule \\ rw []
    \\ simp [Once e_rel_cases]
    \\ reverse conj_tac
    >- simp [Once e_rel_cases]
    \\ rename [‘Disj a xs’]
    \\ Induct_on ‘xs’
    >- simp [Once e_rel_cases,Disj_def]
    \\ Cases \\ simp [Once e_rel_cases,Disj_def]
    \\ ntac 5 $ simp [Once e_rel_cases,Disj_def])
  \\ rw []
  \\ fs [SF DNF_ss]
  \\ PairCases_on ‘h’ \\ gvs []
  \\ fs [rows_of_def]
  \\ irule e_rel_If \\ fs []
  \\ conj_tac >- (ntac 2 $ simp [Once e_rel_cases])
  \\ reverse conj_tac >- metis_tac []
  \\ last_x_assum kall_tac
  \\ qabbrev_tac ‘n = LENGTH h1’ \\ pop_assum kall_tac
  \\ qsuff_tac ‘∀z n.
          e_rel m
          (lets_for n (explode h0) (explode x)
             (MAPi (λi v. (i+z,v)) (MAP explode h1)) (exp_of h2))
          (lets_for n (explode h0) (explode x)
             (MAPi (λi v. (i+z,v)) (MAP explode h1))
             (exp_of
                (let_force
                   (FILTER (can_keep_list h1)
                      (MAP (λ(x,n). (implode (dest_Var x),implode n))
                         (MAP THE (FILTER IS_SOME m)))) h2)))’
  >- (disch_then $ qspecl_then [‘0’,‘n’] mp_tac \\ fs [])
  \\ pop_assum mp_tac \\ qid_spec_tac ‘m’
  \\ Induct_on ‘h1’
  >-
   (rw [lets_for_def]
    \\ ‘∀xs. FILTER (can_keep_list []) xs = xs’ by
         (Induct \\ gvs [can_keep_list_def,FORALL_PROD])
    \\ fs [FORALL_PROD,lets_for_def])
  \\ fs [FORALL_PROD,lets_for_def,combinTheory.o_DEF,ADD1]
  \\ rw [] \\ ntac 6 $ simp [Once e_rel_cases]
  \\ irule e_rel_Let
  \\ conj_tac >- (ntac 6 $ simp [Once e_rel_cases])
  \\ fs [PULL_FORALL]
  \\ first_x_assum $ qspec_then
       ‘(MAP (filter_clash (SOME (explode h))) (MAP (filter_clash NONE) m))’ mp_tac
  \\ disch_then $ qspecl_then [‘z+1’,‘n’] mp_tac
  \\ impl_tac
  >-
   (fs [EVERY_MAP,filter_clash_def]
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ rw [] \\ res_tac \\ fs [])
  \\ match_mp_tac EQ_IMPLIES
  \\ rpt AP_TERM_TAC
  \\ AP_THM_TAC
  \\ rpt AP_TERM_TAC
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘m’
  \\ rpt $ pop_assum kall_tac
  \\ Induct \\ fs []
  \\ Cases \\ fs [filter_clash_def]
  \\ PairCases_on ‘x’ \\ gvs [name_clash_def]
  \\ strip_tac \\ gvs [name_clash_def,can_keep_list_def]
  \\ rw [] \\ gvs []
  \\ rw [] \\ gvs [can_keep_list_def]
QED

Theorem simp_let_force_thm:
  e_rel [] (exp_of x) (exp_of (simp_let_force T x))
Proof
  qspec_then ‘[]’ mp_tac let_force_thm
  \\ fs [simp_let_force_def]
QED

Theorem itree_of_simp_let_force:
  safe_itree (itree_of (exp_of x)) ∧
  closed (exp_of x)
  ⇒
  itree_of (exp_of (simp_let_force do_it x)) = itree_of (exp_of x) ∧
  closed (exp_of (simp_let_force do_it x))
Proof
  reverse $ Cases_on ‘do_it’
  >- simp [simp_let_force_def]
  \\ strip_tac
  \\ assume_tac simp_let_force_thm
  \\ drule_all e_rel_semantics \\ fs []
QED

Triviality let_force_Delay:
  let_force m e = Delay e' ⇒ ∃e0. e = Delay e0
Proof
  simp[Once $ DefnBase.one_line_ify NONE let_force_def] >>
  simp[AllCaseEqs(), PULL_EXISTS]
QED

Theorem simp_let_force_wf_lemmas:
  closed (exp_of (simp_let_force do_it e)) = closed (exp_of e) ∧
  cexp_wf (simp_let_force do_it e) = cexp_wf e ∧
  cexp_ok_bind (simp_let_force do_it e) = cexp_ok_bind e ∧
  cns_arities (simp_let_force do_it e) = cns_arities e
Proof
  reverse $ Cases_on ‘do_it’ >- fs [simp_let_force_def]
  \\ conj_tac >-
   (qspec_then ‘e’ mp_tac (simp_let_force_thm |> GEN_ALL)
    \\ strip_tac \\ imp_res_tac e_rel_nil_closed \\ fs [])
  \\ fs [simp_let_force_def]
  \\ rename [‘let_force m’]
  \\ ‘∃res. let_force m e = res’ by fs []
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘res’
  \\ qid_spec_tac ‘e’
  \\ qid_spec_tac ‘m’
  \\ ho_match_mp_tac let_force_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ rpt disch_tac
  \\ rpt gen_tac
  \\ simp []
  \\ pop_assum mp_tac
  \\ simp [Once let_force_def,AllCaseEqs()]
  \\ rpt strip_tac \\ gvs [cexp_wf_def,cns_arities_def]
  \\ gvs[DefnBase.one_line_ify NONE d_Force_Var_def,
         DefnBase.one_line_ify NONE d_Var_def, AllCaseEqs()]
  \\ gvs[cexp_wf_def, cexp_ok_bind_def, cns_arities_def, EVERY_MAP, EVERY_MEM]
  >- (gvs[MAP_MAP_o, combinTheory.o_DEF] >> ntac 3 AP_TERM_TAC >> gvs[MAP_EQ_f])
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF, FORALL_PROD, LAMBDA_PROD, GSYM FST_THM] >>
    rpt $ (irule AND_CONG >> simp[]) >> strip_tac >>
    eq_tac >> rw[] >> gvs[] >> metis_tac[]
    )
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY, LAMBDA_PROD, GSYM FST_THM] >>
    AP_THM_TAC >> ntac 3 AP_TERM_TAC >> gvs[MAP_EQ_f, FORALL_PROD] >> rw[] >> res_tac
    )
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FORALL_PROD] >>
    reverse $ rpt $ (irule AND_CONG >> simp[] >> strip_tac)
    >- (strip_tac >> metis_tac[]) >>
    strip_tac >> Cases_on `d` >> gvs[] >- gvs[FST_THM, LAMBDA_PROD] >>
    reverse $ rpt $ (irule AND_CONG >> simp[] >> strip_tac) >> strip_tac >>
    rpt (pairarg_tac >> gvs[]) >> simp[FST_THM, LAMBDA_PROD]
    )
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FORALL_PROD] >>
    simp[AC UNION_ASSOC UNION_COMM] >> MK_COMB_TAC
    >- (ntac 3 AP_TERM_TAC >> gvs[MAP_EQ_f, FORALL_PROD] >> metis_tac[]) >>
    Cases_on `d` >> gvs[] >> rpt (pairarg_tac >> gvs[])
    )
  >- (
    rpt $ (irule AND_CONG >> simp[]) >> strip_tac >>
    rw[DefnBase.one_line_ify NONE args_ok_def]
    )
  >- (
    rpt (TOP_CASE_TAC >> gvs[])
    >- (ntac 3 AP_TERM_TAC >> simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f])
    >- (ntac 2 AP_TERM_TAC >> simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f])
    )
  >- (ntac 2 AP_TERM_TAC >> simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f])
QED

val _ = export_theory ();
