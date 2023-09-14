open HolKernel Parse boolLib bossLib;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     combinTheory mlmapTheory indexedListsTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_exp_relTheory
     pure_miscTheory pure_letrec_delargTheory;
open pure_cexpTheory pure_varsTheory balanced_mapTheory pureLangTheory;
open pure_exp_relTheory pure_congruenceTheory
open pure_inlineTheory pure_letrec_spec_cexpTheory

val _ = new_theory "pure_letrec_spec_cexpProof";

Theorem exp_of_SmartLam[simp]:
  exp_of (SmartLam a vs x) = exp_of (Lam a vs x)
Proof
  rw [SmartLam_def] \\ Cases_on ‘vs’ \\ gvs [exp_of_def,Lams_def]
QED

Theorem exp_of_SmartApp[simp]:
  exp_of (SmartApp a x xs) = exp_of (App a x xs)
Proof
  rw [SmartApp_def] \\ Cases_on ‘xs’ \\ gvs [exp_of_def,Apps_def]
QED

Theorem split_at_thm:
  ∀n xs ys zs.
    split_at n xs = (ys,zs) ∧ n ≤ LENGTH xs ⇒
    xs = ys ++ zs ∧ LENGTH ys = n
Proof
  Induct \\ simp [Once split_at_def]
  \\ Cases \\ fs [] \\ rw [] \\ pairarg_tac \\ gvs []
  \\ res_tac \\ fs []
QED

Theorem drop_common_prefix_thm:
  ∀xs ys xs1 ys1.
    drop_common_prefix xs ys = (xs1,ys1) ⇒
    ∃zs. xs = zs ++ xs1 ∧ ys = zs ++ ys1 ∧
         (xs1 ≠ [] ∧ ys1 ≠ [] ⇒ HD xs1 ≠ HD ys1)
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs [drop_common_prefix_def]
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem drop_common_suffix_thm:
  ∀xs ys xs1 ys1.
    drop_common_suffix xs ys = (xs1,ys1) ⇒
    ∃zs. xs = xs1 ++ zs ∧ ys = ys1 ++ zs ∧
         (xs1 ≠ [] ∧ ys1 ≠ [] ⇒ LAST xs1 ≠ LAST ys1)
Proof
  rw [drop_common_suffix_def]
  \\ pairarg_tac \\ gvs []
  \\ imp_res_tac drop_common_prefix_thm
  \\ gvs [SWAP_REVERSE_SYM]
  \\ gvs [GSYM SWAP_REVERSE_SYM,LAST_REVERSE]
QED

Definition min_app_def[simp]:
  min_app f n e =
    (∀a b es. e = App a (Var b f) es ⇒ n ≤ LENGTH es)
End

Theorem spec_one_thm:
  (∀f v vs (e:'a cexp) e1.
     spec_one f v vs e = SOME e1 ∧
     every_cexp (min_app f (LENGTH vs)) e ∧
     explode f ∉ boundvars (exp_of e) ∧
     explode v ∉ boundvars (exp_of e) ∧
     vs = MAP (K T) bs ++ [F] ++ MAP (K T) ts ⇒
     can_spec_arg (explode f) bs (explode v) ts (exp_of e) (exp_of e1) ∧
     boundvars (exp_of e1) ⊆ boundvars (exp_of e) ∧
     every_cexp (min_app f (LENGTH bs + LENGTH ts)) e1) ∧
  (∀f v vs (e:'a cexp list) e1.
     spec_one_list f v vs e = SOME e1 ∧
     EVERY (λe.
       every_cexp (min_app f (LENGTH vs)) e ∧
       explode f ∉ boundvars (exp_of e) ∧
       explode v ∉ boundvars (exp_of e)) e ∧
     vs = MAP (K T) bs ++ [F] ++ MAP (K T) ts ⇒
     LIST_REL (λe e1.
       can_spec_arg (explode f) bs (explode v) ts (exp_of e) (exp_of e1) ∧
       boundvars (exp_of e1) ⊆ boundvars (exp_of e) ∧
       every_cexp (min_app f (LENGTH bs + LENGTH ts)) e1) e e1) ∧
  (∀f v vs (e:(mlstring # 'a cexp) list) e1.
     spec_one_letrec f v vs e = SOME e1 ⇒ ARB e) ∧
  (∀f v vs (e:(mlstring # mlstring list # 'a cexp) list) e1.
     spec_one_case f v vs e = SOME e1 ⇒ ARB e) ∧
  (∀f v vs (e:((mlstring # num) list # 'a cexp) option) e1.
     spec_one_opt f v vs e = SOME e1 ⇒ ARB e)
Proof
  ho_match_mp_tac spec_one_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ rpt disch_tac
  \\ rpt gen_tac \\ rpt disch_tac \\ gvs [exp_of_def,SF ETA_ss]
  \\ gvs [spec_one_def,AllCaseEqs(),exp_of_def,SF ETA_ss]
  >~ [‘Apps’] >-
   (‘∃b. e = Var b f’ by (Cases_on ‘e’ \\ fs [eq_Var_def])
    \\ gvs [exp_of_def] \\ cheat)
  >~ [‘Apps’] >- cheat
  >~ [‘Var’] >-
   (irule can_spec_arg_Var \\ fs [])
  >~ [‘Let a x y’] >- cheat
  >~ [‘Lams’] >- cheat
  >~ [‘Prim’] >- cheat
  >~ [‘Letrec’] >- cheat
  >~ [‘rows_of’] >- cheat
  \\ cheat
QED

Triviality can_spec_arg_map:
  ∀f vs v ws e1 e2.
    can_spec_arg f vs v ws e1 e2 ⇒
    can_spec_arg f (MAP explode vs) v (MAP explode ws) e1 e2
Proof
  ho_match_mp_tac can_spec_arg_ind \\ fs [] \\ rw []
  \\ simp [Once can_spec_arg_cases] \\ gvs [SF ETA_ss]
  \\ metis_tac []
QED

Triviality delete_with_lemma:
  ∀xs ys.
    delete_with (MAP (K T) xs ++ [F] ++ MAP (K T) ys) (xs ++ [h] ++ ys) = xs ++ ys
Proof
  Induct \\ fs [delete_with_def]
  \\ Induct \\ fs [delete_with_def]
QED

Triviality MAP_NEQ:
  ∀xs x. ¬MEM x xs ⇒ MAP (λv. x ≠ v) xs = MAP (K T) xs
Proof
  Induct \\ fs []
QED

Theorem specialise_each_thm:
  ∀p args f c args1 c1.
    specialise_each p args f c = (args1,c1) ∧
    every_cexp (min_app f (LENGTH args)) c ∧
    explode f ∉ boundvars (exp_of c) ∧
    EVERY (λv. v ∉ boundvars (exp_of c)) (MAP explode args) ∧
    ALL_DISTINCT p ∧ ALL_DISTINCT (MAP explode args) ∧
    set p ⊆ set args ∧ ~MEM f args
    ⇒
    Letrec [(explode f,Lams (MAP explode args) (exp_of c))]
      (Apps (Var (explode f)) (MAP Var (MAP explode args)))
    ≅
    Letrec [(explode f,Lams (MAP explode args1) (exp_of c1))]
      (Apps (Var (explode f)) (MAP Var (MAP explode args1)))
Proof
  Induct \\ fs [specialise_each_def,exp_eq_refl]
  \\ rpt gen_tac \\ IF_CASES_TAC \\ strip_tac \\ gvs [exp_eq_refl]
  \\ gvs [CaseEq"bool"] \\ gvs [CaseEq"option"]
  \\ ‘∃args1 args2. args = args1 ++ [h] ++ args2 ∧ ~MEM h args1 ∧ ~MEM h args2’ by
   (qpat_x_assum ‘ALL_DISTINCT args’ mp_tac
    \\ qpat_x_assum ‘MEM h args’ mp_tac
    \\ qid_spec_tac ‘args’ \\ Induct
    \\ fs [] \\ strip_tac \\ Cases_on ‘h = h'’ \\ gvs [] \\ rw []
    >- (qexists_tac ‘[]’ \\ fs [])
    \\ fs [] \\ qexists_tac ‘h'::args1'’ \\ fs [])
  \\ gvs [MAP_NEQ]
  \\ drule (CONJUNCT1 spec_one_thm |> SIMP_RULE std_ss [])
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ irule exp_eq_trans
  \\ irule_at Any (letrec_spec_delarg |> SIMP_RULE std_ss [MAP_APPEND,MAP])
  \\ irule_at Any can_spec_arg_map
  \\ first_x_assum $ irule_at Any
  \\ conj_tac >- (CCONTR_TAC \\ gvs [])
  \\ conj_tac >- (gvs [ALL_DISTINCT_APPEND,MEM_MAP] \\ rw [] \\ gvs [])
  \\ rewrite_tac [GSYM MAP_APPEND]
  \\ last_x_assum irule \\ fs [delete_with_lemma]
  \\ gvs [ALL_DISTINCT_APPEND,SUBSET_DEF,MEM_MAP,EVERY_MEM,PULL_EXISTS,SF SFY_ss]
  \\ metis_tac []
QED

Triviality set_delete_with:
  ∀args f. set (delete_with f args) ⊆ set args
Proof
  Induct \\ Cases_on ‘f’ \\ fs [delete_with_def]
  \\ fs [SUBSET_DEF]
  \\ Cases_on ‘h’ \\ fs [delete_with_def]
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem specialise_each_subset:
  ∀p args f c args1 c1.
    specialise_each p args f c = (args1,c1) ⇒
    set args1 ⊆ set args
Proof
  Induct \\ fs [specialise_each_def] \\ rw []
  \\ rw [] \\ res_tac \\ fs []
  \\ gvs [AllCaseEqs()] \\ res_tac \\ fs []
  \\ irule SUBSET_TRANS
  \\ pop_assum $ irule_at Any
  \\ fs [set_delete_with]
QED

Theorem no_shadowing_Lams_distinct:
  ∀args x.
    no_shadowing (Lams args x) ⇒
    ALL_DISTINCT args
Proof
  Induct \\ simp [Once no_shadowing_cases,Lams_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ pop_assum kall_tac \\ pop_assum mp_tac
  \\ qid_spec_tac ‘args’ \\ Induct \\ fs [Lams_def]
QED

Theorem no_shadowing_Lams:
  ∀args x.
    no_shadowing (Lams args x) ⇒
    EVERY (λv. v ∉ boundvars x) args
Proof
  Induct \\ simp [Once no_shadowing_cases,Lams_def]
  \\ rw [] \\ pop_assum mp_tac
  \\ qid_spec_tac ‘args’ \\ Induct \\ fs [Lams_def]
QED

Theorem LENGTH_const_call_args:
  LENGTH (const_call_args f xs (c:'a cexp)) ≤ LENGTH xs
Proof
  qsuff_tac ‘
      (∀f xs (c:'a cexp). LENGTH (const_call_args f xs c) ≤ LENGTH xs) ∧
      (∀f xs (c:'a cexp list). LENGTH (const_call_args_list f xs c) ≤ LENGTH xs)’
  >- fs []
  \\ ho_match_mp_tac const_call_args_ind \\ rw []
  \\ simp [Once const_call_args_def]
  \\ rw [] \\ rpt (CASE_TAC \\ gvs [])
  \\ irule LESS_EQ_TRANS
  \\ pop_assum $ irule_at Any
  \\ qid_spec_tac ‘c’
  \\ qid_spec_tac ‘xs’
  \\ ho_match_mp_tac min_call_args_ind
  \\ fs [min_call_args_def] \\ rw []
QED

Theorem min_call_args_el:
  ∀xs c i x.
    EL i (min_call_args xs c) = SOME x ∧
    i < LENGTH (min_call_args xs c)
    ⇒
    EL i xs = SOME x ∧ i < LENGTH xs
Proof
  ho_match_mp_tac min_call_args_ind
  \\ rw [] \\ fs [min_call_args_def]
  \\ Cases_on ‘i’ \\ fs [EL_MAP]
  \\ FULL_CASE_TAC \\ gvs []
QED

Theorem const_call_args_el:
  (∀f xs (c:'a cexp) i x.
     i < LENGTH (const_call_args f xs c) ∧
     EL i (const_call_args f xs c) = SOME x ⇒
     EL i xs = SOME x ∧ i < LENGTH xs) ∧
  (∀f xs (c:'a cexp list) i x.
     i < LENGTH (const_call_args_list f xs c) ∧
     EL i (const_call_args_list f xs c) = SOME x ⇒
     EL i xs = SOME x ∧ i < LENGTH xs)
Proof
  ho_match_mp_tac const_call_args_ind
  \\ reverse $ rpt conj_tac
  \\ rpt gen_tac
  \\ rpt disch_tac
  \\ fs [const_call_args_def] \\ fs []
  \\ fs [SF SFY_ss]
  \\ rw [] \\ rpt (CASE_TAC \\ gvs [])
  \\ rw [] \\ rpt (FULL_CASE_TAC \\ gvs [])
  \\ res_tac \\ fs []
  \\ fs [const_call_args_def] \\ fs []
  >- metis_tac []
  \\ drule_all min_call_args_el \\ fs []
QED

Triviality MEM_all_somes:
  ∀xs x. MEM x (all_somes xs) = MEM (SOME x) xs
Proof
  Induct \\ fs [all_somes_def]
  \\ Cases \\ fs [all_somes_def]
QED

Theorem MEM_min_call_args:
  ∀xs c x.
    MEM x (all_somes (min_call_args xs c)) ⇒
    MEM x (all_somes xs)
Proof
  ho_match_mp_tac min_call_args_ind \\ rw []
  \\ fs [min_call_args_def,all_somes_def]
  \\ rpt (FULL_CASE_TAC \\ gvs [])
  \\ gvs [all_somes_def] \\ fs [MEM_all_somes,MEM_MAP]
QED

Theorem const_call_args_distinct:
  (∀f xs (c:'a cexp).
     ALL_DISTINCT (all_somes xs) ⇒
     ALL_DISTINCT (all_somes (const_call_args f xs c))) ∧
  (∀f xs (c:'a cexp list).
     ALL_DISTINCT (all_somes xs) ⇒
     ALL_DISTINCT (all_somes (const_call_args_list f xs c)))
Proof
  ho_match_mp_tac const_call_args_ind \\ rw []
  \\ fs [const_call_args_def] \\ fs []
  \\ rw [] \\ rpt (FULL_CASE_TAC \\ gvs [])
  \\ fs [const_call_args_def] \\ fs [all_somes_def]
  \\ pop_assum irule
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘c’
  \\ qid_spec_tac ‘xs’
  \\ ho_match_mp_tac min_call_args_ind
  \\ fs [min_call_args_def,all_somes_def] \\ rw []
  \\ fs [min_call_args_def,all_somes_def] \\ rw []
  \\ CCONTR_TAC \\ fs []
  \\ imp_res_tac MEM_min_call_args
QED

Triviality all_somes_map_some:
  ∀xs. all_somes (MAP SOME xs) = xs
Proof
  Induct \\ fs [all_somes_def]
QED

Theorem min_app_const_call_args:
  every_cexp (min_app f (LENGTH (const_call_args f ps c))) c1
Proof
  cheat
QED

Theorem specialise_thm:
  specialise f e = SOME out ∧
  no_shadowing (exp_of (Lam a [f] e)) ∧
  NestedCase_free e
  ⇒
  exp_of (Letrec a [(f,e)] rest)
  ≅
  exp_of (Let a f out rest)
Proof
  fs [exp_of_def,Lams_def]
  \\ Cases_on ‘e’ \\ fs [specialise_def]
  \\ strip_tac \\ gvs [exp_of_def,boundvars_Lams,MEM_MAP]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule split_at_thm
  \\ impl_tac >-
   (irule LESS_EQ_TRANS
    \\ irule_at Any LENGTH_const_call_args \\ fs [])
  \\ strip_tac
  \\ gvs [Lams_append]
  \\ qabbrev_tac ‘c1 = SmartLam a ws2 c’
  \\ qabbrev_tac ‘guide = const_call_args f (MAP SOME ws1 ++ MAP SOME ws2) c’
  \\ ‘Lams (MAP explode ws2) (exp_of c) = exp_of c1’ by fs [exp_of_def,Abbr‘c1’]
  \\ fs []
  \\ irule exp_eq_trans
  \\ irule_at (Pos hd) Letrec_expand_1 \\ fs [MEM_MAP]
  \\ irule exp_eq_App_cong \\ fs [exp_eq_refl]
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,exp_of_def]
  \\ gvs [MEM_MAP,exp_of_def]
  \\ drule drop_common_suffix_thm
  \\ strip_tac
  \\ pop_assum kall_tac
  \\ gvs [MAP_MAP_o,combinTheory.o_DEF,exp_of_def]
  \\ ‘∀xs. MAP (λx. pure_exp$Var (explode x)) xs = MAP Var (MAP explode xs)’ by
       fs [MAP_MAP_o,combinTheory.o_DEF,exp_of_def] \\ fs []
  \\ irule exp_eq_trans
  \\ irule_at (Pos last) Letrec_contract_1
  \\ gvs [MEM_MAP]
  \\ rewrite_tac [GSYM MAP_APPEND]
  \\ conj_tac >-
   (imp_res_tac specialise_each_subset
    \\ fs [SUBSET_DEF] \\ CCONTR_TAC \\ gvs [] \\ res_tac)
  \\ irule Lams_cong
  \\ full_simp_tac bool_ss [GSYM MAP_APPEND]
  \\ imp_res_tac no_shadowing_Lams
  \\ imp_res_tac no_shadowing_Lams_distinct
  \\ irule specialise_each_thm \\ simp []
  \\ first_x_assum $ irule_at Any \\ fs []
  \\ conj_tac >- (fs [Abbr‘c1’,exp_of_def,boundvars_Lams,MEM_MAP])
  \\ simp [SUBSET_DEF,MEM_all_somes]
  \\ conj_tac
  >-
   (unabbrev_all_tac
    \\ irule (const_call_args_distinct |> CONJUNCT1)
    \\ rewrite_tac [GSYM MAP_APPEND,all_somes_map_some]
    \\ ‘no_shadowing (exp_of (Lam a (outer_vs ++ zs ++ ws2) c))’ by
         fs [exp_of_def,Lams_append]
    \\ fs [exp_of_def]
    \\ drule no_shadowing_Lams_distinct
    \\ rewrite_tac [GSYM MAP_APPEND]
    \\ metis_tac [ALL_DISTINCT_MAP])
  \\ conj_tac
  >-
   (qsuff_tac ‘∀x. MEM (SOME x) guide ⇒ MEM x (outer_vs ++ zs)’ >- fs []
    \\ qabbrev_tac ‘zs1 = outer_vs ++ zs’
    \\ simp [MEM_EL] \\ strip_tac \\ strip_tac
    \\ pop_assum $ assume_tac o GSYM
    \\ unabbrev_all_tac
    \\ drule_all (const_call_args_el |> CONJUNCT1)
    \\ gvs [] \\ strip_tac
    \\ qexists_tac ‘n’ \\ fs []
    \\ ‘n < LENGTH (outer_vs ++ zs)’ by fs []
    \\ qpat_x_assum ‘_ = SOME x’ mp_tac
    \\ rewrite_tac [GSYM MAP_APPEND] \\ simp [EL_MAP]
    \\ strip_tac \\ rw []
    \\ metis_tac [EL_APPEND1])
  \\ fs [Abbr‘guide’,min_app_const_call_args]
QED

val _ = export_theory();
