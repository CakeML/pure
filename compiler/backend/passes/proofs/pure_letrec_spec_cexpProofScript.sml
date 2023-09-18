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

Theorem check_arg_MAP_K_T:
  ∀xs ys es.
    check_arg v (MAP (K T) xs ++ ys) es ⇒
    ∃es1 es2. es = es1 ++ es2 ∧ LENGTH xs = LENGTH es1 ∧
              check_arg v ys es2
Proof
  Induct \\ fs []
  \\ Cases_on ‘es’ \\ gvs [check_arg_def]
  \\ rw [] \\ last_x_assum dxrule \\ rw []
  \\ pop_assum $ irule_at Any
  \\ qexists_tac ‘h::es1’ \\ fs []
QED

Theorem check_arg_MAP_K_T_ALT:
  ∀xs es.
    check_arg v (MAP (K T) xs) es ⇒
    LENGTH xs ≤ LENGTH es
Proof
  Induct \\ fs [] \\ Cases_on ‘es’ \\ gvs [check_arg_def]
QED

Theorem delete_with_MAP_K_T_APPEND:
  ∀xs ys xs1 ys1.
    LENGTH xs = LENGTH ys ⇒
    delete_with (MAP (K T) xs ++ xs1) (ys ++ ys1) = ys ++ delete_with xs1 ys1
Proof
  Induct \\ Cases_on ‘ys’ \\ fs [delete_with_def]
QED

Theorem delete_with_MAP_K_T:
  ∀xs ys.
    LENGTH xs ≤ LENGTH ys ⇒
    delete_with (MAP (K T) xs) ys = ys
Proof
  Induct \\ Cases_on ‘ys’ \\ fs [delete_with_def]
QED

Theorem can_spec_arg_Var_IMP:
  can_spec_arg f vs v ws x (Var v) ∧ v ≠ f ⇒ x = Var v
Proof
  simp [Once can_spec_arg_cases]
  \\ rw [] \\ fs [mk_apps_def]
  \\ Cases_on ‘ys ++ ys1’ using SNOC_CASES
  \\ fs [Apps_def] \\ fs [SNOC_APPEND,Apps_append,Apps_def]
QED

Theorem can_spec_arg_Lams:
  ∀ps x y.
    can_spec_arg f vs v ws x y ∧ ~MEM v ps ∧ ~MEM f ps ⇒
    can_spec_arg f vs v ws (Lams ps x) (Lams ps y)
Proof
  Induct \\ fs [Lams_def,PULL_EXISTS]
  \\ rw [] \\ irule can_spec_arg_Lam \\ fs []
QED

Theorem can_spec_arg_Apps:
  ∀xs ys x y.
    LIST_REL (can_spec_arg f vs v ws) xs ys ∧
    can_spec_arg f vs v ws x y ⇒
    can_spec_arg f vs v ws (Apps x xs) (Apps y ys)
Proof
  Induct using SNOC_INDUCT \\ fs [Apps_def,PULL_EXISTS]
  \\ rw [] \\ fs [SNOC_APPEND,Apps_append,Apps_def]
  \\ Cases_on ‘ys’ using SNOC_CASES
  \\ rw [] \\ fs [SNOC_APPEND,Apps_append,Apps_def]
  \\ irule can_spec_arg_App \\ fs []
QED

Theorem can_spec_arg_Apps_Var_ALT:
  LENGTH xs = LENGTH vs ∧ LENGTH ws ≤ LENGTH xs1 ∧
  LIST_REL (can_spec_arg f vs v ws) xs ys ∧
  LIST_REL (can_spec_arg f vs v ws) xs1 ys1 ⇒
  can_spec_arg f vs v ws (Apps (Var f) (xs ++ [Var v] ++ xs1))
    (Apps (Var f) (ys ++ ys1))
Proof
  strip_tac
  \\ imp_res_tac LIST_REL_LENGTH
  \\ ‘LENGTH ws ≤ LENGTH ys1’ by fs []
  \\ dxrule miscTheory.LESS_EQ_LENGTH
  \\ dxrule miscTheory.LESS_EQ_LENGTH
  \\ rpt strip_tac \\ gvs []
  \\ drule LIST_REL_APPEND_IMP \\ fs []
  \\ once_rewrite_tac [Apps_append] \\ rw []
  \\ irule can_spec_arg_Apps \\ fs []
  \\ irule (can_spec_arg_Apps_Var |> SIMP_RULE std_ss [mk_apps_def,APPEND_NIL])
  \\ fs []
QED

(*
Definition min_app_def[simp]:
  min_app f n e =
    (∀a b es. e = App a (Var b f) es ⇒ n ≤ LENGTH es)
End
*)

Triviality boundvars_Seq_Fail[simp]:
  boundvars (if MEM w (FLAT (MAP (FST ∘ SND) e'))
             then Seq Fail x else x) = boundvars x
Proof
  rw [] \\ fs [boundvars_def]
QED

Triviality freevars_Seq_Fail[simp]:
  freevars (if MEM w (FLAT (MAP (FST ∘ SND) e'))
             then Seq Fail x else x) = freevars x
Proof
  rw [] \\ fs [freevars_def]
QED

Triviality boundvars_lets_for:
  ∀ts. boundvars (lets_for p_1 w ts p_2) = boundvars p_2 ∪ set (MAP SND ts)
Proof
  Induct \\ fs [lets_for_def,FORALL_PROD,EXTENSION]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
QED

Triviality freevars_lets_for:
  ∀ts. freevars (lets_for p_1 w ts p_2) =
       (freevars p_2 DIFF set (MAP SND ts)) ∪
       (if NULL ts then {} else {w})
Proof
  Induct \\ fs [lets_for_def,FORALL_PROD,EXTENSION]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [] \\ gvs [MEM_MAP]
QED

Theorem boundvars_rows_of:
  ∀es.
    boundvars (rows_of w e es)
    =
    boundvars e ∪
    set (FLAT (MAP (FST o SND) es)) ∪
    BIGUNION (set (MAP (boundvars o SND o SND) es))
Proof
  Induct \\ fs [rows_of_def,FORALL_PROD,boundvars_lets_for]
  \\ fs [combinTheory.o_DEF]
  \\ fs [EXTENSION]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ gvs [MEM_MAP,MEM_FLAT,EXISTS_PROD,PULL_EXISTS]
  \\ metis_tac []
QED

Theorem freevars_rows_of:
  ∀es.
    freevars (rows_of w e es)
    =
    freevars e ∪
    BIGUNION (set (MAP (λ(c,vs,e). (freevars e DIFF set vs) ∪ {w}) es))
Proof
  Induct \\ fs [rows_of_def,FORALL_PROD,freevars_lets_for]
  \\ fs [combinTheory.o_DEF]
  \\ fs [EXTENSION]
  \\ gvs [MEM_MAP,MEM_FLAT,EXISTS_PROD,PULL_EXISTS]
  \\ rpt gen_tac
  \\ Cases_on ‘x = w’ \\ gvs []
  \\ Cases_on ‘x ∈ freevars e’ \\ fs []
  \\ Cases_on ‘x ∈ freevars p_2’ \\ fs []
  \\ Cases_on ‘MEM x p_1'’ \\ fs [] \\ rw []
QED

Triviality can_spec_arg_if:
  can_spec_arg f bs v ts e e1 ⇒
  can_spec_arg f bs v ts (if b then Seq Fail e else e)
                         (if b then Seq Fail e1 else e1)
Proof
  rw [] \\ rpt (irule can_spec_arg_Prim \\ fs [])
QED

Triviality map_eq_lemma:
  ∀xs ys.
    MAP (λ(p1,p1',p2). p1') xs = MAP (λ(p1,p1',p2). p1') ys ∧
    MEM (p_1,p_1',p_2) xs ∧ MEM y p_1' ⇒
    ∃a b c z. MEM (a,b,c) ys ∧ MEM y b
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs [FORALL_PROD] \\ rw []
  \\ PairCases_on ‘h’ \\ gvs [] \\ metis_tac []
QED

Theorem can_spec_arg_Disj:
  ∀xs w f bs v ts. w ≠ f ⇒ can_spec_arg f bs v ts (Disj w xs) (Disj w xs)
Proof
  Induct \\ fs [Disj_def] \\ rw []
  >- (irule_at Any can_spec_arg_Prim \\ fs [])
  \\ PairCases_on ‘h’ \\ fs [Disj_def]
  \\ irule_at Any can_spec_arg_Prim \\ fs []
  \\ irule_at Any can_spec_arg_Prim \\ fs []
  \\ irule_at Any can_spec_arg_Prim \\ fs []
  \\ irule_at Any can_spec_arg_Var \\ fs []
QED

Theorem can_spec_arg_lets_for:
  ∀ps.
    can_spec_arg f bs v ts e1 e2 ∧ f ≠ w ∧
    ~MEM f (MAP SND ps) ∧ ~MEM v (MAP SND ps) ⇒
    can_spec_arg f bs v ts (lets_for b w ps e1) (lets_for b w ps e2)
Proof
  Induct \\ fs [lets_for_def,FORALL_PROD] \\ rw []
  \\ irule_at Any can_spec_arg_App
  \\ irule_at Any can_spec_arg_Lam
  \\ irule_at Any can_spec_arg_Prim \\ fs []
  \\ irule_at Any can_spec_arg_Var \\ fs []
QED

Theorem spec_one_thm:
  (∀f v vs (e:'a cexp) e1.
     spec_one f v vs e = SOME e1 ∧ f ≠ v ∧
     explode f ∉ boundvars (exp_of e) ∧
     explode v ∉ boundvars (exp_of e) ∧
     vs = MAP (K T) bs ++ [F] ++ MAP (K T) ts ⇒
     can_spec_arg (explode f) bs (explode v) ts (exp_of e) (exp_of e1) ∧
     boundvars (exp_of e1) = boundvars (exp_of e) ∧
     freevars (exp_of e1) ⊆ freevars (exp_of e)) ∧
  (∀f v vs (e:'a cexp list) e1.
     spec_one_list f v vs e = SOME e1 ∧ f ≠ v ∧
     EVERY (λe.
       explode f ∉ boundvars (exp_of e) ∧
       explode v ∉ boundvars (exp_of e)) e ∧
     vs = MAP (K T) bs ++ [F] ++ MAP (K T) ts ⇒
     LIST_REL (λe e1.
       can_spec_arg (explode f) bs (explode v) ts (exp_of e) (exp_of e1)) e e1 ∧
     BIGUNION (set (MAP boundvars (MAP exp_of e1))) =
     BIGUNION (set (MAP boundvars (MAP exp_of e))) ∧
     BIGUNION (set (MAP freevars (MAP exp_of e1))) ⊆
     BIGUNION (set (MAP freevars (MAP exp_of e)))) ∧
  (∀f v vs (e:(mlstring # 'a cexp) list) e1.
     spec_one_letrec f v vs e = SOME e1 ∧ f ≠ v ∧
     EVERY (λe.
       explode f ∉ boundvars (exp_of (SND e)) ∧
       explode v ∉ boundvars (exp_of (SND e))) e ∧
     vs = MAP (K T) bs ++ [F] ++ MAP (K T) ts ⇒
     MAP (λ(p1,p2). explode p1) e = MAP (λ(p1,p2). explode p1) e1 ∧
     LIST_REL (can_spec_arg (explode f) bs (explode v) ts)
       (MAP SND (MAP (λ(n,x). (explode n,exp_of x)) e))
       (MAP SND (MAP (λ(n,x). (explode n,exp_of x)) e1)) ∧
     BIGUNION (set (MAP boundvars (MAP (exp_of o SND) e1))) =
     BIGUNION (set (MAP boundvars (MAP (exp_of o SND) e))) ∧
     BIGUNION (set (MAP freevars (MAP (exp_of o SND) e1))) ⊆
     BIGUNION (set (MAP freevars (MAP (exp_of o SND) e)))) ∧
  (∀f v vs (e:(mlstring # mlstring list # 'a cexp) list) e1 e4 e5 w.
     spec_one_case f v vs e = SOME e1 ∧ f ≠ v ∧ f ≠ w ∧
     EVERY (λe.
       explode f ∉ boundvars (exp_of (SND (SND e))) ∧
       explode v ∉ boundvars (exp_of (SND (SND e)))) e ∧
     vs = MAP (K T) bs ++ [F] ++ MAP (K T) ts ∧
     ~MEM f (FLAT (MAP (FST o SND) e)) ∧
     ~MEM v (FLAT (MAP (FST o SND) e)) ∧
     can_spec_arg (explode f) bs (explode v) ts e4 e5 ⇒
     MAP FST e = MAP FST e1 ∧
     MAP (FST o SND) e = MAP (FST o SND) e1 ∧
     can_spec_arg (explode f) bs (explode v) ts
       (rows_of (explode w) e4
                (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) e))
       (rows_of (explode w) e5
                (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) e1)) ∧
     BIGUNION (set (MAP boundvars (MAP (exp_of o SND o SND) e1))) =
     BIGUNION (set (MAP boundvars (MAP (exp_of o SND o SND) e))) ∧
     BIGUNION (set (MAP (λ(p1,p1',p2).
        freevars (exp_of p2) DIFF set (MAP explode p1')) e1)) ⊆
     BIGUNION (set (MAP (λ(p1,p1',p2).
        freevars (exp_of p2) DIFF set (MAP explode p1')) e))) ∧
  (∀f v vs (e:((mlstring # num) list # 'a cexp) option) e1 w.
     spec_one_opt f v vs e = SOME e1 ∧ f ≠ v ∧ f ≠ w ∧
     (case e of
      | NONE => T
      | (SOME (_,e)) => explode f ∉ boundvars (exp_of e) ∧
                        explode v ∉ boundvars (exp_of e)) ∧
     vs = MAP (K T) bs ++ [F] ++ MAP (K T) ts ⇒
     can_spec_arg (explode f) bs (explode v) ts
          (case e of NONE => Fail | SOME (a,e) => IfDisj w a (exp_of e))
          (case e1 of NONE => Fail | SOME (a,e) => IfDisj w a (exp_of e)) ∧
     boundvars (option_CASE e1 Fail (λ(p1,p2). IfDisj w p1 (exp_of p2))) =
     boundvars (option_CASE e Fail (λ(p1,p2). IfDisj w p1 (exp_of p2))) ∧
     freevars (option_CASE e1 Fail (λ(p1,p2). IfDisj w p1 (exp_of p2))) ⊆
     freevars (option_CASE e Fail (λ(p1,p2). IfDisj w p1 (exp_of p2))))
Proof
  ho_match_mp_tac spec_one_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ rpt disch_tac
  \\ rpt gen_tac \\ rpt disch_tac \\ gvs [exp_of_def,SF ETA_ss]
  \\ gvs [spec_one_def,AllCaseEqs(),exp_of_def,SF ETA_ss]
  >~ [‘Apps’] >-
   (‘∃b. e = Var b f’ by (Cases_on ‘e’ \\ fs [eq_Var_def])
    \\ gvs [exp_of_def] \\ gvs [boundvars_Apps]
    \\ last_x_assum mp_tac
    \\ impl_tac >- (gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS] \\ metis_tac [])
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule check_arg_MAP_K_T \\ strip_tac \\ gvs []
    \\ strip_tac \\ gvs [LIST_REL_SPLIT2]
    \\ Cases_on ‘es2’ \\ gvs [check_arg_def]
    \\ ‘∃b. h = Var b v’ by (Cases_on ‘h’ \\ fs [eq_Var_def])
    \\ gvs [] \\ imp_res_tac check_arg_MAP_K_T_ALT
    \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
    \\ gvs [delete_with_MAP_K_T_APPEND,delete_with_def,exp_of_def,delete_with_MAP_K_T]
    \\ drule can_spec_arg_Var_IMP
    \\ strip_tac \\ gvs []
    \\ once_rewrite_tac [EVAL “[x] ++ ys” |> GSYM] \\ rewrite_tac [APPEND_ASSOC]
    \\ irule_at Any can_spec_arg_Apps_Var_ALT
    \\ fs [LIST_REL_MAP]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ fs [SUBSET_DEF])
  >~ [‘Apps’] >-
   (fs [boundvars_Apps]
    \\ irule_at Any can_spec_arg_Apps
    \\ qpat_x_assum ‘_ ⇒ _’ mp_tac
    \\ impl_tac >- (gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS] \\ metis_tac [])
    \\ strip_tac \\ fs [LIST_REL_MAP]
    \\ fs [SUBSET_DEF])
  >~ [‘Lams’] >-
   (fs [boundvars_Lams]
    \\ irule_at Any can_spec_arg_Lams \\ fs []
    \\ fs [SUBSET_DEF])
  >~ [‘Var’] >-
   (irule can_spec_arg_Var \\ fs [])
  >~ [‘Prim’] >-
   (last_x_assum mp_tac
    \\ impl_tac >- (gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS] \\ metis_tac [])
    \\ strip_tac
    \\ irule_at Any can_spec_arg_Prim \\ fs []
    \\ fs [LIST_REL_MAP])
  >~ [‘Let _ x y’] >-
   (irule_at Any can_spec_arg_App \\ fs []
    \\ irule_at Any can_spec_arg_Lam \\ fs []
    \\ fs [SUBSET_DEF])
  >~ [‘Letrec’] >-
   (irule_at Any can_spec_arg_Letrec \\ fs []
    \\ qpat_x_assum ‘_ ⇒ _’ mp_tac
    \\ impl_tac >- (gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD] \\ metis_tac [])
    \\ strip_tac \\ fs []
    \\ fs [MAP_MAP_o,combinTheory.o_DEF] \\ fs [LAMBDA_PROD]
    \\ fs [MEM_MAP,FORALL_PROD]
    \\ fs [SUBSET_DEF]
    \\ metis_tac [])
  >~ [‘rows_of’] >-
   (first_x_assum $ qspec_then ‘w’ mp_tac
    \\ impl_tac >-
     (CASE_TAC \\ fs [] \\ CASE_TAC
      \\ fs [boundvars_rows_of,IfDisj_def])
    \\ strip_tac
    \\ first_x_assum $ qspecl_then
      [‘(case e'' of
         | NONE => Fail
         | SOME (a,e) => IfDisj w a (exp_of e))’,
       ‘(case d of
         | NONE => Fail
         | SOME (a,e) => IfDisj w a (exp_of e))’,‘w’] mp_tac
    \\ impl_tac >-
     (gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD,boundvars_rows_of]
      \\ gvs [MEM_FLAT,MEM_MAP,PULL_EXISTS,EXISTS_PROD]
      \\ metis_tac [])
    \\ strip_tac \\ fs []
    \\ irule_at Any can_spec_arg_if
    \\ irule_at Any can_spec_arg_App \\ fs []
    \\ irule_at Any can_spec_arg_Lam \\ fs []
    \\ fs [boundvars_rows_of,freevars_rows_of]
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD]
    \\ fs [MEM_MAP,FORALL_PROD]
    \\ fs [SUBSET_DEF,EXTENSION]
    \\ fs [MEM_MAP,EXISTS_PROD,MEM_FLAT,PULL_EXISTS]
    \\ conj_tac >- metis_tac [map_eq_lemma]
    \\ rw [] \\ fs []
    \\ DISJ1_TAC
    \\ DISJ2_TAC
    \\ first_x_assum irule
    \\ metis_tac [])
  >- fs [SUBSET_DEF]
  >- fs [SUBSET_DEF]
  >- fs [rows_of_def]
  >- (first_x_assum $ drule_at (Pos last)
      \\ disch_then drule \\ strip_tac \\ fs []
      \\ fs [SUBSET_DEF,rows_of_def]
      \\ irule can_spec_arg_Prim \\ fs []
      \\ irule_at Any can_spec_arg_Prim \\ fs []
      \\ irule_at Any can_spec_arg_Var \\ fs []
      \\ irule_at Any can_spec_arg_lets_for \\ fs []
      \\ CCONTR_TAC
      \\ gvs [MEM_EL,EL_MAPi,EL_MAP])
  >- (irule can_spec_arg_Prim \\ fs [])
  >- (fs [IfDisj_def] \\ fs [SUBSET_DEF]
      \\ irule can_spec_arg_Prim \\ fs []
      \\ irule_at Any can_spec_arg_Prim \\ fs []
      \\ irule_at Any can_spec_arg_Disj \\ fs [])
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
    ∧
    boundvars (exp_of c1) = boundvars (exp_of c) ∧
    freevars (exp_of c1) ⊆ freevars (exp_of c) ∧
    ALL_DISTINCT args1
Proof
  Induct \\ fs [specialise_each_def,exp_eq_refl]
  \\ rpt gen_tac \\ IF_CASES_TAC \\ strip_tac \\ gvs [exp_eq_refl]
  \\ gvs [CaseEq"bool"] \\ gvs [CaseEq"option"] \\ gvs [SF SFY_ss]
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
  \\ irule_at Any exp_eq_trans
  \\ irule_at Any (letrec_spec_delarg |> SIMP_RULE std_ss [MAP_APPEND,MAP])
  \\ irule_at Any can_spec_arg_map
  \\ first_x_assum $ irule_at Any
  \\ conj_tac >- (CCONTR_TAC \\ gvs [])
  \\ conj_tac >- (gvs [ALL_DISTINCT_APPEND,MEM_MAP] \\ rw [] \\ gvs [])
  \\ pop_assum (assume_tac o GSYM) \\ fs []
  \\ rewrite_tac [GSYM MAP_APPEND]
  \\ fs [delete_with_lemma]
  \\ last_x_assum drule
  \\ impl_tac
  >- (gvs [ALL_DISTINCT_APPEND,SUBSET_DEF,MEM_MAP,EVERY_MEM,PULL_EXISTS,SF SFY_ss]
      \\ metis_tac [])
  \\ strip_tac \\ gvs []
  \\ imp_res_tac SUBSET_TRANS
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

Triviality set_map_empty:
  ∀xs. BIGUNION (set (MAP (λx. ∅) xs)) = ∅
Proof
  fs [EXTENSION,MEM_MAP,PULL_EXISTS] \\ Cases \\ fs [] \\ metis_tac []
QED

Triviality set_MAP_explode:
  ∀vs. BIGUNION (set (MAP (λx. {explode x}) vs)) = set (MAP explode vs)
Proof
  Induct \\ fs [] \\ rw [EXTENSION]
QED

Theorem specialise_is_Lam:
  specialise f e = SOME out ⇒ ∃a vs x. out = Lam a vs x
Proof
  Cases_on ‘e’ \\ gvs [specialise_def]
  \\ rpt (pairarg_tac \\ gvs []) \\ rw []
  \\ gvs [SmartLam_def,dest_Lam_def]
QED

Theorem specialise_thm:
  specialise f e = SOME out ∧
  no_shadowing (exp_of (Lam a [f] e))
  ⇒
  Letrec [(explode f,exp_of e)] rest
  ≅
  Let (explode f) (exp_of out) rest
  ∧
  explode f ∉ freevars (exp_of out) ∧
  boundvars (exp_of out) ⊆ boundvars (exp_of e) ∪ {explode f} ∧
  freevars (exp_of out) ⊆ freevars (exp_of e)
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
  \\ fs [exp_of_def,boundvars_Lams,boundvars_Apps] \\ fs [MEM_MAP]
  \\ irule_at Any exp_eq_trans
  \\ irule_at (Pos hd) Letrec_expand_1 \\ fs [MEM_MAP]
  \\ irule_at Any exp_eq_App_cong \\ fs [exp_eq_refl]
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,exp_of_def]
  \\ gvs [MEM_MAP,exp_of_def]
  \\ drule drop_common_suffix_thm
  \\ strip_tac
  \\ pop_assum kall_tac
  \\ gvs [MAP_MAP_o,combinTheory.o_DEF,exp_of_def]
  \\ ‘∀xs. MAP (λx. pure_exp$Var (explode x)) xs = MAP Var (MAP explode xs)’ by
       fs [MAP_MAP_o,combinTheory.o_DEF,exp_of_def] \\ fs []
  \\ irule_at Any exp_eq_trans
  \\ irule_at (Pos $ el 2) Letrec_contract_1
  \\ gvs [MEM_MAP,set_map_empty]
  \\ rewrite_tac [GSYM MAP_APPEND]
  \\ conj_tac >-
   (imp_res_tac specialise_each_subset
    \\ fs [SUBSET_DEF] \\ CCONTR_TAC \\ gvs [] \\ res_tac)
  \\ irule_at Any Lams_cong
  \\ full_simp_tac bool_ss [GSYM MAP_APPEND]
  \\ imp_res_tac no_shadowing_Lams
  \\ imp_res_tac no_shadowing_Lams_distinct
  \\ drule specialise_each_thm
  \\ impl_tac
  >-
   (first_x_assum $ irule_at Any \\ fs []
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
    \\ qsuff_tac ‘∀x. MEM (SOME x) guide ⇒ MEM x (outer_vs ++ zs)’ >- fs []
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
  \\ strip_tac \\ fs []
  \\ conj_tac >- fs [SUBSET_DEF]
  \\ conj_tac >-
   (fs [SUBSET_DEF]
    \\ imp_res_tac specialise_each_subset \\ fs [SUBSET_DEF]
    \\ fs [MEM_MAP] \\ metis_tac [])
  \\ conj_tac >- fs [SUBSET_DEF]
  \\ fs [Abbr‘c1’,exp_of_def,boundvars_Lams,set_MAP_explode]
  \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ conj_tac >- fs [SUBSET_DEF]
  \\ conj_tac >- fs [SUBSET_DEF]
  \\ fs [DIFF_SUBSET]
  \\ conj_tac
  >-
   (imp_res_tac specialise_each_subset \\ fs [SUBSET_DEF]
    \\ fs [MEM_MAP,PULL_EXISTS,SF DNF_ss]
    \\ rw [] \\ res_tac \\ fs []
    \\ gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
    \\ CCONTR_TAC \\ gvs []
    \\ gvs [ALL_DISTINCT_APPEND])
  \\ gvs [SUBSET_DEF]
  \\ imp_res_tac specialise_each_subset \\ fs [SUBSET_DEF]
  \\ fs [MEM_MAP,PULL_EXISTS,SF DNF_ss]
  \\ rw [] \\ res_tac \\ fs []
  \\ metis_tac []
QED

val _ = export_theory();
