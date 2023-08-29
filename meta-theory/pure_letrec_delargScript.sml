(*
   Prove that unused argument can be deleted
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_exp_relTheory
     pure_alpha_equivTheory pure_miscTheory pure_congruenceTheory;

val _ = new_theory "pure_letrec_delarg";

Datatype:
  info = <| fname : string      ;  (* function name *)
            args  : string list ;  (* arguments up to argument to delete *)
            arg   : string      ;  (* argument to delete *)
            w_arg : string      ;  (* argument to delete is this before deletion *)
            args' : string list ;  (* arguments after argument to delete *)
            rhs_T : exp         ;  (* without argument *)
            rhs_F : exp         |> (* with argument *)
End

Definition mk_apps_def:
  mk_apps b f xs v ys = Apps f (xs ++ (if b then [] else [v]) ++ ys)
End

Inductive call_with_arg:
[~Apps_Var:]
  (∀info xs ys xs1 ys1 R b1 b2.
    LENGTH xs = LENGTH info.args ∧
    LENGTH xs1 = LENGTH info.args' ∧
    LIST_REL (call_with_arg b1 b2 T info R) xs ys ∧
    LIST_REL (call_with_arg b1 b2 T info R) xs1 ys1 ⇒
    call_with_arg b1 b2 T info R (mk_apps b1 (Var info.fname) xs (Var info.w_arg) xs1)
                                 (mk_apps b2 (Var info.fname) ys (Var info.w_arg) ys1)) ∧
[~Apps_Const:]
  (∀info xs ys xs1 ys1 R c.
    LENGTH xs = LENGTH info.args ∧
    LENGTH xs1 = LENGTH info.args' ∧ closed c ∧
    LIST_REL (call_with_arg b1 b2 F info R) xs ys ∧
    LIST_REL (call_with_arg b1 b2 F info R) xs1 ys1 ⇒
    call_with_arg b1 b2 F info R (mk_apps b1 (Var info.fname) xs c xs1)
                                 (mk_apps b2 (Var info.fname) ys c ys1)) ∧
[~Var:]
  (∀info n b R.
    n ≠ info.arg ∧ n ≠ info.fname ⇒
    call_with_arg b1 b2 b info R (Var n) (Var n)) ∧
[~Lam:]
  (∀info n x y b R.
    call_with_arg b1 b2 b info R x y ∧
    info.arg ≠ n ∧ info.w_arg ≠ n ∧ info.fname ≠ n ⇒
    call_with_arg b1 b2 b info R (Lam n x) (Lam n y)) ∧
[~App:]
  (∀info f x g y  b R.
    call_with_arg b1 b2 b info R f g ∧
    call_with_arg b1 b2 b info R x y ⇒
    call_with_arg b1 b2 b info R (App f x) (App g y)) ∧
[~Prim:]
  (∀info n xs ys b R.
    LIST_REL (call_with_arg b1 b2 b info R) xs ys ⇒
    call_with_arg b1 b2 b info R (Prim n xs) (Prim n ys)) ∧
[~Letrec:]
  (∀info xs x ys y b R.
    LIST_REL (call_with_arg b1 b2 b info R) (MAP SND xs) (MAP SND ys) ∧
    DISJOINT {info.arg; info.fname; info.w_arg} (set (MAP FST xs)) ∧
    MAP FST xs = MAP FST ys ∧
    call_with_arg b1 b2 b info R x y ⇒
    call_with_arg b1 b2 b info R (Letrec xs x) (Letrec ys y)) ∧
[~closed:]
  (∀info b c1 c2 R.
    closed c1 ∧ closed c2 ∧ R c1 c2 ⇒
    call_with_arg b1 b2 b info R c1 c2)
End

Definition info_ok_def:
  info_ok i ⇔
    (i.args = [] ⇒ i.args' ≠ []) ∧
    i.arg ∉ freevars i.rhs_F ∧
    i.arg ∉ freevars i.rhs_T ∧
    ALL_DISTINCT (i.fname::i.arg::i.w_arg::i.args ++ i.args') ∧
    call_with_arg F T F i (=) i.rhs_F i.rhs_T
End

Definition mk_fun_def:
  mk_fun b i =
    Lams (i.args ++ (if b then [] else [i.arg]) ++ i.args')
      (if b then i.rhs_T else i.rhs_F)
End

Definition mk_letrec_def:
  mk_letrec b i x = Letrec [(i.fname,mk_fun b i)] x
End

Definition mk_rec_def:
  mk_rec b i = mk_letrec b i (mk_fun b i)
End

Theorem call_with_arg_mono[mono]:
  (∀x y. R1 x y ⇒ R2 x y) ⇒
  call_with_arg b1 b2 b i R1 x y ⇒
  call_with_arg b1 b2 b i R2 x y
Proof
  qsuff_tac ‘
    ∀b1 b2 b i R1 x y.
      call_with_arg b1 b2 b i R1 x y ⇒
      (∀x y. R1 x y ⇒ R2 x y) ⇒
      call_with_arg b1 b2 b i R2 x y’
  >- metis_tac []
  \\ ho_match_mp_tac call_with_arg_ind
  \\ rpt strip_tac
  \\ simp [Once call_with_arg_cases]
  \\ gvs [SF SFY_ss,SF ETA_ss]
  \\ metis_tac []
QED

Inductive letrec_delarg:
[~Switch:]
  (∀info x b1 b2.
    call_with_arg b1 b2 F info (letrec_delarg info) x y ∧
    info_ok info ∧
    freevars (mk_fun b1 info) ⊆ {info.fname} ∧
    freevars (mk_fun b2 info) ⊆ {info.fname} ∧
    letrec_delarg info x y ⇒
    letrec_delarg info (mk_letrec b1 info x)
                       (mk_letrec b2 info y)) ∧
[~Apps:]
  (∀info xs ys b1 b2 c.
    LENGTH xs = LENGTH info.args ∧
    LENGTH xs1 = LENGTH info.args' ∧ info_ok info ∧
    LIST_REL (letrec_delarg info) xs ys ∧
    LIST_REL (letrec_delarg info) xs1 ys1 ∧ closed c ∧
    closed (mk_rec b1 info) ∧
    closed (mk_rec b2 info) ⇒
    letrec_delarg info
      (mk_apps b1 (mk_rec b1 info) xs c xs1)
      (mk_apps b2 (mk_rec b2 info) ys c ys1)) ∧
[~Var:]
  (∀info n.
    letrec_delarg info (Var n) (Var n)) ∧
[~Lam:]
  (∀info n x y.
    letrec_delarg info x y ⇒
    letrec_delarg info (Lam n x) (Lam n y)) ∧
[~App:]
  (∀info f g x y.
    letrec_delarg info f g ∧ letrec_delarg info x y ⇒
    letrec_delarg info (App f x) (App g y)) ∧
[~Prim:]
  (∀info n xs ys.
    LIST_REL (letrec_delarg info) xs ys ⇒
    letrec_delarg info (Prim n xs) (Prim n ys)) ∧
[~Letrec:]
  (∀info  xs ys x y.
    LIST_REL (letrec_delarg info) (MAP SND xs) (MAP SND ys) ∧
    MAP FST xs = MAP FST ys ∧ letrec_delarg info x y ⇒
    letrec_delarg info (Letrec xs x) (Letrec ys y))
End

Theorem letrec_delarg_refl:
  ∀i x. letrec_delarg i x x
Proof
  gen_tac \\ ho_match_mp_tac freevars_ind
  \\ rw [] \\ simp [Once letrec_delarg_cases]
  \\ rpt disj2_tac
  >- (Induct_on ‘es’ \\ fs [])
  \\ Induct_on ‘lcs’ \\ fs [FORALL_PROD,SF DNF_ss]
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem call_with_arg_sym:
  ∀b1 b2 b i R x y.
    call_with_arg b1 b2 b i R x y ⇒ call_with_arg b2 b1 b i (λx y. R y x) y x
Proof
  ho_match_mp_tac call_with_arg_ind
  \\ rpt strip_tac
  \\ simp [Once call_with_arg_cases]
  \\ once_rewrite_tac [LIST_REL_SWAP] \\ fs []
  \\ disj1_tac
  \\ irule_at (Pos hd) EQ_REFL
  \\ irule_at (Pos hd) EQ_REFL
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs [] \\ pop_assum $ irule_at Any
QED

Triviality LIST_REL_ignore_first:
  ∀xs ys. LIST_REL (λx y. P x) xs ys ⇔ EVERY P xs ∧ LENGTH xs = LENGTH ys
Proof
  Induct \\ fs [PULL_EXISTS] \\ rw [] \\ eq_tac \\ rw [] \\ res_tac
  \\ gvs [] \\ Cases_on ‘ys’ \\ gvs []
QED

Theorem call_with_arg_dup:
  ∀b1 b2 b i R x y.
    call_with_arg b1 b2 b i R x y ⇒ call_with_arg b1 b1 b i $= x x
Proof
  ho_match_mp_tac call_with_arg_ind
  \\ rpt strip_tac
  \\ simp [Once call_with_arg_cases]
  \\ gvs [LIST_REL_ignore_first]
  \\ gvs [LIST_REL_same]
  \\ disj1_tac
  \\ gvs [LIST_REL_ignore_first]
  \\ irule_at (Pos hd) EQ_REFL
  \\ irule_at (Pos hd) EQ_REFL
  \\ imp_res_tac LIST_REL_LENGTH
  \\ gvs [LIST_REL_same]
QED

Theorem letrec_delarg_sym:
  letrec_delarg i x y ⇔ letrec_delarg i y x
Proof
  qsuff_tac ‘∀i x y. letrec_delarg i x y ⇒  letrec_delarg i y x’
  >- metis_tac []
  \\ ho_match_mp_tac letrec_delarg_ind
  \\ rw []
  \\ imp_res_tac LIST_REL_LENGTH
  >- (irule letrec_delarg_Switch \\ fs []
      \\ imp_res_tac call_with_arg_sym \\ gvs [SF ETA_ss])
  >- (irule letrec_delarg_Apps \\ fs []
      \\ simp [Once LIST_REL_SWAP]
      \\ simp [Once LIST_REL_SWAP])
  >- (irule letrec_delarg_Var \\ fs [])
  >- (irule letrec_delarg_Lam \\ fs [])
  >- (irule letrec_delarg_App \\ fs [])
  >- (irule letrec_delarg_Prim \\ fs [] \\ simp [Once LIST_REL_SWAP])
  >- (irule letrec_delarg_Letrec \\ fs [] \\ simp [Once LIST_REL_SWAP])
QED

Triviality mk_letrec_neq[simp]:
  mk_letrec b i x ≠ Lam v t ∧
  mk_letrec b i x ≠ App x1 x2 ∧
  mk_letrec b i x ≠ Prim p ps ∧
  ∀y. Lam v z ≠ Apps y (xs ++ [x]) ∧
      Letrec bs bb ≠ Apps y (xs ++ [x]) ∧
      Prim p ps ≠ Apps y (xs ++ [x])
Proof
  fs [mk_letrec_def]
  \\ Induct_on ‘xs’
  \\ fs [Apps_def]
QED

Triviality EVERY_FLOOKUP_closed_lemma:
  EVERY (λe. freevars e ⊆ set (MAP FST ys)) (MAP SND ys) ⇒
  (∀n v.
     FLOOKUP (FEMPTY |++ MAP (λ(g,x). (g,Letrec ys x)) ys) n = SOME v ⇒
     closed v)
Proof
  fs [alistTheory.flookup_fupdate_list,AllCaseEqs()]
  \\ rw [] \\ imp_res_tac ALOOKUP_MEM
  \\ gvs [MEM_MAP,EXISTS_PROD,EVERY_MEM,PULL_EXISTS]
  \\ res_tac \\ fs []
QED

Triviality LIST_REL_freevars_lemma_1:
  ∀xs ys.
    LIST_REL (λx y. freevars x = freevars y) xs ys ⇒
    MAP freevars xs = MAP freevars ys
Proof
  Induct \\ fs [PULL_EXISTS]
QED

Theorem call_with_arg_freevars:
  ∀b1 b2 b i R x y.
    call_with_arg b1 b2 b i R x y ⇒ ~b ⇒ freevars x = freevars y
Proof
  ho_match_mp_tac call_with_arg_ind
  \\ rpt strip_tac \\ gvs []
  \\ gvs [closed_def]
  \\ imp_res_tac LIST_REL_freevars_lemma_1 \\ gvs [mk_apps_def,SF ETA_ss]
  \\ rw [] \\ gvs []
  \\ gvs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD]
  \\ AP_THM_TAC
  \\ ntac 4 AP_TERM_TAC
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘ys’
  \\ qid_spec_tac ‘xs’
  \\ Induct \\ gvs [FORALL_PROD,MAP_EQ_CONS,PULL_EXISTS]
QED

Theorem free_vars_mk_fun_subset:
  info_ok i ⇒
  freevars (mk_fun b2 i) ⊆ freevars (mk_fun b1 i)
Proof
  strip_tac
  \\ fs [mk_fun_def,info_ok_def]
  \\ rpt IF_CASES_TAC \\ gvs []
  \\ DEP_REWRITE_TAC [freevars_subst]
  \\ fs [SUBSET_DEF]
  \\ fs [FRANGE_DEF]
  \\ gvs [SUBSET_DEF]
  \\ rpt strip_tac
  \\ CCONTR_TAC \\ gvs []
  \\ drule call_with_arg_freevars \\ gvs []
  \\ CCONTR_TAC \\ gvs []
QED

Theorem free_vars_mk_fun:
  info_ok i ⇒
  freevars (mk_fun b i) = freevars (mk_fun T i)
Proof
  strip_tac
  \\ imp_res_tac free_vars_mk_fun_subset
  \\ gvs [SUBSET_DEF,EXTENSION]
  \\ metis_tac []
QED

Triviality LIST_REL_freevars_lemma:
  ∀xs ys.
    LIST_REL (λx y. letrec_delarg i x y ∧ freevars x = freevars y) xs ys ⇒
    MAP freevars xs = MAP freevars ys
Proof
  Induct \\ fs [PULL_EXISTS]
QED

Theorem letrec_delarg_freevars:
  ∀i x y. letrec_delarg i x y ⇒ freevars x = freevars y
Proof
  Induct_on ‘letrec_delarg’ \\ rw [] \\ gvs []
  >- (fs [mk_letrec_def,mk_rec_def] \\ metis_tac [free_vars_mk_fun])
  >- (gvs [mk_apps_def,closed_def]
      \\ imp_res_tac LIST_REL_freevars_lemma \\ gvs []
      \\ rw [] \\ gvs [])
  >- (imp_res_tac LIST_REL_freevars_lemma \\ gvs [SF ETA_ss])
  \\ last_x_assum mp_tac
  \\ qid_spec_tac ‘xs’
  \\ qid_spec_tac ‘ys’
  \\ Induct \\ fs []
  \\ fs [PULL_EXISTS]
  \\ strip_tac \\ Cases \\ fs []
  \\ strip_tac \\ res_tac \\ fs [UNCURRY]
  \\ gvs [EXTENSION]
  \\ metis_tac []
QED

Theorem subst_mk_apps:
  subst m1 (mk_apps b1 f xs c xs1) =
  mk_apps b1 (subst m1 f) (MAP (subst m1) xs) (subst m1 c) (MAP (subst m1) xs1)
Proof
  fs [mk_apps_def,subst_Apps] \\ rw [] \\ fs []
QED

Theorem closed_mk_apps:
  closed (mk_apps b1 f xs c xs1) ⇔
  EVERY closed xs ∧ EVERY closed xs1 ∧ closed f ∧ (~b1 ⇒ closed c)
Proof
  fs [mk_apps_def] \\ rw [] \\ fs [] \\ eq_tac \\ gvs []
QED

Theorem subst_call_with_arg:
  ∀b1 b2 b i R x y.
    call_with_arg b1 b2 b i R x y ⇒
    ∀m1 m2.
      R = letrec_delarg i ∧ ~b ∧
      FDOM m1 = FDOM m2 ∧
      i.fname ∉ FDOM m2 ∧
      (∀k. k ∈ FDOM m2 ⇒
           letrec_delarg i (m1 ' k) (m2 ' k) ∧ closed (m1 ' k) ∧
           closed (m2 ' k)) ⇒
      call_with_arg b1 b2 F i (letrec_delarg i) (subst m1 x) (subst m2 y)
Proof
  ho_match_mp_tac call_with_arg_ind
  \\ rpt strip_tac \\ gvs []
  >-
   (fs [subst_Apps]
    \\ fs [subst_def,FLOOKUP_DEF,subst_mk_apps]
    \\ irule call_with_arg_Apps_Const \\ fs []
    \\ rw []
    \\ simp [LIST_REL_MAP]
    \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
    \\ rw [] \\ gvs [SF SFY_ss])
  >-
   (fs [subst_def,FLOOKUP_DEF]
    \\ IF_CASES_TAC \\ fs []
    >- (irule call_with_arg_closed \\ res_tac \\ fs [])
    \\ irule call_with_arg_Var \\ fs [])
  >-
   (fs [subst_def] \\ irule call_with_arg_Lam \\ fs []
    \\ last_x_assum irule
    \\ gvs [FDOM_DOMSUB,DOMSUB_FAPPLY_THM])
  >-
   (fs [subst_def] \\ irule call_with_arg_App \\ fs [])
  >-
   (fs [subst_def] \\ irule call_with_arg_Prim \\ fs [LIST_REL_MAP]
    \\ last_x_assum mp_tac
    \\ match_mp_tac LIST_REL_mono \\ fs [])
  >-
   (fs [subst_def] \\ irule call_with_arg_Letrec \\ fs [LIST_REL_MAP]
    \\ gvs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_INTRO]
    \\ reverse conj_tac
    >-
     (first_x_assum $ irule
      \\ gvs [FDIFF_def,DRESTRICT_DEF])
    \\ last_x_assum mp_tac
    \\ match_mp_tac LIST_REL_mono
    \\ gvs [FORALL_PROD]
    \\ rw []
    \\ first_x_assum $ irule
    \\ gvs [FDIFF_def,DRESTRICT_DEF])
  \\ irule call_with_arg_closed \\ fs []
QED

Theorem boundvars_Apps:
  ∀es e. boundvars (Apps e es) = boundvars e ∪ BIGUNION (set (MAP boundvars es))
Proof
  Induct \\ fs [Apps_def, AC UNION_COMM UNION_ASSOC]
QED

Theorem subst_call_with_arg_F_F:
  ∀b1 b2 b i R x y.
    call_with_arg b1 b2 b i R x y ⇒
    ∀m1 m2.
      R = letrec_delarg i ∧ ~b ∧
      i.fname ∉ FDOM m1 ∧
      (∀k. k ≠ i.arg ⇒ (k ∈ FDOM m1 <=> k ∈ FDOM m2)) ∧
      info_ok i ∧
      (∀k. k ∈ FDOM m2 ∧ k ≠ i.arg ⇒
           letrec_delarg i (m1 ' k) (m2 ' k) ∧ closed (m1 ' k) ∧
           closed (m2 ' k)) ⇒
      call_with_arg b1 b2 F i (letrec_delarg i) (subst m1 x) (subst m2 y)
Proof
  ho_match_mp_tac call_with_arg_ind
  \\ rpt strip_tac \\ gvs []
  >-
   (fs [subst_Apps]
    \\ ‘i.fname ∉ FDOM m2’ by (fs [info_ok_def] \\ metis_tac [])
    \\ fs [subst_def,FLOOKUP_DEF,subst_mk_apps]
    \\ irule call_with_arg_Apps_Const \\ fs [info_ok_def]
    \\ simp [LIST_REL_MAP] \\ rw []
    \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
    \\ rw [] \\ gvs [SF SFY_ss]
    \\ first_x_assum $ irule \\ fs [boundvars_Apps,MEM_MAP]
    \\ metis_tac [])
  >-
   (fs [subst_def,FLOOKUP_DEF]
    \\ ‘n ∈ FDOM m1 <=> n ∈ FDOM m2’ by (fs [EXTENSION] \\ metis_tac [])
    \\ IF_CASES_TAC \\ fs []
    >- (irule call_with_arg_closed \\ res_tac \\ fs [])
    \\ irule call_with_arg_Var \\ fs [])
  >-
   (fs [subst_def] \\ irule call_with_arg_Lam \\ fs []
    \\ last_x_assum irule
    \\ gvs [FDOM_DOMSUB,DOMSUB_FAPPLY_THM,FLOOKUP_DEF]
    \\ gvs [EXTENSION] \\ metis_tac [])
  >-
   (fs [subst_def] \\ irule call_with_arg_App \\ fs [])
  >-
   (fs [subst_def] \\ irule call_with_arg_Prim \\ fs [LIST_REL_MAP]
    \\ last_x_assum mp_tac
    \\ match_mp_tac LIST_REL_mono \\ fs [] \\ rw []
    \\ first_x_assum $ irule \\ fs [boundvars_Apps,MEM_MAP]
    \\ metis_tac [])
  >-
   (fs [subst_def] \\ irule call_with_arg_Letrec \\ fs [LIST_REL_MAP]
    \\ gvs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_INTRO]
    \\ reverse conj_tac
    >-
     (first_x_assum $ irule
      \\ gvs [FDIFF_def,DRESTRICT_DEF,FLOOKUP_DEF])
    \\ last_x_assum mp_tac
    \\ match_mp_tac LIST_REL_mono
    \\ gvs [FORALL_PROD]
    \\ rw []
    \\ first_x_assum $ irule
    \\ gvs [FDIFF_def,DRESTRICT_DEF,FLOOKUP_DEF])
  \\ irule call_with_arg_closed \\ fs []
QED

Theorem subst_letrec_delarg:
  ∀i x y m1 m2.
    letrec_delarg i x y ∧
    FDOM m1 = FDOM m2 ∧
    (∀k v1 v2.
      FLOOKUP m1 k = SOME v1 ∧ FLOOKUP m2 k = SOME v2 ⇒
      letrec_delarg i v1 v2 ∧ closed v1 ∧ closed v2) ⇒
    letrec_delarg i (subst m1 x) (subst m2 y)
Proof
  Induct_on ‘letrec_delarg’ \\ rw []
  >-
   (fs [mk_letrec_def,subst_def]
    \\ ‘subst (FDIFF m1 {i.fname}) (mk_fun b1 i) = mk_fun b1 i ∧
        subst (FDIFF m2 {i.fname}) (mk_fun b2 i) = mk_fun b2 i’ by
      (rw [] \\ irule subst_ignore
       \\ fs [IN_DISJOINT,SUBSET_DEF] \\ metis_tac [])
    \\ fs [GSYM mk_letrec_def]
    \\ irule letrec_delarg_Switch
    \\ last_x_assum $ irule_at Any
    \\ fs [FDIFF_def,DRESTRICT_DEF,FLOOKUP_DEF]
    \\ drule_at (Pos last) call_with_arg_mono
    \\ disch_then $ qspec_then ‘letrec_delarg i’ mp_tac \\ fs []
    \\ gvs [GSYM FDIFF_def] \\ strip_tac
    \\ irule subst_call_with_arg \\ gvs []
    \\ gvs [FDIFF_def,DRESTRICT_DEF])
  >-
   (fs [subst_Apps,info_ok_def,subst_mk_apps]
    \\ irule letrec_delarg_Apps \\ fs []
    \\ fs [info_ok_def,LIST_REL_MAP] \\ rw []
    \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
    \\ gvs [SF SFY_ss])
  >-
   (fs [subst_def] \\ rpt CASE_TAC \\ fs [letrec_delarg_refl]
    \\ res_tac \\ fs [] \\ gvs [FLOOKUP_DEF])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_delarg_cases] \\ disj2_tac
    \\ last_x_assum irule \\ fs []
    \\ fs [DOMSUB_FLOOKUP_THM,AllCaseEqs()]
    \\ rw [] \\ res_tac \\ fs [SUBSET_DEF])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_delarg_cases]
    \\ disj2_tac
    \\ rpt $ last_x_assum $ irule_at Any \\ fs [])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_delarg_cases,SF ETA_ss] \\ disj2_tac
    \\ last_x_assum mp_tac \\ fs []
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    \\ rw [] \\ metis_tac [])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_delarg_cases] \\ disj2_tac \\ disj2_tac
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
    \\ reverse conj_tac
    >-
     (last_x_assum irule
      \\ fs [FDOM_FDIFF,EXTENSION,FLOOKUP_FDIFF,SUBSET_DEF]
      \\ rw [] \\ res_tac \\ fs [])
    \\ last_x_assum mp_tac
    \\ last_x_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘m2’
    \\ qid_spec_tac ‘m1’
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    \\ strip_tac \\ Cases \\ fs []
    \\ rw []
    >-
     (first_x_assum irule
      \\ fs [FDOM_FDIFF,EXTENSION,FLOOKUP_FDIFF,SUBSET_DEF]
      \\ rw [] \\ res_tac \\ fs [])
    \\ rewrite_tac [GSYM finite_mapTheory.FDIFF_FDOMSUB_INSERT]
    \\ first_x_assum irule
    \\ fs [FDOM_FDIFF,EXTENSION,FLOOKUP_FDIFF]
    \\ fs [DOMSUB_FLOOKUP_THM,AllCaseEqs(),SUBSET_DEF]
    \\ rw [] \\ res_tac \\ fs [])
QED

Theorem letrec_delarg_subst1:
  letrec_delarg i a1 a2 ∧ letrec_delarg i z y ∧ closed a1 ∧ closed a2 ⇒
  letrec_delarg i (subst1 v a1 z) (subst1 v a2 y)
Proof
  strip_tac
  \\ irule subst_letrec_delarg
  \\ fs [FLOOKUP_DEF]
QED

Triviality eval_wh_Constructor_NIL_bisim =
  eval_wh_Constructor_bisim |> Q.GEN ‘xs’ |> Q.SPEC ‘[]’ |> SIMP_RULE (srw_ss()) [];

Theorem closed_mk_rec:
  info_ok i ∧ closed (mk_rec b1 i) ⇒ closed (mk_rec b2 i)
Proof
  Cases_on ‘b1 = b2’ >- fs []
  \\ Cases_on ‘b1’ \\ gvs []
  \\ fs [mk_rec_def,mk_fun_def,mk_letrec_def,info_ok_def] \\ rw []
  \\ drule call_with_arg_freevars
  \\ gvs [SUBSET_DEF] \\ rw []
  \\ metis_tac []
QED

Triviality LIST_REL_letrec_delarg_closed:
  ∀xs ys. LIST_REL (letrec_delarg i) xs ys ∧ EVERY closed xs ⇒ EVERY closed ys
Proof
  Induct \\ rw [] \\ fs []
  \\ imp_res_tac letrec_delarg_freevars \\ fs [closed_def]
QED

Theorem ALOOKUP_REVERSE_LIST_REL:
  ∀bs ys.
    LIST_REL p (MAP SND bs) (MAP SND ys) ∧
    MAP FST ys = MAP FST bs ∧
    ALOOKUP (REVERSE (MAP (λ(g,x). (g,f x)) bs)) k' = SOME v1 ∧
    ALOOKUP (REVERSE (MAP (λ(g,x). (g,h x)) ys)) k' = SOME v2 ⇒
    ∃x y. p x y ∧ v1 = f x ∧ v2 = h y ∧ MEM x (MAP SND bs) ∧ MEM y (MAP SND ys)
Proof
  Induct using SNOC_INDUCT \\ fs [PULL_EXISTS]
  \\ Cases \\ Cases using SNOC_CASES
  \\ gvs [GSYM REVERSE_APPEND,MAP_SNOC,LIST_REL_SNOC,REVERSE_SNOC]
  \\ rename [‘SND hh’] \\ PairCases_on ‘hh’ \\ fs []
  \\ fs [AllCaseEqs()]
  \\ rpt strip_tac \\ gvs []
  \\ metis_tac []
QED

Theorem closed_mk_rec:
  info_ok i ∧ freevars (mk_fun b1 i) ⊆ {i.fname} ⇒
  closed (mk_rec b1 i)
Proof
  gvs [closed_def,mk_rec_def,mk_letrec_def,mk_fun_def,info_ok_def]
  \\ gvs [EXTENSION,SUBSET_DEF] \\ metis_tac []
QED

Theorem closed_mk_rec_copy:
  info_ok i ∧ closed (mk_rec b1 i) ⇒ closed (mk_rec b2 i)
Proof
  Cases_on ‘b1 = b2’ >- fs []
  \\ Cases_on ‘b1’ \\ gvs []
  \\ fs [mk_rec_def,mk_fun_def,mk_letrec_def,info_ok_def] \\ rw []
  \\ drule call_with_arg_freevars
  \\ gvs [SUBSET_DEF] \\ rw []
  \\ metis_tac []
QED

Theorem call_with_arg_imp_letrec_delarg:
  call_with_arg b1 b2 F i (letrec_delarg i) x y ∧
  info_ok i ∧
  freevars (mk_fun b1 i) ⊆ {i.fname} ∧
  freevars (mk_fun b2 i) ⊆ {i.fname} ⇒
  letrec_delarg i (subst1 i.fname (mk_rec b1 i) x)
                  (subst1 i.fname (mk_rec b2 i) y)
Proof
  qsuff_tac ‘∀b1 b2 b i x.
    call_with_arg b1 b2 b i (letrec_delarg i) x y ∧ info_ok i ∧ ~b ∧
    freevars (mk_fun b1 i) ⊆ {i.fname} ∧
    freevars (mk_fun b2 i) ⊆ {i.fname} ⇒
    letrec_delarg i (subst1 i.fname (mk_rec b1 i) x)
                    (subst1 i.fname (mk_rec b2 i) y)’
  >- metis_tac []
  \\ Induct_on ‘call_with_arg’
  \\ rpt strip_tac \\ gvs []
  >-
   (imp_res_tac closed_mk_rec
    \\ fs [subst_Apps,subst1_def,info_ok_def,subst_mk_apps]
    \\ irule letrec_delarg_Apps \\ fs [] \\ fs [info_ok_def]
    \\ gvs [LIST_REL_MAP] \\ rw []
    \\ first_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
    \\ fs [])
  >- (gvs [subst1_def] \\ simp [Once letrec_delarg_cases])
  >- (gvs [subst1_def] \\ simp [Once letrec_delarg_cases])
  >- (gvs [subst1_def] \\ simp [Once letrec_delarg_cases])
  >- (gvs [subst1_def] \\ irule letrec_delarg_Prim
      \\ last_x_assum mp_tac
      \\ qid_spec_tac ‘ys’
      \\ qid_spec_tac ‘xs’
      \\ Induct \\ fs [PULL_EXISTS])
  >-
   (gvs [subst1_def] \\ irule letrec_delarg_Letrec
    \\ fs [MAP_MAP_o,combinTheory.o_DEF]
    \\ fs [LAMBDA_PROD]
    \\ rpt $ pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ gvs [FORALL_PROD,PULL_EXISTS,MAP_EQ_CONS])
QED

Definition wh_Closures_def:
  wh_Closures (v::vs) e = wh_Closure v (Lams vs e)
End

Triviality eval_wh_to_Apps_div:
  ∀xs x k.
    eval_wh_to k x = wh_Diverge ⇒
    eval_wh_to k (Apps x xs) = wh_Diverge
Proof
  Induct \\ fs [Apps_def] \\ rw []
  \\ last_x_assum irule \\ fs [eval_wh_to_def]
QED

Definition mk_body_def:
  mk_body b i =
    subst1 i.fname (mk_rec b i) (if b then i.rhs_T else i.rhs_F)
End

Triviality ignore_FDIFF:
  DISJOINT (FDOM f) m ⇒ FDIFF f m = f
Proof
  fs [fmap_EXT,FDIFF_def,DRESTRICT_DEF]
  \\ fs [IN_DISJOINT,EXTENSION]
  \\ metis_tac []
QED

Theorem eval_wh_to_mk_rec:
  eval_wh_to k (mk_rec b i) ≠ wh_Diverge ∧ info_ok i ∧
  freevars (mk_fun b i) ⊆ {i.fname} ⇒
  0 < k ∧
  ∀l.
    0 < l ⇒
    eval_wh_to l (mk_rec b i) =
    wh_Closures (i.args ++ (if b then [] else [i.arg]) ++ i.args') (mk_body b i)
Proof
  fs [mk_rec_def,mk_letrec_def,eval_wh_to_def,AllCaseEqs()]
  \\ strip_tac \\ gvs []
  \\ fs [mk_fun_def]
  \\ fs [subst_funs_def,bind_def,FUPDATE_LIST,FLOOKUP_UPDATE]
  \\ fs [subst_Lams]
  \\ fs [GSYM mk_fun_def,GSYM mk_rec_def,GSYM mk_letrec_def]
  \\ DEP_REWRITE_TAC [ignore_FDIFF]
  \\ fs [mk_body_def]
  \\ Cases_on ‘i.args ++ (if b then [] else [i.arg]) ++ i.args'’ \\ fs []
  \\ fs [Lams_def,eval_wh_Lam,eval_wh_to_def,wh_Closures_def]
  \\ gvs [info_ok_def] \\ rw []
QED

Theorem eval_wh_mk_rec:
  info_ok i ∧
  freevars (mk_fun b i) ⊆ {i.fname} ⇒
  eval_wh (mk_rec b i) =
  wh_Closures (i.args ++ (if b then [] else [i.arg]) ++ i.args') (mk_body b i)
Proof
  fs [mk_rec_def,mk_letrec_def,eval_wh_Letrec,AllCaseEqs()]
  \\ strip_tac \\ gvs []
  \\ fs [mk_fun_def]
  \\ fs [subst_funs_def,bind_def,FUPDATE_LIST,FLOOKUP_UPDATE]
  \\ fs [subst_Lams]
  \\ fs [GSYM mk_fun_def,GSYM mk_rec_def,GSYM mk_letrec_def]
  \\ DEP_REWRITE_TAC [ignore_FDIFF]
  \\ fs [mk_body_def,info_ok_def]
  \\ Cases_on ‘i.args ++ (if b then [] else [i.arg]) ++ i.args'’ \\ fs []
  \\ fs [Lams_def,eval_wh_Lam,wh_Closures_def]
  \\ rw []
QED

Theorem eval_wh_to_Apps:
  ∀xs vs x k e.
    (∀l. 0 < l ⇒ eval_wh_to l x = wh_Closures vs e) ∧
    LENGTH vs = LENGTH xs ∧ xs ≠ [] ∧ 0 < k ∧
    EVERY closed xs ∧ ALL_DISTINCT vs ⇒
    eval_wh_to k (Apps x xs) =
    eval_wh_to (k-1) (subst (FEMPTY |++ (ZIP(vs,xs))) e)
Proof
  Induct \\ fs [Apps_def] \\ rw []
  \\ Cases_on ‘xs’ \\ gvs [Apps_def]
  >- (gvs [LENGTH_EQ_NUM_compute,FUPDATE_LIST,eval_wh_to_def,wh_Closures_def,Lams_def]
      \\ rw [bind_def] \\ gvs [FLOOKUP_UPDATE])
  \\ Cases_on ‘vs’ \\ gvs [FUPDATE_LIST]
  \\ rename [‘ALL_DISTINCT ts’]
  \\ last_x_assum $ qspecl_then [‘ts’,‘App x h’,‘k’] mp_tac \\ fs []
  \\ fs [wh_Closures_def,ADD_CLAUSES]
  \\ rename [‘wh_Closure v (Lams args e)’]
  \\ disch_then $ qspec_then ‘subst1 v h e’ mp_tac
  \\ impl_tac
  >-
   (simp [eval_wh_to_def,bind_def,FLOOKUP_UPDATE,subst_Lams]
    \\ Cases_on ‘args’ \\ fs [Lams_def,eval_wh_to_def,wh_Closures_def]
    \\ qsuff_tac ‘FDIFF (FEMPTY |+ (v,h)) (h'' INSERT set t') = FEMPTY |+ (v,h)’
    >- fs [] \\ gvs [fmap_EXT,FDIFF_def])
  \\ strip_tac \\ fs []
  \\ DEP_REWRITE_TAC [subst_subst_FUNION]
  \\ gvs [FRANGE_DEF]
  \\ AP_TERM_TAC
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ gvs [fmap_EXT]
  \\ gvs [FDOM_FUPDATE_LIST,GSYM FUPDATE_LIST,FUNION_DEF]
  \\ strip_tac \\ rw [] \\ gvs []
  >-
   (DEP_REWRITE_TAC [FUPDATE_LIST_APPLY_NOT_MEM]
    \\ gvs [FAPPLY_FUPDATE_THM]
    \\ DEP_REWRITE_TAC [MAP_FST_ZIP]
    \\ fs [])
  \\ irule FUPDATE_SAME_LIST_APPLY \\ fs []
QED

Theorem eval_wh_to_Apps_other:
  ∀xs vs x e.
    eval_wh x = wh_Closures vs e ∧
    LENGTH vs = LENGTH xs ∧ xs ≠ [] ∧
    EVERY closed xs ∧ ALL_DISTINCT vs ⇒
    eval_wh (Apps x xs) =
    eval_wh (subst (FEMPTY |++ (ZIP(vs,xs))) e)
Proof
  Induct \\ fs [Apps_def] \\ rw []
  \\ Cases_on ‘xs’ \\ gvs [Apps_def]
  >- (gvs [LENGTH_EQ_NUM_compute,FUPDATE_LIST,eval_wh_App,wh_Closures_def,Lams_def]
      \\ rw [bind_def] \\ gvs [FLOOKUP_UPDATE])
  \\ Cases_on ‘vs’ \\ gvs [FUPDATE_LIST]
  \\ rename [‘ALL_DISTINCT ts’]
  \\ last_x_assum $ qspecl_then [‘ts’,‘App x h’] mp_tac \\ fs []
  \\ fs [wh_Closures_def,ADD_CLAUSES]
  \\ rename [‘wh_Closure v (Lams args e)’]
  \\ disch_then $ qspec_then ‘subst1 v h e’ mp_tac
  \\ impl_tac
  >-
   (simp [eval_wh_App,bind_def,FLOOKUP_UPDATE,subst_Lams]
    \\ Cases_on ‘args’ \\ fs [Lams_def,eval_wh_Lam,wh_Closures_def]
    \\ qsuff_tac ‘FDIFF (FEMPTY |+ (v,h)) (h'' INSERT set t') = FEMPTY |+ (v,h)’
    >- fs [] \\ gvs [fmap_EXT,FDIFF_def])
  \\ strip_tac \\ fs []
  \\ DEP_REWRITE_TAC [subst_subst_FUNION]
  \\ gvs [FRANGE_DEF]
  \\ AP_TERM_TAC
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ gvs [fmap_EXT]
  \\ gvs [FDOM_FUPDATE_LIST,GSYM FUPDATE_LIST,FUNION_DEF]
  \\ strip_tac \\ rw [] \\ gvs []
  >-
   (DEP_REWRITE_TAC [FUPDATE_LIST_APPLY_NOT_MEM]
    \\ gvs [FAPPLY_FUPDATE_THM]
    \\ DEP_REWRITE_TAC [MAP_FST_ZIP]
    \\ fs [])
  \\ irule FUPDATE_SAME_LIST_APPLY \\ fs []
QED

Theorem subst_simp:
  LENGTH vs = LENGTH xs ∧ ~MEM v vs ∧ closed c ⇒
  subst (FEMPTY |++ ZIP (vs ++ [v],xs ++ [c])) (if b1 then subst1 v c x else x) =
  subst (FEMPTY |++ ZIP (vs ++ [v],xs ++ [c])) x
Proof
  rw []
  \\ DEP_REWRITE_TAC [subst_subst_FUNION]
  \\ gvs [FRANGE_DEF]
  \\ DEP_REWRITE_TAC [GSYM ZIP_APPEND] \\ fs []
  \\ fs [FUPDATE_LIST,FOLDL_APPEND]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ gvs [fmap_EXT,FUNION_DEF]
  \\ rw [] \\ fs [EXTENSION]
  \\ metis_tac []
QED

Theorem freecars_mk_body:
  closed (mk_rec b1 i) ⇒
  freevars (mk_body b1 i) ⊆ set i.args ∪ {i.arg} ∪ set i.args'
Proof
  rw [mk_body_def]
  \\ DEP_REWRITE_TAC [freevars_subst]
  \\ gvs [FRANGE_FUPDATE,closed_def,mk_rec_def,mk_letrec_def,mk_fun_def]
  \\ last_x_assum mp_tac
  \\ DEP_REWRITE_TAC [freevars_subst]
  \\ gvs [FRANGE_FUPDATE,closed_def,mk_rec_def,mk_letrec_def,mk_fun_def]
  \\ gvs [EXTENSION,SUBSET_DEF]
  \\ metis_tac []
QED

Theorem freecars_mk_body_alt:
  closed (mk_rec b1 i) ⇒
  freevars (mk_body b1 i) ⊆
  if b1 then set i.args ∪ set i.args' else set i.args ∪ {i.arg} ∪ set i.args'
Proof
  rw [mk_body_def]
  \\ DEP_REWRITE_TAC [freevars_subst]
  \\ gvs [FRANGE_FUPDATE,closed_def,mk_rec_def,mk_letrec_def,mk_fun_def]
  \\ last_x_assum mp_tac
  \\ DEP_REWRITE_TAC [freevars_subst]
  \\ gvs [FRANGE_FUPDATE,closed_def,mk_rec_def,mk_letrec_def,mk_fun_def]
  \\ gvs [EXTENSION,SUBSET_DEF]
  \\ metis_tac []
QED

Theorem FRANGE_FUPDATE_LIST_ZIP_IMP:
  ∀xs ys v m.
    v ∈ FRANGE (m |++ ZIP (xs,ys)) ⇒
    v ∈ FRANGE m ∨ MEM v ys
Proof
  Induct \\ fs [ZIP_def,FUPDATE_LIST]
  \\ Cases_on ‘ys’ \\ fs [ZIP_def,FUPDATE_LIST]
  \\ rw [] \\ res_tac \\ asm_rewrite_tac []
  \\ CCONTR_TAC \\ gvs []
  \\ gvs [FRANGE_DEF,DOMSUB_FAPPLY_THM,AllCaseEqs()]
QED

Theorem LIST_REL_letrec_delarg_closed:
  ∀xs ys. LIST_REL (letrec_delarg i) xs ys ∧ EVERY closed xs ⇒ EVERY closed ys
Proof
  Induct \\ fs [PULL_EXISTS] \\ rw []
  \\ imp_res_tac letrec_delarg_freevars
  \\ fs [closed_def]
QED

Theorem call_with_arg_gen:
  call_with_arg F T F i $= i.rhs_F i.rhs_T ⇒
  call_with_arg b1 b2 F i $= (if b1 then i.rhs_T else i.rhs_F)
                             (if b2 then i.rhs_T else i.rhs_F)
Proof
  Cases_on ‘b1 ≠ b2’ \\ fs []
  >-
   (Cases_on ‘b1’ \\ gvs [] \\ strip_tac
    \\ drule call_with_arg_sym
    \\ simp [Once EQ_SYM_EQ, SF ETA_ss])
  \\ Cases_on ‘b1’ \\ gvs [] \\ rw []
  \\ drule call_with_arg_sym
  \\ simp [Once EQ_SYM_EQ, SF ETA_ss] \\ rw []
  \\ imp_res_tac call_with_arg_dup \\ fs []
QED

Triviality lemma1:
  LENGTH xs2 = LENGTH xs1 ∧ ~MEM k xs1 ⇒
  ALOOKUP (REVERSE (ZIP (xs1,xs2))) k = NONE
Proof
  fs [ALOOKUP_NONE,MAP_REVERSE,MAP_FST_ZIP]
QED

Triviality lemma2:
  ∀xs1 ys1 vs k'.
    LENGTH xs1 = LENGTH vs ∧
    EVERY closed xs1 ∧ MEM k' vs ∧
    LIST_REL (letrec_delarg i) xs1 ys1
    ⇒
    ∃x y.
      ALOOKUP (REVERSE (ZIP (vs,xs1))) k' = SOME x ∧
      ALOOKUP (REVERSE (ZIP (vs,ys1))) k' = SOME y ∧
      letrec_delarg i x y ∧ closed x ∧ closed y
Proof
  Induct using SNOC_INDUCT
  \\ Cases_on ‘vs’ using SNOC_CASES
  \\ Cases_on ‘ys1’ using SNOC_CASES
  \\ gvs [] \\ rw []
  \\ gvs [SNOC_APPEND]
  \\ DEP_REWRITE_TAC [GSYM ZIP_APPEND]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs [REVERSE_APPEND]
  \\ imp_res_tac letrec_delarg_freevars
  \\ rw []
  \\ fs [closed_def]
QED

Theorem Apps_rec_lemma:
  eval_wh_to k (mk_apps b1 (mk_rec b1 i) xs c xs1) ≠ wh_Diverge ∧
  LENGTH xs = LENGTH i.args ∧
  LENGTH xs1 = LENGTH i.args' ∧ info_ok i ∧
  closed (mk_rec b1 i) ∧
  closed (mk_rec b2 i) ∧
  EVERY closed xs ∧ EVERY closed xs1 ∧ closed c ∧
  LIST_REL (letrec_delarg i) xs ys ∧
  LIST_REL (letrec_delarg i) xs1 ys1 ⇒
  ∃k1 x1 y1.
    eval_wh_to k (mk_apps b1 (mk_rec b1 i) xs c xs1) = eval_wh_to k1 x1 ∧
    eval_wh (mk_apps b2 (mk_rec b2 i) ys c ys1) = eval_wh y1 ∧
    closed x1 ∧
    letrec_delarg i x1 y1 ∧
    k1 < k
Proof
  rw []
  \\ Cases_on ‘eval_wh_to k (mk_rec b1 i) = wh_Diverge’
  >- (fs [mk_apps_def] \\ drule eval_wh_to_Apps_div \\ strip_tac \\ fs [])
  \\ ‘freevars (mk_fun b1 i) ⊆ {i.fname} ∧
      freevars (mk_fun b2 i) ⊆ {i.fname}’ by
        fs [closed_def,mk_rec_def,mk_letrec_def,SUBSET_DIFF_EMPTY]
  \\ drule_all eval_wh_to_mk_rec \\ strip_tac
  \\ drule eval_wh_to_Apps
  \\ simp [mk_apps_def]
  \\ disch_then $ qspecl_then [‘xs ++ (if b1 then [] else [c]) ++ xs1’,‘k’] mp_tac
  \\ impl_tac
  >- (fs [info_ok_def,ALL_DISTINCT_APPEND]
      \\ rw [] \\ gvs [] \\ CCONTR_TAC \\ gvs [])
  \\ strip_tac \\ gvs []
  \\ irule_at (Pos hd) EQ_REFL
  \\ qexists_tac
     ‘(subst (FEMPTY |++ ZIP (i.args ++ (if b2 then [] else [i.arg]) ++ i.args',
                              ys ++ (if b2 then [] else [c]) ++ ys1)) (mk_body b2 i))’
  \\ gvs [SF SFY_ss]
  \\ conj_tac >-
   (irule eval_wh_to_Apps_other
    \\ irule_at Any eval_wh_mk_rec \\ fs []
    \\ imp_res_tac LIST_REL_letrec_delarg_closed \\ fs []
    \\ imp_res_tac LIST_REL_LENGTH
    \\ fs [info_ok_def,ALL_DISTINCT_APPEND]
    \\ rw [] \\ gvs []
    \\ CCONTR_TAC \\ gvs [])
  \\ conj_tac >-
   (irule IMP_closed_subst
    \\ conj_tac >-
     (rw []
      \\ drule $ REWRITE_RULE [SUBSET_DEF] FRANGE_FUPDATE_LIST_SUBSET
      \\ fs []
      \\ DEP_REWRITE_TAC [MAP_SND_ZIP] \\ fs [EVERY_MEM,info_ok_def]
      \\ rw [] \\ res_tac \\ fs [])
    \\ irule SUBSET_TRANS
    \\ irule_at Any freecars_mk_body_alt \\ fs []
    \\ gvs [FDOM_FUPDATE_LIST]
    \\ DEP_REWRITE_TAC [MAP_FST_ZIP]
    \\ gvs [SUBSET_DEF]
    \\ rw [] \\ fs [SUBSET_DEF])
  \\ fs [mk_body_def]
  \\ DEP_ONCE_REWRITE_TAC [subst_subst]
  \\ conj_tac >-
   (fs [FRANGE_FUPDATE,FDOM_FUPDATE_LIST]
    \\ DEP_REWRITE_TAC [MAP_FST_ZIP] \\ fs [info_ok_def]
    \\ rw [] \\ imp_res_tac FRANGE_FUPDATE_LIST_ZIP_IMP \\ fs []
    \\ fs [EVERY_MEM] \\ res_tac \\ fs [])
  \\ qpat_abbrev_tac ‘pp = subst1 _ _ (subst _ _)’
  \\ DEP_ONCE_REWRITE_TAC [subst_subst]
  \\ unabbrev_all_tac
  \\ conj_tac >-
   (fs [FRANGE_FUPDATE,FDOM_FUPDATE_LIST]
    \\ DEP_REWRITE_TAC [MAP_FST_ZIP] \\ fs [info_ok_def]
    \\ imp_res_tac LIST_REL_LENGTH
    \\ rw [] \\ imp_res_tac FRANGE_FUPDATE_LIST_ZIP_IMP \\ fs []
    \\ fs [EVERY_MEM] \\ res_tac \\ fs []
    \\ drule_all LIST_REL_MEM_ALT
    \\ strip_tac \\ res_tac
    \\ imp_res_tac letrec_delarg_freevars \\ gvs [closed_def] )
  \\ irule call_with_arg_imp_letrec_delarg \\ fs []
  \\ irule subst_call_with_arg_F_F
  \\ simp []
  \\ gvs [FDOM_FUPDATE_LIST]
  \\ DEP_REWRITE_TAC [MAP_FST_ZIP]
  \\ conj_tac
  >- (imp_res_tac LIST_REL_LENGTH \\ gvs [] \\ rw [] \\ gvs [])
  \\ conj_tac
  >- (rw [] \\ gvs [] \\ rw [] \\ eq_tac \\ rw [] \\ gvs [])
  \\ reverse conj_tac >-
   (conj_tac >- (fs [info_ok_def] \\ rw [] \\ fs [])
    \\ fs [info_ok_def]
    \\ irule call_with_arg_mono
    \\ qexists_tac ‘$=’
    \\ conj_tac >- fs [letrec_delarg_refl]
    \\ irule call_with_arg_gen \\ fs [])
  \\ strip_tac \\ strip_tac
  \\ qabbrev_tac ‘b1' = if b1 then [] else [i.arg]’
  \\ qabbrev_tac ‘b2' = if b2 then [] else [i.arg]’
  \\ qabbrev_tac ‘c1' = if b1 then [] else [c]’
  \\ qabbrev_tac ‘c2' = if b2 then [] else [c]’
  \\ DEP_REWRITE_TAC [TO_FLOOKUP]
  \\ conj_tac
  >-
   (fs [FLOOKUP_FUPDATE_LIST,AllCaseEqs(),ALOOKUP_NONE,MAP_REVERSE]
    \\ DEP_REWRITE_TAC [MAP_FST_ZIP]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ unabbrev_all_tac \\ gvs [] \\ rw [] \\ gvs []
    \\ every_case_tac \\ gvs [])
  \\ DEP_REWRITE_TAC [GSYM ZIP_APPEND]
  \\ conj_tac
  >-
   (imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ Cases_on ‘b1’ \\ Cases_on ‘b2’ \\ unabbrev_all_tac \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs [])
  \\ simp [flookup_fupdate_list,REVERSE_APPEND,ALOOKUP_APPEND]
  \\ ‘~MEM k' b2' ∧ ~MEM k' b1'’ by (unabbrev_all_tac \\ rw [] \\ gvs [])
  \\ Cases_on ‘MEM k' i.args'’
  >-
   (gvs []
    \\ ‘∃x y.
          ALOOKUP (REVERSE (ZIP (i.args',xs1))) k' = SOME x ∧
          ALOOKUP (REVERSE (ZIP (i.args',ys1))) k' = SOME y ∧
          letrec_delarg i x y ∧ closed x ∧ closed y’ by (irule lemma2 \\ fs [])
    \\ fs [])
  \\ ‘ALOOKUP (REVERSE (ZIP (i.args',xs1))) k' = NONE ∧
      ALOOKUP (REVERSE (ZIP (i.args',ys1))) k' = NONE ∧
      ALOOKUP (REVERSE (ZIP (b1',c1'))) k' = NONE ∧
      ALOOKUP (REVERSE (ZIP (b2',c2'))) k' = NONE’ by
   (fs [ALOOKUP_NONE,MAP_REVERSE]
    \\ DEP_REWRITE_TAC [MAP_FST_ZIP] \\ fs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ Cases_on ‘b1’ \\ Cases_on ‘b2’ \\ unabbrev_all_tac \\ gvs [])
  \\ simp []
  \\ ‘∃x y.
        ALOOKUP (REVERSE (ZIP (i.args,xs))) k' = SOME x ∧
        ALOOKUP (REVERSE (ZIP (i.args,ys))) k' = SOME y ∧
        letrec_delarg i x y ∧ closed x ∧ closed y’ by (irule lemma2 \\ fs [])
  \\ simp []
QED

Theorem eval_forward_letrec_delarg:
  info_ok i ⇒
  eval_forward T (letrec_delarg i)
Proof
  strip_tac
  \\ simp [eval_forward_def]
  \\ gen_tac \\ completeInduct_on ‘k’
  \\ gvs [PULL_FORALL,AND_IMP_INTRO]
  \\ gen_tac \\ completeInduct_on ‘exp_size e1’
  \\ rpt strip_tac
  \\ gvs [PULL_FORALL,AND_IMP_INTRO]
  \\ qpat_x_assum ‘letrec_delarg i _ _’ mp_tac
  \\ simp [Once letrec_delarg_cases,mk_letrec_neq]
  \\ strip_tac \\ gvs []
  >~ [‘Lam v z’] >-
   (gvs [eval_wh_to_def]
    \\ ‘eval_wh (Lam v y) = wh_Closure v y’ by fs [eval_wh_Lam]
    \\ drule_all eval_wh_Closure_bisim
    \\ strip_tac \\ fs [GSYM PULL_FORALL]
    \\ rw [] \\ first_x_assum drule
    \\ disch_then $ irule_at Any
    \\ irule_at Any letrec_delarg_subst1
    \\ fs [])
  >~ [‘App e1 e2y’] >-
   (fs [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k e1)’ \\ fs []
    >-
     (first_x_assum $ qspec_then ‘e1’ mp_tac \\ fs [exp_size_def]
      \\ disch_then drule
      \\ imp_res_tac letrec_delarg_freevars
      \\ ‘(g ≃ g) T ∧ closed g’ by
        (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
         \\ fs [closed_def])
      \\ disch_then drule_all
      \\ rw [] \\ fs []
      \\ ‘eval_wh g ≠ wh_Diverge ∧ dest_wh_Closure (eval_wh g) = NONE’ by
        (every_case_tac \\ fs [])
      \\ irule eval_wh_Error_bisim
      \\ first_x_assum $ irule_at Any
      \\ fs [eval_wh_App])
    \\ PairCases_on ‘x’ \\ fs []
    \\ rw [] \\ gvs []
    \\ Cases_on ‘eval_wh_to k e1’ \\ gvs [dest_wh_Closure_def]
    \\ first_x_assum $ qspec_then ‘e1’ mp_tac \\ fs [exp_size_def]
    \\ disch_then drule
    \\ imp_res_tac letrec_delarg_freevars
    \\ ‘(g ≃ g) T ∧ closed g’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule_all
    \\ strip_tac \\ fs [GSYM PULL_FORALL]
    \\ rename [‘eval_wh g = wh_Closure v1 e1’]
    \\ first_x_assum $ qspec_then ‘e2y’ mp_tac
    \\ imp_res_tac letrec_delarg_freevars
    \\ ‘closed y’ by fs [closed_def]
    \\ disch_then drule_all \\ strip_tac \\ gvs []
    \\ fs [bind_def,FLOOKUP_DEF]
    \\ last_x_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
    \\ disch_then irule
    \\ irule_at Any IMP_closed_subst
    \\ fs [FRANGE_DEF]
    \\ irule_at Any pure_eval_lemmasTheory.eval_wh_Closure_closed
    \\ drule eval_wh_to_IMP_eval_wh \\ fs [] \\ strip_tac
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ first_x_assum $ irule_at $ Pos last \\ fs []
    \\ irule app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ irule app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos last \\ fs []
    \\ irule eval_wh_IMP_app_bisimilarity
    \\ irule_at Any IMP_closed_subst
    \\ fs [FRANGE_DEF]
    \\ irule_at Any pure_eval_lemmasTheory.eval_wh_Closure_closed
    \\ first_assum $ irule_at $ Pos hd \\ fs []
    \\ fs [eval_wh_App,bind_def,FLOOKUP_DEF])
  >~ [‘Letrec bs x’] >-
   (rw [eval_wh_to_def] \\ gvs [] \\ first_x_assum irule
    \\ rename [‘(Letrec ys y ≃ e2) T’]
    \\ irule_at Any app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos $ el 2
    \\ qexists_tac ‘subst_funs ys y’
    \\ irule_at Any eval_wh_IMP_app_bisimilarity
    \\ simp [eval_wh_Letrec] \\ gvs []
    \\ fs [subst_funs_def,bind_def]
    \\ ‘MAP FST ys = MAP FST bs’ by fs [] \\ fs []
    \\ drule EVERY_FLOOKUP_closed_lemma \\ strip_tac
    \\ ‘EVERY (λe. freevars e ⊆ set (MAP FST ys)) (MAP SND ys)’ by
      (fs [EVERY_MEM] \\ rw []
       \\ drule_all LIST_REL_MEM_ALT \\ rw []
       \\ imp_res_tac letrec_delarg_freevars \\ fs []
       \\ res_tac  \\ gvs [] \\ metis_tac [])
    \\ imp_res_tac letrec_delarg_freevars \\ fs []
    \\ drule EVERY_FLOOKUP_closed_lemma  \\ strip_tac
    \\ asm_rewrite_tac []
    \\ rpt $ irule_at Any IMP_closed_subst
    \\ gvs [] \\ irule_at Any subst_letrec_delarg \\ gs [FORALL_FRANGE]
    \\ asm_rewrite_tac []
    \\ fs [FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
    \\ fs [alistTheory.flookup_fupdate_list,AllCaseEqs()]
    \\ rpt gen_tac \\ strip_tac
    \\ drule_all ALOOKUP_REVERSE_LIST_REL \\ strip_tac \\ gvs []
    \\ conj_tac >- simp [Once letrec_delarg_cases]
    \\ gvs [EVERY_MEM] \\ res_tac)
  >~ [‘mk_letrec’] >-
   (gvs [mk_letrec_def]
    \\ rw [eval_wh_to_def]
    \\ last_x_assum irule \\ fs []
    \\ irule_at Any app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos $ el 2
    \\ qexists_tac ‘subst_funs [(i.fname,mk_fun b2 i)] y’
    \\ irule_at Any eval_wh_IMP_app_bisimilarity
    \\ simp [eval_wh_Letrec] \\ gvs []
    \\ ‘freevars (mk_fun b2 i) ⊆ {i.fname}’ by
      (irule_at Any SUBSET_TRANS
       \\ first_assum $ irule_at Any
       \\ fs [free_vars_mk_fun_subset])
    \\ fs [subst_funs_def,bind_def]
    \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST]
    \\ DEP_REWRITE_TAC [IMP_closed_subst]
    \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST,FRANGE_DEF]
    \\ imp_res_tac letrec_delarg_freevars
    \\ fs [GSYM mk_letrec_def,GSYM mk_rec_def]
    \\ irule call_with_arg_imp_letrec_delarg \\ fs [])
  >~ [‘mk_apps’] >-
   (Cases_on ‘eval_wh_to k (mk_apps b1 (mk_rec b1 i) xs c xs1) = wh_Diverge’ >- fs []
    \\ drule_then (drule_at $ Pos last) Apps_rec_lemma
    \\ disch_then (drule_at $ Pos last)
    \\ disch_then $ qspec_then ‘b2’ mp_tac
    \\ impl_tac
    >- (imp_res_tac LIST_REL_LENGTH \\ gvs [closed_mk_apps])
    \\ strip_tac
    \\ simp []
    \\ drule_all closed_mk_rec_copy \\ strip_tac
    \\ last_x_assum irule \\ fs []
    \\ first_assum $ irule_at Any
    \\ irule app_bisimilarity_trans
    \\ first_assum $ irule_at $ Pos last
    \\ irule app_bisimilarity_sym
    \\ irule eval_wh_IMP_app_bisimilarity
    \\ fs [closed_mk_rec,SF SFY_ss,closed_mk_apps]
    \\ imp_res_tac LIST_REL_letrec_delarg_closed \\ fs []
    \\ imp_res_tac letrec_delarg_freevars
    \\ fs [closed_def])
  \\ rename [‘Prim p xs’]
  \\ Cases_on ‘p’ \\ fs []
  >~ [‘Cons s xs’] >-
   (rw [eval_wh_to_def]
    \\ ‘eval_wh (Cons s ys) = wh_Constructor s ys’ by fs [eval_wh_Cons]
    \\ drule_all eval_wh_Constructor_bisim \\ strip_tac \\ fs []
    \\ drule_then drule LIST_REL_COMP
    \\ match_mp_tac LIST_REL_mono \\ fs [])
  >~ [‘If’] >-
   (fs [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    >-
     (rw []
      \\ drule_at Any eval_wh_Error_bisim
      \\ fs [eval_wh_Prim,AllCaseEqs()]
      \\ disch_then irule
      \\ imp_res_tac LIST_REL_LENGTH
      \\ Cases_on ‘ys’ \\ fs []
      \\ rpt (Cases_on ‘t’ \\ fs [] \\ Cases_on ‘t'’ \\ fs []))
    \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ fs [SF DNF_ss]
    \\ reverse (Cases_on ‘∃s. eval_wh_to (k − 1) h = wh_Constructor s []’ \\ fs [])
    >-
     (Cases_on ‘eval_wh_to (k − 1) h’ \\ gvs [] \\ rw []
      \\ irule eval_wh_Error_bisim
      \\ last_x_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
      \\ qpat_x_assum ‘letrec_delarg _ h y’ assume_tac
      \\ disch_then drule \\ fs []
      \\ imp_res_tac letrec_delarg_freevars
      \\ ‘(y ≃ y) T ∧ closed y’ by
       (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
        \\ fs [closed_def])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ imp_res_tac LIST_REL_LENGTH
      \\ qpat_x_assum ‘(_ ≃ e2) T’ $ irule_at Any
      \\ fs [eval_wh_If]
      \\ rw [] \\ gvs [])
    \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
    \\ qpat_x_assum ‘letrec_delarg _ h y’ assume_tac
    \\ disch_then drule \\ fs []
    \\ imp_res_tac letrec_delarg_freevars
    \\ ‘(y ≃ y) T ∧ closed y’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule \\ fs [] \\ strip_tac
    \\ reverse (rw []) \\ fs []
    >-
     (irule eval_wh_Error_bisim
      \\ last_x_assum $ irule_at Any
      \\ fs [eval_wh_If])
    \\ rename [‘eval_wh_to (k − 1) h2’]
    \\ qpat_x_assum ‘letrec_delarg _ h2 _’ assume_tac
    \\ last_x_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
    \\ disch_then drule
    \\ disch_then irule \\ fs []
    \\ irule app_bisimilarity_trans
    \\ first_x_assum $ irule_at Any \\ fs []
    \\ irule eval_wh_IMP_app_bisimilarity
    \\ fs [closed_def,eval_wh_If])
  >~ [‘Seq’] >-
   (fs [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    >-
     (rw []
      \\ drule_at Any eval_wh_Error_bisim
      \\ fs [eval_wh_Prim,AllCaseEqs()]
      \\ disch_then irule
      \\ imp_res_tac LIST_REL_LENGTH
      \\ Cases_on ‘ys’ \\ fs []
      \\ rpt (Cases_on ‘t’ \\ fs [] \\ Cases_on ‘t'’ \\ fs []))
    \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘k=0’ \\ fs [SF DNF_ss]
    \\ Cases_on ‘eval_wh_to (k − 1) h = wh_Diverge’ \\ fs []
    \\ Cases_on ‘eval_wh_to (k − 1) h = wh_Error’ \\ gvs []
    >-
     (rw [] \\ qpat_x_assum ‘letrec_delarg _ h y’ assume_tac
      \\ last_x_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
      \\ disch_then drule
      \\ imp_res_tac letrec_delarg_freevars
      \\ ‘(y ≃ y) T ∧ closed y’ by
       (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
        \\ fs [closed_def])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ irule eval_wh_Error_bisim
      \\ first_x_assum $ irule_at $ Pos $ last
      \\ fs [eval_wh_Seq])
    \\ imp_res_tac letrec_delarg_freevars
    \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
    \\ disch_then irule \\ fs []
    \\ first_x_assum $ irule_at $ Pos last
    \\ irule app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos last \\ fs []
    \\ irule eval_wh_IMP_app_bisimilarity
    \\ fs [closed_def,eval_wh_Seq,AllCaseEqs()]
    \\ qsuff_tac ‘eval_wh y ≠ wh_Error ∧ eval_wh y ≠ wh_Diverge’ >- fs []
    \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
    \\ disch_then drule \\ fs []
    \\ ‘(y ≃ y) T ∧ closed y’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule \\ fs [] \\ strip_tac
    \\ Cases_on ‘eval_wh_to (k − 1) h’ \\ fs [])
  >~ [‘IsEq cname arity onoff’] >-
   (fs [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    >-
     (rw []
      \\ drule_at Any eval_wh_Error_bisim
      \\ fs [eval_wh_Prim,AllCaseEqs()]
      \\ disch_then irule
      \\ imp_res_tac LIST_REL_LENGTH
      \\ Cases_on ‘ys’ \\ fs []
      \\ rpt (Cases_on ‘t’ \\ fs [] \\ Cases_on ‘t'’ \\ fs []))
    \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘k=0’ \\ fs [SF DNF_ss]
    \\ reverse (Cases_on ‘∃s xs. eval_wh_to (k − 1) h = wh_Constructor s xs ∧
                   ~is_eq_fail onoff s ∧ (s = cname ⇒ arity = LENGTH xs)’ \\ fs [])
    >-
     (Cases_on ‘eval_wh_to (k − 1) h’ \\ gvs [] \\ rw []
      \\ irule eval_wh_Error_bisim
      \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
      \\ disch_then drule \\ fs []
      \\ qpat_x_assum ‘letrec_delarg _ h y’ assume_tac
      \\ imp_res_tac letrec_delarg_freevars
      \\ ‘(y ≃ y) T ∧ closed y’ by
       (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
        \\ fs [closed_def])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ first_x_assum $ irule_at $ Pos last
      \\ imp_res_tac LIST_REL_LENGTH
      \\ fs [eval_wh_Prim])
    \\ IF_CASES_TAC \\ gvs []
    \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
    \\ disch_then drule \\ fs []
    \\ imp_res_tac letrec_delarg_freevars
    \\ ‘(y ≃ y) T ∧ closed y’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule \\ fs [] \\ strip_tac
    \\ irule eval_wh_Constructor_NIL_bisim
    \\ first_x_assum $ irule_at $ Pos last
    \\ imp_res_tac LIST_REL_LENGTH
    \\ fs [eval_wh_IsEq])
  >~ [‘Proj cname i’] >-
   (fs [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    >-
     (rw []
      \\ drule_at Any eval_wh_Error_bisim
      \\ fs [eval_wh_Prim,AllCaseEqs()]
      \\ disch_then irule
      \\ imp_res_tac LIST_REL_LENGTH
      \\ Cases_on ‘ys’ \\ fs []
      \\ Cases_on ‘t’ \\ fs [])
    \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘k=0’ \\ fs [SF DNF_ss]
    \\ imp_res_tac LIST_REL_LENGTH
    \\ reverse (Cases_on ‘∃s xs. eval_wh_to (k − 1) h = wh_Constructor s xs ∧
                                 s = cname ∧ i < LENGTH xs’ \\ fs [])
    >-
     (Cases_on ‘eval_wh_to (k − 1) h’ \\ gvs [] \\ rw []
      \\ irule eval_wh_Error_bisim
      \\ last_x_assum $ irule_at Any
      \\ qpat_x_assum ‘letrec_delarg _ h y’ assume_tac
      \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
      \\ disch_then drule \\ fs []
      \\ imp_res_tac letrec_delarg_freevars
      \\ ‘(y ≃ y) T ∧ closed y’ by
       (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
        \\ fs [closed_def])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ imp_res_tac LIST_REL_LENGTH
      \\ fs [eval_wh_Prim] \\ rw [] \\ fs [])
    \\ last_assum irule \\ fs []
    \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
    \\ disch_then drule \\ fs []
    \\ imp_res_tac letrec_delarg_freevars
    \\ ‘(y ≃ y) T ∧ closed y’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule \\ fs [] \\ strip_tac
    \\ fs [LIST_REL_EL_EQN]
    \\ gvs []
    \\ pop_assum drule \\ strip_tac
    \\ first_x_assum $ irule_at $ Pos last
    \\ irule_at Any app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ irule_at Any app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos $ el 2 \\ fs []
    \\ irule_at Any eval_wh_IMP_app_bisimilarity
    \\ fs [eval_wh_Proj]
    \\ dxrule eval_wh_freevars_SUBSET
    \\ dxrule eval_wh_to_freevars_SUBSET
    \\ fs [PULL_EXISTS,MEM_MAP,closed_def,EXTENSION]
    \\ fs [MEM_EL]
    \\ metis_tac [])
  >~ [‘AtomOp a’] >-
   (fs [eval_wh_to_def]
    \\ Cases_on ‘get_atoms (MAP (if k = 0 then K wh_Diverge else
                                   (λa. eval_wh_to (k − 1) a)) xs)’ \\ fs []
    \\ Cases_on ‘x’ \\ fs []
    >-
     (rw []
      \\ fs [get_atoms_def,AllCaseEqs(),EXISTS_MEM]
      \\ gvs [MEM_MAP]
      \\ Cases_on ‘k=0’ \\ gvs [error_Atom_def]
      \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
      \\ drule_all LIST_REL_MEM \\ strip_tac
      \\ disch_then drule \\ fs []
      \\ rename [‘letrec_delarg _ x y’]
      \\ imp_res_tac letrec_delarg_freevars
      \\ ‘(y ≃ y) T ∧ closed y ∧ closed x’ by
        (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
         \\ fs [closed_def,EVERY_MEM] \\ res_tac \\ fs [])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ Cases_on ‘eval_wh_to (k − 1) x’ \\ gvs [error_Atom_def]
      \\ irule eval_wh_Error_bisim
      \\ last_x_assum $ irule_at Any
      \\ fs [eval_wh_Prim,get_atoms_def]
      \\ qsuff_tac ‘EXISTS error_Atom (MAP eval_wh ys)’ >- fs []
      \\ fs [EXISTS_MEM,MEM_MAP,PULL_EXISTS]
      \\ first_x_assum $ irule_at Any
      \\ fs [])
    \\ rename [‘eval_op a atoms’]
    \\ qsuff_tac ‘get_atoms (MAP eval_wh ys) = SOME (SOME atoms)’
    >-
     (rw []
      \\ Cases_on ‘eval_op a atoms’ \\ fs []
      >-
       (rw [] \\ irule eval_wh_Error_bisim
        \\ last_x_assum $ irule_at Any
        \\ gvs [eval_wh_Prim])
      \\ Cases_on ‘x’ \\ fs []
      >-
       (rw [] \\ irule eval_wh_Atom_bisim
        \\ last_x_assum $ irule_at Any
        \\ gvs [eval_wh_Prim])
      \\ Cases_on ‘y’ \\ fs []
      \\ rw [] \\ irule eval_wh_Constructor_NIL_bisim
      \\ last_x_assum $ irule_at Any
      \\ gvs [eval_wh_Prim])
    \\ fs [get_atoms_def,AllCaseEqs()]
    \\ gvs []
    \\ Cases_on ‘xs = []’ >- gvs []
    \\ Cases_on ‘k = 0’ >- (Cases_on ‘xs’ \\ fs [])
    \\ gvs [MEM_MAP]
    \\ rw []
    >-
     (fs [EVERY_MEM,MEM_MAP] \\ rw []
      \\ drule_all LIST_REL_MEM_ALT \\ rw []
      \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
      \\ disch_then drule \\ fs []
      \\ imp_res_tac letrec_delarg_freevars
      \\ ‘(y ≃ y) T ∧ closed y’ by
        (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
         \\ fs [closed_def] \\ res_tac \\ fs [])
      \\ disch_then drule_all
      \\ rw [] \\ fs [PULL_EXISTS]
      \\ first_x_assum drule \\ strip_tac
      \\ Cases_on ‘eval_wh_to (k − 1) x’ \\ fs []
      \\ res_tac \\ fs [])
    >-
     (CCONTR_TAC \\ fs []
      \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
      \\ drule_all LIST_REL_MEM_ALT \\ strip_tac
      \\ ‘closed x ∧ ¬error_Atom (eval_wh_to (k − 1) x)’ by (res_tac \\ fs [])
      \\ ‘eval_wh_to (k − 1) x ≠ wh_Diverge’ by (CCONTR_TAC \\ fs [] \\ res_tac \\ fs [])
      \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
      \\ goal_assum drule \\ fs []
      \\ imp_res_tac letrec_delarg_freevars
      \\ ‘(y ≃ y) T ∧ closed y ∧ closed x’ by
        (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
         \\ fs [closed_def,EVERY_MEM] \\ res_tac \\ fs [])
      \\ first_assum $ irule_at $ Pos hd \\ fs []
      \\ Cases_on ‘eval_wh_to (k − 1) x’ \\ fs [])
    \\ AP_TERM_TAC
    \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ match_mp_tac LIST_REL_IMP_MAP_EQ
    \\ rw []
    \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
    \\ ‘closed x ∧ ¬error_Atom (eval_wh_to (k − 1) x)’ by (res_tac \\ fs [])
    \\ ‘eval_wh_to (k − 1) x ≠ wh_Diverge’ by (CCONTR_TAC \\ fs [] \\ res_tac \\ fs [])
    \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
    \\ disch_then drule \\ fs []
    \\ imp_res_tac letrec_delarg_freevars
    \\ ‘(y ≃ y) T ∧ closed y ∧ closed x’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def,EVERY_MEM] \\ res_tac \\ fs [])
    \\ disch_then drule \\ fs []
    \\ Cases_on ‘eval_wh_to (k − 1) x’ \\ fs [])
QED

Theorem eval_forward_letrec_delarg_rev:
  info_ok i ⇒
  eval_forward T (λx y. letrec_delarg i y x)
Proof
  simp [Once letrec_delarg_sym,SF ETA_ss,eval_forward_letrec_delarg]
QED

Theorem letrec_delarg_Apps_simple:
  ∀xs ys x y i.
    letrec_delarg i x y ∧
    LIST_REL (letrec_delarg i) xs ys ⇒
    letrec_delarg i (Apps x xs) (Apps y ys)
Proof
  Induct \\ fs [Apps_def,PULL_EXISTS] \\ rw []
  \\ last_x_assum irule \\ fs []
  \\ irule letrec_delarg_App  \\ fs []
QED

Theorem letrec_delarg_imp_equiv:
  ∀i x y.
    info_ok i ∧ closed x ∧ closed y ∧ letrec_delarg i x y ⇒
    (x ≃ y) T
Proof
  rw [] \\ irule eval_forward_imp_bisim \\ fs []
  \\ qexists_tac ‘letrec_delarg i’
  \\ fs [letrec_delarg_refl,eval_forward_letrec_delarg,eval_forward_letrec_delarg_rev]
QED

Triviality call_with_arg_T_with:
  ∀b1 b2 b i R x y.
    call_with_arg b1 b2 b i R x y ⇒ b ⇒
    call_with_arg b1 b2 b (i with <|rhs_T := rhs1; rhs_F := rhs2|>) R x y
Proof
  ho_match_mp_tac call_with_arg_ind
  \\ rpt strip_tac \\ gvs []
  \\ rpt (simp [Once call_with_arg_cases] \\ gvs [SF ETA_ss] \\ NO_TAC)
  \\ simp [Once call_with_arg_cases] \\ gvs []
  \\ disj1_tac
  \\ irule_at Any EQ_REFL
  \\ irule_at Any EQ_REFL
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
  \\ conj_tac
  >-
   (qpat_x_assum ‘LIST_REL _ _ _’ kall_tac
    \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ qid_spec_tac ‘xs’
    \\ qid_spec_tac ‘ys’
    \\ Induct \\ fs [PULL_EXISTS])
  \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
  \\ qid_spec_tac ‘xs1’
  \\ qid_spec_tac ‘ys1’
  \\ Induct \\ fs [PULL_EXISTS]
QED

Triviality MAP_FST_EQ_IMP:
  ∀xs ys x y.
    MAP FST xs = MAP FST ys ⇒
    MEM (x,y) xs ⇒ ∃z. MEM (x,z) ys
Proof
  Induct
  \\ fs [FORALL_PROD,MAP_EQ_CONS,PULL_EXISTS]
  \\ metis_tac []
QED

Theorem call_with_arg_subst:
  ∀b1 b2 b i rhs1 rhs2 m.
    call_with_arg b1 b2 b i (=) rhs1 rhs2 ⇒
    i.fname ∉ FDOM m ∧
    (i.w_arg ∈ freevars rhs1 ⇒ i.w_arg ∈ FDOM m) ∧
    (i.w_arg ∈ freevars rhs2 ⇒ i.w_arg ∈ FDOM m) ∧
    (∀n v. FLOOKUP m n = SOME v ⇒ closed v) ∧ b ⇒
    call_with_arg b1 b2 F i (=) (subst m rhs1) (subst m rhs2)
Proof
  Induct_on ‘call_with_arg’
  \\ rpt strip_tac
  \\ rpt var_eq_tac
  \\ gvs [subst_def]
  >-
   (fs [subst_Apps,subst_def,FLOOKUP_DEF]
    \\ gvs [mk_apps_def,subst_Apps]
    \\ ‘FLOOKUP m i.fname = NONE’ by fs [FLOOKUP_DEF]
    \\ qsuff_tac ‘∃c. closed c ∧
       (MAP (subst m) (if b1 then [] else [Var i.w_arg]) = if b1 then [] else [c]) ∧
       (MAP (subst m) (if b2 then [] else [Var i.w_arg]) = if b2 then [] else [c])’
    >-
     (strip_tac \\ gvs []
      \\ gvs [GSYM mk_apps_def,subst_def]
      \\ irule call_with_arg_Apps_Const \\ fs []
      \\ fs [LIST_REL_MAP]
      \\ strip_tac
      \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
      \\ fs [] \\ rw []
      \\ first_x_assum irule \\ fs [MEM_MAP,PULL_EXISTS]
      \\ metis_tac [])
    \\ reverse $ Cases_on ‘b1’ \\ gvs []
    >- (res_tac \\ gvs [subst_def,FLOOKUP_DEF]
        \\ rw [] \\ fs [subst_def,FLOOKUP_DEF])
    \\ reverse $ Cases_on ‘b2’ \\ gvs []
    >- (res_tac \\ gvs [subst_def,FLOOKUP_DEF]
        \\ rw [] \\ fs [subst_def,FLOOKUP_DEF])
    \\ qexists_tac ‘Lit ARB’ \\ fs [closed_def])
  >-
   (Cases_on ‘FLOOKUP m n’ \\ fs [] \\ res_tac
    >- (irule_at Any call_with_arg_Var \\ fs [])
    \\ irule_at Any call_with_arg_closed \\ fs [])
  >-
   (irule_at Any call_with_arg_Lam \\ fs []
    \\ first_x_assum irule \\ fs [FDOM_DOMSUB,DOMSUB_FLOOKUP_THM]
    \\ rw [] \\ res_tac \\ gvs [])
  >-
   (irule_at Any call_with_arg_App \\ fs [SF SFY_ss])
  >-
   (irule_at Any call_with_arg_Prim \\ fs [SF SFY_ss,LIST_REL_MAP]
    \\ last_x_assum mp_tac
    \\ match_mp_tac LIST_REL_mono \\ fs []
    \\ rw [] \\ gvs [SF SFY_ss]
    \\ first_x_assum irule \\ fs [SF SFY_ss]
    \\ rw []
    \\ gvs [MEM_MAP,PULL_EXISTS]
    \\ res_tac)
  >-
   (irule call_with_arg_Letrec
    \\ fs [SF SFY_ss,EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]
    \\ fs [SF SFY_ss,LIST_REL_MAP_MAP]
    \\ fs [LIST_REL_same] \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]
    \\ gvs [EXISTS_PROD]
    \\ gvs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_INTRO,LIST_REL_MAP]
    \\ conj_tac >- (CCONTR_TAC \\ gvs [] \\ imp_res_tac MAP_FST_EQ_IMP \\ gvs [])
    \\ first_x_assum $ irule_at Any
    \\ gvs [FLOOKUP_DRESTRICT,FDIFF_def,SF SFY_ss]
    \\ gvs [MEM_MAP,PULL_EXISTS,FORALL_PROD]
    \\ last_x_assum mp_tac
    \\ match_mp_tac LIST_REL_mono \\ fs [FORALL_PROD] \\ rw []
    \\ last_x_assum $ irule_at Any
    \\ gvs [FLOOKUP_DRESTRICT,FDIFF_def,SF SFY_ss,DRESTRICT_DEF]
    \\ gvs [MEM_MAP,PULL_EXISTS,FORALL_PROD])
  \\ simp [Once call_with_arg_cases]
QED

Theorem subst_subst1_lemma:
  ∀rhs m w c v.
    FLOOKUP m w = SOME c ∧ v ∉ FDOM m ∧
    w ∉ boundvars rhs ∧
    v ∉ boundvars rhs ∧
    (∀n v. FLOOKUP m n = SOME v ⇒ closed v) ⇒
    subst m (subst1 v (Var w) rhs) =
    subst1 v c (subst m rhs)
Proof
  ho_match_mp_tac freevars_ind \\ rw []
  >- (rw [subst1_def] \\ fs [subst_def,FLOOKUP_DEF]
      \\ rw [] \\ fs [subst1_def])
  >- (rw [subst1_def] \\ fs [subst_def,FLOOKUP_DEF]
      \\ fs [MAP_MAP_o,combinTheory.o_DEF]
      \\ fs [MAP_EQ_f,DOMSUB_FUPDATE_THM,MEM_MAP]
      \\ metis_tac [])
  >- (rw [subst1_def] \\ fs [subst_def,FLOOKUP_DEF])
  >- (rw [subst1_def] \\ fs [subst_def,DOMSUB_FUPDATE_THM]
      \\ first_x_assum irule
      \\ gvs [FLOOKUP_DEF,DOMSUB_FAPPLY_THM] \\ rw []
      \\ CCONTR_TAC \\ gvs [])
  \\ rw [subst1_def] \\ fs [subst_def,DOMSUB_FUPDATE_THM]
  \\ fs [MAP_MAP_o,combinTheory.o_DEF]
  \\ fs [MAP_EQ_f,DOMSUB_FUPDATE_THM,MEM_MAP,FORALL_PROD]
  \\ gvs [LAMBDA_PROD] \\ rw []
  \\ gvs [FDIFF_def]
  \\ fs [MEM_MAP,FORALL_PROD,FST_INTRO]
  \\ first_x_assum irule
  \\ gvs [FLOOKUP_DRESTRICT,SF SFY_ss]
  \\ gvs [DRESTRICT_DEF,MEM_MAP,FORALL_PROD]
  \\ metis_tac []
QED

Theorem app_bisimilarity_Letrec_suff_lemma[local]:
  (subst1 f (Letrec [(f,r)] r) x ≃ y) b ∧
  freevars r ⊆ {f} ∧ freevars x ⊆ {f} ⇒
  (Letrec [(f,r)] x ≃ y) b
Proof
  rw []
  \\ irule app_bisimilarity_trans
  \\ last_x_assum $ irule_at Any
  \\ irule eval_wh_IMP_app_bisimilarity
  \\ gvs [closed_def,eval_wh_Letrec]
  \\ fs [subst_funs_def,FUPDATE_LIST,bind_def,FLOOKUP_UPDATE]
  \\ DEP_REWRITE_TAC [freevars_subst]
  \\ gvs [] \\ gvs [SUBSET_DEF,EXTENSION]
  \\ metis_tac []
QED

Theorem app_bisimilarity_Letrec_suff:
  (subst1 f (Letrec [(f,r)] r) x ≃ subst1 f (Letrec [(f,r')] r') y) b ∧
  freevars r ⊆ {f} ∧ freevars x ⊆ {f} ∧
  freevars r' ⊆ {f} ∧ freevars y ⊆ {f} ⇒
  (Letrec [(f,r)] x ≃ Letrec [(f,r')] y) b
Proof
  rw []
  \\ irule app_bisimilarity_Letrec_suff_lemma
  \\ irule_at Any app_bisimilarity_sym
  \\ irule_at Any app_bisimilarity_Letrec_suff_lemma
  \\ irule_at Any app_bisimilarity_sym
  \\ fs []
QED

Theorem letrec_del_arg:
  call_with_arg F T T i (=) rhs1 rhs2 ∧
  i.arg = v ∧ i.w_arg = w ∧ i.args = vs ∧ i.args' = ws ∧ i.fname = f ∧
  EVERY (λx. f ∉ freevars x) xs ∧
  EVERY (λx. f ∉ freevars x) ys ∧
  (vs = [] ⇒ ws ≠ []) ∧
  v ∉ freevars rhs1 ∧
  v ∉ freevars rhs2 ∧
  ALL_DISTINCT (f::w::v::vs++ws) ∧
  LENGTH xs = LENGTH vs ∧
  LENGTH ys = LENGTH ws ∧
  DISJOINT {v; w; f} (boundvars rhs1)
  ⇒
  Letrec [(f,Lams (vs ++ [v] ++ ws) rhs1)]
    (Apps (Var f) (xs ++ [Var w] ++ ys))
  ≅
  Letrec [(f,Lams (vs ++ ws) rhs2)]
    (Apps (Var f) (xs ++ ys))
Proof
  rpt strip_tac \\ fs []
  \\ fs [exp_eq_def]
  \\ rpt strip_tac \\ fs []
  \\ rename [‘bind m’]
  \\ fs [bind_def]
  \\ IF_CASES_TAC \\ fs []
  \\ fs [subst_def,subst_Lams,subst_Apps,FDIFF_SING,DOMSUB_FLOOKUP_THM]
  \\ ‘w IN FDOM m’ by (fs [SUBSET_DEF] \\ metis_tac [])
  \\ ‘∃c. FLOOKUP m w = SOME c ∧ closed c’ by fs [FLOOKUP_DEF]
  \\ fs []
  \\ qabbrev_tac ‘rhs_F = (subst (FDIFF (m \\ f) (set vs ∪ {v} ∪ set ws)) rhs1)’
  \\ qabbrev_tac ‘rhs_T = (subst (FDIFF (m \\ f) (set vs ∪ set ws)) rhs2)’
  \\ qabbrev_tac ‘i2 = i with <| rhs_F := rhs_F ; rhs_T := rhs_T |>’
  \\ qpat_abbrev_tac ‘x_F = Apps _ (_ ++ _ ++ _)’
  \\ qpat_abbrev_tac ‘x_T = Apps _ (_ ++ _)’
  \\ irule app_bisimilarity_Letrec_suff
  \\ ntac 2 (conj_asm1_tac >-
   (unabbrev_all_tac \\ gvs [] \\ DEP_REWRITE_TAC [freevars_subst]
    \\ gvs [FRANGE_DEF,PULL_EXISTS,FDIFF_def,DRESTRICT_DEF,
            DOMSUB_FAPPLY_THM,SF SFY_ss,FLOOKUP_DEF,SUBSET_DEF]
    \\ metis_tac []))
  \\ ntac 2 (conj_asm1_tac >-
   (fs [Abbr ‘x_F’,Abbr ‘x_T’,PULL_EXISTS,MEM_MAP,closed_def]
    \\ simp [SUBSET_DEF,MEM_MAP,PULL_EXISTS,PULL_FORALL]
    \\ rpt gen_tac
    \\ DEP_REWRITE_TAC [freevars_subst]
    \\ gvs [FRANGE_DEF,FLOOKUP_DEF,DOMSUB_FAPPLY_THM,PULL_EXISTS,closed_def]
    \\ gvs [SUBSET_DEF,MEM_MAP]
    \\ metis_tac []))
  \\ irule letrec_delarg_imp_equiv
  \\ rpt (conj_asm1_tac >- (irule IMP_closed_subst \\ gvs [FRANGE_DEF]))
  \\ qexists_tac ‘i2’
  \\ conj_asm1_tac
  >-
   (gvs [info_ok_def,Abbr‘i2’]
    \\ rewrite_tac [GSYM CONJ_ASSOC]
    \\ conj_asm1_tac >-
     (gvs [Abbr‘rhs_F’] \\ DEP_REWRITE_TAC [freevars_subst]
      \\ gvs [FRANGE_DEF,PULL_EXISTS,FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM]
      \\ gvs [SF SFY_ss,FLOOKUP_DEF])
    \\ conj_asm1_tac >-
     (gvs [Abbr‘rhs_T’] \\ DEP_REWRITE_TAC [freevars_subst]
      \\ gvs [FRANGE_DEF,PULL_EXISTS,FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM]
      \\ gvs [SF SFY_ss,FLOOKUP_DEF])
    \\ unabbrev_all_tac \\ gvs []
    \\ ‘subst (FDIFF (m \\ i.fname) (set i.args ∪ {i.arg} ∪ set i.args')) rhs1 =
        subst (FDIFF (m \\ i.fname) (set i.args ∪ set i.args')) rhs1’ by
     (simp [Once UNION_COMM]
      \\ simp [UNION_ASSOC]
      \\ once_rewrite_tac [EQ_SYM_EQ]
      \\ simp [Once UNION_COMM]
      \\ once_rewrite_tac [EQ_SYM_EQ]
      \\ simp [Once (GSYM FDIFF_FDIFF),FDIFF_SING]
      \\ once_rewrite_tac [EQ_SYM_EQ]
      \\ irule subst_fdomsub
      \\ fs [])
    \\ fs []
    \\ irule call_with_arg_subst \\ fs [SF SFY_ss]
    \\ gvs [FLOOKUP_DEF,FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM]
    \\ irule call_with_arg_T_with \\ fs [])
  \\ ‘(Letrec [(f,Lams (vs ++ [v] ++ ws) rhs_F)] (Lams (vs ++ [v] ++ ws) rhs_F)) =
      mk_rec F i2’ by fs [mk_rec_def,mk_letrec_def,mk_fun_def,Abbr‘i2’]
  \\ ‘(Letrec [(f,Lams (vs ++ ws) rhs_T)] (Lams (vs ++ ws) rhs_T)) =
      mk_rec T i2’ by fs [mk_rec_def,mk_letrec_def,mk_fun_def,Abbr‘i2’]
  \\ fs [Abbr‘x_T’,Abbr‘x_F’,subst_Apps,subst_def,FLOOKUP_UPDATE]
  \\ ‘(∀a. MAP (subst (FEMPTY |+ (f,a)))
           (MAP (subst (m \\ f)) xs) = MAP (subst (m \\ f)) xs) ∧
      (∀a. MAP (subst (FEMPTY |+ (f,a)))
           (MAP (subst (m \\ f)) ys) = MAP (subst (m \\ f)) ys)’ by
   (gvs [MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f] \\ rw []
    \\ irule subst1_ignore
    \\ DEP_REWRITE_TAC [freevars_subst]
    \\ gvs [FRANGE_DEF,PULL_EXISTS,DOMSUB_FAPPLY_THM,EVERY_MEM,MEM_MAP,PULL_EXISTS]
    \\ res_tac \\ fs [FLOOKUP_DEF])
  \\ fs []
  \\ qsuff_tac ‘
        letrec_delarg i2
          (mk_apps F (mk_rec F i2) (MAP (subst (m \\ f)) xs) c
             (MAP (subst (m \\ f)) ys))
          (mk_apps T (mk_rec T i2) (MAP (subst (m \\ f)) xs) c
             (MAP (subst (m \\ f)) ys))’
  >- fs [mk_apps_def]
  \\ irule letrec_delarg_Apps
  \\ fs [LIST_REL_MAP,LIST_REL_same,letrec_delarg_refl]
  \\ gvs [Abbr‘i2’]
QED

val _ = export_theory();
