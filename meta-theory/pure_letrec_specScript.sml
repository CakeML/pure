(*
   Prove that invariant argument in Letrec can be replaced
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_exp_relTheory
     pure_alpha_equivTheory pure_miscTheory pure_congruenceTheory;

val _ = new_theory "pure_letrec_spec";

Datatype:
  info = <| args  : string list ;
            arg   : string      ;
            const : exp         ;
            fname : string      ;
            rhs   : exp         |>
End

Inductive call_with_arg:
[~Apps_Var:]
  (∀info xs.
    LENGTH xs = LENGTH info.args ⇒
    call_with_arg T info (Apps (Var info.fname) (xs ++ [Var info.arg]))) ∧
[~Apps_Const:]
  (∀info xs.
    LENGTH xs = LENGTH info.args ⇒
    call_with_arg F info (Apps (Var info.fname) (xs ++ [info.const]))) ∧
[~Var:]
  (∀info n b.
    n ≠ info.arg ∧ n ≠ info.fname ⇒
    call_with_arg b info (Var n)) ∧
[~Lam:]
  (∀info n x b.
    call_with_arg b info x ∧
    info.arg ≠ n ∧ info.fname ≠ n ⇒
    call_with_arg b info (Lam n x)) ∧
[~App:]
  (∀info f x b.
    call_with_arg b info f ∧ call_with_arg b info x ⇒
    call_with_arg b info (App f x)) ∧
[~Prim:]
  (∀info n xs b.
    EVERY (call_with_arg b info) xs ⇒
    call_with_arg b info (Prim n xs)) ∧
[~Letrec:]
  (∀info xs x b.
    EVERY (call_with_arg b info) (MAP SND xs) ∧
    DISJOINT {info.arg; info.fname} (set (MAP FST xs)) ∧
    call_with_arg b info x ⇒
    call_with_arg b info (Letrec xs x)) ∧
[~closed:]
  (∀info b c.
    closed c ⇒
    call_with_arg b info c)
End

Definition info_ok_def:
  info_ok i ⇔
    closed i.const ∧
    call_with_arg T i i.rhs
End

Definition mk_fun_def:
  mk_fun b i =
    Lams (i.args ++ [i.arg]) $ if b then subst1 i.arg i.const i.rhs else i.rhs
End

Definition mk_letrec_def:
  mk_letrec b i x = Letrec [(i.fname,mk_fun b i)] x
End

Definition mk_rec_def:
  mk_rec b i = mk_letrec b i (mk_fun b i)
End

(*

Switch:
      Letrec [(f,Lams (vs ++ [v]) rhs1] (... Apps f (xs ++ [c]) ...)
  -->
      ... Apps (Letrec [(f,Lams (vs ++ [v]) rhs1] (Lams (vs ++ [v]) rhs1)) (xs ++ [c]) ...

Apps:
      Apps (Letrec [(f,Lams (vs ++ [v]) rhs1] (Lams (vs ++ [v]) rhs1)) (xs ++ [c])
  -->
      rhs1[c/v,..]

*)

Inductive letrec_spec:
[~Switch:]
  (∀info x b1 b2.
    call_with_arg F info x ⇒
    letrec_spec info (mk_letrec b1 info x)
                     (mk_letrec b2 info x)) ∧
[~Apps:]
  (∀info xs ys b1 b2.
    LENGTH xs = LENGTH info.args ∧
    LIST_REL (letrec_spec info) xs ys ⇒
    letrec_spec info
      (Apps (mk_rec b1 info) (xs ++ [info.const]))
      (Apps (mk_rec b2 info) (ys ++ [info.const]))) ∧
[~Var:]
  (∀info n.
    letrec_spec info (Var n) (Var n)) ∧
[~Lam:]
  (∀info n x y.
    letrec_spec info x y ⇒
    letrec_spec info (Lam n x) (Lam n y)) ∧
[~App:]
  (∀info f g x y.
    letrec_spec info f g ∧ letrec_spec info x y ⇒
    letrec_spec info (App f x) (App g y)) ∧
[~Prim:]
  (∀info n xs ys.
    LIST_REL (letrec_spec info) xs ys ⇒
    letrec_spec info (Prim n xs) (Prim n ys)) ∧
[~Letrec:]
  (∀info  xs ys x y.
    LIST_REL (letrec_spec info) (MAP SND xs) (MAP SND ys) ∧
    MAP FST xs = MAP FST ys ∧ letrec_spec info x y ⇒
    letrec_spec info (Letrec xs x) (Letrec ys y))
End

Theorem letrec_spec_refl:
  ∀i x. letrec_spec i x x
Proof
  gen_tac \\ ho_match_mp_tac freevars_ind
  \\ rw [] \\ simp [Once letrec_spec_cases]
  \\ rpt disj2_tac
  >- (Induct_on ‘es’ \\ fs [])
  \\ Induct_on ‘lcs’ \\ fs [FORALL_PROD,SF DNF_ss]
  \\ rw [] \\ res_tac \\ fs []
QED

Triviality LIST_REL_SWAP:
  ∀R xs ys. LIST_REL R xs ys = LIST_REL (λx y. R y x) ys xs
Proof
  Induct_on ‘xs’ \\ fs []
QED

Theorem letrec_spec_sym:
  letrec_spec i x y ⇔ letrec_spec i y x
Proof
  qsuff_tac ‘∀i x y. letrec_spec i x y ⇒  letrec_spec i y x’
  >- metis_tac []
  \\ ho_match_mp_tac letrec_spec_ind
  \\ rw []
  \\ imp_res_tac LIST_REL_LENGTH
  >- (irule letrec_spec_Switch \\ fs [])
  >- (irule letrec_spec_Apps \\ fs [] \\ simp [Once LIST_REL_SWAP])
  >- (irule letrec_spec_Var \\ fs [])
  >- (irule letrec_spec_Lam \\ fs [])
  >- (irule letrec_spec_App \\ fs [])
  >- (irule letrec_spec_Prim \\ fs [] \\ simp [Once LIST_REL_SWAP])
  >- (irule letrec_spec_Letrec \\ fs [] \\ simp [Once LIST_REL_SWAP])
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

Theorem letrec_spec_freevars:
  ∀i x y. letrec_spec i x y ⇒ freevars x = freevars y
Proof
  cheat (*
  Induct_on ‘letrec_spec’ \\ rw [] \\ gvs []
  >-
   (PairCases_on ‘b’ \\ fs [mk_bind_def,MAP_FST_mk_bind]
    \\ rw [EXTENSION] \\ eq_tac \\ rw [] \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS]
    \\ fs [mk_seq_bind_def,MEM_MAP,EXISTS_PROD,PULL_EXISTS,FORALL_PROD,mk_bind_def]
    \\ gvs [freevars_mk_seqs]
    \\ metis_tac [freevars_mk_seqs])
  >-
   (simp [subset_funs_mk_bind,subset_funs_mk_seq_bind]
    \\ DEP_REWRITE_TAC [mk_seqs_subst]
    \\ DEP_REWRITE_TAC [pure_exp_lemmasTheory.subst_subst_FUNION]
    \\ DEP_REWRITE_TAC [freevars_subst]
    \\ fs [FDOM_FUPDATE_LIST]
    \\ drule_at Any freevars_mk_seqs \\ strip_tac
    \\ drule mk_bind_closed
    \\ drule mk_seq_bind_closed
    \\ fs [SF SFY_ss]
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,mk_bind_def,mk_seq_bind_def]
    \\ fs [FRANGE_FLOOKUP,PULL_EXISTS,FLOOKUP_FUNION,AllCaseEqs()]
    \\ fs [SF SFY_ss, SF DNF_ss]
    \\ rw []
    \\ imp_res_tac FEVERY_FLOOKUP
    \\ fs []
    \\ fs [obligation_def,IN_DISJOINT,EVERY_MEM]
    \\ res_tac \\ fs []
    \\ fs [SUBSET_DEF,EXTENSION,MEM_MAP,EXISTS_PROD,FORALL_PROD,MEM_FILTER])
  >- (pop_assum mp_tac
      \\ qid_spec_tac ‘xs’
      \\ qid_spec_tac ‘ys’
      \\ Induct \\ Cases_on ‘xs’ \\ fs [])
  \\ last_x_assum mp_tac
  \\ qid_spec_tac ‘xs’
  \\ qid_spec_tac ‘ys’
  \\ Induct \\ fs []
  \\ fs [PULL_EXISTS]
  \\ strip_tac \\ Cases \\ fs []
  \\ strip_tac \\ res_tac \\ fs [UNCURRY]
  \\ gvs [EXTENSION]
  \\ metis_tac [] *)
QED

Theorem subst_letrec_spec:
  ∀binds x y m1 m2.
    letrec_spec i x y ∧
    FDOM m1 = FDOM m2 ∧
    (∀k v1 v2.
      FLOOKUP m1 k = SOME v1 ∧ FLOOKUP m2 k = SOME v2 ⇒
      letrec_spec i v1 v2 ∧ closed v1 ∧ closed v2) ⇒
    letrec_spec i (subst m1 x) (subst m2 y)
Proof
  cheat (*
  Induct_on ‘letrec_spec’ \\ rw []
  >-
   (DEP_REWRITE_TAC [closed_subst]
    \\ irule_at Any letrec_spec_change \\ fs [MAP_FST_mk_bind]
    \\ drule_at Any freevars_mk_seqs
    \\ PairCases_on ‘b’ \\ fs [mk_bind_def,EVERY_MEM]
    \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS,mk_seq_bind_def,mk_bind_def]
    \\ gvs [SF SFY_ss]
    \\ fs [obligation_def,EVERY_MEM,FORALL_PROD]
    \\ rw [] \\ res_tac
    \\ gvs [SUBSET_DEF]
    \\ metis_tac [])
  >-
   (simp [subst_def]
    \\ DEP_REWRITE_TAC [pure_exp_lemmasTheory.subst_subst_FUNION]
    \\ conj_tac >- fs [FRANGE_DEF,FEVERY_DEF,PULL_EXISTS]
    \\ irule letrec_spec_seq
    \\ last_x_assum $ irule_at Any
    \\ fs [FEVERY_DEF,FUNION_DEF,FLOOKUP_DEF]
    \\ rw [])
  >-
   (fs [subst_def] \\ rpt CASE_TAC \\ fs [letrec_spec_refl]
    \\ res_tac \\ fs [] \\ gvs [FLOOKUP_DEF])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_spec_cases]
    \\ last_x_assum irule \\ fs []
    \\ fs [DOMSUB_FLOOKUP_THM,AllCaseEqs()]
    \\ rw [] \\ res_tac \\ fs [SUBSET_DEF])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_spec_cases]
    \\ rpt $ last_x_assum $ irule_at Any \\ fs [])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_spec_cases,SF ETA_ss]
    \\ disj2_tac
    \\ last_x_assum mp_tac \\ fs []
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    \\ rw [] \\ metis_tac [])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_spec_cases] \\ disj2_tac
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
    \\ rw [] \\ res_tac \\ fs []) *)
QED

Theorem letrec_spec_subst1:
  letrec_spec i a1 a2 ∧ letrec_spec i z y ∧ closed a1 ∧ closed a2 ⇒
  letrec_spec i (subst1 v a1 z) (subst1 v a2 y)
Proof
  strip_tac
  \\ irule subst_letrec_spec
  \\ fs [FLOOKUP_DEF]
QED

Theorem MEM_LIST_REL:
  ∀xs ys P y. LIST_REL P xs ys ∧ MEM y ys ⇒ ∃x. MEM x xs ∧ P x y
Proof
  Induct \\ fs [PULL_EXISTS]
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
  \\ metis_tac []
QED

Theorem MEM_LIST_REL1:
  ∀xs ys P x. LIST_REL P xs ys ∧ MEM x xs ⇒ ∃y. MEM y ys ∧ P x y
Proof
  Induct \\ fs [PULL_EXISTS]
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
  \\ metis_tac []
QED

Theorem LIST_REL_COMP:
  ∀xs ys zs.
    LIST_REL f xs ys ∧ LIST_REL g ys zs ⇒
    LIST_REL (λx z. ∃y. f x y ∧ g y z) xs zs
Proof
  Induct \\ fs [PULL_EXISTS]
  \\ metis_tac []
QED

Triviality LIST_REL_IMP_MAP_EQ:
  ∀xs ys P f g.
    (∀x y. MEM x xs ∧ MEM y ys ∧ P x y ⇒ f x = g y) ⇒
    LIST_REL P xs ys ⇒ MAP g ys = MAP f xs
Proof
  Induct \\ fs [PULL_EXISTS,SF DNF_ss] \\ metis_tac []
QED

Triviality eval_wh_Constructor_NIL_bisim =
  eval_wh_Constructor_bisim |> Q.GEN ‘xs’ |> Q.SPEC ‘[]’ |> SIMP_RULE (srw_ss()) [];

Theorem Apps_rec_lemma:
  eval_wh_to k (Apps (mk_rec b1 i) (xs ++ [i.const])) ≠ wh_Diverge ∧
  LENGTH xs = LENGTH i.args ∧
  closed (mk_rec b1 i) ∧
  EVERY closed xs ∧
  LIST_REL (letrec_spec i) xs ys ⇒
  ∃k1 x1 y1.
    eval_wh_to k (Apps (mk_rec b1 i) (xs ++ [i.const])) = eval_wh_to k1 x1 ∧
    eval_wh (Apps (mk_rec b2 i) (ys ++ [i.const])) = eval_wh y1 ∧
    closed x1 ∧
    letrec_spec i x1 y1 ∧
    k1 < k
Proof
  cheat
QED

Theorem closed_mk_rec:
  closed (mk_rec b1 i) ⇒ closed (mk_rec b2 i)
Proof
  cheat
QED

Triviality LIST_REL_letrec_spec_closed:
  ∀xs ys. LIST_REL (letrec_spec i) xs ys ∧ EVERY closed xs ⇒ EVERY closed ys
Proof
  Induct \\ rw [] \\ fs []
  \\ imp_res_tac letrec_spec_freevars \\ fs [closed_def]
QED

Triviality FORALL_FRANGE:
  (∀x. x IN FRANGE v ⇒ p x) ⇔ ∀k x. FLOOKUP v k = SOME x ⇒ p x
Proof
  fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS]
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

Theorem free_vars_mk_fun:
  freevars (mk_fun b2 i) ⊆ freevars (mk_fun b1 i)
Proof
  cheat (* true? *)
QED

Theorem call_with_arg_imp_letrec_spec:
  call_with_arg F i x ∧ info_ok i ⇒
  letrec_spec i (subst1 i.fname (mk_rec b1 i) x)
                (subst1 i.fname (mk_rec b2 i) x)
Proof
  cheat
QED

Theorem eval_forward_letrec_spec:
  info_ok i ⇒
  eval_forward T (letrec_spec i)
Proof
  strip_tac
  \\ simp [eval_forward_def]
  \\ gen_tac \\ completeInduct_on ‘k’
  \\ gvs [PULL_FORALL,AND_IMP_INTRO]
  \\ gen_tac \\ completeInduct_on ‘exp_size e1’
  \\ rpt strip_tac
  \\ gvs [PULL_FORALL,AND_IMP_INTRO]
  \\ Cases_on ‘e1’
  >~ [‘Var’] >- fs [eval_wh_to_def]
  >~ [‘Lam v z’] >-
   (qpat_x_assum ‘letrec_spec i (Lam v z) _’ mp_tac
    \\ simp [Once letrec_spec_cases,mk_letrec_neq]
    \\ strip_tac \\ gvs [eval_wh_to_def]
    \\ ‘eval_wh (Lam v y) = wh_Closure v y’ by fs [eval_wh_Lam]
    \\ drule_all eval_wh_Closure_bisim
    \\ strip_tac \\ fs [GSYM PULL_FORALL]
    \\ rw [] \\ first_x_assum drule
    \\ disch_then $ irule_at Any
    \\ irule_at Any letrec_spec_subst1
    \\ fs [])
  >~ [‘App e1 e2y’] >-
   (qpat_x_assum ‘letrec_spec _ _ _’ mp_tac
    \\ simp [Once letrec_spec_cases] \\ reverse strip_tac \\ gvs []
    >-
     (fs [eval_wh_to_def]
      \\ IF_CASES_TAC \\ fs []
      \\ Cases_on ‘dest_wh_Closure (eval_wh_to k e1)’ \\ fs []
      >-
       (first_x_assum $ qspec_then ‘e1’ mp_tac \\ fs [exp_size_def]
        \\ disch_then drule
        \\ imp_res_tac letrec_spec_freevars
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
      \\ imp_res_tac letrec_spec_freevars
      \\ ‘(g ≃ g) T ∧ closed g’ by
        (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
         \\ fs [closed_def])
      \\ disch_then drule_all
      \\ strip_tac \\ fs [GSYM PULL_FORALL]
      \\ rename [‘eval_wh g = wh_Closure v1 e1’]
      \\ first_x_assum $ qspec_then ‘e2y’ mp_tac
      \\ imp_res_tac letrec_spec_freevars
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
    \\ ‘closed (App e1 e2y)’ by fs []
    \\ pop_assum mp_tac
    \\ qpat_x_assum ‘App e1 e2y = Apps _ _’ $ rewrite_tac o single
    \\ strip_tac
    \\ Cases_on ‘eval_wh_to k (Apps (mk_rec b1 i) (xs ++ [i.const])) = wh_Diverge’ >- fs []
    \\ fs []
    \\ drule_all Apps_rec_lemma
    \\ disch_then $ qspec_then ‘b2’ strip_assume_tac
    \\ simp []
    \\ last_x_assum irule \\ fs []
    \\ first_assum $ irule_at Any
    \\ irule app_bisimilarity_trans
    \\ first_assum $ irule_at $ Pos last
    \\ irule app_bisimilarity_sym
    \\ irule eval_wh_IMP_app_bisimilarity
    \\ fs [closed_mk_rec,SF SFY_ss]
    \\ drule_all LIST_REL_letrec_spec_closed \\ fs []
    \\ imp_res_tac letrec_spec_freevars
    \\ fs [closed_def])
  >~ [‘Letrec bs x’] >-
   (qpat_x_assum ‘letrec_spec _ _ _’ mp_tac
    \\ simp [Once letrec_spec_cases] \\ reverse strip_tac \\ gvs []
    >-
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
         \\ drule_all MEM_LIST_REL \\ rw []
         \\ imp_res_tac letrec_spec_freevars \\ fs []
         \\ res_tac  \\ gvs [] \\ metis_tac [])
      \\ imp_res_tac letrec_spec_freevars \\ fs []
      \\ drule EVERY_FLOOKUP_closed_lemma  \\ strip_tac
      \\ asm_rewrite_tac []
      \\ rpt $ irule_at Any IMP_closed_subst
      \\ gvs [] \\ irule_at Any subst_letrec_spec \\ gs [FORALL_FRANGE]
      \\ asm_rewrite_tac []
      \\ fs [FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
      \\ fs [alistTheory.flookup_fupdate_list,AllCaseEqs()]
      \\ rpt gen_tac \\ strip_tac
      \\ drule_all ALOOKUP_REVERSE_LIST_REL \\ strip_tac \\ gvs []
      \\ conj_tac >- simp [Once letrec_spec_cases]
      \\ gvs [EVERY_MEM] \\ res_tac)
    \\ gvs [mk_letrec_def]
    \\ rw [eval_wh_to_def]
    \\ last_x_assum irule \\ fs []
    \\ irule_at Any app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos $ el 2
    \\ qexists_tac ‘subst_funs [(i.fname,mk_fun b2 i)] x’
    \\ irule_at Any eval_wh_IMP_app_bisimilarity
    \\ simp [eval_wh_Letrec] \\ gvs []
    \\ ‘freevars (mk_fun b2 i) ⊆ {i.fname}’ by
      (irule_at Any SUBSET_TRANS
       \\ first_assum $ irule_at Any
       \\ fs [free_vars_mk_fun])
    \\ fs [subst_funs_def,bind_def]
    \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST]
    \\ DEP_REWRITE_TAC [IMP_closed_subst]
    \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST,FRANGE_DEF]
    \\ fs [GSYM mk_letrec_def,GSYM mk_rec_def]
    \\ irule call_with_arg_imp_letrec_spec \\ fs [])
  \\ rename [‘letrec_spec _ (Prim p xs) _’]
  \\ qpat_x_assum ‘letrec_spec _ _ _’ mp_tac
  \\ simp [Once letrec_spec_cases]
  \\ reverse strip_tac \\ gvs []
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
      \\ qpat_x_assum ‘letrec_spec _ h y’ assume_tac
      \\ disch_then drule \\ fs []
      \\ imp_res_tac letrec_spec_freevars
      \\ ‘(y ≃ y) T ∧ closed y’ by
       (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
        \\ fs [closed_def])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ imp_res_tac LIST_REL_LENGTH
      \\ qpat_x_assum ‘(_ ≃ e2) T’ $ irule_at Any
      \\ fs [eval_wh_If]
      \\ rw [] \\ gvs [])
    \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
    \\ qpat_x_assum ‘letrec_spec _ h y’ assume_tac
    \\ disch_then drule \\ fs []
    \\ imp_res_tac letrec_spec_freevars
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
    \\ qpat_x_assum ‘letrec_spec _ h2 _’ assume_tac
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
     (rw [] \\ qpat_x_assum ‘letrec_spec _ h y’ assume_tac
      \\ last_x_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
      \\ disch_then drule
      \\ imp_res_tac letrec_spec_freevars
      \\ ‘(y ≃ y) T ∧ closed y’ by
       (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
        \\ fs [closed_def])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ irule eval_wh_Error_bisim
      \\ first_x_assum $ irule_at $ Pos $ last
      \\ fs [eval_wh_Seq])
    \\ imp_res_tac letrec_spec_freevars
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
      \\ qpat_x_assum ‘letrec_spec _ h y’ assume_tac
      \\ imp_res_tac letrec_spec_freevars
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
    \\ imp_res_tac letrec_spec_freevars
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
      \\ qpat_x_assum ‘letrec_spec _ h y’ assume_tac
      \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
      \\ disch_then drule \\ fs []
      \\ imp_res_tac letrec_spec_freevars
      \\ ‘(y ≃ y) T ∧ closed y’ by
       (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
        \\ fs [closed_def])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ imp_res_tac LIST_REL_LENGTH
      \\ fs [eval_wh_Prim] \\ rw [] \\ fs [])
    \\ last_assum irule \\ fs []
    \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
    \\ disch_then drule \\ fs []
    \\ imp_res_tac letrec_spec_freevars
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
      \\ drule_all MEM_LIST_REL1 \\ strip_tac
      \\ disch_then drule \\ fs []
      \\ rename [‘letrec_spec _ x y’]
      \\ imp_res_tac letrec_spec_freevars
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
      \\ drule_all MEM_LIST_REL \\ rw []
      \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
      \\ disch_then drule \\ fs []
      \\ imp_res_tac letrec_spec_freevars
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
      \\ drule_all MEM_LIST_REL \\ strip_tac
      \\ ‘closed x ∧ ¬error_Atom (eval_wh_to (k − 1) x)’ by (res_tac \\ fs [])
      \\ ‘eval_wh_to (k − 1) x ≠ wh_Diverge’ by (CCONTR_TAC \\ fs [] \\ res_tac \\ fs [])
      \\ last_assum $ qspec_then ‘k-1’ mp_tac \\ fs []
      \\ goal_assum drule \\ fs []
      \\ imp_res_tac letrec_spec_freevars
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
    \\ imp_res_tac letrec_spec_freevars
    \\ ‘(y ≃ y) T ∧ closed y ∧ closed x’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def,EVERY_MEM] \\ res_tac \\ fs [])
    \\ disch_then drule \\ fs []
    \\ Cases_on ‘eval_wh_to (k − 1) x’ \\ fs [])
QED

Theorem eval_forward_letrec_spec_rev:
  info_ok i ⇒
  eval_forward T (λx y. letrec_spec i y x)
Proof
  simp [Once letrec_spec_sym,SF ETA_ss,eval_forward_letrec_spec]
QED

Theorem Letrec_spec_equiv_closed:
  ∀i x.
    info_ok i ∧ call_with_arg F i x ∧
    closed (mk_letrec T i x) ∧
    closed (mk_letrec F i x) ⇒
    (mk_letrec F i x ≃ mk_letrec T i x) T
Proof
  rw [] \\ irule eval_forward_imp_bisim \\ fs []
  \\ qexists_tac ‘letrec_spec i’
  \\ irule_at Any letrec_spec_Switch
  \\ fs [letrec_spec_refl,eval_forward_letrec_spec,eval_forward_letrec_spec_rev]
QED

Theorem FDIFF_SING:
  FDIFF f {x} = f \\ x
Proof
  fs [FDIFF_def,fmap_EXT,DRESTRICT_DEF,DOMSUB_FAPPLY_NEQ]
  \\ gvs [EXTENSION]
QED

Theorem Apps_append:
  ∀xs ys x. Apps x (xs ++ ys) = Apps (Apps x xs) ys
Proof
  Induct \\ fs [Apps_def]
QED

Theorem call_with_arg_Apps:
  ∀xs x.
    call_with_arg b i x ∧
    EVERY (call_with_arg b i) xs ⇒
    call_with_arg b i (Apps x xs)
Proof
  Induct \\ fs [Apps_def] \\ rw []
  \\ last_x_assum irule \\ fs []
  \\ irule call_with_arg_App \\ fs []
QED

Triviality call_with_arg_T_with:
  ∀b i x.
    call_with_arg b i x ⇒ b ⇒
    call_with_arg b (i with <|const := c; rhs := rhs1|>) x
Proof
  Induct_on ‘call_with_arg’
  \\ rpt strip_tac
  \\ simp [Once call_with_arg_cases]
  \\ gvs [] \\ gvs [EVERY_MEM]
  \\ metis_tac []
QED

Theorem call_with_arg_subst:
  ∀b i rhs m.
    call_with_arg b i rhs ∧ i.arg ∉ FDOM m ∧ i.fname ∉ FDOM m ∧
    (∀n v. FLOOKUP m n = SOME v ⇒ closed v) ∧ b ⇒
    call_with_arg b i (subst m rhs)
Proof
  Induct_on ‘call_with_arg’
  \\ rpt strip_tac
  \\ gvs [subst_def]
  >-
   (fs [subst_Apps,subst_def,FLOOKUP_DEF]
    \\ irule call_with_arg_Apps_Var \\ fs [])
  >-
   (Cases_on ‘FLOOKUP m n’ \\ fs []
    >- (irule call_with_arg_Var \\ fs [])
    \\ irule call_with_arg_closed \\ fs [SF SFY_ss])
  >-
   (irule call_with_arg_Lam \\ fs []
    \\ first_x_assum irule
    \\ fs [DOMSUB_FLOOKUP_THM,SF SFY_ss])
  >- (irule call_with_arg_App \\ fs [SF SFY_ss])
  >- (irule call_with_arg_Prim \\ fs [SF SFY_ss,EVERY_MEM,MEM_MAP,PULL_EXISTS])
  \\ rpt (irule call_with_arg_closed \\ fs [] \\ NO_TAC)
  \\ irule call_with_arg_Letrec
  \\ fs [SF SFY_ss,EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]
  \\ rw []
  >-
   (last_x_assum $ drule_then strip_assume_tac
    \\ first_assum irule \\ fs []
    \\ fs [FDIFF_def,FLOOKUP_DRESTRICT,SF SFY_ss])
  \\ first_assum irule \\ fs []
  \\ fs [FDIFF_def,FLOOKUP_DRESTRICT,SF SFY_ss]
QED

Triviality FST_INTRO:
  (λ(p1,p2). p1) = FST
Proof
  fs [FUN_EQ_THM,FORALL_PROD]
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

Theorem Letrec_specialise:
  call_with_arg T i rhs ∧ i.arg = v ∧ i.args = vs ∧ i.fname = f ∧
  EVERY (λx. f ∉ freevars x) xs ∧
  EVERY (λx. f ∉ freevars x) ys ∧
  ALL_DISTINCT [v; w; f] ∧ ~MEM w vs ∧
  LENGTH xs = LENGTH vs ∧
  DISJOINT {v; w; f} (boundvars rhs)
  ⇒
  Letrec [(f,Lams (vs ++ [v]) rhs)]
    (Apps (Var f) (xs ++ [Var w] ++ ys))
  ≅
  Letrec [(f,Lams (vs ++ [v]) (subst1 v (Var w) rhs))]
    (Apps (Var f) (xs ++ [Var w] ++ ys))
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
  \\ qabbrev_tac ‘rhs1 = (subst (FDIFF (m \\ f) (set vs ∪ {v})) rhs)’
  \\ ‘subst (FDIFF (m \\ f) (set vs ∪ {v})) (subst1 v (Var w) rhs) =
      subst1 v c rhs1’ by
   (gvs [Abbr‘rhs1’]
    \\ irule subst_subst1_lemma
    \\ gvs [FRANGE_DEF,PULL_EXISTS,DOMSUB_FAPPLY_THM,FLOOKUP_DEF,closed_def]
    \\ gvs [FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM])
  \\ pop_assum $ rewrite_tac o single
  \\ qabbrev_tac ‘i2 = i with <| rhs := rhs1 ; const := c |>’
  \\ qpat_abbrev_tac ‘x = Apps _ _’
  \\ qspecl_then [‘i2’,‘x’] mp_tac Letrec_spec_equiv_closed
  \\ fs [mk_letrec_def,mk_fun_def,Abbr‘i2’,info_ok_def]
  \\ disch_then irule
  \\ fs [DIFF_SUBSET]
  \\ conj_tac
  >-
   (gvs [Abbr‘x’,BIGUNION_SUBSET,MEM_MAP,PULL_EXISTS,closed_def]
    \\ rw [] \\ DEP_REWRITE_TAC [freevars_subst]
    \\ fs [DIFF_SUBSET]
    \\ gvs [FRANGE_DEF,PULL_EXISTS,DOMSUB_FAPPLY_THM,FLOOKUP_DEF,closed_def]
    \\ gvs [SUBSET_DEF]
    \\ metis_tac [])
  \\ DEP_REWRITE_TAC [freevars_subst]
  \\ fs [DIFF_SUBSET]
  \\ conj_asm1_tac
  >-
   (gvs [Abbr‘rhs1’]
    \\ DEP_REWRITE_TAC [freevars_subst]
    \\ fs [DIFF_SUBSET]
    \\ gvs [FRANGE_DEF,PULL_EXISTS,DOMSUB_FAPPLY_THM,FLOOKUP_DEF,closed_def]
    \\ gvs [FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM]
    \\ gvs [SUBSET_DEF]
    \\ metis_tac [])
  \\ conj_tac >- gvs [SUBSET_DEF]
  \\ conj_tac
  >-
   (gvs [Abbr‘x’]
    \\ simp [Once Apps_append]
    \\ irule call_with_arg_Apps
    \\ conj_tac
    >-
     (rw [EVERY_MEM]
      \\ irule call_with_arg_closed
      \\ gvs [MEM_MAP,closed_def,BIGUNION_SUBSET]
      \\ DEP_REWRITE_TAC [freevars_subst]
      \\ gvs [FRANGE_DEF,PULL_EXISTS,DOMSUB_FAPPLY_THM,FLOOKUP_DEF,closed_def,EVERY_MEM]
      \\ res_tac \\ fs [EXTENSION,SUBSET_DEF] \\ metis_tac [])
    \\ simp [Once call_with_arg_cases]
    \\ disj1_tac
    \\ irule_at Any EQ_REFL \\ fs [])
  \\ irule call_with_arg_T_with \\ fs [Abbr‘rhs1’]
  \\ irule call_with_arg_subst \\ fs [SF SFY_ss]
  \\ gvs [FLOOKUP_DEF,FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM]
QED

val _ = export_theory();
