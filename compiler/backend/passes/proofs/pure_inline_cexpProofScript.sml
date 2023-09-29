(*
  Inlining optimization proofs for cexp
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     combinTheory mlmapTheory indexedListsTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_exp_relTheory
     pure_alpha_equivTheory pure_miscTheory pure_congruenceTheory
     pure_letrec_seqTheory pure_demandTheory pure_dead_letProofTheory;
open pure_cexpTheory pure_varsTheory balanced_mapTheory pureLangTheory;
open pure_inlineTheory pure_inline_cexpTheory pure_letrec_spec_cexpProofTheory
     pure_barendregtTheory pure_freshenProofTheory var_setTheory;

val _ = new_theory "pure_inline_cexpProof";

Definition crhs_to_rhs_def:
  crhs_to_rhs (cExp e) = (Exp $ exp_of e) ∧
  crhs_to_rhs (cRec e) = (Rec $ exp_of e)
End

(* xs and m have the same elements *)
Definition memory_inv_def:
  memory_inv xs m (ns:(mlstring,unit) map # num) ⇔
    { explode a | ∃e. lookup m a = SOME e } = set (MAP FST xs) ∧
    EVERY (λ(v,r). v ∈ set_of ns ∧ ∃e:'a cexp. avoid_set_ok ns e ∧ r = Exp (exp_of e)) xs ∧
    ∀v e. (lookup m v = SOME e) ⇒
          ∃e1. e = cExp (e1:'a cexp) ∧ cheap e1 ∧
               MEM (explode v, (crhs_to_rhs e)) xs ∧
               avoid_set_ok ns e1 ∧
               NestedCase_free e1 ∧
               letrecs_distinct (exp_of e1) ∧
               cexp_wf e1
End

Theorem inline_list_empty:
  (inline_list m ns cl h l = ([], ns1)) ⇒ l = []
Proof
  rw []
  \\ Cases_on `l`
  >- fs []
  \\ fs [inline_def]
  \\ Cases_on `inline m ns cl h h'`
  \\ gvs []
  \\ Cases_on `inline_list m r cl h t`
  \\ gvs []
QED

Theorem no_shadowing_Apps_EVERY:
  ∀e es.
    no_shadowing (Apps e es) ⇒
    no_shadowing e ∧ EVERY no_shadowing es
Proof
  strip_tac
  \\ Induct_on `es` using SNOC_INDUCT
  >- fs [Apps_def]
  \\ fs [Apps_def,SNOC,Apps_SNOC,EVERY_SNOC]
QED

Theorem no_shadowing_Letrec_EVERY:
  ∀e xs.
    no_shadowing (Letrec xs e) ⇒
      no_shadowing e ∧
      EVERY (λ(v, e). no_shadowing e) xs ∧
      DISJOINT (boundvars e) (set (MAP FST xs))
Proof
  strip_tac
  \\ strip_tac
  \\ simp [Once no_shadowing_cases]
  \\ strip_tac
  \\ fs [DISJOINT_SYM,EVERY_MEM]
  \\ rw []
  \\ Cases_on `e'`
  \\ last_x_assum $ qspec_then `(q,r)` assume_tac
  \\ gvs []
QED

Theorem list_subst_rel_Apps:
  (∀ts us l t1 u1.
    list_subst_rel l t1 u1 ∧
    LIST_REL (list_subst_rel l) ts us ⇒
    list_subst_rel l (Apps t1 ts) (Apps u1 us))
Proof
  Induct
  >- fs [Apps_def]
  \\ fs [Apps_def,PULL_EXISTS]
  \\ rw []
  \\ last_x_assum irule
  \\ fs []
  \\ irule list_subst_rel_App
  \\ fs []
QED

Theorem memory_inv_APPEND:
  memory_inv xs m ns ∧
  map_ok m ∧ cheap e1 ∧
  avoid_set_ok ns e1 ∧ explode v ∈ set_of ns ∧
  NestedCase_free e1 ∧
  letrecs_distinct (exp_of e1) ∧
  cexp_wf e1 ∧
  ¬MEM (explode v) (MAP FST xs) ⇒
  memory_inv (xs ++ [(explode v,Exp (exp_of e1))]) (insert m v (cExp e1)) ns
Proof
  gvs [memory_inv_def]
  \\ rw []
  >- (
    fs [EXTENSION,mlmapTheory.lookup_insert,AllCaseEqs()]
    \\ metis_tac []
  )
  \\ gvs [mlmapTheory.lookup_insert,AllCaseEqs()]
  \\ gvs [crhs_to_rhs_def,exp_of_def]
  \\ first_x_assum $ irule_at Any \\ fs []
QED

(*
Theorem memory_inv_APPEND_Rec:
  memory_inv xs m ∧
  map_ok m ∧
  ¬MEM (explode v) (MAP FST xs) ⇒
  memory_inv (xs ++ [(explode v,Rec (exp_of e1))]) (insert m v (cRec e1))
Proof
  gvs [memory_inv_def]
  \\ rw []
  >- (
    fs [EXTENSION,mlmapTheory.lookup_insert,AllCaseEqs()]
    \\ metis_tac []
  )
  \\ gvs [mlmapTheory.lookup_insert,AllCaseEqs()]
  \\ gvs [crhs_to_rhs_def,exp_of_def]
QED
*)

Theorem DISJOINT_boundvars_Apps:
  ∀s e es.
    DISJOINT (boundvars (Apps e es)) s ⇒
    DISJOINT (boundvars e) s ∧
    EVERY (λx. DISJOINT (boundvars x) s) es
Proof
  strip_tac
  \\ strip_tac
  \\ Induct using SNOC_INDUCT
  >- fs [Apps_def]
  \\ fs [Apps_def,SNOC,Apps_SNOC]
  \\ strip_tac
  \\ strip_tac
  \\ simp [boundvars_def]
  \\ gvs []
  \\ fs [EVERY_SNOC]
QED

Theorem EVERY_DISJOINT_MEM:
  ∀s xs.
    (∀s1. MEM s1 xs ⇒ DISJOINT s1 s) ⇒
    EVERY (λx. DISJOINT x s) xs
Proof
  rw []
  \\ simp [EVERY_MEM]
QED

Theorem SND_intro:
  (λ(p1, p2). p2) = SND
Proof
  simp [FUN_EQ_THM,FORALL_PROD]
QED

Theorem branch_vars_eq_lemma:
  ∀bs cs.
    LENGTH bs = LENGTH cs ⇒
    MAP (λx. FST (SND x)) (MAP2 (λ(v,vs,_) e. (v,vs,e)) bs cs) =
      MAP (λx. FST (SND x)) bs
Proof
  Induct_on `bs`
  >- fs []
  \\ Cases_on `h`
  \\ Cases_on `r`
  \\ Cases_on `cs`
  >- fs [FST,SND,MAP2]
  \\ fs [FST,SND,MAP2]
QED

Theorem inline_list_size_EQ:
  ∀l l1 ns.
    inline_list m ns cl h l = (l1, ns1) ⇒
      LENGTH l = LENGTH l1
Proof
  Induct_on `l`
  >- fs [inline_def]
  \\ rw [inline_def]
  \\ Cases_on `inline m ns cl h h'`
  \\ gvs []
  \\ Cases_on `inline_list m r cl h l`
  \\ gvs []
  \\ last_x_assum irule
  \\ gvs []
  \\ qexists `r`
  \\ gvs []
QED

Theorem list_subst_rel_lets_for:
  list_subst_rel xs a b ⇒
  list_subst_rel xs
    (lets_for c v vs a)
    (lets_for c v vs b)
Proof
  rw []
  \\ Induct_on `vs`
  >- fs [lets_for_def]
  \\ rw []
  \\ Cases_on `h`
  \\ fs [lets_for_def]
  \\ irule list_subst_rel_App
  \\ irule_at Any list_subst_rel_Lam
  \\ fs [list_subst_rel_refl]
QED

Theorem lets_for_no_shadowing:
  ∀vs a.
    no_shadowing (lets_for c v vs a) ⇒
    no_shadowing a
Proof
  strip_tac
  \\ Induct_on `vs`
  >- fs [lets_for_def]
  \\ rw []
  \\ Cases_on `h`
  \\ fs [lets_for_def]
QED

Theorem lets_for_DISJOINT:
  ∀vs a s.
    DISJOINT (boundvars (lets_for c v vs a)) s ⇒
    DISJOINT (boundvars a) s
Proof
  strip_tac
  \\ Induct_on `vs`
  >- fs [lets_for_def]
  \\ rw []
  \\ Cases_on `h`
  \\ fs [lets_for_def]
QED

Theorem App_Let_notin:
  v ∉ freevars e ⇒
  (App (Let v a body) e ≅? Let v a (App body e)) b
Proof
  rw []
  \\ simp [Once exp_eq_sym]
  \\ irule exp_eq_trans
  \\ irule_at Any Let_App
  \\ irule exp_eq_App_cong
  \\ gvs [exp_eq_refl]
  \\ irule Let_not_in_freevars
  \\ fs []
QED

(*
Theorem make_Let1_lemma:
  ∀acc_v acc_e a es vs body.
    EVERY (λe.
      DISJOINT (set (MAP explode acc_v)) (freevars (exp_of e)) ∧
      DISJOINT (set (MAP explode vs)) (freevars (exp_of e))) es ∧
    LENGTH acc_v = LENGTH acc_e ⇒
    ((exp_of (App a (Lets a acc_v acc_e (Lam a vs body)) es)) ≅?
    (exp_of (make_Let_GO acc_v acc_e a es vs body))) b
Proof
  recInduct make_Let_GO_ind
  \\ reverse $ rw []
  >- (
    gvs [exp_of_def,Apps_def,Lams_def,Lets_def,make_Let_GO_def,exp_eq_refl]
    \\ irule exp_eq_Apps_cong
    \\ rw []
    >- (
      Induct_on `es` \\ gvs [exp_eq_refl]
    )
    \\ irule exp_eq_App_cong \\ gvs [exp_eq_refl]
    \\ last_x_assum mp_tac
    \\ last_x_assum mp_tac
    \\ last_x_assum mp_tac
    \\ qid_spec_tac `acc_e`
    \\ Induct_on `acc_v` \\ gvs [exp_eq_refl,Lams_def,Lets_def,exp_of_def]
    \\ rw []
    \\ Cases_on `acc_e` \\ gvs []
    \\ gvs [Lets_def,exp_of_def]
    \\ irule exp_eq_Let_cong
    \\ gvs [exp_eq_refl]
    \\ last_x_assum $ irule_at Any
    \\ gvs [EVERY_MEM]
  )
  >- gvs [exp_of_def,Apps_def,Lams_def,Lets_def,make_Let_GO_def,exp_eq_refl]
  >- (
    gvs [exp_of_def,Apps_def,Lams_def,Lets_def,make_Let_GO_def,exp_eq_refl]
    \\ last_x_assum mp_tac
    \\ qid_spec_tac `acc_e`
    \\ Induct_on `acc_v` \\ gvs [exp_eq_refl,Lams_def,Lets_def,exp_of_def]
    \\ rw []
    \\ Cases_on `acc_e` \\ gvs []
    \\ gvs [Lets_def,exp_of_def]
    \\ irule exp_eq_Let_cong
    \\ gvs [exp_eq_refl]
    \\ last_x_assum $ irule_at Any
    \\ gvs [EVERY_MEM]
  )
  \\ gvs [exp_of_def,Apps_def,Lams_def,Lets_def,make_Let_GO_def,exp_eq_refl]
  \\ irule exp_eq_trans
  \\ last_x_assum $ irule_at Any
  \\ conj_tac
  >- gvs [EVERY_MEM]
  \\ irule exp_eq_Apps_cong
  \\ gvs [LIST_REL_MAP]
  \\ rw []
  >- (
    Induct_on `es` \\ gvs [exp_eq_refl]
  )
  \\ last_x_assum mp_tac
  \\ last_x_assum mp_tac
  \\ last_x_assum mp_tac
  \\ last_x_assum mp_tac
  \\ last_x_assum mp_tac
  \\ qid_spec_tac `acc_v`
  \\ qid_spec_tac `acc_e`
  \\ Induct
  >- gvs [exp_eq_refl,Lets_def,exp_of_def,Apps_def,Lams_def]
  \\ rw []
  \\ Cases_on `acc_v`
  >- gvs [exp_eq_refl,Lets_def,exp_of_def,Apps_def,Lams_def]
  \\ rw []
  \\ gvs [Lets_def,exp_of_def,Apps_def,Lams_def]
  \\ last_x_assum $ drule
  \\ rw []
  \\ irule exp_eq_trans
  \\ irule_at Any App_Let_notin
  \\ gvs []
  \\ irule exp_eq_Let_cong
  \\ gvs [exp_eq_refl]
  \\ last_x_assum $ irule_at Any
  \\ gvs [EVERY_MEM]
QED

Theorem make_Let1_eq_SOME:
  no_shadowing (exp_of e) ∧
  DISJOINT (boundvars (exp_of e)) (freevars (exp_of e)) ∧
  make_Let1 e = SOME x ⇒
  ((exp_of e) ≅? (exp_of x)) b
Proof
  rw []
  \\ Cases_on `e` \\ gvs [make_Let1_def]
  \\ Cases_on `c` \\ gvs [make_Let1_def]
  \\ Induct_on `l` \\ gvs [make_Let_GO_def]
  >- (
    Cases_on `l'`
    \\ gvs [make_Let_GO_def,exp_eq_refl,exp_of_def,Apps_def,Lams_def,Lets_def]
  )
  \\ rw []
  \\ Induct_on `l'` \\ gvs [make_Let_GO_def]
  >- gvs [Lams_def,make_Let_GO_def,exp_eq_refl,exp_of_def,Apps_def,Lets_def]
  \\ rw []
  \\ gvs [exp_of_def,Apps_def,Lams_def]
  \\ gvs [make_Let_GO_def,exp_eq_refl,exp_of_def,Apps_def,Lams_def,Lets_def]
  \\ irule exp_eq_trans
  \\ irule_at Any make_Let1_lemma
  \\ gvs [exp_of_def,Apps_def,Lams_def,Lets_def,make_Let_GO_def,exp_eq_refl]
QED
*)

Theorem exp_of_Lets:
  ∀vs xs b.
    LENGTH vs = LENGTH xs ⇒
    exp_of (Lets a (ZIP (vs,xs)) b) =
    Lets (ZIP (MAP explode vs, MAP exp_of xs)) (exp_of b)
Proof
  Induct \\ Cases_on ‘xs’
  \\ gvs [pure_inline_cexpTheory.Lets_def,pure_letrecProofTheory.Lets_def]
  \\ fs [exp_of_def]
QED

Theorem Lets_append:
  ∀xs ys b. Lets (xs ++ ys) b = Lets xs (Lets ys b)
Proof
  Induct \\ fs [pure_letrecProofTheory.Lets_def,FORALL_PROD]
QED

Theorem subst_Lets:
  ∀xs vs f b.
    LENGTH xs = LENGTH vs ∧
    EVERY (λe. DISJOINT (set vs) (freevars e)) xs
    ⇒
    subst f (Lets (ZIP (vs,xs)) b) =
    Lets (ZIP (vs, MAP (subst f) xs)) (subst (FDIFF f (set vs)) b)
Proof
  Induct using SNOC_INDUCT
  \\ Cases_on ‘vs’ using SNOC_CASES
  \\ fs [pure_letrecProofTheory.Lets_def]
  \\ rw [] \\ gvs [ZIP_SNOC,MAP_SNOC]
  \\ fs [SNOC_APPEND,Lets_append,pure_letrecProofTheory.Lets_def]
  \\ last_x_assum $ DEP_REWRITE_TAC o single
  \\ fs [subst_def] \\ gvs [EVERY_MEM]
  \\ AP_TERM_TAC
  \\ rename [‘n ∉ freevars y’]
  \\ ‘subst f y = subst (FDIFF f (set l)) y’ by
   (irule pure_exp_lemmasTheory.subst_FDIFF'
    \\ gvs [IN_DISJOINT] \\ metis_tac [])
  \\ fs [GSYM pure_miscTheory.FDIFF_SING,FDIFF_FDIFF]
QED

Theorem eval_wh_Lets:
  ∀xs b.
    EVERY closed (MAP SND xs) ⇒
    eval_wh (Lets xs b) =
    eval_wh (subst (FEMPTY |++ xs) b)
Proof
  Induct using SNOC_INDUCT
  \\ fs [pure_letrecProofTheory.Lets_def,FUPDATE_LIST]
  \\ PairCases \\ fs [MAP_SNOC,EVERY_SNOC]
  \\ fs [SNOC_APPEND,Lets_append]
  \\ fs [pure_letrecProofTheory.Lets_def,FUPDATE_LIST,subst_def]
  \\ fs [eval_wh_App]
  \\ fs [eval_wh_Lam,bind_def,FLOOKUP_SIMP]
  \\ fs [FOLDL_APPEND] \\ rw []
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC [pure_exp_lemmasTheory.subst_subst_DISJOINT_FUNION]
  \\ fs [TO_FLOOKUP,PULL_EXISTS,DOMSUB_FLOOKUP_THM]
  \\ rw []
  >-
   (fs [GSYM FUPDATE_LIST]
    \\ imp_res_tac FLOOKUP_LUPDATE
    \\ fs [EVERY_MEM,PULL_EXISTS,MEM_MAP]
    \\ res_tac \\ fs [closed_def])
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ gvs [TO_FLOOKUP,FLOOKUP_FUNION,FUN_EQ_THM]
  \\ rw [DOMSUB_FLOOKUP_THM]
  \\ gvs [FLOOKUP_SIMP]
  \\ CASE_TAC \\ fs []
QED

Theorem Apps_Lams_eq_Lets:
  ∀es vs b.
    LENGTH vs = LENGTH es ∧
    EVERY (λe. DISJOINT (set vs) (freevars e)) es ⇒
    Apps (Lams vs b) es ≅ Lets (ZIP (vs,es)) b
Proof
  rw [exp_eq_def] \\ rw [bind_def]
  \\ irule eval_wh_IMP_app_bisimilarity
  \\ rpt $ irule_at Any IMP_closed_subst
  \\ fs [TO_FLOOKUP]
  \\ fs [subst_Apps,subst_Lams]
  \\ DEP_REWRITE_TAC [eval_wh_Apps_Lams]
  \\ DEP_REWRITE_TAC [subst_Lets] \\ fs []
  \\ DEP_REWRITE_TAC [eval_wh_Lets]
  \\ DEP_REWRITE_TAC [MAP_SND_ZIP] \\ fs []
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS] \\ rw []
  \\ irule IMP_closed_subst
  \\ fs [SUBSET_DEF,MEM_MAP,PULL_EXISTS,TO_FLOOKUP]
  \\ metis_tac []
QED

Theorem Apps_Lams_eq_Lets_freevars:
  ∀es vs b.
    LENGTH vs = LENGTH es ∧
    EVERY (λe. DISJOINT (set vs) (freevars e)) es ⇒
    freevars (Lets (ZIP (vs,es)) b) = freevars (Apps (Lams vs b) es)
Proof
  fs [freevars_Apps,freevars_Lams]
  \\ Induct using SNOC_INDUCT
  \\ Cases_on ‘vs’ using SNOC_CASES
  \\ fs [pure_letrecProofTheory.Lets_def,EVERY_SNOC]
  \\ gvs [ZIP_SNOC]
  \\ fs [SNOC_APPEND,Lets_append,pure_letrecProofTheory.Lets_def] \\ rw []
  \\ last_x_assum $ DEP_REWRITE_TAC o single \\ fs []
  \\ gvs [EVERY_MEM] \\ gvs [EXTENSION]
  \\ rw [] \\ eq_tac \\ rw [] \\ gvs [] \\ gvs [IN_DISJOINT]
  \\ metis_tac []
QED

Theorem Apps_Lams_eq_Lets_boundvars:
  ∀es vs b.
    LENGTH vs = LENGTH es ∧
    EVERY (λe. DISJOINT (set vs) (freevars e)) es ⇒
    boundvars (Lets (ZIP (vs,es)) b) = boundvars (Apps (Lams vs b) es)
Proof
  fs [boundvars_Apps,boundvars_Lams]
  \\ Induct using SNOC_INDUCT
  \\ Cases_on ‘vs’ using SNOC_CASES
  \\ fs [pure_letrecProofTheory.Lets_def,EVERY_SNOC]
  \\ gvs [ZIP_SNOC]
  \\ fs [SNOC_APPEND,Lets_append,pure_letrecProofTheory.Lets_def] \\ rw []
  \\ last_x_assum $ DEP_REWRITE_TAC o single \\ fs []
  \\ gvs [EVERY_MEM] \\ gvs [EXTENSION]
  \\ rw [] \\ eq_tac \\ rw [] \\ gvs [] \\ gvs [IN_DISJOINT]
  \\ metis_tac []
QED

Triviality NOT_NONE_UNIT:
  (x ≠ NONE) ⇔ x = SOME ()
Proof
  Cases_on ‘x’ \\ fs []
QED

Theorem avoid_set_ok_subset:
  avoid_set_ok ns e ∧ set_of ns ⊆ set_of ns1 ∧ vars_ok ns1 ⇒ avoid_set_ok ns1 e
Proof
  PairCases_on ‘ns’
  \\ PairCases_on ‘ns1’
  \\ fs [avoid_set_ok_def,set_of_def,SUBSET_DEF,PULL_EXISTS]
  \\ fs [vars_ok_def] \\ rw []
  \\ gvs [mlmapTheory.lookup_thm,TO_FLOOKUP]
  \\ res_tac \\ gvs [NOT_NONE_UNIT]
QED

Theorem memory_inv_subset:
  memory_inv xs m ns ∧
  set_of ns ⊆ set_of ns1 ∧
  vars_ok ns1
  ⇒
  memory_inv xs m ns1
Proof
  fs [memory_inv_def] \\ rw [] \\ res_tac \\ fs [EVERY_MEM,FORALL_PROD]
  \\ gvs [SUBSET_DEF]
  \\ metis_tac [avoid_set_ok_subset,SUBSET_DEF]
QED

Theorem avoid_set_ok_imp_vars_ok:
  avoid_set_ok ns ce ⇒ vars_ok ns
Proof
  fs [avoid_set_ok_def]
QED

Theorem letrecs_distinct_Apps[simp]:
  ∀es e.
    letrecs_distinct (Apps e es) ⇔
      letrecs_distinct e ∧ EVERY letrecs_distinct es
Proof
  Induct
  \\ asm_rewrite_tac [Apps_def,EVERY_DEF,pure_letrecProofTheory.letrecs_distinct_def]
  \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs []
QED

Theorem avoid_set_ok_App[simp]:
  avoid_set_ok ns (App a e es) ⇔
  avoid_set_ok ns e ∧ EVERY (avoid_set_ok ns) es
Proof
  fs [avoid_set_ok_def,exp_of_def,MEM_MAP,boundvars_Apps,EVERY_MEM]
  \\ metis_tac []
QED

val set_of_lemma = inline_ind
  |> Q.SPEC ‘λm ns cl h x. ∀t ns1.
    (inline m ns cl h x) = (t, ns1) ∧ vars_ok ns ⇒
    set_of ns ⊆ set_of ns1 ∧ vars_ok ns1’
  |> Q.SPEC ‘λm ns cl h es. ∀ts ns1.
    (inline_list m ns cl h es) = (ts, ns1) ∧ vars_ok ns ⇒
    set_of ns ⊆ set_of ns1 ∧ vars_ok ns1’
  |> CONV_RULE (DEPTH_CONV BETA_CONV);

Theorem inline_set_of:
  ^(set_of_lemma |> concl |> rand)
Proof
  match_mp_tac set_of_lemma
  \\ rpt conj_tac \\ rpt gen_tac \\ rpt disch_tac \\ rpt gen_tac \\ rpt disch_tac
  >~ [`Var _ _`] >- (
    gvs [inline_def]
    \\ Cases_on `lookup m v` \\ gvs [list_subst_rel_refl]
    \\ Cases_on `x` \\ gvs [list_subst_rel_refl]
    \\ Cases_on `is_Lam c` \\ gvs [memory_inv_def,list_subst_rel_refl,exp_of_def]
    \\ Cases_on ‘cl = 0’ \\ gvs []
  )
  >~ [`App _ _ _`] >-
   (pop_assum mp_tac
    \\ rewrite_tac [inline_def] \\ simp_tac (srw_ss()) [LET_THM]
    \\ rpt (pairarg_tac \\ fs [])
    \\ fs [AllCaseEqs()]
    \\ rw [] \\ fs []
    \\ rpt (pairarg_tac \\ fs [])
    \\ gvs [AllCaseEqs()]
    \\ imp_res_tac fresh_cexp_subset
    \\ imp_res_tac SUBSET_TRANS \\ fs []
    \\ imp_res_tac SUBSET_TRANS)
  \\ gvs [inline_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac SUBSET_TRANS
  \\ gvs [AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac SUBSET_TRANS
QED

Definition mem_inv_def:
  mem_inv m ns =
    ∀n v. lookup m n = SOME v ⇒ ∃e. avoid_set_ok ns e ∧ v = cExp e
End

Theorem mem_inv_subset:
  mem_inv m ns ∧ set_of ns ⊆ set_of ns1 ∧ vars_ok ns1 ⇒ mem_inv m ns1
Proof
  fs [mem_inv_def] \\ rw []
  \\ res_tac \\ gvs []
  \\ irule avoid_set_ok_subset
  \\ metis_tac []
QED

Definition fake_avoid_set_ok_def:
  fake_avoid_set_ok = avoid_set_ok
End

Theorem avoid_set_ok_change_exp:
  (allvars (exp_of e) = allvars (exp_of e1)) ⇒
  avoid_set_ok ns e ⇒ avoid_set_ok ns e1
Proof
  rewrite_tac [avoid_set_ok_def] \\ metis_tac [allvars_thm]
QED

Theorem TO_IN_set_of:
  vars_ok ns ⇒
  (lookup (FST ns) v = SOME () ⇔ explode v ∈ set_of ns)
Proof
  PairCases_on ‘ns’ \\ gvs [vars_ok_def,set_of_def]
  \\ gvs [TO_FLOOKUP,mlmapTheory.lookup_thm,NOT_NONE_UNIT] \\ rw []
QED

Theorem avoid_set_ok_allvars =
  avoid_set_ok_def |> REWRITE_RULE [GSYM allvars_thm];

Theorem avoid_set_ok_subset_exp:
  (allvars (exp_of e1) ⊆ allvars (exp_of e) ∪ set_of ns) ⇒
  avoid_set_ok ns e ⇒ avoid_set_ok ns e1
Proof
  fs [avoid_set_ok_allvars,TO_IN_set_of,SF CONJ_ss, SUBSET_DEF]
  \\ metis_tac []
QED

Theorem allvars_Apps:
  allvars (Apps x xs) = allvars x ∪ BIGUNION (set (MAP allvars xs))
Proof
  fs [allvars_thm,boundvars_Apps]
  \\ gvs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ gvs []
  \\ gvs [MEM_MAP,allvars_thm,PULL_EXISTS]
  \\ metis_tac []
QED

Theorem allvars_Prim:
  allvars (Prim x xs) = BIGUNION (set (MAP allvars xs))
Proof
  fs [allvars_thm,EXTENSION,MEM_MAP,allvars_thm]
QED

Theorem allvars_Lams:
  allvars (Lams vs x) = allvars x ∪ set vs
Proof
  fs [allvars_thm,boundvars_Lams]
  \\ gvs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ gvs []
  \\ metis_tac []
QED

Theorem allvars_Lets:
  allvars (Lets xs x) = allvars x ∪ set (MAP FST xs) ∪
                        BIGUNION (set (MAP allvars (MAP SND xs)))
Proof
  Induct_on ‘xs’
  \\ fs [pure_letrecProofTheory.Lets_def] \\ PairCases
  \\ fs [pure_letrecProofTheory.Lets_def]
  \\ gvs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ gvs []
  \\ metis_tac []
QED

Theorem avoid_set_ok_Lam:
  avoid_set_ok ns (Lam a vs e) ⇔
  avoid_set_ok ns e ∧ set (MAP explode vs) ⊆ set_of ns
Proof
  fs [avoid_set_ok_allvars,exp_of_def,allvars_Lams]
  \\ eq_tac \\ rw [] \\ gvs []
  >-
  (gvs [SUBSET_DEF]
   \\ PairCases_on ‘ns’ \\ gvs [vars_ok_def,set_of_def]
   \\ gvs [TO_FLOOKUP,mlmapTheory.lookup_thm,NOT_NONE_UNIT] \\ rw []
   \\ qexists_tac ‘implode x’ \\ fs [])
  \\ gvs [SUBSET_DEF]
  \\ PairCases_on ‘ns’ \\ gvs [vars_ok_def,set_of_def]
  \\ gvs [TO_FLOOKUP,mlmapTheory.lookup_thm,NOT_NONE_UNIT] \\ rw []
  \\ res_tac \\ gvs []
QED

Theorem avoid_set_ok_Prim:
  avoid_set_ok ns (Prim a p es) ⇔
  EVERY (avoid_set_ok ns) es ∧ vars_ok ns
Proof
  fs [avoid_set_ok_allvars,exp_of_def,allvars_Prim,EVERY_MEM,PULL_EXISTS,MEM_MAP]
  \\ gvs [SF CONJ_ss] \\ metis_tac []
QED

Theorem avoid_set_ok_Let:
  avoid_set_ok ns (Let a v e1 e2) ⇔
  explode v ∈ set_of ns ∧
  avoid_set_ok ns e1 ∧
  avoid_set_ok ns e2
Proof
  fs [avoid_set_ok_allvars,exp_of_def,SF DNF_ss]
  \\ Cases_on ‘vars_ok ns’ \\ fs [TO_IN_set_of]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
QED

Theorem allvars_if:
  allvars (if b then Seq Fail x else x) = allvars x
Proof
  rw [] \\ fs []
QED

Theorem allvars_IfDisj:
  ∀xs v e. w ∈ allvars (IfDisj v xs e) ⇒ w = explode v ∨ w ∈ allvars e
Proof
  Induct \\ fs [IfDisj_def,Disj_def]
  \\ PairCases \\ fs [Disj_def] \\ metis_tac []
QED

Theorem allvars_IfDisj_alt:
  ∀xs v e. w ∈ allvars e ⇒ w ∈ allvars (IfDisj v xs e)
Proof
  Induct \\ fs [IfDisj_def,Disj_def]
  \\ PairCases \\ fs [Disj_def] \\ metis_tac []
QED

Theorem allvars_lets_for:
  ∀xs v e c.
    allvars (lets_for c v xs e) =
    allvars e ∪ set (MAP (K v) xs) ∪ set (MAP SND xs)
Proof
  Induct  \\ fs [lets_for_def,FORALL_PROD]
  \\ gvs [EXTENSION] \\ metis_tac []
QED

Theorem avoid_set_ok_Case:
  avoid_set_ok ns (Case a e v rows e1) ⇔
  explode v ∈ set_of ns ∧
  avoid_set_ok ns e ∧
  EVERY (λ(c,vs,x). avoid_set_ok ns x ∧ EVERY (λv. explode v ∈ set_of ns) vs) rows ∧
  (∀vs x. e1 = SOME (vs,x) ⇒ avoid_set_ok ns x)
Proof
  fs [avoid_set_ok_allvars,exp_of_def,SF DNF_ss,allvars_if]
  \\ Cases_on ‘vars_ok ns’ \\ fs [TO_IN_set_of]
  \\ Cases_on ‘explode v ∈ set_of ns’ \\ fs []
  \\ simp [AC CONJ_ASSOC CONJ_COMM]
  \\ irule (METIS_PROVE [] “(a ⇒ (b ⇔ b1)) ⇒ (a ∧ b ⇔ a ∧ b1)”)
  \\ strip_tac
  \\ Induct_on ‘rows’ \\ fs [rows_of_def]
  >-
   (CASE_TAC \\ gvs [] \\ CASE_TAC \\ gvs []
    \\ metis_tac [allvars_IfDisj,allvars_IfDisj_alt])
  \\ fs [rows_of_def,FORALL_PROD]
  \\ rpt gen_tac
  \\ gvs [SF DNF_ss,allvars_lets_for]
  \\ gvs [o_DEF,indexedListsTheory.MAPi_EQ_MAP |> SIMP_RULE std_ss [SF ETA_ss]]
  \\ gvs [MEM_MAP,PULL_EXISTS,EVERY_MEM]
  \\ metis_tac []
QED

Theorem avoid_set_ok_Letrec:
  avoid_set_ok ns (Letrec a xs x) ⇔
  (set (MAP explode (MAP FST xs)) ⊆ set_of ns ∧
   EVERY (avoid_set_ok ns) (MAP SND xs) ∧
   avoid_set_ok ns x)
Proof
  fs [avoid_set_ok_allvars,exp_of_def,SF DNF_ss,MEM_MAP,PULL_EXISTS, FORALL_PROD, EVERY_MEM]
  \\ fs [TO_IN_set_of,SUBSET_DEF,SF CONJ_ss]
  \\ gvs [MEM_MAP,FORALL_PROD,EXISTS_PROD,EVERY_MEM,PULL_EXISTS]
  \\ Cases_on ‘vars_ok ns’ \\ fs [TO_IN_set_of]
  \\ metis_tac []
QED

Triviality App_Lam_to_Lets_allvars:
  App_Lam_to_Lets exp = SOME exp1 ⇒
  allvars (exp_of exp) = allvars (exp_of exp1)
Proof
  Cases_on ‘exp’ \\ gvs [App_Lam_to_Lets_def]
  \\ Cases_on ‘c’ \\ gvs [App_Lam_to_Lets_def] \\ rw []
  \\ fs [exp_of_def,allvars_Apps,NOT_LESS]
  \\ drule miscTheory.LESS_EQ_LENGTH \\ rw [] \\ gvs []
  \\ pop_assum $ assume_tac o GSYM \\ fs []
  \\ fs [TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]
  \\ DEP_REWRITE_TAC [exp_of_Lets]
  \\ fs [allvars_Lets]
  \\ DEP_REWRITE_TAC [MAP_FST_ZIP,MAP_SND_ZIP]
  \\ fs [SF ETA_ss,allvars_Lams]
  \\ gvs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ gvs []
  \\ metis_tac []
QED

Theorem inline_list_length:
  ∀es m ns c h xs ns1.
    inline_list m ns c h es = (xs,ns1) ⇒ LENGTH es = LENGTH xs
Proof
  Induct \\ fs [inline_def] \\ rw [] \\ rpt (pairarg_tac \\ gvs [])
  \\ res_tac \\ fs []
QED

Triviality MAP2_lemma:
  ∀vbs vbs1.
    LENGTH vbs = LENGTH vbs1 ⇒
    MAP FST (MAP2 (λ(v,_) x. (v,x)) vbs vbs1) = MAP FST vbs ∧
    MAP SND (MAP2 (λ(v,_) x. (v,x)) vbs vbs1) = vbs1
Proof
  Induct \\ Cases_on ‘vbs1’ \\ gvs []
  \\ PairCases \\ fs []
QED

Theorem Case_lemma:
  ∀ns ns1a ns2 ns1 bs bs2.
    LENGTH bs = LENGTH bs2 ∧
    set_of ns ⊆ set_of ns1a ∧
    set_of ns1a ⊆ set_of ns2 ∧
    set_of ns2 ⊆ set_of ns1 ∧ vars_ok ns1 ∧
    EVERY (avoid_set_ok ns2) bs2 ∧
    EVERY (λ(c,vs,x).
             avoid_set_ok ns x ∧ EVERY (λv. explode v ∈ set_of ns) vs) bs
    ⇒
    EVERY (λ(c,vs,x).
             avoid_set_ok ns1 x ∧ EVERY (λv. explode v ∈ set_of ns1) vs)
          (MAP2 (λ(v,vs,_) e. (v,vs,e)) bs bs2)
Proof
  ntac 4 gen_tac
  \\ Induct \\ Cases_on ‘bs2’ \\ fs [FORALL_PROD]
  \\ rpt gen_tac \\ rpt disch_tac
  \\ gvs []
  \\ gvs [EVERY_MEM]
  \\ irule_at Any avoid_set_ok_subset
  \\ qexists_tac ‘ns2’ \\ fs []
  \\ gvs [SUBSET_DEF]
QED

val avoid_set_ok_lemma = inline_ind
  |> Q.SPEC ‘λm ns cl h x. ∀t ns1.
    (inline m ns cl h x) = (t, ns1) ∧
    mem_inv m ns ∧ map_ok m ∧
    avoid_set_ok ns x ⇒
    fake_avoid_set_ok ns1 t’
  |> Q.SPEC ‘λm ns cl h es. ∀ts ns1.
    (inline_list m ns cl h es) = (ts, ns1) ∧
    mem_inv m ns ∧ map_ok m ∧
    EVERY (avoid_set_ok ns) es ⇒
    EVERY (fake_avoid_set_ok ns1) ts’
  |> CONV_RULE (DEPTH_CONV BETA_CONV);

Theorem inline_avoid_set_ok:
  ^(avoid_set_ok_lemma |> concl |> rand)
Proof
  match_mp_tac avoid_set_ok_lemma
  \\ rpt conj_tac \\ rpt gen_tac \\ rpt disch_tac \\ rpt gen_tac \\ rpt disch_tac
  \\ gvs [inline_def]
  >~ [‘Var’] >-
   (gvs [fake_avoid_set_ok_def,AllCaseEqs()]
    \\ gvs[ mem_inv_def] \\ res_tac \\ fs [])
  >~ [‘App’] >-
   (rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ gvs [fake_avoid_set_ok_def]
    \\ imp_res_tac avoid_set_ok_imp_vars_ok
    \\ imp_res_tac inline_set_of \\ gvs []
    \\ imp_res_tac avoid_set_ok_subset \\ gvs [EVERY_MEM,SF SFY_ss]
    \\ imp_res_tac mem_inv_subset \\ gvs []
    \\ rpt (gen_tac \\ metis_tac [avoid_set_ok_subset,SUBSET_TRANS])
    \\ last_x_assum irule
    \\ drule_all fresh_cexp_subset
    \\ gvs [avoid_set_ok_avoid_ok]
    \\ strip_tac \\ gvs []
    \\ irule_at Any mem_inv_subset \\ fs []
    \\ first_assum $ irule_at Any \\ fs []
    \\ fs [pure_freshenTheory.freshen_cexp_def]
    \\ drule $ cj 1 freshen_aux_avoid_ok \\ fs []
    \\ gvs [EVERY_MEM]
    \\ gvs [mem_inv_def] \\ res_tac \\ fs [] \\ gvs []
    \\ gvs [GSYM avoid_set_ok_avoid_ok]
    \\ match_mp_tac avoid_set_ok_change_exp
    \\ imp_res_tac App_Lam_to_Lets_allvars \\ fs [])
  >~ [‘Let’] >-
   (rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ gvs [fake_avoid_set_ok_def]
    \\ imp_res_tac avoid_set_ok_imp_vars_ok
    \\ imp_res_tac inline_set_of \\ gvs []
    \\ imp_res_tac avoid_set_ok_subset \\ gvs [EVERY_MEM,SF SFY_ss]
    \\ imp_res_tac mem_inv_subset \\ gvs []
    \\ gvs [avoid_set_ok_Let]
    \\ ‘map_ok (heuristic_insert m h v e1)’ by
     (Cases_on ‘heuristic_insert m h v e1 = m’ >- fs []
      \\ fs [heuristic_insert_def,AllCaseEqs(),mlmapTheory.insert_thm])
    \\ qsuff_tac ‘mem_inv (heuristic_insert m h v e1) ns3’
    >- (rw [] \\ fs [] \\ metis_tac [avoid_set_ok_subset])
    \\ Cases_on ‘heuristic_insert m h v e1 = m’ >- fs []
    \\ fs [heuristic_insert_def,AllCaseEqs()]
    \\ gvs [mem_inv_def,lookup_insert,mlmapTheory.lookup_insert]
    \\ rw [] \\ res_tac \\ fs [] \\ gvs [])
  >~ [‘Lam’] >-
   (rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ gvs [fake_avoid_set_ok_def]
    \\ gvs [avoid_set_ok_Lam]
    \\ imp_res_tac avoid_set_ok_imp_vars_ok
    \\ imp_res_tac inline_set_of \\ gvs []
    \\ gvs [SUBSET_DEF])
  >~ [‘Letrec’] >-
   (rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ gvs [fake_avoid_set_ok_def,avoid_set_ok_Letrec]
    \\ ‘map_ok (heuristic_insert_Rec m h vbs)’ by
     (Cases_on ‘heuristic_insert_Rec m h vbs = m’ >- fs []
      \\ fs [heuristic_insert_Rec_def,AllCaseEqs(),mlmapTheory.insert_thm]
      \\ rpt (CASE_TAC \\ gvs [mlmapTheory.insert_thm])) \\ fs []
    \\ drule inline_list_length \\ fs [MAP2_lemma]
    \\ strip_tac
    \\ irule_at Any SUBSET_TRANS
    \\ first_assum $ irule_at $ Pos hd
    \\ imp_res_tac avoid_set_ok_imp_vars_ok
    \\ imp_res_tac inline_set_of \\ gvs []
    \\ imp_res_tac SUBSET_TRANS \\ fs []
    \\ conj_tac
    >- (gvs [EVERY_MEM] \\ rw [] \\ res_tac
        \\ metis_tac [avoid_set_ok_subset,SUBSET_REFL])
    \\ last_x_assum irule
    \\ irule_at Any avoid_set_ok_subset \\ qexists_tac ‘ns’ \\ fs []
    \\ drule mem_inv_subset
    \\ disch_then $ qspec_then ‘ns1'’ mp_tac
    \\ impl_tac >- metis_tac []
    \\ Cases_on ‘heuristic_insert_Rec m h vbs = m’ >- fs []
    \\ rw []
    \\ fs [heuristic_insert_Rec_def,AllCaseEqs(),mlmapTheory.insert_thm]
    \\ rpt (CASE_TAC \\ gvs [mlmapTheory.insert_thm])
    \\ gvs [mem_inv_def]
    \\ gvs [mlmapTheory.lookup_insert] \\ rw []
    \\ res_tac \\ gvs []
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ ‘avoid_set_ok ns1' r’ by metis_tac [avoid_set_ok_subset]
    \\ pop_assum mp_tac
    \\ match_mp_tac avoid_set_ok_subset_exp
    \\ irule SUBSET_TRANS
    \\ drule_then (irule_at Any) specialise_allvars
    \\ simp_tac std_ss [SUBSET_DEF,IN_UNION,SF DNF_ss,IN_INSERT]
    \\ gvs [])
  >~ [‘Prim’] >-
   (rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ gvs [fake_avoid_set_ok_def,avoid_set_ok_Prim]
    \\ imp_res_tac inline_set_of \\ fs [])
  >~ [‘Case’] >-
   (rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ gvs [fake_avoid_set_ok_def]
    \\ rename [‘inline_list m ns1a cl h’]
    \\ gvs [avoid_set_ok_Case]
    \\ imp_res_tac avoid_set_ok_imp_vars_ok
    \\ imp_res_tac inline_set_of \\ gvs []
    \\ imp_res_tac avoid_set_ok_subset \\ gvs []
    \\ imp_res_tac mem_inv_subset \\ gvs []
    \\ ‘explode v ∈ set_of ns1’ by gvs [SUBSET_DEF] \\ fs []
    \\ imp_res_tac inline_list_length \\ fs []
    \\ ‘EVERY (avoid_set_ok ns1a) (MAP (λ(v,vs,e). e) bs)’ by
      (gvs [EVERY_MEM,EXISTS_PROD,PULL_EXISTS,MEM_MAP]
       \\ rw [] \\ res_tac \\ fs []
       \\ metis_tac [avoid_set_ok_subset]) \\ fs []
    \\ irule Case_lemma \\ gvs []
    \\ last_x_assum $ irule_at $ Pos hd
    \\ fs [] \\ metis_tac [SUBSET_TRANS])
  \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
  \\ gvs [fake_avoid_set_ok_def]
  \\ last_x_assum $ irule_at Any
  \\ imp_res_tac avoid_set_ok_imp_vars_ok
  \\ imp_res_tac inline_set_of \\ gvs []
  \\ imp_res_tac avoid_set_ok_subset \\ gvs [EVERY_MEM,SF SFY_ss]
  \\ imp_res_tac mem_inv_subset \\ gvs []
  \\ metis_tac [avoid_set_ok_subset,SUBSET_REFL]
QED

Theorem inline_wf:
  inline m vars cl h ce = (ce',vars') ∧
  vars_ok vars ∧ NestedCase_free ce ∧ cexp_wf ce ∧ letrecs_distinct (exp_of ce)
  ⇒ NestedCase_free ce' ∧ cexp_wf ce' ∧ letrecs_distinct (exp_of ce') ∧
    freevars (exp_of ce') = freevars (exp_of ce) ∧
    cns_arities ce' ⊆ cns_arities ce
Proof
  cheat (* inline_wf *)
QED

Theorem inline_list_wf:
  inline_list m vars cl h ce = (ce',vars') ∧
  vars_ok vars ∧ EVERY NestedCase_free ce ∧ EVERY cexp_wf ce ∧
  EVERY letrecs_distinct (MAP exp_of ce)
  ⇒ EVERY NestedCase_free ce' ∧ EVERY cexp_wf ce' ∧
    EVERY letrecs_distinct (MAP exp_of ce') ∧
    LIST_REL (λce ce'. freevars (exp_of ce') = freevars (exp_of ce) ∧
                       cns_arities ce' ⊆ cns_arities ce) ce ce'
Proof
  cheat (* inline_list_wf *)
QED

Theorem list_subst_rel_Lams:
  ∀l t u w. list_subst_rel l t u ⇒ list_subst_rel l (Lams w t) (Lams w u)
Proof
  Induct_on ‘w’ \\ fs [Lams_def] \\ rw []
  \\ irule list_subst_rel_Lam
  \\ res_tac \\ fs []
QED

Theorem letrecs_distinct_Lams:
  ∀vs e. letrecs_distinct (Lams vs e) ⇔ letrecs_distinct e
Proof
  Induct \\ fs [Lams_def]
  \\ fs [EVERY_MEM,pure_letrecProofTheory.letrecs_distinct_def]
QED

Theorem no_shadowing_Lams_e:
  ∀vs e. no_shadowing (Lams vs e) ⇒ no_shadowing e
Proof
  Induct \\ fs [Lams_def]
QED

Theorem boundvars_Lets:
  boundvars (Lets binds e) =
    set (MAP FST binds) ∪ BIGUNION (set $ MAP (boundvars o SND) binds) ∪ boundvars e
Proof
  Induct_on `binds` >> rw[pure_letrecProofTheory.Lets_def] >>
  PairCases_on `h` >> gvs[pure_letrecProofTheory.Lets_def] >>
  rw[EXTENSION] >> metis_tac[]
QED

Theorem allvars_Lets:
  allvars (Lets binds e) =
    set (MAP FST binds) ∪ BIGUNION (set $ MAP (allvars o SND) binds) ∪ allvars e
Proof
  Induct_on `binds` >> rw[pure_letrecProofTheory.Lets_def] >>
  PairCases_on `h` >> gvs[pure_letrecProofTheory.Lets_def] >>
  rw[EXTENSION] >> metis_tac[]
QED

Theorem unique_boundvars_Lets:
  unique_boundvars (Lets binds e) ⇔
    unique_boundvars e ∧
    EVERY unique_boundvars (MAP SND binds) ∧
    ALL_DISTINCT (MAP FST binds) ∧
    list_disjoint (set (MAP FST binds) :: boundvars e :: MAP (boundvars o SND) binds)
Proof
  Induct_on `binds` >> rw[unique_boundvars_def, pure_letrecProofTheory.Lets_def] >>
  PairCases_on `h` >> gvs[pure_letrecProofTheory.Lets_def] >>
  simp[unique_boundvars_def, list_disjoint_cons, boundvars_Lets] >>
  eq_tac >> rw[] >> gvs[]
  >- (gvs[EVERY_MEM] >> metis_tac[DISJOINT_SYM])
  >- (gvs[EVERY_MEM] >> metis_tac[])
  >- (gvs[EVERY_MEM] >> metis_tac[])
  >- (gvs[EVERY_MEM] >> metis_tac[DISJOINT_SYM])
  >- (gvs[EVERY_MEM] >> metis_tac[DISJOINT_SYM])
QED

Theorem freevars_Lets_SUBSET:
  freevars (Lets binds e) ⊆
    (freevars e DIFF set (MAP FST binds)) ∪
      BIGUNION (set $ MAP (freevars o SND) binds)
Proof
  Induct_on `binds` >> rw[pure_letrecProofTheory.Lets_def] >>
  PairCases_on `h` >> gvs[pure_letrecProofTheory.Lets_def] >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem IMP_barendregt_Lets:
  barendregt e ∧ EVERY barendregt (MAP SND binds) ∧
  ALL_DISTINCT (MAP FST binds) ∧
  DISJOINT (boundvars e)
    (set (MAP FST binds) ∪ BIGUNION (set $ MAP (allvars o SND) binds)) ∧
  (∀l mid r. binds = l ++ [mid] ++ r ⇒
    DISJOINT (boundvars (SND mid))
      (allvars e ∪ set (MAP FST binds) ∪
        BIGUNION (set $ MAP (allvars o SND) (l ++ r))) ∧
    DISJOINT (freevars (SND mid)) (set (MAP FST binds)))
  ⇒ barendregt (Lets binds e)
Proof
  reverse $ rw[barendregt_def, unique_boundvars_Lets, SF ETA_ss] >>
  gvs[MEM_MAP, PULL_EXISTS, AC CONJ_ASSOC CONJ_COMM, SF DNF_ss]
  >- (
    irule DISJOINT_SUBSET >> irule_at Any freevars_Lets_SUBSET >>
    rw[boundvars_Lets]
    >- simp[DISJOINT_ALT]
    >- (
      gvs[MEM_MAP] >>
      dxrule_at Concl $ iffLR MEM_SING_APPEND >> strip_tac >> gvs[] >>
      rpt $ first_x_assum $ qspec_then `a` mp_tac >>
      simp[allvars_thm] >> gvs[DISJOINT_ALT] >> metis_tac[]
      )
    >- gvs[DISJOINT_ALT]
    >- (
      gvs[MEM_MAP] >>
      dxrule_at Concl $ iffLR MEM_SING_APPEND >> strip_tac >> gvs[] >>
      rpt $ first_x_assum $ qspec_then `a` mp_tac >> simp[]
      )
    >- (
      gvs[MEM_MAP] >>
      dxrule_at Concl $ iffLR MEM_SING_APPEND >> strip_tac >> gvs[]
      >- (
        dxrule_at Concl $ iffLR MEM_SING_APPEND >> strip_tac >> gvs[] >>
        rpt $ first_x_assum $ qspec_then `a' ++ [y] ++ c'` mp_tac >> rw[] >>
        gvs[allvars_thm] >> metis_tac[DISJOINT_SYM]
        )
      >- gvs[barendregt_def]
      >- (
        dxrule_at Concl $ iffLR MEM_SING_APPEND >> strip_tac >> gvs[] >>
        rpt $ first_x_assum $ qspec_then `a` mp_tac >> rw[] >>
        gvs[allvars_thm] >> metis_tac[DISJOINT_SYM]
        )
      )
    >- (gvs[MEM_MAP, allvars_thm] >> metis_tac[DISJOINT_SYM])
    )
  >- (
    rw[list_disjoint_cons, list_disjoint]
    >- (
      gvs[MAP_EQ_APPEND, MEM_MAP] >> rename1 `l ++ [mid] ++ r` >>
      rpt $ first_x_assum $ drule_at Any >> rw[allvars_thm] >>
      simp[Once DISJOINT_SYM]
      )
    >- (
      rw[EVERY_MEM] >> gvs[MEM_MAP] >>
      last_x_assum drule >> rw[allvars_thm] >> simp[Once DISJOINT_SYM]
      )
    >- (
      rw[EVERY_MEM] >> gvs[MEM_MAP] >>
      dxrule_at Concl $ iffLR MEM_SING_APPEND >> strip_tac >> gvs[] >>
      rpt $ first_x_assum $ qspec_then `a` mp_tac >> simp[]
      )
    )
  >- gvs[EVERY_MEM, barendregt_def]
QED

Theorem barendregt_Lets_lemma_lemma[local]:
  barendregt (Apps (Lams vs b) ys) /\ LENGTH vs = LENGTH ys ⇒
  barendregt (Lets (ZIP (vs,ys)) b)
Proof
  rw[barendregt_Apps, barendregt_Lams] >> gvs[allvars_Lams, boundvars_Lams] >>
  irule IMP_barendregt_Lets >> simp[MAP_ZIP] >> conj_tac >> rpt gen_tac >> strip_tac
  >- (
    gvs[ZIP_EQ_APPEND] >> rename1 `le ++ me ++ re` >>
    rename1 `LENGTH rx = LENGTH re` >>
    rename1 `LENGTH mx = LENGTH me` >>
    rename1 `LENGTH lx = LENGTH le` >>
    `mx = [FST mid] ∧ me = [SND mid]` by (
      Cases_on `mx` >> Cases_on `me` >> gvs[] >>
      Cases_on `t` >> Cases_on `t'` >> gvs[]) >>
    gvs[AC CONJ_ASSOC CONJ_COMM] >>
    first_x_assum $ qspec_then `le` assume_tac >> gvs[] >>
    gvs[MEM_MAP, PULL_EXISTS, SF DNF_ss] >> gvs[allvars_thm, SF DNF_ss] >>
    ntac 2 $ simp[Once DISJOINT_SYM] >> gvs[MEM_ZIP, MEM_EL, PULL_EXISTS]
    )
  >- (
    gvs[MEM_MAP, PULL_EXISTS] >> simp[Once DISJOINT_SYM]
    )
QED

Theorem barendregt_Lets_lemma[local]:
  barendregt (Apps (Apps (Lams vs b) ys) xs) ∧ LENGTH vs = LENGTH ys ⇒
  barendregt (Apps (Lets (ZIP (vs,ys)) b) xs)
Proof
  simp[Once barendregt_Apps] >> strip_tac >> simp[Once barendregt_Apps] >>
  irule_at Any barendregt_Lets_lemma_lemma >> goal_assum dxrule >>
  gvs[boundvars_Apps, boundvars_Lams, boundvars_Lets,
      allvars_Apps, allvars_Lams, allvars_Lets] >>
  gvs[MEM_MAP, PULL_EXISTS, MAP_ZIP] >>
  reverse conj_tac >> rpt gen_tac >> strip_tac
  >- (
    first_x_assum drule >> strip_tac >> gvs[SF DNF_ss] >>
    rw[MEM_ZIP] >> gvs[] >> metis_tac[DISJOINT_SYM, EL_MEM]
    ) >>
  rw[] >> gvs[MEM_ZIP] >>
  dxrule_at Concl $ iffLR MEM_SING_APPEND >> strip_tac >> gvs[] >>
  first_x_assum $ qspec_then `a` mp_tac >> rw[] >>
  gvs[MEM_EL] >> metis_tac[DISJOINT_SYM]
QED

Theorem letrecs_distinct_Lets:
  ∀vs xs x.
    EVERY letrecs_distinct xs ∧ letrecs_distinct x ∧ LENGTH vs = LENGTH xs ⇒
    letrecs_distinct (Lets (ZIP (vs,xs)) x)
Proof
  Induct \\ Cases_on ‘xs’
  \\ fs [pure_letrecProofTheory.Lets_def] \\ rw []
  \\ fs [pure_letrecProofTheory.letrecs_distinct_def]
QED

Theorem NestedCase_free_SmartApp:
  ∀a f xs. NestedCase_free (SmartApp a f xs) = NestedCase_free (App a f xs)
Proof
  simp[NestedCase_free_def, SF ETA_ss]
QED

Theorem NestedCase_free_Lets:
  ∀vs xs x a.
    NestedCase_free x ∧ EVERY NestedCase_free xs ∧ LENGTH vs = LENGTH xs ⇒
    NestedCase_free (Lets a (ZIP (vs,xs)) x)
Proof
  Induct \\ Cases_on ‘xs’ \\ fs [Lets_def,NestedCase_free_def]
QED

Theorem cexp_wf_Lets:
  ∀vs xs x a.
    cexp_wf x ∧ EVERY cexp_wf xs ∧ LENGTH vs = LENGTH xs ⇒
    cexp_wf (Lets a (ZIP (vs,xs)) x)
Proof
  Induct \\ Cases_on ‘xs’ \\ fs [Lets_def,cexp_wf_def]
QED

Theorem avoid_set_ok_switch:
  avoid_set_ok ns (y:'a cexp) ∧
  freevars (exp_of x) ∪ boundvars (exp_of x) ⊆
  freevars (exp_of y) ∪ boundvars (exp_of y) ⇒
  avoid_set_ok ns (x:'a cexp)
Proof
  fs [avoid_set_ok_def,SUBSET_DEF]
  \\ metis_tac []
QED

Theorem avoid_set_ok_SmartApp:
  avoid_set_ok ns (SmartApp a f xs) = avoid_set_ok ns (App a f xs)
Proof
  rw [SmartApp_def]
  \\ gvs [NULL_EQ]
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ Cases_on ‘f’ \\ gvs [dest_App_def] \\ rw []
  \\ eq_tac \\ rw []
QED

Theorem avoid_set_ok_Lets:
  avoid_set_ok ns (App a2 (Lam a1 vs x) xs) ∧ LENGTH xs = LENGTH vs ⇒
  avoid_set_ok ns (Lets a (ZIP (vs,xs)) x)
Proof
  rewrite_tac [avoid_set_ok_def]
  \\ rpt strip_tac \\ asm_rewrite_tac []
  \\ first_x_assum irule
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac ‘xs’
  \\ qid_spec_tac ‘vs’
  \\ gvs [exp_of_def,boundvars_Apps,boundvars_Lams]
  \\ Induct \\ Cases_on ‘xs’ \\ gvs [Lets_def,exp_of_def]
  \\ metis_tac []
QED

Theorem avoid_set_ok_set_of:
  avoid_set_ok ns e ⇒
  boundvars (exp_of e) ⊆ set_of ns ∧
  freevars (exp_of e) ⊆ set_of ns
Proof
  PairCases_on ‘ns’
  \\ gvs [avoid_set_ok_def,set_of_def,SUBSET_DEF,vars_ok_def]
  \\ gvs [TO_FLOOKUP,GSYM mlmapTheory.lookup_thm] \\ rw []
  \\ first_x_assum $ qspec_then ‘x’ mp_tac \\ fs [] \\ rw []
  \\ qexists_tac ‘implode x’ \\ fs []
QED

Theorem memory_inv_imp_set_of:
  memory_inv xs m ns ⇒
  set (MAP FST xs) ⊆ set_of ns ∧
  freevars_of xs ⊆ set_of ns ∧
  vars_of xs ⊆ set_of ns
Proof
  strip_tac
  \\ fs [memory_inv_def]
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ Induct_on ‘xs’ \\ gvs [vars_of_def,freevars_of_def]
  \\ PairCases \\ fs []
  \\ Cases_on ‘h1’ \\ fs []
  \\ gvs [vars_of_def,freevars_of_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ imp_res_tac avoid_set_ok_set_of \\ fs []
QED

Theorem freshen_cexp_disjoint:
  freshen_cexp e ns = (e1,ns1) ∧ avoid_set_ok ns e ∧
  cexp_wf e ∧ NestedCase_free e ∧ letrecs_distinct (exp_of e) ⇒
  DISJOINT (boundvars (exp_of e1)) (set_of ns)
Proof
  strip_tac >> gvs[avoid_set_ok_avoid_ok] >>
  dxrule_all freshen_cexp_freshen_global >> strip_tac >>
  dxrule_all freshen_global_boundvars >> simp[]
QED

Triviality freshen_cexp_disjoint_lemma:
  freshen_cexp e ns = (e1,ns1) ∧ avoid_set_ok ns e ∧
  cexp_wf e ∧ NestedCase_free e ∧ letrecs_distinct (exp_of e) ∧
  s ⊆ set_of ns
  ⇒
  DISJOINT (boundvars (exp_of e1)) s
Proof
  rw []
  \\ drule_all freshen_cexp_disjoint
  \\ fs [IN_DISJOINT,SUBSET_DEF]
  \\ metis_tac []
QED

val lemma = inline_ind
  |> Q.SPEC ‘λm ns cl h x. ∀xs t ns1.
    memory_inv xs m ns ∧
    map_ok m ∧
    avoid_set_ok ns x ∧
    NestedCase_free x ∧
    letrecs_distinct (exp_of x) ∧
    cexp_wf x ∧
    no_shadowing (exp_of x) ∧
    DISJOINT (set (MAP FST xs)) (boundvars (exp_of x)) ∧
    (inline m ns cl h x) = (t, ns1) ⇒
    list_subst_rel xs (exp_of x) (exp_of t)’
  |> Q.SPEC ‘λm ns cl h es. ∀xs ts ns1.
    memory_inv xs m ns ∧
    map_ok m ∧
    EVERY (λx.
             avoid_set_ok ns x ∧
             NestedCase_free x ∧
             letrecs_distinct (exp_of x) ∧
             cexp_wf x) es ∧
    EVERY (λe. no_shadowing (exp_of e)) es ∧
    EVERY (λx. DISJOINT (set (MAP FST xs)) (boundvars (exp_of x))) es ∧
    (inline_list m ns cl h es) = (ts, ns1) ⇒
    LIST_REL (λx t. list_subst_rel xs (exp_of x) (exp_of t)) es ts’
  |> CONV_RULE (DEPTH_CONV BETA_CONV);

Theorem inline_cexp_list_subst_rel:
  ^(lemma |> concl |> rand)
Proof
  match_mp_tac lemma
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  >~ [`Var _ _`] >- (
    Cases_on `inline m ns cl h (Var a v) = (Var a v, ns)`
    >- gvs [list_subst_rel_refl,exp_of_def]
    \\ gvs [inline_def]
    \\ Cases_on `lookup m v` \\ gvs [list_subst_rel_refl]
    \\ Cases_on `x` \\ gvs [list_subst_rel_refl]
    \\ Cases_on `is_Lam c` \\ gvs [memory_inv_def,list_subst_rel_refl,exp_of_def]
    \\ Cases_on ‘cl = 0’ \\ gvs []
    \\ first_assum drule \\ strip_tac \\ fs []
    \\ gvs []
    \\ irule_at Any list_subst_rel_Var
    \\ fs [crhs_to_rhs_def]
    \\ qpat_x_assum ‘MEM _ _’ $ irule_at Any
    \\ qexists_tac ‘exp_of c’ \\ fs [exp_eq_refl]
    \\ qsuff_tac ‘no_shadowing (exp_of c) ∧ boundvars (exp_of c) = {} ∧
                  NestedCase_free c ∧
                  letrecs_distinct (exp_of c) ∧ cexp_wf c’ >- (res_tac \\ fs [])
    \\ fs []
    \\ Cases_on ‘c’ \\ gvs [cheap_def]
    \\ fs [exp_of_def,is_Lam_def,NULL_EQ]
  )
  >~ [`App _ _ _`] >- (
    gvs [inline_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [list_subst_rel_refl,exp_of_def,SF ETA_ss]
    \\ qspecl_then [`set (MAP FST xs)`,`exp_of e`,`MAP exp_of es`]
                   assume_tac DISJOINT_boundvars_Apps
    \\ drule no_shadowing_Apps_EVERY
    \\ strip_tac
    \\ Cases_on `get_Var_name e`
    >- (
      gvs [exp_of_def,SF ETA_ss]
      \\ irule list_subst_rel_Apps
      \\ fs [LIST_REL_MAP,o_DEF]
      \\ last_x_assum $ irule_at Any
      \\ last_x_assum $ irule_at Any
      \\ fs [EVERY_MAP,DISJOINT_SYM,cexp_wf_def]
      \\ fs [EVERY_MEM,pure_letrecProofTheory.letrecs_distinct_def]
      \\ imp_res_tac avoid_set_ok_imp_vars_ok \\ fs []
      \\ imp_res_tac inline_set_of \\ fs []
      \\ irule_at Any avoid_set_ok_subset \\ fs []
      \\ qexists_tac ‘ns’ \\ fs []
      \\ irule_at Any memory_inv_subset \\ fs []
      \\ last_x_assum $ irule_at Any \\ fs []
    )
    \\ gvs []
    \\ Cases_on `lookup m x`
    >- (
      gvs [exp_of_def,SF ETA_ss]
      \\ irule list_subst_rel_Apps
      \\ fs [LIST_REL_MAP,o_DEF]
      \\ last_x_assum $ irule_at Any
      \\ last_x_assum $ irule_at Any
      \\ gvs [memory_inv_def,DISJOINT_SYM]
      \\ fs [EVERY_MAP,DISJOINT_SYM,cexp_wf_def]
      \\ fs [EVERY_MEM,pure_letrecProofTheory.letrecs_distinct_def,FORALL_PROD]
      \\ imp_res_tac avoid_set_ok_imp_vars_ok \\ fs []
      \\ imp_res_tac inline_set_of \\ fs []
      \\ irule_at Any avoid_set_ok_subset \\ fs []
      \\ qexists_tac ‘ns’ \\ fs []
      >-
       (conj_tac \\ rw []
        >- (gvs [SUBSET_DEF] \\ metis_tac [])
        \\ last_x_assum drule
        \\ metis_tac [avoid_set_ok_subset])
    )
    \\ gvs []
    \\ rename [‘lookup m x = SOME aa’]
    \\ reverse $ Cases_on `aa`
    >- (
      gvs [exp_of_def,SF ETA_ss]
      \\ irule list_subst_rel_Apps
      \\ fs [LIST_REL_MAP,o_DEF]
      \\ last_x_assum $ irule_at Any
      \\ last_x_assum $ irule_at Any
      \\ gvs [memory_inv_def,DISJOINT_SYM]
      \\ fs [EVERY_MAP,DISJOINT_SYM,cexp_wf_def]
      \\ fs [EVERY_MEM,pure_letrecProofTheory.letrecs_distinct_def]
      \\ imp_res_tac avoid_set_ok_imp_vars_ok \\ fs []
      \\ imp_res_tac inline_set_of \\ fs []
      \\ irule_at Any avoid_set_ok_subset \\ fs []
      \\ qexists_tac ‘ns’ \\ fs []
      \\ rw [] \\ first_x_assum drule
      \\ strip_tac \\ gvs []
      \\ irule_at Any avoid_set_ok_subset \\ fs []
      \\ metis_tac []
    )
    \\ gvs []
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [`freshen_cexp _ _ = (q_fresh, r_fresh)`]
    \\ Cases_on `App_Lam_to_Lets q_fresh`
    >- (
      gvs [exp_of_def,SF ETA_ss]
      \\ irule list_subst_rel_Apps
      \\ fs [LIST_REL_MAP,o_DEF]
      \\ last_x_assum $ irule_at Any
      \\ gvs [memory_inv_def,DISJOINT_SYM]
      \\ fs [EVERY_MAP,DISJOINT_SYM]
      \\ irule_at Any list_subst_rel_refl
      \\ fs [EVERY_MAP,DISJOINT_SYM,cexp_wf_def]
      \\ fs [EVERY_MEM,pure_letrecProofTheory.letrecs_distinct_def]
    )
    \\ gvs []
    \\ rename [`inline _ _ _ _ _ = (q_inline, r_inline)`]
    \\ Cases_on `cl = 0`
    >- (
      gvs [exp_of_def,SF ETA_ss]
      \\ irule list_subst_rel_Apps
      \\ fs [LIST_REL_MAP,o_DEF]
      \\ last_x_assum $ irule_at Any
      \\ gvs [memory_inv_def,DISJOINT_SYM]
      \\ fs [EVERY_MAP,DISJOINT_SYM]
      \\ irule_at Any list_subst_rel_refl
      \\ fs [EVERY_MAP,DISJOINT_SYM,cexp_wf_def]
      \\ fs [EVERY_MEM,pure_letrecProofTheory.letrecs_distinct_def]
    )
    \\ gvs []
    \\ Cases_on ‘e’ \\ gvs [get_Var_name_def,exp_of_def]
    \\ rename [‘lookup m v = SOME (cExp c)’]
    \\ first_x_assum drule
    \\ impl_tac >- fs [boundvars_Apps,EVERY_MEM,MEM_MAP,PULL_EXISTS,cexp_wf_def]
    \\ strip_tac
    \\ Cases_on ‘q_fresh’ \\ gvs [App_Lam_to_Lets_def]
    \\ rename [‘App_Lam_to_Lets (App a2 c2 l2)’]
    \\ Cases_on ‘c2’ \\ gvs [App_Lam_to_Lets_def]
    \\ rename [‘App a2 (Lam a3 l3 c3) es2’]
    \\ irule list_subst_rel_trans
    \\ last_x_assum $ irule_at Any
    \\ irule_at Any list_subst_rel_ExpEq
    \\ irule_at (Pos hd) list_subst_rel_Apps
    \\ irule_at (Pos hd) list_subst_rel_VarSimp
    \\ ‘MEM (explode v,Exp (exp_of c)) xs’ by
          (fs [memory_inv_def] \\ res_tac  \\ fs [crhs_to_rhs_def])
    \\ pop_assum $ irule_at Any
    \\ qexists_tac ‘MAP exp_of es1’
    \\ gvs [LIST_REL_MAP]
    \\ rename [‘inline_list m ns cl h es = (es1,ns6)’]
    \\ drule pure_freshenProofTheory.freshen_cexp_correctness
    \\ impl_keep_tac
    >-
     (fs [exp_of_def,cexp_wf_def,SF ETA_ss]
      \\ fs [memory_inv_def] \\ res_tac \\ fs [] \\ gvs []
      \\ drule inline_list_wf
      \\ impl_tac >- (fs [] \\ fs [avoid_set_ok_def])
      \\ strip_tac
      \\ imp_res_tac LIST_REL_LENGTH \\ fs []
      \\ pop_assum $ assume_tac o GSYM
      \\ asm_rewrite_tac [GSYM LENGTH_NIL] \\ fs []
      \\ conj_tac
      >-
       (fs [EVERY_MEM] \\ rw []
        \\ irule avoid_set_ok_subset
        \\ fs [PULL_EXISTS] \\ qexists_tac ‘ns’ \\ fs []
        \\ imp_res_tac inline_set_of \\ fs []
        \\ imp_res_tac avoid_set_ok_imp_vars_ok
        \\ gvs [] \\ res_tac \\ gvs [])
      \\ rewrite_tac [GSYM fake_avoid_set_ok_def]
      \\ irule $ cj 2 inline_avoid_set_ok
      \\ first_x_assum $ irule_at $ Pos $ el 2 \\ fs []
      \\ fs [mem_inv_def] \\ rw []
      \\ res_tac \\ gvs []
    )
    \\ strip_tac
    \\ irule_at Any exp_eq_trans
    \\ fs [exp_of_def,SF ETA_ss]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ fs [NOT_LESS]
    \\ drule miscTheory.LESS_EQ_LENGTH
    \\ strip_tac
    \\ rename [‘es2 = es2a ++ es2b’] \\ gvs []
    \\ pop_assum $ assume_tac o GSYM
    \\ fs [TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]
    \\ rewrite_tac [Apps_append]
    \\ irule_at Any pure_demandTheory.exp_eq_Apps_cong
    \\ fs [LIST_REL_same,exp_eq_refl,exp_of_Lets]
    \\ irule_at Any Apps_Lams_eq_Lets \\ fs []
    \\ fs [freevars_Apps,boundvars_Apps]
    \\ DEP_REWRITE_TAC [Apps_Lams_eq_Lets_boundvars]
    \\ DEP_REWRITE_TAC [Apps_Lams_eq_Lets_freevars]
    \\ gvs [SF CONJ_ss,Apps_append]
    \\ qabbrev_tac ‘app_lam = Apps (Lams (MAP explode l3) (exp_of c3)) (MAP exp_of es2a)’
    \\ gvs [MEM_MAP,PULL_EXISTS,EVERY_MEM]
    \\ irule_at Any barendregt_imp_no_shadowing
    \\ irule_at Any barendregt_Lets_lemma \\ fs []
    \\ irule_at Any memory_inv_subset
    \\ qexists_tac ‘ns’ \\ fs []
    \\ ‘set_of ns ⊆ set_of r_fresh ∧ vars_ok r_fresh ∧ vars_ok ns6’ by
     (imp_res_tac avoid_set_ok_imp_vars_ok \\ fs []
      \\ imp_res_tac $ cj 1 inline_set_of \\ gvs []
      \\ imp_res_tac $ cj 2 inline_set_of
      \\ drule fresh_cexp_subset \\ simp []
      \\ metis_tac [SUBSET_TRANS])
    \\ irule_at Any letrecs_distinct_Lets \\ fs []
    \\ drule freshen_cexp_letrecs_distinct
    \\ impl_tac
    >- (fs [exp_of_def,EVERY_MEM,MEM_MAP,PULL_EXISTS])
    \\ strip_tac
    \\ gvs [exp_of_def]
    \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS,letrecs_distinct_Lams]
    \\ fs [NestedCase_free_SmartApp]
    \\ irule_at Any cexp_wf_Lets \\ fs [EVERY_MEM,cexp_wf_def]
    \\ irule_at Any NestedCase_free_Lets
    \\ fs [EVERY_MEM,avoid_set_ok_SmartApp]
    \\ irule_at Any avoid_set_ok_Lets \\ fs [EVERY_MEM]
    \\ qpat_x_assum ‘avoid_set_ok _ _’ $ irule_at $ Pos hd
    \\ qpat_x_assum ‘barendregt _’ assume_tac
    \\ first_assum mp_tac
    \\ rewrite_tac [barendregt_def]
    \\ strip_tac
    \\ gvs [boundvars_Apps,MEM_MAP,PULL_EXISTS]
    \\ ‘(∀y'. MEM y' es2a ⇒
          DISJOINT (freevars (exp_of y')) (boundvars app_lam))’
          by (unabbrev_all_tac \\ gvs [MEM_MAP,PULL_EXISTS]) \\ fs []
    \\ ‘∀y. MEM y es2a ⇒
            DISJOINT (set (MAP explode l3)) (freevars (exp_of y))’
          by (unabbrev_all_tac \\ gvs [MEM_MAP,PULL_EXISTS]
              \\ gvs [boundvars_Apps,boundvars_Lams]) \\ fs []
    \\ ‘∀y'. MEM y' es2b ⇒
           DISJOINT (freevars (exp_of c3) DIFF set (MAP explode l3))
             (boundvars (exp_of y')) ∧
           ∀y''. MEM y'' es2a ⇒
             DISJOINT (freevars (exp_of y'')) (boundvars (exp_of y'))’
          by (unabbrev_all_tac \\ gvs [MEM_MAP,PULL_EXISTS]
              \\ gvs [boundvars_Apps,boundvars_Lams]) \\ fs [SF SFY_ss]
    \\ ‘DISJOINT (freevars (exp_of c3) DIFF set (MAP explode l3))
          (boundvars app_lam)’
          by (unabbrev_all_tac \\ gvs [MEM_MAP,PULL_EXISTS]
              \\ gvs [boundvars_Apps,boundvars_Lams]) \\ fs []
    \\ ‘∀y'.
           MEM y' es2b ⇒
           DISJOINT (boundvars app_lam) (freevars (exp_of y')) ∧
           ∀y''.
             MEM y'' es2b ⇒
             DISJOINT (boundvars (exp_of y'')) (freevars (exp_of y'))’
          by (unabbrev_all_tac \\ gvs [MEM_MAP,PULL_EXISTS]
              \\ gvs [boundvars_Apps,boundvars_Lams]
              \\ gvs [IN_DISJOINT] \\ metis_tac []) \\ fs [SF SFY_ss]
    \\ ‘memory_inv xs m ns6’ by
         (irule memory_inv_subset \\ fs []
          \\ qexists_tac ‘ns’ \\ fs []
          \\ imp_res_tac SUBSET_TRANS
          \\ imp_res_tac avoid_set_ok_imp_vars_ok
          \\ imp_res_tac inline_set_of)
    \\ drule memory_inv_imp_set_of \\ strip_tac
    \\ ‘avoid_set_ok ns6 (App a c es1)’ by gvs [avoid_set_ok_App,EVERY_MEM]
    \\ drule_then drule freshen_cexp_disjoint_lemma
    \\ fs [cexp_wf_def,EVERY_MEM,exp_of_def,MEM_MAP,PULL_EXISTS]
    \\ disch_then (fn th => ntac 3 (dxrule th))
    \\ fs [exp_of_def,Apps_append,SF ETA_ss]
    \\ fs [boundvars_Apps,MEM_MAP,PULL_EXISTS]
  )
  >~ [`Let _ _ _`] >- (
    gvs [inline_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [exp_of_def]
    \\ fs [cexp_wf_def,pure_letrecProofTheory.letrecs_distinct_def]
    \\ ‘avoid_set_ok ns e1 ∧ avoid_set_ok ns e2’ by
          (fs [avoid_set_ok_def,exp_of_def] \\ metis_tac [])
    \\ fs [heuristic_insert_def]
    \\ Cases_on `cheap e1 ∧ h e1`
    >- (
      irule list_subst_rel_Let
      \\ conj_tac
      >- (
        last_x_assum irule
        \\ fs [cexp_wf_def,pure_letrecProofTheory.letrecs_distinct_def]
        \\ fs [DISJOINT_SYM,memory_inv_def]
      )
      \\ last_x_assum irule
      \\ fs [DISJOINT_SYM]
      \\ fs [mlmapTheory.insert_thm]
      \\ irule_at Any memory_inv_APPEND \\ fs []
      \\ imp_res_tac inline_avoid_set_ok
      \\ imp_res_tac inline_set_of
      \\ imp_res_tac avoid_set_ok_imp_vars_ok
      \\ gvs []
      \\ ‘avoid_set_ok ns3 (Let a v e1 e2)’ by metis_tac [avoid_set_ok_subset]
      \\ ‘explode v ∈ set_of ns3’ by
       (gvs [avoid_set_ok_def,exp_of_def]
        \\ PairCases_on ‘ns3’ \\ gvs [set_of_def,vars_ok_def]
        \\ gvs [GSYM mlmapTheory.lookup_thm, TO_FLOOKUP, NOT_NONE_UNIT]
        \\ first_x_assum $ qspec_then ‘explode v’ mp_tac \\ fs [])
      \\ metis_tac [memory_inv_subset,avoid_set_ok_subset,SUBSET_TRANS]
    )
    \\ full_simp_tac pure_ss []
    \\ pop_assum kall_tac
    \\ fs []
    \\ irule list_subst_rel_App
    \\ reverse $ conj_tac
    >- (
      last_x_assum irule
      \\ fs [DISJOINT_SYM,memory_inv_def,cexp_wf_def]
    )
    \\ irule list_subst_rel_Lam
    \\ last_x_assum irule
    \\ fs [DISJOINT_SYM]
    \\ imp_res_tac inline_set_of
    \\ imp_res_tac avoid_set_ok_imp_vars_ok
    \\ imp_res_tac SUBSET_TRANS
    \\ gvs []
    \\ metis_tac [memory_inv_subset,avoid_set_ok_subset]
  )
  >~ [`Letrec _ _ _`] >- (
    gvs [inline_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [list_subst_rel_refl,exp_of_def]
    \\ fs [pure_letrecProofTheory.letrecs_distinct_def]
    \\ ‘avoid_set_ok ns e ∧ EVERY (avoid_set_ok ns o SND) vbs’ by
      (fs [avoid_set_ok_def,EVERY_MEM,exp_of_def,MEM_MAP,PULL_EXISTS,
           FORALL_PROD,EXISTS_PROD] \\ metis_tac [])
    \\ rename [‘inline_list m ns cl h (MAP SND vbs) = (vbs1,ns2)’]
    \\ imp_res_tac inline_set_of
    \\ imp_res_tac avoid_set_ok_imp_vars_ok
    \\ gvs []
    \\ ‘memory_inv xs m ns2 ∧ avoid_set_ok ns2 e ∧
        EVERY (avoid_set_ok ns2 o SND) vbs’ by
     (irule_at Any memory_inv_subset
      \\ qexists_tac ‘ns’ \\ fs [EVERY_MEM,FORALL_PROD]
      \\ rw [] \\ irule avoid_set_ok_subset \\ fs []
      \\ qexists_tac ‘ns’ \\ fs [EVERY_MEM,FORALL_PROD]
      \\ res_tac \\ fs [])
    \\ drule no_shadowing_Letrec_EVERY \\ strip_tac
    \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]
    \\ gvs [MEM_MAP,PULL_EXISTS,FORALL_PROD,EVERY_MEM,cexp_wf_def]
    \\ Cases_on `heuristic_insert_Rec m h vbs = m`
    >- (
      irule list_subst_rel_Letrec
      \\ last_x_assum $ irule_at Any
      \\ gvs [] \\ fs [DISJOINT_SYM]
      \\ gvs [MAP_MAP_o,o_DEF,FORALL_PROD,LAMBDA_PROD,SND_intro,EVERY_MAP]
      \\ last_x_assum $ qspec_then `xs` mp_tac
      \\ impl_tac >- fs [SF SFY_ss]
      \\ sg `EVERY (λ(p1,p2). DISJOINT (boundvars (exp_of p2)) (set (MAP FST xs))) vbs`
      >-  simp [EVERY_MEM,FORALL_PROD,SF SFY_ss]
      \\ pop_assum mp_tac
      \\ qid_spec_tac `vbs1`
      \\ qid_spec_tac `vbs`
      \\ Induct
      \\ fs [PULL_EXISTS,FORALL_PROD]
    )
    \\ gvs [heuristic_insert_Rec_def,AllCaseEqs()]
    \\ Cases_on `vbs`
    >- gvs []
    \\ reverse $ Cases_on `t` \\ gvs []
    \\ PairCases_on `h'`
    \\ rename [`(w, u)`]
    \\ gvs []
    \\ Cases_on ‘specialise w u’ \\ gvs []
    \\ fs [inline_def]
    \\ pairarg_tac \\ gvs []
    \\ irule list_subst_rel_LetRecIntroExp
    \\ conj_tac
    >- (
      last_x_assum $ irule_at Any
      \\ gvs [DISJOINT_SYM]
    )
    \\ last_x_assum $ irule_at Any
    \\ qexists_tac `(exp_of x)`
    \\ drule specialise_thm
    \\ fs [exp_of_def, GSYM PULL_FORALL]
    \\ impl_tac
    >- (
      fs [Lams_def]
      \\ fs [Once no_shadowing_cases]
    )
    \\ strip_tac \\ fs []
    \\ fs [mlmapTheory.insert_thm]
    \\ irule_at Any memory_inv_APPEND \\ fs []
    \\ rename [‘explode w ∈ set_of ns8’]
    \\ ‘explode w ∈ set_of ns8’ by
     (‘avoid_set_ok ns8 (Letrec a [(w,u)] e)’ by metis_tac [avoid_set_ok_subset]
      \\ gvs [avoid_set_ok_def,exp_of_def]
      \\ PairCases_on ‘ns8’ \\ gvs [set_of_def,vars_ok_def]
      \\ gvs [GSYM mlmapTheory.lookup_thm, TO_FLOOKUP, NOT_NONE_UNIT]
      \\ first_x_assum $ qspec_then ‘explode w’ mp_tac \\ fs [])
    \\ qpat_x_assum ‘no_shadowing (Letrec _ _)’ mp_tac
    \\ simp [Once no_shadowing_cases] \\ strip_tac
    \\ ‘cheap x’ by (imp_res_tac specialise_is_Lam \\ simp [cheap_def])
    \\ once_rewrite_tac [DISJOINT_SYM] \\ asm_rewrite_tac []
    \\ conj_tac
    >-
     (fs [avoid_set_ok_def,SUBSET_DEF] \\ rw [] \\ res_tac \\ fs []
      \\ gvs [] \\ rename [‘FST ns5’] \\ PairCases_on ‘ns5’ \\ fs []
      \\ PairCases_on ‘ns’ \\ gvs [exp_of_def]
      \\ last_x_assum $ qspec_then ‘explode w’ mp_tac
      \\ fs [] \\ gvs [set_of_def,TO_FLOOKUP,PULL_EXISTS]
      \\ gvs [mlmapTheory.lookup_thm,vars_ok_def,NOT_NONE_UNIT])
    \\ drule_all speclise_wf
    \\ strip_tac \\ fs []
    \\ gvs [IN_DISJOINT,SUBSET_DEF]
    \\ CCONTR_TAC \\ gvs [] \\ res_tac \\ metis_tac []
  )
  >~ [`Lam _ _`] >- (
    gvs [inline_def,exp_of_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [exp_of_def]
    \\ irule_at Any list_subst_rel_Lams
    \\ last_x_assum irule
    \\ imp_res_tac no_shadowing_Lams_e
    \\ fs [cexp_wf_def,letrecs_distinct_Lams]
    \\ fs [boundvars_Lams] \\ fs [DISJOINT_SYM]
    \\ fs [avoid_set_ok_def,exp_of_def,boundvars_Lams]
    \\ metis_tac []
  )
  >~ [`Prim _ _ _`] >- (
    gvs [inline_def,exp_of_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [inline_def,exp_of_def]
    \\ irule list_subst_rel_Prim
    \\ fs [LIST_REL_MAP,o_DEF,FORALL_PROD,LIST_REL_MAP2,PULL_EXISTS]
    \\ last_x_assum irule
    \\ fs [EVERY_MEM,cexp_wf_def,
           pure_letrecProofTheory.letrecs_distinct_def,MEM_MAP,PULL_EXISTS]
    \\ rw []
    \\ fs [avoid_set_ok_def,exp_of_def,MEM_MAP,PULL_EXISTS]
    \\ metis_tac []
  )
  >~ [`Case _ _ _ _ _`] >- cheat (* (

    gvs [inline_def]
    \\ Cases_on `inline m ns cl h e`
    \\ gvs []
    \\ Cases_on `inline_list m r cl h (MAP (λ(v, vs, e). e) bs)`
    \\ gvs []
    \\ Cases_on `(case f of
        NONE => (NONE,r')
      | SOME (vs,e') =>
        (λ(e4,ns4). (SOME (vs,e4),ns4)) (inline m r' cl h e'))`
    \\ gvs []
    \\ sg `LENGTH (MAP (λ(v,vs,e). e) bs) = LENGTH q'`
    >- (
      irule inline_list_size_EQ
      \\ metis_tac []
    )
    \\ fs [LENGTH_MAP]
    \\ sg `MAP (λx. FST (SND x)) (MAP2 (λ(v,vs,_) e. (v,vs,e)) bs q') =
      MAP (λx. FST (SND x)) bs`
    >- (
      irule branch_vars_eq_lemma
      \\ gvs []
    )
    \\ gvs [memory_inv_def,list_subst_rel_refl,exp_of_def,o_DEF]
    \\ gvs [MAP_MAP_o,o_DEF,FST,SND,MAP_ZIP,FST_intro]
    \\ sg `f = NONE ⇔ q'' = NONE`
    >- (
      Cases_on `f`
      >- fs []
      \\ PairCases_on `x`
      \\ gvs []
      \\ Cases_on `inline m r' cl h x1`
      \\ gvs []
    )
    \\ sg `(∀v1 x1. f = SOME (v1, x1) ⇒ no_shadowing (exp_of x1))`
    >- (
      rw []
      \\ Cases_on `MEM v (FLAT (MAP (λx. FST (SND x)) bs))`
      >- (
        gvs []
        \\ qpat_x_assum `no_shadowing (rows_of _ _ _)` mp_tac
        \\ qid_spec_tac `bs`
        \\ Induct
        >- fs [rows_of_def,IfDisj_def]
        \\ rw []
        \\ Cases_on `h'`
        \\ Cases_on `r''`
        \\ fs [rows_of_def,IfDisj_def,MAP]
      )
      \\ gvs []
      \\ qpat_x_assum `no_shadowing (rows_of _ _ _)` mp_tac
      \\ qid_spec_tac `bs`
      \\ Induct
      >- fs [rows_of_def,IfDisj_def]
      \\ rw []
      \\ Cases_on `h'`
      \\ Cases_on `r''`
      \\ fs [rows_of_def,IfDisj_def,MAP]
    )
    \\ sg `EVERY (λe. no_shadowing (exp_of e)) (MAP (λ(v,vs,e). e) bs)`
    >- (
      rw []
      \\ Cases_on `MEM v (FLAT (MAP (λx. FST (SND x)) bs))`
      >- (
        gvs []
        \\ qpat_x_assum `no_shadowing (rows_of _ _ _)` mp_tac
        \\ qid_spec_tac `bs`
        \\ Induct
        >- fs [rows_of_def,IfDisj_def]
        \\ rw []
        \\ Cases_on `h'`
        \\ Cases_on `r''`
        \\ fs [rows_of_def,lets_for_def,IfDisj_def,MAP,MAPi_def]
        \\ irule lets_for_no_shadowing
        \\ metis_tac []
      )
      \\ gvs []
      \\ qpat_x_assum `no_shadowing (rows_of _ _ _)` mp_tac
      \\ qid_spec_tac `bs`
      \\ Induct
      >- fs [rows_of_def,IfDisj_def]
      \\ rw []
      \\ Cases_on `h'`
      \\ Cases_on `r''`
      \\ fs [rows_of_def,lets_for_def,IfDisj_def,MAP,MAPi_def]
      \\ irule lets_for_no_shadowing
      \\ metis_tac []
    )
    \\ sg `(∀v1 x1. f = SOME (v1, x1) ⇒ DISJOINT (boundvars (exp_of x1)) (set (MAP FST xs)))`
    >- (
      rw []
      \\ Cases_on `MEM v (FLAT (MAP (λx. FST (SND x)) bs))`
      >- (
        gvs []
        \\ qpat_x_assum `DISJOINT (boundvars (rows_of _ _ _)) (set (MAP FST xs))` mp_tac
        \\ qid_spec_tac `bs`
        \\ Induct
        >- fs [rows_of_def,IfDisj_def]
        \\ rw []
        \\ Cases_on `h'`
        \\ Cases_on `r''`
        \\ fs [rows_of_def,lets_for_def,IfDisj_def,MAP,MAPi_def]
      )
      \\ gvs []
      \\ qpat_x_assum `DISJOINT (boundvars (rows_of _ _ _)) (set (MAP FST xs))` mp_tac
      \\ qid_spec_tac `bs`
      \\ Induct
      >- fs [rows_of_def,IfDisj_def]
      \\ rw []
      \\ Cases_on `h'`
      \\ Cases_on `r''`
      \\ fs [rows_of_def,lets_for_def,IfDisj_def,MAP,MAPi_def]
    )
    \\ sg `EVERY (λx. DISJOINT (boundvars (exp_of x)) (set (MAP FST xs))) (MAP (λ(v,vs,e). e) bs)`
    >- (
      rw []
      \\ Cases_on `MEM v (FLAT (MAP (λx. FST (SND x)) bs))`
      >- (
        gvs []
        \\ qpat_x_assum `DISJOINT (boundvars (rows_of _ _ _)) (set (MAP FST xs))` mp_tac
        \\ qid_spec_tac `bs`
        \\ Induct
        >- fs [rows_of_def,IfDisj_def]
        \\ rw []
        \\ Cases_on `h'`
        \\ Cases_on `r''`
        \\ fs [rows_of_def,lets_for_def,IfDisj_def,MAP,MAPi_def]
        \\ irule lets_for_DISJOINT
        \\ metis_tac []
      )
      \\ gvs []
      \\ qpat_x_assum `DISJOINT (boundvars (rows_of _ _ _)) (set (MAP FST xs))` mp_tac
      \\ qid_spec_tac `bs`
      \\ Induct
      >- fs [rows_of_def,IfDisj_def]
      \\ rw []
      \\ Cases_on `h'`
      \\ Cases_on `r''`
      \\ fs [rows_of_def,lets_for_def,IfDisj_def,MAP,MAPi_def]
      \\ irule lets_for_DISJOINT
      \\ metis_tac []
    )
    \\ sg `list_subst_rel xs
      (rows_of (explode v)
          (case f of NONE => Fail | SOME (a,e) => IfDisj v a (exp_of e))
          (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) bs))
      (rows_of (explode v)
          (case q'' of NONE => Fail | SOME (a,e) => IfDisj v a (exp_of e))
          (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x'))
            (MAP2 (λ(v,vs,_) e. (v,vs,e)) bs q')))`
    >- (
      last_x_assum $ qspec_then `xs` assume_tac
      \\ pop_assum mp_tac
      \\ pop_assum mp_tac
      \\ pop_assum mp_tac
      \\ pop_assum mp_tac
      \\ pop_assum mp_tac
      \\ pop_assum mp_tac
      \\ pop_assum mp_tac
      \\ qpat_x_assum `inline_list m r cl h (MAP (λ(v,vs,e). e) bs) = (q',r')` mp_tac
      \\ qid_spec_tac `r`
      \\ qid_spec_tac `q'`
      \\ qid_spec_tac `bs`
      \\ Induct
      >- (
        rw []
        \\ fs [rows_of_def,MAP2]
        \\ Cases_on `f`
        >- fs [list_subst_rel_refl]
        \\ PairCases_on `x`
        \\ gvs []
        \\ Cases_on `q''`
        >- fs []
        \\ PairCases_on `x`
        \\ Cases_on `inline m r' cl h x1`
        \\ gvs [IfDisj_def]
        \\ irule list_subst_rel_Prim
        \\ fs [LIST_REL_EL_EQN,list_subst_rel_refl]
        \\ last_x_assum irule
        \\ fs [DISJOINT_SYM]
      )
      \\ rpt strip_tac
      \\ fs [rows_of_def,MAP2,MAP]
      \\ Cases_on `h'`
      \\ rename [`(a,b)::bs`]
      \\ Cases_on `b`
      \\ rename [`MAP2 _ _ qs`]
      \\ Cases_on `qs`
      >- fs []
      \\ gvs [rows_of_def,MAP2,MAP,FORALL_PROD]
      \\ irule list_subst_rel_Prim
      \\ simp [LIST_REL_EL_EQN,list_subst_rel_refl,lets_for_def]
      \\ irule_at Any list_subst_rel_lets_for
      \\ gvs [DISJOINT_SYM]
      \\ rename [`inline_list m r cl h (head::MAP (λ(v,vs,e). e) bs)`]
      \\ gvs [DISJOINT_SYM,memory_inv_def,inline_def]
      \\ Cases_on `inline m r cl h head`
      \\ gvs []
      \\ rename [`inline_list m r1 cl h (MAP (λ(v,vs,e). e) bs)`]
      \\ Cases_on `inline_list m r1 cl h (MAP (λ(v,vs,e). e) bs)`
      \\ gvs []
      \\ first_x_assum $ irule_at Any
      \\ gvs []
      \\ PairCases_on `r1`
      \\ metis_tac []
    )
    \\ Cases_on `MEM v (FLAT (MAP (λx. FST (SND x)) bs))`
    >- (
      gvs []
      \\ irule list_subst_rel_Prim
      \\ fs [LIST_REL_def,list_subst_rel_refl]
      \\ irule list_subst_rel_App
      \\ first_x_assum $ irule_at Any
      \\ fs [DISJOINT_SYM,memory_inv_def]
      \\ irule list_subst_rel_Lam
      \\ fs []
    )
    \\ gvs []
    \\ irule list_subst_rel_App
    \\ first_x_assum $ irule_at Any
    \\ fs [DISJOINT_SYM,memory_inv_def]
    \\ irule list_subst_rel_Lam
    \\ fs []
  ) *)
  >~ [`NestedCase _ _ _ _ _ _`] >- (
    gvs [NestedCase_free_def]
  )
  >~ [`LIST_REL _ [] _`] >- (
    gvs [inline_def]
  )
  >~ [`LIST_REL _ _ _`] >- (
    gvs [inline_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ last_x_assum irule \\ fs []
    \\ imp_res_tac avoid_set_ok_imp_vars_ok
    \\ imp_res_tac inline_set_of
    \\ gvs [EVERY_MEM]
    \\ imp_res_tac SUBSET_TRANS
    \\ metis_tac [avoid_set_ok_subset,memory_inv_subset]
  )
QED

Theorem inline_cexp_list_subst_rel_spec:
  ∀m ns cl h x xs t ns1.
    memory_inv xs m ns ∧
    map_ok m ∧ avoid_set_ok ns x ∧
    NestedCase_free x ∧ cexp_wf x ∧ letrecs_distinct (exp_of x) ∧
    no_shadowing (exp_of x) ∧
    DISJOINT (set (MAP FST xs)) (boundvars (exp_of x)) ∧
    (inline m ns cl h x) = (t, ns1) ⇒
    list_subst_rel xs (exp_of x) (exp_of t)
Proof
  rw []
  \\ assume_tac inline_cexp_list_subst_rel
  \\ gvs []
  \\ last_x_assum irule
  \\ gvs []
  \\ metis_tac []
QED

Theorem inline_all_thm:
  ∀cl h x.
    NestedCase_free x ∧
    letrecs_distinct (exp_of x) ∧
    cexp_wf x ∧
    closed (exp_of x) ⇒
    (exp_of x) ≅ (exp_of (inline_all cl h x))
Proof
  rw []
  \\ fs [inline_all_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ irule exp_eq_trans
  \\ irule_at (Pos last) (CONJUNCT1 $ SPEC_ALL dead_let_correct)
  \\ irule exp_eq_trans
  \\ irule_at (Pos last) list_subst_rel_IMP_exp_eq
  \\ irule_at Any inline_cexp_list_subst_rel_spec \\ fs []
  \\ pop_assum $ irule_at Any \\ fs []
  \\ fs [memory_inv_def]
  \\ drule pure_freshenProofTheory.freshen_cexp_correctness
  \\ impl_tac
  >- fs [pure_freshenProofTheory.avoid_set_ok_boundvars_of]
  \\ strip_tac
  \\ fs [closed_def]
  \\ imp_res_tac barendregt_imp_no_shadowing
  \\ drule_at Any freshen_cexp_letrecs_distinct
  \\ simp[boundvars_of_SUBSET]
QED

(********** Syntactic well-formedness results **********)

Theorem inline_letrecs_distinct:
  inline empty vs cl h ce = (ce',vs') ∧
  letrecs_distinct (exp_of ce)
  ⇒ letrecs_distinct (exp_of ce')
Proof
  cheat (* inline_letrecs_distinct *)
QED

Theorem inline_all_letrecs_distinct:
  inline_all cl h ce = ce' ∧ letrecs_distinct (exp_of ce)
  ⇒ letrecs_distinct (exp_of ce')
Proof
  cheat (* inline_all_letrecs_distinct *)
QED

Theorem inline_top_level_letrecs_distinct:
  inline_top_level c ce = ce' ∧ letrecs_distinct (exp_of ce)
  ⇒ letrecs_distinct (exp_of ce')
Proof
  cheat (* inline_top_level_letrecs_distinct *)
QED

Theorem inline_all_wf:
  inline_all cl h ce = ce' ∧ closed (exp_of ce) ∧
  NestedCase_free ce ∧ cexp_wf ce ∧ letrecs_distinct (exp_of ce)
  ⇒ closed (exp_of ce') ∧
    NestedCase_free ce' ∧ cexp_wf ce' ∧ letrecs_distinct (exp_of ce') ∧
    cns_arities ce' ⊆ cns_arities ce
Proof
  simp[inline_all_def] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  dxrule freshen_cexp_correctness >>
  rpt $ disch_then $ dxrule_at Any >> simp[avoid_set_ok_boundvars_of] >> strip_tac >>
  dxrule inline_wf >> rpt $ disch_then $ dxrule_at Any >> impl_tac
  >- (
    gvs[avoid_set_ok_def] >> irule unique_boundvars_letrecs_distinct >>
    gvs[pure_barendregtTheory.barendregt_def]
    ) >>
  strip_tac >> qspec_then `inlined_e` assume_tac dead_let_correct >> gvs[] >>
  gvs[closed_def, SUBSET_DEF]
QED


(********** Top-level theorems **********)

Theorem inline_top_level_correct:
  NestedCase_free ce ∧
  letrecs_distinct (exp_of ce) ∧
  cexp_wf ce ∧
  closed (exp_of ce) ∧
  inline_top_level c ce = ce'
  ⇒ exp_of ce ≅ exp_of ce' ∧
    NestedCase_free ce' ∧
    letrecs_distinct (exp_of ce') ∧
    cexp_wf ce' ∧
    closed (exp_of ce') ∧
    (cns_arities ce' ⊆ cns_arities ce)
Proof
  simp[inline_top_level_def] >> strip_tac >> gvs[] >>
  drule_all inline_all_thm >> dxrule_at Any inline_all_wf >>
  rpt $ disch_then $ dxrule_at Any >> strip_tac >> gvs[]
QED

(*******************)

val _ = export_theory();
