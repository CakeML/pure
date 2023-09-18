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
     pure_freshenProofTheory;

val _ = new_theory "pure_inline_cexpProof";

Definition crhs_to_rhs_def:
  crhs_to_rhs (cExp e) = (Exp $ exp_of e) ∧
  crhs_to_rhs (cRec e) = (Rec $ exp_of e)
End

(* xs and m have the same elements *)
Definition memory_inv_def:
  memory_inv xs m ⇔
    { explode a | ∃e. lookup m a = SOME e } = set (MAP FST xs) ∧
    ∀v e. (lookup m v = SOME e) ⇒
          ∃e1. e = cExp e1 ∧ cheap e1 ∧
               MEM (explode v, (crhs_to_rhs e)) xs
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
  memory_inv xs m ∧
  map_ok m ∧ cheap e1 ∧
  ¬MEM (explode v) (MAP FST xs) ⇒
  memory_inv (xs ++ [(explode v,Exp (exp_of e1))]) (insert m v (cExp e1))
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
  cheat
QED

Theorem Apps_Lams_eq_Lets_boundvars:
  ∀es vs b.
    LENGTH vs = LENGTH es ∧
    EVERY (λe. DISJOINT (set vs) (freevars e)) es ⇒
    boundvars (Lets (ZIP (vs,es)) b) = boundvars (Apps (Lams vs b) es)
Proof
  cheat
QED

val lemma = inline_ind
  |> Q.SPEC `λm ns cl h x. ∀xs t ns1.
    memory_inv xs m ∧
    map_ok m ∧
    no_shadowing (exp_of x) ∧
    DISJOINT (set (MAP FST xs)) (boundvars (exp_of x)) ∧
    (inline m ns cl h x) = (t, ns1) ⇒
    list_subst_rel xs (exp_of x) (exp_of t)`
  |> Q.SPEC `λm ns cl h es. ∀xs ts ns1.
    memory_inv xs m ∧
    map_ok m ∧
    EVERY (λe. no_shadowing (exp_of e)) es ∧
    EVERY (λx. DISJOINT (set (MAP FST xs)) (boundvars (exp_of x))) es ∧
    (inline_list m ns cl h es) = (ts, ns1) ⇒
    LIST_REL (λx t. list_subst_rel xs (exp_of x) (exp_of t)) es ts`
  |> SIMP_RULE std_ss [];

Theorem inline_cexp_list_subst_rel:
  ^(lemma |> concl |> rand)
Proof
  match_mp_tac lemma
  \\ rpt strip_tac
  >~ [`Var _ _`] >- (
    Cases_on `∃e. inline m ns cl h (Var a v) = (Var a v, e)`
    >- gvs [list_subst_rel_refl,exp_of_def]
    \\ gvs [inline_def]
    \\ Cases_on `lookup m v` \\ gvs [list_subst_rel_refl]
    \\ Cases_on `x` \\ gvs [list_subst_rel_refl]
    \\ Cases_on `is_Lam c` \\ gvs [memory_inv_def,list_subst_rel_refl,exp_of_def]
    \\ Cases_on ‘cl = 0’ \\ gvs []
    \\ first_assum drule \\ strip_tac \\ fs []
    \\ gvs []
    \\ irule list_subst_rel_Var
    \\ fs [crhs_to_rhs_def]
    \\ pop_assum $ irule_at Any
    \\ qexists_tac ‘exp_of c’ \\ fs [exp_eq_refl]
    \\ qsuff_tac ‘no_shadowing (exp_of c) ∧ boundvars (exp_of c) = {}’ >- fs []
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
      \\ gvs [memory_inv_def,DISJOINT_SYM]
      \\ fs [EVERY_MAP,DISJOINT_SYM]
    )
    \\ gvs []
    \\ Cases_on `lookup m x`
    >- (
      gvs [exp_of_def,SF ETA_ss]
      \\ irule list_subst_rel_Apps
      \\ fs [LIST_REL_MAP,o_DEF]
      \\ last_x_assum $ irule_at Any
      \\ gvs [memory_inv_def,DISJOINT_SYM]
      \\ fs [EVERY_MAP,DISJOINT_SYM]
    )
    \\ gvs []
    \\ rename [‘lookup m x = SOME aa’]
    \\ reverse $ Cases_on `aa`
    >- (
      gvs [exp_of_def,SF ETA_ss]
      \\ irule list_subst_rel_Apps
      \\ fs [LIST_REL_MAP,o_DEF]
      \\ last_x_assum $ irule_at Any
      \\ gvs [memory_inv_def,DISJOINT_SYM]
      \\ fs [EVERY_MAP,DISJOINT_SYM]
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
      \\ irule list_subst_rel_refl
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
      \\ irule list_subst_rel_refl
    )
    \\ gvs []
    \\ Cases_on ‘e’ \\ gvs [get_Var_name_def,exp_of_def]
    \\ rename [‘lookup m v = SOME (cExp c)’]
    \\ first_x_assum drule
    \\ impl_tac >- fs [boundvars_Apps,EVERY_MEM,MEM_MAP,PULL_EXISTS]
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
    \\ drule pure_freshenProofTheory.freshen_cexp_correctness
    \\ impl_tac
    >- cheat (* freshen preconditions *)
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
    \\ gvs [MEM_MAP,PULL_EXISTS]
    (*
      Most of these follow from barendregt, but more is needed
      from some of the conjunctions in the goal.

      I suspect the induction needs to assume something like

         set (MAP FST xs) ⊆ ns
         vars_of xs ⊆ ns
         freevars_of xs ⊆ ns

      so that we know that these are disjoint from the
      boundvars of any expression produced by freshen.

      And to maintain those, we also need to assume:

         freevars (exp_of x) ⊆ ns
         boundvars (exp_of x) ⊆ ns

    *)
    \\ cheat
  )
  >~ [`Let _ _ _`] >- (
    gvs [inline_def]
    \\ Cases_on `inline m ns cl h e1`
    \\ gvs []
    \\ Cases_on `inline (heuristic_insert m h v e1) r cl h e2`
    \\ gvs []
    \\ gvs [list_subst_rel_refl,exp_of_def]
    \\ fs [heuristic_insert_def]
    \\ Cases_on `cheap e1 ∧ h e1`
    >- (
      irule list_subst_rel_Let
      \\ conj_tac
      >- (
        last_x_assum irule
        \\ fs [DISJOINT_SYM,memory_inv_def]
      )
      \\ last_x_assum irule
      \\ fs [DISJOINT_SYM]
      \\ fs [mlmapTheory.insert_thm]
      \\ irule memory_inv_APPEND
      \\ fs []
    )
    \\ full_simp_tac pure_ss []
    \\ pop_assum kall_tac
    \\ fs []
    \\ irule list_subst_rel_App
    \\ reverse $ conj_tac
    >- (
      last_x_assum irule
      \\ fs [DISJOINT_SYM,memory_inv_def]
    )
    \\ irule list_subst_rel_Lam
    \\ last_x_assum irule
    \\ fs [DISJOINT_SYM,memory_inv_def]
  )
  >~ [`Letrec _ _ _`] >- (
    gvs [inline_def]
    \\ Cases_on `inline_list m ns cl h (MAP SND vbs)`
    \\ gvs []
    \\ Cases_on `inline (heuristic_insert_Rec m h vbs) r cl h e`
    \\ gvs []
    \\ gvs [list_subst_rel_refl,exp_of_def]
    \\ Cases_on `heuristic_insert_Rec m h vbs = m`
    >- (
      irule list_subst_rel_Letrec
      \\ last_x_assum $ irule_at Any
      \\ gvs []
      \\ drule no_shadowing_Letrec_EVERY
      \\ strip_tac \\ fs [DISJOINT_SYM]
      \\ gvs [MAP_MAP_o,o_DEF,FORALL_PROD,LAMBDA_PROD,SND_intro,EVERY_MAP]
      \\ last_x_assum $ qspec_then `xs` assume_tac
      \\ sg `EVERY (λ(p1,p2). DISJOINT (boundvars (exp_of p2)) (set (MAP FST xs))) vbs`
      >- (
        simp [EVERY_MEM]
        \\ rw []
        \\ Cases_on `e'`
        \\ gvs []
        \\ first_x_assum $ qspec_then `boundvars (exp_of r')` assume_tac
        \\ first_x_assum irule
        \\ gvs [MEM_MAP]
        \\ qexists `(q'',r')`
        \\ gvs []
      )
      \\ last_x_assum drule
      \\ pop_assum mp_tac
      \\ pop_assum mp_tac
      \\ qpat_x_assum `DISJOINT _ _` mp_tac
      \\ qid_spec_tac `q`
      \\ qid_spec_tac `vbs`
      \\ Induct
      >- fs []
      \\ fs [PULL_EXISTS,FORALL_PROD]
    )
    \\ gvs [heuristic_insert_Rec_def]
    \\ Cases_on `vbs`
    >- gvs []
    \\ gvs []
    \\ reverse $ Cases_on `t`
    >- gvs []
    \\ PairCases_on `h'`
    \\ rename [`(w, u)`]
    \\ gvs []
    \\ Cases_on `¬h u`
    >- gvs []
    \\ gvs []
    \\ Cases_on `q`
    >- (
      gvs [MAP2,inline_def]
      \\ Cases_on `inline m ns cl h u`
      \\ gvs []
    )
    \\ reverse $ Cases_on `t`
    >- (
      gvs [MAP2,inline_def]
      \\ Cases_on `inline m ns cl h u`
      \\ gvs []
    )
    \\ gvs [MAP2,inline_def]
    \\ irule list_subst_rel_LetRecIntroExp
    \\ conj_tac
    >- (
      last_x_assum $ irule_at Any
      \\ gvs [DISJOINT_SYM]
      \\ fs [Once no_shadowing_cases]
    )
    \\ last_x_assum $ irule_at Any
    \\ Cases_on `specialise w u` \\ gvs []
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
    \\ qpat_x_assum ‘no_shadowing _’ mp_tac
    \\ simp [Once no_shadowing_cases] \\ strip_tac
    \\ ‘cheap x’ by (imp_res_tac specialise_is_Lam \\ simp [cheap_def])
    \\ once_rewrite_tac [DISJOINT_SYM] \\ asm_rewrite_tac []
    \\ gvs [IN_DISJOINT,SUBSET_DEF]
    \\ CCONTR_TAC \\ gvs [] \\ res_tac \\ metis_tac []
  )
  >~ [`Lam _ _`] >- (
    gvs [inline_def]
    \\ Cases_on `inline m ns cl h e`
    \\ gvs []
    \\ gvs [memory_inv_def,list_subst_rel_refl,exp_of_def,FORALL_PROD]
    \\ Induct_on `vs`
    >- fs [Lams_def,list_subst_rel_refl,inline_def,exp_of_def,MAP]
    \\ rw []
    \\ gvs [Lams_def]
    \\ irule list_subst_rel_Lam
    \\ last_x_assum irule
  )
  >~ [`Prim _ _ _`] >- (
    gvs [inline_def]
    \\ Cases_on `inline_list m ns cl h es`
    \\ gvs []
    \\ gvs [memory_inv_def,list_subst_rel_refl,exp_of_def,FORALL_PROD]
    \\ irule list_subst_rel_Prim
    \\ fs [LIST_REL_MAP,o_DEF,FORALL_PROD,LIST_REL_MAP2,PULL_EXISTS]
    \\ last_x_assum irule
    \\ fs []
    \\ fs [EVERY_MAP]
    \\ simp [EVERY_MEM]
    \\ rw []
    \\ first_x_assum $ qspec_then `boundvars (exp_of x)` assume_tac
    \\ fs [MAP_MAP_o,o_DEF]
    \\ first_x_assum irule
    \\ fs [MEM_MAP]
    \\ rw []
    \\ qexists `x`
    \\ rw []
  )
  >~ [`Case _ _ _ _ _`] >- (
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
  )
  >~ [`NestedCase _ _ _ _ _ _`] >- (
    gvs [inline_def,list_subst_rel_refl]
  )
  >~ [`LIST_REL _ [] _`] >- (
    gvs [inline_def]
  )
  >~ [`LIST_REL _ _ _`] >- (
    gvs [inline_def]
    \\ Cases_on `inline m ns cl h e`
    \\ gvs []
    \\ Cases_on `inline_list m r cl h es`
    \\ gvs []
  )
QED

Theorem inline_cexp_list_subst_rel_spec:
  ∀m ns cl h x xs t ns1.
    memory_inv xs m ∧
    map_ok m ∧
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
QED

(********** Syntactic well-formedness results **********)

Theorem inline_wf:
  inline empty vars cl h ce = (ce',vars') ∧
  vars_ok vars ∧ NestedCase_free ce ∧ cexp_wf ce ∧ letrecs_distinct (exp_of ce)
  ⇒ NestedCase_free ce' ∧ cexp_wf ce' ∧ letrecs_distinct (exp_of ce') ∧
    freevars (exp_of ce') = freevars (exp_of ce) ∧
    cns_arities ce' ⊆ cns_arities ce
Proof
  cheat
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
