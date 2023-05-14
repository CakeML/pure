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
     pure_letrec_seqTheory pure_demandTheory;
open pure_cexpTheory pure_varsTheory balanced_mapTheory pureLangTheory;
open pure_inlineTheory pure_inline_cexpTheory;

val _ = new_theory "pure_inline_cexpProof";

Definition crhs_to_rhs_def:
  crhs_to_rhs (cExp e) = (Exp $ exp_of e) ∧
  crhs_to_rhs (cRec e) = (Rec $ exp_of e)
End

(* xs and m have the same elements *)
Definition memory_inv_def:
  memory_inv xs m ⇔
    { explode a | ∃e. lookup m a = SOME e } = set (MAP FST xs) ∧
    ∀v e. (lookup m v = SOME e) ⇒ (MEM (explode v, (crhs_to_rhs e)) xs)
End

Theorem inline_list_empty:
  (inline_list m ns h l = ([], ns1)) ⇒ l = []
Proof
  rw []
  \\ Cases_on `l`
  >- fs []
  \\ fs [inline_def]
  \\ Cases_on `inline m ns h h'`
  \\ gvs []
  \\ Cases_on `inline_list m r h t`
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
  map_ok m ∧
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
    inline_list m ns h l = (l1, ns1) ⇒
      LENGTH l = LENGTH l1
Proof
  Induct_on `l`
  >- fs [inline_def]
  \\ rw [inline_def]
  \\ Cases_on `inline m ns h h'`
  \\ gvs []
  \\ Cases_on `inline_list m r h l`
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

val lemma = inline_ind
  |> Q.SPEC `λm ns h x. ∀xs t ns1.
    memory_inv xs m ∧
    map_ok m ∧
    no_shadowing (exp_of x) ∧
    DISJOINT (set (MAP FST xs)) (boundvars (exp_of x)) ∧
    (inline m ns h x) = (t, ns1) ⇒
    list_subst_rel xs (exp_of x) (exp_of t)`
  |> Q.SPEC `λm ns h es. ∀xs ts ns1.
    memory_inv xs m ∧
    map_ok m ∧
    EVERY (λe. no_shadowing (exp_of e)) es ∧
    EVERY (λx. DISJOINT (set (MAP FST xs)) (boundvars (exp_of x))) es ∧
    (inline_list m ns h es) = (ts, ns1) ⇒
    LIST_REL (λx t. list_subst_rel xs (exp_of x) (exp_of t)) es ts`
  |> SIMP_RULE std_ss []

Theorem inline_cexp_list_subst_rel:
  ^(lemma |> concl |> rand)
Proof
  match_mp_tac lemma
  \\ rpt strip_tac
  >~ [`Var _ _`] >- (
    Cases_on `inline m ns h (Var a v) = (Var a v, _)`
    >- gvs [list_subst_rel_refl,exp_of_def]
    \\ gvs [inline_def]
    \\ Cases_on `lookup m v` \\ gvs [list_subst_rel_refl]
    \\ Cases_on `x` \\ gvs [list_subst_rel_refl]
    \\ Cases_on `is_Lam c` \\ gvs [memory_inv_def,list_subst_rel_refl,exp_of_def]
    \\ irule list_subst_rel_VarSimp
    \\ res_tac
    \\ fs [crhs_to_rhs_def]
  )
  >~ [`App _ _ _`] >- (
    gvs [inline_def]
    \\ Cases_on `(case get_Var_name e of
      | NONE => inline m ns h e
      | SOME v =>
        case lookup m v of
        | NONE => inline m ns h e
        | SOME (cExp v1) => (v1,ns)
        | SOME (cRec v2) => inline m ns h e)`
    \\ gvs []
    \\ Cases_on `inline_list m r h es`
    \\ gvs []
    \\ rename [`list_subst_rel _ _ (exp_of (App a t ts))`]
    \\ gvs [exp_of_def,SF ETA_ss]
    \\ irule list_subst_rel_Apps
    \\ fs [LIST_REL_MAP,o_DEF]
    \\ last_x_assum $ irule_at Any
    \\ gvs [memory_inv_def,DISJOINT_SYM]
    \\ qspecl_then [`set (MAP FST xs)`,`exp_of e`,`MAP exp_of es`] assume_tac DISJOINT_boundvars_Apps
    \\ drule no_shadowing_Apps_EVERY
    \\ strip_tac
    \\ fs [EVERY_MAP,DISJOINT_SYM]
    \\ Cases_on `get_Var_name e`
    >- gvs []
    \\ Cases_on `e` \\ gvs [get_Var_name_def]
    \\ gvs [exp_of_def]
    \\ Cases_on `lookup m m'` \\ gvs []
    \\ Cases_on `x` \\ gvs []
    \\ irule list_subst_rel_VarSimp
    \\ res_tac
    \\ fs [crhs_to_rhs_def]
  )
  >~ [`Let _ _ _`] >- (
    gvs [inline_def]
    \\ Cases_on `inline m ns h e1`
    \\ gvs []
    \\ Cases_on `inline (heuristic_insert m h v e1) r h e2`
    \\ gvs []
    \\ gvs [list_subst_rel_refl,exp_of_def]
    \\ fs [heuristic_insert_def]
    \\ Cases_on `h e1`
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
    \\ Cases_on `inline_list m ns h (MAP SND vbs)`
    \\ gvs []
    \\ Cases_on `inline (heuristic_insert_Rec m h vbs) r h e`
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
      \\ Cases_on `inline m ns h u`
      \\ gvs []
    )
    \\ reverse $ Cases_on `t`
    >- (
      gvs [MAP2,inline_def]
      \\ Cases_on `inline m ns h u`
      \\ gvs []
    )
    \\ gvs [MAP2,inline_def]
    \\ irule list_subst_rel_LetrecIntro
    \\ last_x_assum $ irule_at Any
    \\ fs [DISJOINT_SYM]
    \\ fs [mlmapTheory.insert_thm]
    \\ irule_at Any memory_inv_APPEND_Rec
    \\ fs []
    \\ drule no_shadowing_Letrec_EVERY
    \\ rw []
  )
  >~ [`Lam _ _`] >- (
    gvs [inline_def]
    \\ Cases_on `inline m ns h e`
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
    \\ Cases_on `inline_list m ns h es`
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
    \\ Cases_on `inline m ns h e`
    \\ gvs []
    \\ Cases_on `inline_list m r h (MAP (λ(v, vs, e). e) bs)`
    \\ gvs []
    \\ Cases_on `(case f of
        NONE => (NONE,r')
      | SOME (vs,e') =>
        (λ(e4,ns4). (SOME (vs,e4),ns4)) (inline m r' h e'))`
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
      \\ Cases_on `inline m r' h x1`
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
      \\ qpat_x_assum `inline_list m r h (MAP (λ(v,vs,e). e) bs) = (q',r')` mp_tac
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
        \\ Cases_on `inline m r' h x1`
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
      \\ rename [`inline_list m r h (head::MAP (λ(v,vs,e). e) bs)`]
      \\ gvs [DISJOINT_SYM,memory_inv_def,inline_def]
      \\ Cases_on `inline m r h head`
      \\ gvs []
      \\ rename [`inline_list m r1 h (MAP (λ(v,vs,e). e) bs)`]
      \\ Cases_on `inline_list m r1 h (MAP (λ(v,vs,e). e) bs)`
      \\ gvs []
      \\ first_x_assum $ irule_at Any
      \\ gvs []
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
  \\ gvs [inline_def]
  \\ Cases_on `inline m ns h e`
  \\ gvs []
  \\ Cases_on `inline_list m r h es`
  \\ gvs []
QED

Theorem inline_cexp_list_subst_rel_spec:
  ∀m ns h x xs t ns1.
    memory_inv xs m ∧
    map_ok m ∧
    no_shadowing (exp_of x) ∧
    DISJOINT (set (MAP FST xs)) (boundvars (exp_of x)) ∧
    (inline m ns h x) = (t, ns1) ⇒
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
  ∀h x.
    no_shadowing (exp_of x) ∧
    closed (exp_of x) ∧
    (t, ns1) = inline_all h x ⇒
    (exp_of x) ≅ (exp_of t)
Proof
  rw []
  \\ irule list_subst_rel_IMP_exp_eq
  \\ fs [inline_all_def]
  \\ irule inline_cexp_list_subst_rel_spec
  \\ fs []
  \\ qexists `h` \\ qexists `empty` \\ qexists `empty` \\ qexists `ns1`
  \\ fs [map_ok_empty,memory_inv_def] 
QED

(*******************)

val _ = export_theory();
