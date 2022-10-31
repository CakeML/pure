(*
  Proof of correctness for the pure_to_thunk compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory combinTheory
     pure_semanticsTheory thunkLangTheory thunk_semanticsTheory pure_evalTheory
     thunkLang_primitivesTheory pure_exp_lemmasTheory pure_miscTheory
     pure_to_thunk_2ProofTheory pure_cexpTheory pureLangTheory thunk_cexpTheory
     var_setTheory pure_namesTheory pure_namesProofTheory;

val _ = new_theory "pure_to_thunkProof";

val _ = set_grammar_ancestry
          ["pure_to_thunk_2Proof", "pure_cexp", "thunk_exp_of",
           "thunkLang", "thunk_cexp", "pureLang", "var_set", "pure_namesProof"];

Definition any_el_def:
  any_el n [] = thunk_cexp$Prim (AtomOp Add) [] ∧
  any_el n (x::xs) = if n = 0 then x else any_el (n-1) xs
End

Definition to_thunk_def:
  to_thunk (s:vars) (pure_cexp$Var c v) =
    (thunk_cexp$Force (Var v),s) ∧
  to_thunk s (Lam c ns x) =
    (let (x,s) = to_thunk s x in (Lam ns x,s)) ∧
  to_thunk s (App c x ys) =
    (let (x,s) = to_thunk s x in
     let (ys,s) = to_thunk_list s ys in
       (App x (MAP Delay ys), s)) ∧
  to_thunk s (Letrec c xs y) =
    (let (y,s) = to_thunk s y in
     let (ys,s) = to_thunk_list s (MAP SND xs) in
       (Letrec (MAP2 (λ(n,_) y. (n, Delay y)) xs ys) y,s)) ∧
  to_thunk s (Let c v x y) =
    (let (x,s) = to_thunk s x in
     let (y,s) = to_thunk s y in
       (Let (SOME v) (Delay x) y,s)) ∧
  to_thunk s (Prim c p xs) =
    (let (xs,s) = to_thunk_list s xs in
       case p of
       | Seq => (Let NONE (any_el 0 xs) (any_el 1 xs),s)
       | AtomOp a => (Prim (AtomOp a) xs,s)
       | Cons t => (Prim (Cons t) (MAP Delay xs),s)) ∧
  to_thunk s (Case c x v ys opt) =
    (let (x,s) = to_thunk s x in
     let (rs,s) = to_thunk_list s (MAP (SND o SND) ys) in
     let (w,s) = invent_var (v ^ strlit "_forced") s in
       case opt of
       | NONE =>
           ((Let (SOME v) (Delay x) $
             Let (SOME w) (Force (Var v)) $
              Case w (MAP2 (λ(c,n,_) y. (c,n,y)) ys rs) NONE,s))
       | SOME (a,y) =>
          let (y,s) = to_thunk s y in
            ((Let (SOME v) (Delay x) $
              Let (SOME w) (Force (Var v)) $
               Case w (MAP2 (λ(c,n,_) y. (c,n,y)) ys rs) (SOME (a,y))),s)) ∧
  to_thunk s (NestedCase c g gv p e pes) = to_thunk s e ∧
  to_thunk_list s [] = ([],s) ∧
  to_thunk_list s (x::xs) =
    (let (x,s) = to_thunk s x in
     let (xs,s) = to_thunk_list s xs in
       (x::xs,s))
Termination
  WF_REL_TAC `measure $ λx. case x of
              | INL x => cexp_size (K 0) (SND x)
              | INR x => list_size (cexp_size (K 0)) (SND x)`
  \\ fs [pure_cexpTheory.cexp_size_eq] \\ rw []
  >~ [‘list_size (cexp_size (K 0)) (MAP SND xs)’] >-
    (pop_assum kall_tac
     \\ Induct_on ‘xs’ \\ fs [listTheory.list_size_def,FORALL_PROD]
     \\ rw [] \\ fs [basicSizeTheory.pair_size_def])
  >~ [‘list_size (cexp_size (K 0)) (MAP (λx. SND (SND x)) ys)’] >-
    (Induct_on ‘ys’ \\ fs [listTheory.list_size_def,FORALL_PROD]
     \\ rw [] \\ fs [basicSizeTheory.pair_size_def])
End

Definition compile_to_thunk_def:
  compile_to_thunk e = FST (to_thunk (pure_names e) e)
End

Triviality BIGUNION_set_MAP_SUBSET:
  ∀ys f t. BIGUNION (set (MAP f ys)) ⊆ t ⇔ EVERY (λy. f y ⊆ t) ys
Proof
  Induct \\ fs []
QED

Theorem MEM_explode_MAP_explode:
  ∀xs. MEM w xs ⇒ MEM (explode w) (MAP explode xs)
Proof
  Induct \\ fs [] \\ rw [] \\ fs []
QED

Theorem freevars_IMP_allvars:
  ∀x i. i IN freevars x ⇒ i IN allvars x
Proof
  ho_match_mp_tac pure_expTheory.freevars_ind
  \\ rw [] \\ gvs [MEM_MAP,PULL_EXISTS]
  \\ res_tac \\ fs []
  >- (first_assum $ irule_at Any \\ fs [])
  \\ rename [‘MEM yy _’] \\ PairCases_on ‘yy’
  \\ fs [EXISTS_PROD,FORALL_PROD]
  \\ res_tac \\ fs [] \\ metis_tac []
QED

Theorem exp_rel_to_thunk:
  (∀s (x:'a pure_cexp$cexp) x1 s1.
    to_thunk s x = (x1,s1) ∧ NestedCase_free x ∧ vars_ok s ∧
    allvars_of x ⊆ set_of s ∧ cexp_wf x ⇒
    exp_rel x x1 ∧ set_of s ⊆ set_of s1 ∧ vars_ok s1) ∧
  (∀s (xs:('a pure_cexp$cexp) list) xs1 s1.
    to_thunk_list s xs = (xs1,s1) ∧ EVERY NestedCase_free xs ∧ vars_ok s ∧
    EVERY (λx.  allvars_of x ⊆ set_of s) xs ∧ EVERY cexp_wf xs ⇒
    LIST_REL exp_rel xs xs1 ∧ set_of s ⊆ set_of s1 ∧ vars_ok s1)
Proof
  ho_match_mp_tac to_thunk_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ rewrite_tac [to_thunk_def]
  \\ strip_tac \\ gvs [] \\ rpt gen_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ TRY strip_tac \\ gvs [cexp_wf_def]
  >~ [‘exp_rel (Var _ _)’] >-
   (irule exp_rel_Var)
  >~ [‘exp_rel (Lam _ ns x)’] >-
   (irule exp_rel_Lam \\ fs [])
  >~ [‘exp_rel (App _ _ _)’] >-
   (irule_at Any exp_rel_App \\ fs []
    \\ qpat_x_assum ‘_ ⇒ _’ mp_tac
    \\ impl_tac
    >- fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss]
    \\ fs [] \\ imp_res_tac SUBSET_TRANS \\ fs [])
  >~ [‘exp_rel (Letrec _ _ _)’] >-
   (irule_at Any exp_rel_Letrec \\ fs []
    \\ qpat_x_assum ‘_ ⇒ _’ mp_tac \\ impl_tac
    >- fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss]
    \\ strip_tac
    \\ irule_at Any SUBSET_TRANS
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ qpat_x_assum ‘LIST_REL exp_rel _ _’ mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD])
  >~ [‘exp_rel (Case _ _ _ _ _)’] >-
   (qpat_x_assum ‘_ ⇒ _’ mp_tac \\ impl_tac
    >- fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss]
    \\ strip_tac
    \\ irule_at Any SUBSET_TRANS
    \\ first_assum $ irule_at $ Pos hd \\ fs []
    \\ irule_at Any SUBSET_TRANS
    \\ first_assum $ irule_at $ Pos hd \\ fs []
    \\ gvs [AllCaseEqs()]
    \\ drule_all invent_var_thm
    \\ strip_tac \\ fs []
    \\ fs [BIGUNION_set_MAP_SUBSET]
    \\ ‘v ≠ w’ by (CCONTR_TAC \\ gvs [SUBSET_DEF] \\ metis_tac [])
    >-
     (irule exp_rel_Case \\ fs []
      \\ qpat_x_assum ‘LIST_REL exp_rel _ _’ mp_tac
      \\ rpt $ qpat_x_assum ‘EVERY _ _’ mp_tac
      \\ qid_spec_tac ‘ys’
      \\ qid_spec_tac ‘rs’
      \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD,MAP_EQ_CONS,AND_IMP_INTRO]
      \\ rpt gen_tac \\ strip_tac
      \\ rename [‘set (MAP explode p1) ⊆ set_of s’]
      \\ Cases_on ‘MEM w p1’ \\ fs []
      >-
       (fs [SUBSET_DEF]
        \\ drule_then assume_tac MEM_explode_MAP_explode
        \\ first_x_assum $ drule_then assume_tac
        \\ fs [SUBSET_DEF] \\ metis_tac [])
      \\ fs [pureLangTheory.allvars_of,SUBSET_DEF]
      \\ CCONTR_TAC \\ fs []
      \\ drule expof_caseProofTheory.freevars_exp_of'
      \\ strip_tac \\ fs []
      \\ drule freevars_IMP_allvars
      \\ strip_tac
      \\ metis_tac [])
    \\ pairarg_tac \\ gvs []
    \\ qpat_x_assum ‘_ ⇒ _’ mp_tac \\ impl_tac
    >- fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss]
    \\ strip_tac \\ fs []
    \\ irule exp_rel_Case \\ fs []
    \\ qpat_x_assum ‘LIST_REL exp_rel _ _’ mp_tac
    \\ rpt $ qpat_x_assum ‘EVERY _ _’ mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘rs’
    \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD,MAP_EQ_CONS,AND_IMP_INTRO]
    >-
     (imp_res_tac expof_caseProofTheory.freevars_exp_of' \\ fs []
      \\ rw [] \\ fs [SUBSET_DEF]
      \\ CCONTR_TAC \\ fs []
      \\ imp_res_tac freevars_IMP_allvars \\ fs [allvars_of]
      \\ res_tac \\ res_tac \\ res_tac \\ metis_tac [])
    \\ rpt gen_tac \\ strip_tac
    \\ rename [‘set (MAP explode p1) ⊆ set_of s’]
    \\ Cases_on ‘MEM w p1’ \\ fs []
    >-
     (fs [SUBSET_DEF]
      \\ drule_then assume_tac MEM_explode_MAP_explode
      \\ first_x_assum $ drule_then assume_tac
      \\ fs [SUBSET_DEF] \\ metis_tac [])
    \\ fs [pureLangTheory.allvars_of,SUBSET_DEF]
    \\ CCONTR_TAC \\ fs []
    \\ imp_res_tac expof_caseProofTheory.freevars_exp_of' \\ fs []
    \\ imp_res_tac freevars_IMP_allvars \\ fs []
    \\ fs [SUBSET_DEF]
    \\ metis_tac [])
  >~ [‘exp_rel (Let c v x y)’] >-
   (irule_at Any exp_rel_Let
    \\ qpat_x_assum ‘_ ⇒ _’ mp_tac \\ impl_tac
    >- fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss]
    \\ strip_tac \\ fs []
    \\ irule_at Any SUBSET_TRANS
    \\ first_assum $ irule_at $ Pos hd \\ fs [])
  >~ [‘Prim c p xs’] >-
   (Cases_on ‘p’
    >~ [‘Cons m’] >-
     (gvs [] \\ irule_at Any exp_rel_Cons \\ gvs []
      \\ qpat_x_assum ‘_ ⇒ _’ mp_tac \\ impl_tac
      >- fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss]
      \\ strip_tac \\ fs [])
    >~ [‘AtomOp a’] >-
     (gvs [] \\ irule_at Any exp_rel_Prim \\ gvs []
      \\ qpat_x_assum ‘_ ⇒ _’ mp_tac \\ impl_tac
      >- fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss]
      \\ strip_tac \\ fs [])
    >~ [‘Seq’] >-
     (gvs [num_args_ok_def,LENGTH_EQ_NUM_compute,any_el_def]
      \\ irule_at Any exp_rel_Seq \\ gvs []))
  \\ qpat_x_assum ‘_ ⇒ _’ mp_tac \\ impl_tac
  >- fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss]
  \\ strip_tac \\ fs [] \\ fs [SUBSET_DEF] \\ metis_tac []
QED

Theorem compile_to_thunk_itree_of:
  cexp_wf x ∧ closed (exp_of x) ∧ NestedCase_free x ∧
  safe_itree (pure_semantics$itree_of (exp_of x)) ⇒
  pure_semantics$itree_of (exp_of x) =
  thunk_semantics$itree_of (exp_of (compile_to_thunk x))
Proof
  fs [compile_to_thunk_def] \\ rw []
  \\ Cases_on ‘to_thunk (pure_names x) x’ \\ fs []
  \\ drule (exp_rel_to_thunk |> CONJUNCT1) \\ fs []
  \\ fs [pure_names_ok,pure_names_eq_allvars]
  \\ fs [pure_semanticsTheory.itree_of_def]
  \\ rw [thunk_semanticsTheory.itree_of_def]
  \\ drule_all exp_rel_semantics \\ fs []
QED

val _ = export_theory ();
