(*
  Correctness of compilation pass that introduces Box
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory intLib
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory combinTheory
     envLangTheory thunkLang_primitivesTheory env_cexpTheory env_semanticsTheory
     env_box_1ProofTheory env_boxTheory;
local open pure_semanticsTheory in end

val _ = new_theory "env_boxProof";

val _ = set_grammar_ancestry ["env_box_1Proof","env_box"];

Theorem to_box_compile_rel:
  (∀x x1 b1.
     to_box x = (x1,b1) ⇒
     compile_rel (exp_of x) (exp_of x1) ∧
     (b1 ⇒ can_box (exp_of x1))) ∧
  (∀x x1.
     to_box_letrec x = x1 ⇒
     LIST_REL (λ(m,x) (n,x1).
       m = n ∧ compile_rel (exp_of x) (exp_of x1)) x x1) ∧
  (∀x x1 b1.
     to_box_list x = (x1,b1) ⇒
     LIST_REL (λx x1. compile_rel (exp_of x) (exp_of x1)) x x1 ∧
     (b1 ⇒ EVERY (can_box o exp_of) x1))
Proof
  ho_match_mp_tac to_box_ind
  \\ cheat
QED

Theorem itree_of_compile_to_box:
  closed (exp_of x) ⇒
  itree_of (exp_of x) =
  itree_of (exp_of (compile_to_box c x))
Proof
  rw [compile_to_box_def]
  \\ pairarg_tac \\ gvs []
  \\ gvs [itree_of_def]
  \\ irule compile_rel_semantics \\ fs []
  \\ imp_res_tac to_box_compile_rel
QED

Triviality MAP2_NIL:
  ∀xs ys. LENGTH ys = LENGTH xs ⇒ (MAP2 f xs ys = [] ⇔ xs = [])
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs []
QED

Theorem compile_to_box_wf:
  cexp_wf (compile_to_box c x) = cexp_wf x ∧
  cns_arities (compile_to_box c x) = cns_arities x
Proof
  simp [compile_to_box_def]
  \\ IF_CASES_TAC \\ fs []
  \\ pairarg_tac \\ fs []
  \\ qsuff_tac ‘
       (∀x e1 b. to_box x = (e1,b) ⇒
                 cexp_wf e1 = cexp_wf x ∧
                 cns_arities e1 = cns_arities x) ∧
       (∀x e1. to_box_letrec x = e1 ⇒
               LENGTH e1 = LENGTH x ∧
               MAP (λ(p1,p2). explode p1) e1 =
               MAP (λ(p1,p2). explode p1) x ∧
               EVERY (λ(_,x). ∃n m. x = Lam n m ∨ x = Delay m) e1 =
               EVERY (λ(_,x). ∃n m. x = Lam n m ∨ x = Delay m) x ∧
               LIST_REL (λa b. cexp_wf (SND a) = cexp_wf (SND b)) x e1 ∧
               BIGUNION (set (MAP (λa. cns_arities (SND a)) e1)) =
               BIGUNION (set (MAP (λa. cns_arities (SND a)) x))) ∧
       (∀x e1 b. to_box_list x = (e1,b) ⇒
                 LENGTH e1 = LENGTH x ∧
                 LIST_REL (λa b. cexp_wf a = cexp_wf b) x e1 ∧
                 BIGUNION (set (MAP (λa. cns_arities a) e1)) =
                 BIGUNION (set (MAP (λa. cns_arities a) x)))’
  >- (rw [] \\ res_tac \\ fs [])
  \\ rpt $ pop_assum kall_tac
  \\ ho_match_mp_tac to_box_ind
  \\ rpt conj_tac
  \\ rpt (disch_tac ORELSE gen_tac)
  \\ gvs [to_box_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs(),cns_arities_def]
  >- gvs [LIST_REL_EL_EQN,EVERY_EL]
  >-
   (‘MAP FST (MAP2 (λ(n,cs,_) e. (n,cs,e)) rs ys) = MAP FST rs ∧
     MAP (explode ∘ FST) (MAP2 (λ(n,cs,_) e. (n,cs,e)) rs ys) =
     MAP (explode ∘ FST) rs ∧
     MAP (λ(cn,vs,e). (explode cn,LENGTH vs))
              (MAP2 (λ(n,cs,_) e. (n,cs,e)) rs ys) =
     MAP (λ(cn,vs,e). (explode cn,LENGTH vs)) rs ∧
     MAP (λ(cn,vs,e). cns_arities e)
                (MAP2 (λ(n,cs,_) e. (n,cs,e)) rs ys) =
     MAP (λe. cns_arities e) ys ∧
     MAP (λ(p1,p1',p2). p1') (MAP2 (λ(n,cs,_) e. (n,cs,e)) rs ys) =
     MAP (λ(p1,p1',p2). p1') rs’ by
     (qpat_x_assum ‘LENGTH _ = LENGTH _’ mp_tac
      \\ qid_spec_tac ‘ys’
      \\ qid_spec_tac ‘rs’
      \\ rpt $ pop_assum kall_tac
      \\ Induct \\ Cases_on ‘ys’ \\ gvs []
      \\ gvs [FORALL_PROD] \\ rw []) \\ fs []
    \\ gvs [EVERY_MAP]
    \\ ‘EVERY (λx. (λ(_,vs,x'). ALL_DISTINCT vs ∧ cexp_wf x') x)
          (MAP2 (λ(n,cs,_) e. (n,cs,e)) rs ys) =
        EVERY (λx. (λ(_,vs,x'). ALL_DISTINCT vs ∧ cexp_wf x') x) rs’ by
     (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
      \\ qid_spec_tac ‘ys’
      \\ qid_spec_tac ‘rs’
      \\ rpt $ pop_assum kall_tac
      \\ Induct \\ Cases_on ‘ys’ \\ gvs []
      \\ gvs [FORALL_PROD] \\ rw [])
    \\ Cases_on ‘d’ \\ gvs []
    \\ gvs [MAP_MAP_o,o_DEF,LAMBDA_PROD,MAP2_NIL]
    \\ PairCases_on ‘x’ \\ gvs []
    \\ pairarg_tac \\ gvs [])
  >-
   (gvs [LAMBDA_PROD,EVERY_MAP]
    \\ ‘EVERY (λ(p1,p2). cexp_wf p2) (to_box_letrec x) =
        EVERY (λ(p1,p2). cexp_wf p2) x’ by
      gvs [LIST_REL_EL_EQN,EVERY_EL,UNCURRY]
    \\ gvs [])
  \\ Cases_on ‘dest_Delay x’ \\ gvs []
  >-
   (qsuff_tac ‘(∃n m. e1 = Lam n m ∨ e1 = Delay m) =
               (∃n m. x = Lam n m ∨ x = Delay m)’ >- fs []
    \\ Cases_on ‘x’ \\ gvs [to_box_def,dest_Delay_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ Cases_on ‘c’ \\ gvs [to_box_def]
    \\ rpt (pairarg_tac \\ gvs []))
  \\ ‘∃y. x = Delay y’ by (Cases_on ‘x’ \\ gvs [dest_Delay_def])
  \\ gvs [dest_Delay_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [cns_arities_def]
QED

val _ = export_theory ();
