(*
  Proof of correctness for the pure_to_thunk compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory combinTheory
     pure_semanticsTheory thunkLangTheory thunk_semanticsTheory pure_evalTheory
     thunkLang_primitivesTheory pure_exp_lemmasTheory pure_miscTheory
     pure_to_thunk_1ProofTheory pure_cexpTheory pureLangTheory
     thunk_case_liftProofTheory
     thunk_case_projProofTheory thunk_exp_ofTheory
     thunk_let_forceProofTheory
     thunk_cexpTheory
     expof_caseProofTheory;

val _ = new_theory "pure_to_thunkProof";

val _ = set_grammar_ancestry
          ["pure_to_thunk_1Proof", "pure_cexp", "thunk_exp_of",
           "thunkLang", "thunk_cexp", "pureLang", "expof_caseProof"];

Inductive exp_rel:
[~Var:]
  (∀(n:mlstring).
     exp_rel (pure_cexp$Var i n)
             (thunk_cexp$Force (Var n))) ∧
[~Lam:]
  (∀(s:mlstring list) x y.
     exp_rel x y ⇒
       exp_rel (pure_cexp$Lam i s x) (Lam s y)) ∧
[~Let:]
  (∀s x y x1 y1.
     exp_rel x x1 ∧ exp_rel y y1 ⇒
       exp_rel (Let i s x y) (Let (SOME s) (Delay x1) y1)) ∧
[~Letrec:]
  (∀i xs xs1 y y1.
     LIST_REL (λ(n,x) (m,x1). n = m ∧
                              ∃y. exp_rel x y ∧ x1 = Delay y) xs xs1 ∧ exp_rel y y1 ⇒
       exp_rel (Letrec i xs y) (Letrec xs1 y1)) ∧
[~App:]
  (∀f g xs ys.
     exp_rel f g ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (App i f xs) (App g (MAP Delay ys))) ∧
[~Cons:]
  (∀xs ys n.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim i (Cons n) xs) (Prim (Cons n) (MAP Delay ys))) ∧
[~Prim:]
  (∀xs ys a.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim i (AtomOp a) xs) (Prim (AtomOp a) ys)) ∧
[~Seq:]
  (∀x1 x2 y1 y2.
     exp_rel x1 y1 ∧ exp_rel x2 y2 ⇒
       exp_rel (Prim i Seq [x1; x2]) (Let NONE y1 y2)) ∧
[~Case:]
  (∀i x v xs ys fresh.
     ~MEM v (FLAT (MAP (FST ∘ SND) xs)) ∧ xs ≠ [] ∧
     LIST_REL (λ(x1,x2,x3) (y1,y2,y3).
       x1 = y1 ∧ x2 = y2 ∧ ~MEM fresh x2 ∧
       exp_rel x3 y3 ∧ explode fresh ∉ freevars (exp_of' x3)) xs ys ∧
     (∀x. eopt = SOME x ⇒ explode fresh ∉ freevars (exp_of' x)) ∧
     exp_rel x a_exp ∧ fresh ≠ v ∧
     OPTREL exp_rel eopt yopt ⇒
       exp_rel (Case i x v xs eopt)
               (Let (SOME v) (Delay a_exp) $
                Let (SOME fresh) (Force (Var v)) $
                  Case fresh ys yopt))
End

Overload to_thunk = “pure_to_thunk_1Proof$compile_rel”
Overload lift_rel = “thunk_case_liftProof$compile_rel”
Overload force_rel = “thunk_let_forceProof$exp_rel”
Overload proj_rel = “thunk_case_projProof$compile_rel”

Overload VV[local] = “thunk_let_forceProof$Var”

val to_thunk_freevars = pure_to_thunk_1ProofTheory.compile_rel_freevars;

Theorem lets_for_lemma[local]:
  ∀vs k.
    to_thunk (exp_of' h2) y1 ∧
    lift_rel y1 y2 ∧
    force_rel NONE y2 y3 ∧
    proj_rel y3 (exp_of yy2) ∧
    ~MEM fresh vs ∧ ~MEM h vs ∧ fresh ≠ h ∧
    fresh ∉ freevars (exp_of' h2) ⇒
    ∃x1 x2 x3.
      to_thunk
        (lets_for' (k + LENGTH vs) cn h
          (MAPi (λx v. (x+k,v)) vs) (exp_of' h2)) x1 ∧
      lift_rel x1 x2 ∧ fresh ∉ freevars x1 ∧
      force_rel (SOME (VV h,fresh)) x2 x3 ∧
      proj_rel x3
        (lets_for (k + LENGTH vs) cn fresh
          (MAPi (λx v. (x+k,v)) vs) (exp_of yy2))
Proof
  Induct
  \\ fs [lets_for_def,lets_for'_def]
  >-
   (rw [] \\ imp_res_tac to_thunk_freevars
    \\ rpt $ first_x_assum $ irule_at Any \\ fs []
    \\ irule thunk_let_forceProofTheory.exp_rel_NONE_IMP_SOME \\ fs [])
  \\ rw [] \\ gvs []
  \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases, PULL_EXISTS]
  \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases, PULL_EXISTS]
  \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases, PULL_EXISTS]
  \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases, PULL_EXISTS]
  \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases, PULL_EXISTS]
  \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases, PULL_EXISTS]
  \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Let
  \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Proj \\ fs [PULL_EXISTS]
  \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Var
  \\ irule_at Any thunk_case_projProofTheory.compile_rel_Proj \\ fs []
  \\ fs [o_DEF,freevars_def]
  \\ last_x_assum $ qspec_then ‘SUC k’ mp_tac
  \\ fs [ADD_CLAUSES] \\ rw []
  \\ rpt $ first_x_assum $ irule_at Any
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Let
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_If \\ fs []
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Prim \\ fs [PULL_EXISTS]
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Prim \\ fs [PULL_EXISTS]
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Prim \\ fs [PULL_EXISTS]
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Force
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Var
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Let
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Force
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Prim \\ fs [PULL_EXISTS]
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Force
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Var
  \\ rpt $ first_x_assum $ irule_at Any
  \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Let
  \\ fs [name_clash_def]
  \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Let
  \\ fs [name_clash_def]
  \\ rpt $ simp [Once thunk_let_forceProofTheory.exp_rel_cases]
QED

Triviality MEM_EQ_MEM_MAP_explode:
  ∀h1 f. MEM f h1 ⇔ MEM (explode f) (MAP explode h1)
Proof
  Induct \\ fs []
QED

val cexp_wf_def = pure_cexpTheory.cexp_wf_def;

Theorem exp_rel_imp_combined:
  ∀x y.
    exp_rel x y ∧ cexp_wf x ⇒
    ∃y1 y2 y3.
      to_thunk (exp_of' x) y1 ∧
      lift_rel y1 y2 ∧
      force_rel NONE y2 y3 ∧
      proj_rel y3 (exp_of y)
Proof
  Induct_on ‘exp_rel’
  \\ rw [exp_of'_def,pure_cexpTheory.cexp_wf_def] \\ fs [pure_cexpTheory.op_of_def]
  >~ [‘Var n’] >-
   (simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases]
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Force
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Var
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Force
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Var
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Force
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Var)
  >~ [‘rows_of'’] >-
   (irule_at Any thunk_case_projProofTheory.compile_rel_Let_SOME
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Let
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Let
    \\ fs [name_clash_def]
    \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases,PULL_EXISTS]
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Delay
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Delay
    \\ qpat_x_assum ‘proj_rel y3 (exp_of y)’ $ irule_at Any
    \\ qpat_x_assum ‘force_rel NONE y2 y3’ $ irule_at Any
    \\ qpat_x_assum ‘lift_rel y1 y2’ $ irule_at Any
    \\ qpat_x_assum ‘to_thunk (exp_of' x) y1’ $ irule_at Any
    \\ Cases_on ‘xs’ \\ fs []
    \\ PairCases_on ‘h’ \\ fs []
    \\ rename [‘_ = yy :: _’]
    \\ PairCases_on ‘yy’ \\ gvs [rows_of'_def]
    \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases,PULL_EXISTS]
    \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases,PULL_EXISTS]
    \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases,PULL_EXISTS]
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Lift
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Force
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Var
    \\ fs [freevars_def]
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Let_SOME
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Force
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Var
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Let_Force_Var
    \\ fs []
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_If \\ fs []
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Prim \\ fs [PULL_EXISTS]
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Force_Var
    \\ fs [rows_of_def]
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_If \\ fs []
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Prim \\ fs []
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Var \\ fs []
    \\ drule lets_for_lemma
    \\ rpt $ disch_then drule
    \\ ‘¬MEM (explode fresh) (MAP explode h1)’ by fs [MEM_EQ_MEM_MAP_explode]
    \\ disch_then drule
    \\ ‘¬MEM (explode v) (MAP explode h1)’ by fs [MEM_EQ_MEM_MAP_explode]
    \\ disch_then drule
    \\ disch_then $ qspecl_then [‘explode h0’,‘0’] strip_assume_tac
    \\ gvs []
    \\ rpt $ pop_assum $ irule_at Any
    \\ rename [‘LIST_REL _ ys1 ys2’]
    \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ qpat_x_assum ‘EVERY _ _’ mp_tac
    \\ qpat_x_assum ‘¬MEM v (FLAT (MAP (FST ∘ SND) ys1))’ mp_tac
    \\ qid_spec_tac ‘ys2’
    \\ qid_spec_tac ‘ys1’
    \\ Induct \\ fs [PULL_EXISTS]
    >-
     (fs [rows_of_def,rows_of'_def]
      \\ Cases_on ‘yopt’ \\ fs []
      >-
       (irule_at Any thunk_case_projProofTheory.compile_rel_Prim \\ fs []
        \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Prim \\ fs []
        \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Prim \\ fs []
        \\ Cases_on ‘eopt’ \\ fs []
        \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases, freevars_def])
      \\ Cases_on ‘eopt’ \\ fs []
      \\ rpt $ first_assum $ irule_at Any
      \\ irule_at Any thunk_let_forceProofTheory.exp_rel_NONE_IMP_SOME
      \\ fs [] \\ imp_res_tac to_thunk_freevars \\ fs [])
    \\ fs [FORALL_PROD]
    \\ rw [] \\ gvs []
    \\ first_x_assum dxrule
    \\ strip_tac
    \\ fs [rows_of_def,rows_of'_def]
    \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases,PULL_EXISTS]
    \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases,PULL_EXISTS]
    \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases,PULL_EXISTS]
    \\ fs [freevars_def]
    \\ qpat_x_assum ‘to_thunk _ _’ $ irule_at Any
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_If \\ fs [PULL_EXISTS]
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Prim \\ fs [PULL_EXISTS]
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Force
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Var
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_If \\ fs [PULL_EXISTS]
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Prim \\ fs [PULL_EXISTS]
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Var
    \\ simp [Once thunk_let_forceProofTheory.exp_rel_cases]
    \\ simp [Once thunk_let_forceProofTheory.exp_rel_cases]
    \\ simp [Once thunk_let_forceProofTheory.exp_rel_cases]
    \\ drule lets_for_lemma
    \\ ntac 3 $ disch_then drule
    \\ disch_then $ drule_at $ Pos last
    \\ rename [‘lets_for' (LENGTH cs) (explode cn)’]
    \\ disch_then $ qspecl_then [‘explode v’,
            ‘explode cn’,‘MAP explode cs’,‘0’] mp_tac
    \\ impl_tac >- fs [GSYM MEM_EQ_MEM_MAP_explode]
    \\ fs [] \\ strip_tac
    \\ rpt $ pop_assum $ irule_at Any
    \\ first_assum $ irule_at Any
    \\ first_assum $ irule_at Any)
  >~ [‘Seq’] >-
   (fs [pure_cexpTheory.op_of_def]
    \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases,PULL_EXISTS]
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Let
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Let
    \\ fs [name_clash_def]
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Let_NONE
    \\ metis_tac [])
  >~ [‘Let’] >-
   (irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Let
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Let
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Let
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Delay
    \\ fs [name_clash_def]
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Let_SOME
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Delay
    \\ metis_tac [])
  >~ [‘Cons _ _’] >-
   (irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Cons
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Prim
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Prim
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Cons
    \\ pop_assum mp_tac
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    \\ rw [] \\ gvs []
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Delay
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Delay
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
    \\ rpt $ first_assum $ irule_at Any
    \\ last_x_assum drule \\ strip_tac
    \\ rpt $ first_assum $ irule_at Any)
  >~ [‘Apps’] >-
   (pop_assum kall_tac
    \\ rpt $ pop_assum mp_tac
    \\ qid_spec_tac ‘x’
    \\ qid_spec_tac ‘y1’
    \\ qid_spec_tac ‘y2’
    \\ qid_spec_tac ‘y3’
    \\ qid_spec_tac ‘y’
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    >- (fs [pure_expTheory.Apps_def] \\ metis_tac [])
    \\ rw [] \\ gvs []
    \\ fs [pure_expTheory.Apps_def]
    \\ rename [‘App (exp_of x5) (Delay (exp_of h5))’]
    \\ ‘LIST_REL exp_rel [h] [h5]’ by fs []
    \\ qpat_x_assum ‘exp_rel x x5’ assume_tac
    \\ drule_at (Pos last) exp_rel_App
    \\ disch_then drule
    \\ disch_then $ qspec_then ‘ARB’ assume_tac
    \\ first_x_assum $ drule
    \\ fs [GSYM PULL_EXISTS]
    \\ rename [‘LIST_REL _ xs ys’]
    \\ disch_then $ qspec_then ‘ys’ mp_tac
    \\ fs [pure_expTheory.Apps_def,exp_of'_def]
    \\ disch_then irule
    \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_App
    \\ qpat_x_assum ‘to_thunk (exp_of' _) _’ $ irule_at Any
    \\ qpat_x_assum ‘to_thunk (exp_of' _) _’ $ irule_at Any
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_App
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
    \\ qpat_x_assum ‘lift_rel _ _’ $ irule_at Any
    \\ qpat_x_assum ‘lift_rel _ _’ $ irule_at Any
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_App
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Delay
    \\ qpat_x_assum ‘force_rel _ _ _’ $ irule_at Any
    \\ qpat_x_assum ‘force_rel _ _ _’ $ irule_at Any
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_App
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Delay
    \\ fs [cexp_wf_def])
  >~ [‘AtomOp’] >-
   (irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Prim \\ fs []
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Prim
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Prim
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Prim \\ fs []
    \\ pop_assum mp_tac
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    \\ rw [] \\ gvs []
    \\ last_x_assum drule \\ strip_tac
    \\ rpt $ first_assum $ irule_at Any)
  >~ [‘Lams’] >-
   (qpat_x_assum ‘_ ≠ []’ kall_tac
    \\ qid_spec_tac ‘s’ \\ Induct \\ fs [pure_expTheory.Lams_def]
    >- (rpt $ first_assum $ irule_at Any)
    \\ rw []
    \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Lam
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Lam
    \\ rpt $ first_assum $ irule_at Any)
  >~ [‘Letrec’] >-
   (qpat_x_assum ‘_ ≠ []’ kall_tac
    \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Letrec \\ fs []
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Letrec \\ fs []
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Letrec
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Letrec
    \\ rpt $ first_assum $ irule_at Any
    \\ rename [‘LIST_REL _ xs ys’]
    \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ qpat_x_assum ‘EVERY _ _’ mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ gvs [PULL_EXISTS] \\ rw []
    \\ last_x_assum drule_all \\ strip_tac
    \\ gvs [EXISTS_PROD]
    \\ rpt $ pop_assum $ irule_at Any
    \\ pop_assum kall_tac
    \\ rename [‘_ x1 x2’]
    \\ PairCases_on ‘x1’
    \\ PairCases_on ‘x2’
    \\ gvs []
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Delay
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Delay
    \\ rpt $ first_assum $ irule_at Any
    \\ EVAL_TAC \\ fs [])
QED

Theorem exp_rel_semantics:
  ∀x y.
    exp_rel x y ∧ cexp_wf x ∧ closed (exp_of x) ∧ NestedCase_free x ∧
    pure_semantics$safe_itree (semantics (exp_of x) Done [])
    ⇒
    closed (exp_of y) ∧
    semantics (exp_of x) Done [] = semantics (exp_of y) Done []
Proof
  rpt gen_tac \\ strip_tac
  \\ drule_all_then strip_assume_tac exp_rel_imp_combined
  \\ drule_then assume_tac exp_of_exp_eq
  \\ ‘closed (exp_of' x)’ by
    fs [pure_expTheory.closed_def,expof_caseProofTheory.freevars_exp_of']
  \\ ‘semantics (exp_of x) Done [] = semantics (exp_of' x) Done []’ by
    (simp_tac pure_ss [Once EQ_SYM_EQ]
     \\ irule_at Any pure_obs_sem_equalTheory.bisimilarity_IMP_semantics_eq
     \\ fs [pure_exp_relTheory.app_bisimilarity_eq])
  \\ fs []
  \\ drule_all compile_semantics
  \\ strip_tac \\ fs []
  \\ drule compile_rel_semantics
  \\ impl_keep_tac >-
   (imp_res_tac pure_to_thunk_1ProofTheory.compile_rel_freevars
    \\ fs [closed_def,pure_expTheory.closed_def])
  \\ strip_tac \\ fs []
  \\ drule case_force_semantics \\ fs []
  \\ impl_keep_tac >-
   (imp_res_tac thunk_case_liftProofTheory.compile_rel_freevars \\ fs [closed_def])
  \\ strip_tac \\ fs []
  \\ irule_at Any compile_rel_closed \\ fs []
  \\ first_assum $ irule_at $ Pos hd
  \\ irule_at Any compile_case_proj_semantics \\ fs []
  \\ drule exp_rel_NONE_freevars
  \\ fs [closed_def]
QED

val _ = export_theory ();
