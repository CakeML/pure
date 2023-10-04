(*
  Proof of correctness for the pure_to_thunk compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory combinTheory
     pure_semanticsTheory thunkLangTheory thunk_semanticsTheory pure_evalTheory
     thunkLang_primitivesTheory pure_exp_lemmasTheory pure_miscTheory
     pure_to_thunk_1ProofTheory pure_cexpTheory pureLangTheory
     thunk_unthunkProofTheory
     thunk_case_liftProofTheory
     thunk_case_projProofTheory thunk_exp_ofTheory
     thunk_let_forceProofTheory
     thunk_cexpTheory
     expof_caseProofTheory;
local open pure_obs_sem_equalTheory in end

val _ = new_theory "pure_to_thunk_2Proof";

val _ = set_grammar_ancestry
          ["pure_to_thunk_1Proof", "pure_cexp", "thunk_exp_of",
           "thunkLang", "thunk_cexp", "pureLang", "expof_caseProof"];

Overload mk_delay_rel = ``λf x y. (∃c v. x = Var c v ∧ y = Var v) ∨
                                  (∃z. f x z ∧ y = Delay z)``

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
  (∀s x y z1 y1.
     (~(∃c v. x = Var c v ∧ z1 = Var v) ⇒
      (∃x1. exp_rel x x1 ∧ z1 = Delay x1)) ∧
     exp_rel y y1 ⇒
       exp_rel (Let i s x y) (Let (SOME s) z1 y1)) ∧
[~Letrec:]
  (∀i xs xs1 y y1.
     LIST_REL (λ(n,x) (m,x1). n = m ∧
                              ∃y. exp_rel x y ∧ x1 = Delay y) xs xs1 ∧ exp_rel y y1 ⇒
       exp_rel (Letrec i xs y) (Letrec xs1 y1)) ∧
[~App:]
  (∀f g xs ys.
     exp_rel f g ∧
     LIST_REL (λx z1. ~(∃c v. x = Var c v ∧ z1 = Var v) ⇒
                      (∃x1. exp_rel x x1 ∧ z1 = Delay x1)) xs ys ⇒
       exp_rel (App i f xs) (App g ys)) ∧
[~Cons:]
  (∀xs ys n.
     LIST_REL (λx z1. ~(∃c v. x = Var c v ∧ z1 = Var v) ⇒
                      (∃x1. exp_rel x x1 ∧ z1 = Delay x1)) xs ys ∧
     explode n ∉ monad_cns ⇒
       exp_rel (Prim i (Cons n) xs) (Prim (Cons n) ys)) ∧
[~Ret_Raise:]
  (∀mop xs ys n.
     (if n = «Ret» then mop = Ret else n = «Raise» ∧ mop = Raise) ∧
     LIST_REL (λx z1. ~(∃c v. x = Var c v ∧ z1 = Var v) ⇒
                      (∃x1. exp_rel x x1 ∧ z1 = Delay x1)) xs ys ⇒
       exp_rel (Prim i (Cons n) xs) (Monad mop ys)) ∧
[~Bind_Handle:]
  (∀mop xs ys n.
     (if n = «Bind» then mop = Bind else n = «Handle» ∧ mop = Handle) ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim i (Cons n) xs) (Monad mop ys)) ∧
[~Act_Length:]
  (∀mop xs ys n.
     (if n = «Act» then mop = Act else n = «Length» ∧ mop = Length) ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim i (Cons n) xs)
               (Monad Bind [Monad mop ys; Lam [«v»] (Monad Ret [Delay $ Var «v»])])) ∧
[~Alloc:]
  (∀x1 x2 y1 y2.
     exp_rel x1 y1 ∧ mk_delay_rel exp_rel x2 y2 ⇒
       exp_rel (Prim i (Cons «Alloc») [x1; x2])
               (Monad Bind [Monad Alloc [y1; y2];
                            Lam [«v»] (Monad Ret [Delay $ Var «v»])])) ∧
[~Deref:]
  (∀xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim i (Cons «Deref») xs)
               (Monad Handle [Monad Deref ys;
                              Lam [«v»] (Monad Raise [Delay $ Var «v»])])) ∧
[~Update:]
  (∀x1 x2 x3 y1 y2 y3.
     exp_rel x1 y1 ∧ exp_rel x2 y2 ∧ mk_delay_rel exp_rel x3 y3 ⇒
       exp_rel (Prim i (Cons «Update») [x1;x2;x3])
               (Monad Bind [
                  Monad Handle [Monad Update [y1;y2;y3];
                                Lam [«v»] (Monad Raise [Delay $ Var «v»])];
                  Lam [«v»] (Monad Ret [Delay $ Var «v»])])) ∧
[~Prim:]
  (∀xs ys a.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim i (AtomOp a) xs) (Prim (AtomOp a) ys)) ∧
[~Seq:]
  (∀x1 x2 y1 y2 fresh.
     exp_rel x1 y1 ∧ exp_rel x2 y2 ∧
     explode fresh ∉ freevars (exp_of' x2) ⇒
       exp_rel (Prim i Seq [x1; x2]) (Let (SOME fresh) y1 y2)) ∧
[~Case:]
  (∀i x v xs ys fresh.
     ~MEM v (FLAT (MAP (FST ∘ SND) xs)) ∧ xs ≠ [] ∧
     LIST_REL (λ(x1,x2,x3) (y1,y2,y3).
       x1 = y1 ∧ x2 = y2 ∧ ~MEM fresh x2 ∧
       exp_rel x3 y3 ∧ explode fresh ∉ freevars (exp_of' x3)) xs ys ∧
     (∀a x. eopt = SOME (a,x) ⇒ explode fresh ∉ freevars (exp_of' x)) ∧
     (~(∃c z. x = Var c z ∧ a_exp = Var z) ⇒
      (∃x1. exp_rel x x1 ∧ a_exp = Delay x1)) ∧
     fresh ≠ v ∧
     OPTREL (λ(a,x) (b,y). a = b ∧ exp_rel x y) eopt yopt ⇒
       exp_rel (Case i x v xs eopt)
               (Let (SOME v) a_exp $
                Let (SOME fresh) (Force (Var v)) $
                  Case fresh ys yopt))
End

Overload to_thunk = “pure_to_thunk_1Proof$compile_rel”
Overload lift_rel = “thunk_case_liftProof$compile_rel”
Overload force_rel = “thunk_let_forceProof$exp_rel”
Overload proj_rel = “thunk_case_projProof$compile_rel”
Overload delay_force = “thunk_unthunkProof$delay_force”

Overload VV[local] = “thunk_let_forceProof$Var”

val to_thunk_freevars = pure_to_thunk_1ProofTheory.compile_rel_freevars;

Theorem lets_for_lemma[local]:
  ∀vs k.
    to_thunk (exp_of' h2) y1 ∧
    lift_rel y1 y2 ∧
    force_rel NONE y2 y3 ∧
    proj_rel y3 y4 ∧
    delay_force y4 (exp_of yy2) ∧
    ~MEM fresh vs ∧ ~MEM h vs ∧ fresh ≠ h ∧ cn ∉ monad_cns ∧
    fresh ∉ freevars (exp_of' h2) ⇒
    ∃x1 x2 x3 x4.
      to_thunk
        (lets_for' (k + LENGTH vs) cn h
          (MAPi (λx v. (x+k,v)) vs) (exp_of' h2)) x1 ∧
      lift_rel x1 x2 ∧ fresh ∉ freevars x1 ∧
      force_rel (SOME (VV h,fresh)) x2 x3 ∧
      proj_rel x3 x4 ∧
      delay_force x4
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
  \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Seq \\ fs []
  \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases, PULL_EXISTS]
  \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases, PULL_EXISTS]
  \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases, PULL_EXISTS]
  \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases, PULL_EXISTS]
  \\ simp[pure_configTheory.monad_cns_def,
         mop_rel_cases, mop_ret_rel_cases, mop_delay_rel_cases]
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
  \\ irule_at Any thunk_unthunkProofTheory.delay_force_Let
  \\ irule_at Any thunk_unthunkProofTheory.delay_force_If \\ fs []
  \\ irule_at Any thunk_unthunkProofTheory.delay_force_Prim \\ fs []
  \\ irule_at Any thunk_unthunkProofTheory.delay_force_Prim \\ fs []
  \\ irule_at Any thunk_unthunkProofTheory.delay_force_Var \\ fs []
  \\ irule_at Any thunk_unthunkProofTheory.delay_force_Prim \\ fs []
  \\ irule_at Any thunk_unthunkProofTheory.delay_force_Let
  \\ irule_at Any thunk_unthunkProofTheory.delay_force_Prim \\ fs []
  \\ irule_at Any thunk_unthunkProofTheory.delay_force_Var \\ fs []
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

Definition Disj'_def:
  Disj' v [] = Cons "False" [] ∧
  Disj' v ((cn,l)::xs) = If (IsEq cn l T v) (Cons "True" []) (Disj' v xs)
End

Theorem to_thunk_Disj:
  ∀xs v. to_thunk (Disj v xs) (Disj' (Force (Var v)) xs)
Proof
  Induct \\ fs [pureLangTheory.Disj_def,FORALL_PROD,Disj'_def] \\ rw []
  \\ ntac 4 (simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases])
  \\ simp[pure_configTheory.monad_cns_def]
QED

Theorem lift_rel_Disj:
  ∀xs v. lift_rel (Disj' (Force (Var v)) xs) (Disj' (Force (Var v)) xs)
Proof
  Induct \\ fs [pureLangTheory.Disj_def,FORALL_PROD,Disj'_def] \\ rw []
  \\ ntac 5 (simp [Once thunk_case_liftProofTheory.compile_rel_cases])
QED

Theorem force_rel_Disj:
  ∀xs v. force_rel (SOME (VV v,f)) (Disj' (Force (Var v)) xs) (Disj f xs)
Proof
  Induct \\ fs [Disj'_def,FORALL_PROD,Disj_def] \\ rw []
  \\ rpt (simp [Once thunk_let_forceProofTheory.exp_rel_cases])
QED

Theorem proj_rel_Disj:
  ∀xs v. proj_rel (Disj v xs) (Disj v xs)
Proof
  Induct \\ fs [Disj_def,FORALL_PROD] \\ rw []
  \\ rpt (irule_at Any thunk_case_projProofTheory.compile_rel_If \\ fs [])
  \\ rpt (irule_at Any thunk_case_projProofTheory.compile_rel_Cons \\ fs [])
  \\ rpt (irule_at Any thunk_case_projProofTheory.compile_rel_Prim \\ fs [])
  \\ rpt (irule_at Any thunk_case_projProofTheory.compile_rel_Var \\ fs [])
QED

Theorem delay_force_Disj:
  ∀xs v. delay_force (Disj v xs) (Disj v xs)
Proof
  Induct \\ fs [Disj_def,FORALL_PROD] \\ rw []
  \\ rpt (irule_at Any thunk_unthunkProofTheory.delay_force_If \\ fs [])
  \\ rpt (irule_at Any thunk_unthunkProofTheory.delay_force_Prim \\ fs [])
  \\ rpt (irule_at Any thunk_unthunkProofTheory.delay_force_Var \\ fs [])
QED

Triviality freevars_Disj':
  ∀xs. f ≠ v ⇒ f ∉ freevars (Disj' (Force (Var v)) xs)
Proof
  Induct \\ fs [pureLangTheory.Disj_def,FORALL_PROD,Disj'_def] \\ rw []
  \\ fs [freevars_def]
QED

Theorem to_thunk_cases[local] = Once pure_to_thunk_1ProofTheory.compile_rel_cases;
Theorem lift_cases[local] = Once thunk_case_liftProofTheory.compile_rel_cases;
Theorem force_cases[local] = Once thunk_let_forceProofTheory.exp_rel_cases;
Theorem proj_cases[local] = Once thunk_case_projProofTheory.compile_rel_cases;
Theorem delay_force_cases[local] = Once thunk_unthunkProofTheory.delay_force_cases;

Theorem exp_rel_imp_combined:
  ∀x y.
    exp_rel x y ∧ cexp_wf x ⇒
    ∃y1 y2 y3 y4.
      to_thunk (exp_of' x) y1 ∧
      lift_rel y1 y2 ∧
      force_rel NONE y2 y3 ∧
      proj_rel y3 y4 ∧
      delay_force y4 (exp_of y)
Proof
  Induct_on ‘exp_rel’
  \\ rw [exp_of'_def,pure_cexpTheory.cexp_wf_def] \\ fs [pure_cexpTheory.op_of_def]
  >~ [‘Var n’] >-
   (simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases]
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Force
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Var
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
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Let
    \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases,PULL_EXISTS]
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Let
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Force
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Var
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Delay
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Delay
    \\ gvs [PULL_EXISTS]
    \\ ‘∃q1 q2 q3 q4.
          to_thunk (exp_of' x) q1 ∧
          lift_rel q1 q2 ∧
          force_rel NONE q2 q3 ∧
          proj_rel q3 q4 ∧
          delay_force (Delay q4) (exp_of a_exp)’ by
      (qpat_x_assum ‘(∀c z. x = Var c z ⇒ a_exp ≠ Var z) ⇒ _’ mp_tac
       \\ disch_then (assume_tac o ONCE_REWRITE_RULE [IMP_DISJ_THM])
       \\ reverse $ gvs []
       >- metis_tac [delay_force_Delay]
       \\ fs [exp_of'_def]
       \\irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Var
       \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Force
       \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Force
       \\ irule_at Any thunk_case_projProofTheory.compile_rel_Force
       \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Var
       \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Var
       \\ irule_at Any thunk_case_projProofTheory.compile_rel_Var
       \\ irule_at Any thunk_unthunkProofTheory.delay_force_Delat_Force_Var)
    \\ qpat_x_assum ‘to_thunk (exp_of' x) _’ $ irule_at Any
    \\ qpat_x_assum ‘lift_rel _ _’ $ irule_at Any
    \\ qpat_x_assum ‘force_rel NONE _ _’ $ irule_at Any
    \\ qpat_x_assum ‘proj_rel _ _’ $ irule_at Any \\ fs []
    \\ qpat_x_assum ‘(∀c z. x = Var c z ⇒ a_exp ≠ Var z) ⇒ _’ kall_tac
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
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_If \\ fs []
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Prim \\ fs []
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Var \\ fs []
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
    \\ qpat_x_assum ‘EVERY (λa. cexp_wf a) _’ mp_tac
    \\ qpat_x_assum ‘¬MEM v (FLAT (MAP (FST ∘ SND) ys1))’ mp_tac
    \\ `∀cn. MEM cn (MAP FST ys1) ⇒ explode cn ∉ monad_cns` by gvs[]
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ys2’
    \\ qid_spec_tac ‘ys1’
    \\ Induct \\ fs [PULL_EXISTS]
    >-
     (fs [rows_of_def,rows_of'_def]
      \\ Cases_on ‘yopt’ \\ fs []
      \\ Cases_on ‘eopt’ \\ gvs []
      >-
       (irule_at Any thunk_unthunkProofTheory.delay_force_Prim \\ fs []
        \\ irule_at Any thunk_case_projProofTheory.compile_rel_Prim \\ fs []
        \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Prim \\ fs []
        \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Prim \\ fs []
        \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases, freevars_def])
      \\ PairCases_on ‘x'’ \\ PairCases_on ‘x''’ \\ gvs []
      \\ fs [IfDisj_def]
      \\ irule_at Any thunk_unthunkProofTheory.delay_force_If \\ fs []
      \\ irule_at Any thunk_case_projProofTheory.compile_rel_If \\ fs []
      \\ irule_at Any thunk_let_forceProofTheory.exp_rel_If \\ fs []
      \\ irule_at Any thunk_case_liftProofTheory.compile_rel_If \\ fs []
      \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_If \\ fs []
      \\ irule_at Any to_thunk_Disj
      \\ first_assum $ irule_at $ Pos hd
      \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Prim \\ fs []
      \\ irule_at Any lift_rel_Disj
      \\ first_assum $ irule_at $ Pos hd
      \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Prim \\ fs []
      \\ irule_at Any force_rel_Disj
      \\ irule_at Any thunk_let_forceProofTheory.exp_rel_NONE_IMP_SOME
      \\ first_assum $ irule_at $ Pos hd
      \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Prim \\ fs []
      \\ irule_at Any proj_rel_Disj
      \\ fs [freevars_def,SF DNF_ss]
      \\ first_assum $ irule_at $ Pos hd
      \\ fs [] \\ imp_res_tac to_thunk_freevars \\ fs []
      \\ irule_at Any thunk_case_projProofTheory.compile_rel_Prim \\ fs []
      \\ irule_at Any freevars_Disj' \\ fs []
      \\ irule_at Any thunk_unthunkProofTheory.delay_force_Prim \\ fs []
      \\ irule_at Any delay_force_Disj)
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
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_If \\ fs [PULL_EXISTS]
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Prim \\ fs [PULL_EXISTS]
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Var
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_If \\ fs [PULL_EXISTS]
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Prim \\ fs [PULL_EXISTS]
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Var
    \\ simp [Once thunk_let_forceProofTheory.exp_rel_cases]
    \\ simp [Once thunk_let_forceProofTheory.exp_rel_cases]
    \\ simp [Once thunk_let_forceProofTheory.exp_rel_cases]
    \\ drule lets_for_lemma
    \\ ntac 4 $ disch_then drule
    \\ disch_then $ drule_at $ Pos last
    \\ rename [‘lets_for' (LENGTH cs) (explode cn)’]
    \\ disch_then $ qspecl_then [‘explode v’,
            ‘explode cn’,‘MAP explode cs’,‘0’] mp_tac
    \\ impl_tac >- fs [GSYM MEM_EQ_MEM_MAP_explode]
    \\ fs [] \\ strip_tac
    \\ rpt $ pop_assum $ irule_at Any
    \\ first_assum $ irule_at Any
    \\ first_assum $ irule_at Any
    \\ fs [])
  >~ [‘Seq’] >-
   (fs [pure_cexpTheory.op_of_def]
    \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Seq_fresh \\ fs []
    \\ qpat_x_assum ‘explode fresh ∉ _’ $ irule_at Any
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Let
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Let
    \\ fs [name_clash_def]
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Let_SOME
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Let
    \\ metis_tac [])
  >~ [‘Let’] >-
   (irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Let
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Let
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Let
    \\ fs [name_clash_def]
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Let_SOME
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Let
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Delay
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Delay
    \\ gvs [IMP_DISJ_THM,exp_of'_def]
    >-
     (irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Var
      \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Force
      \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Force
      \\ irule_at Any thunk_case_projProofTheory.compile_rel_Force
      \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Var
      \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Var
      \\ irule_at Any thunk_case_projProofTheory.compile_rel_Var
      \\ irule_at Any thunk_unthunkProofTheory.delay_force_Delat_Force_Var
      \\ metis_tac [])
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Delay
    \\ metis_tac [])
  >~ [‘Cons _ _’] >-
   (irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Cons
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Prim
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Prim
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Cons
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Prim
    \\ fs []
    \\ pop_assum mp_tac
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    \\ rw [] \\ gvs []
    \\ fs []
    \\ rpt $ first_assum $ irule_at Any
    \\ last_x_assum drule \\ strip_tac
    \\ rpt $ first_assum $ irule_at Any
    \\ rpt $ qpat_x_assum ‘LIST_REL _ _ _’ kall_tac
    \\ qpat_x_assum ‘(∀c z. h = Var c z ⇒ h5 ≠ Var z) ⇒ _’ mp_tac
    \\ disch_then (assume_tac o ONCE_REWRITE_RULE [IMP_DISJ_THM])
    \\ reverse $ gvs []
    >-
     (qpat_x_assum ‘to_thunk (exp_of' _) _’ $ irule_at Any
      \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
      \\ qpat_x_assum ‘lift_rel y1 _’ $ irule_at Any
      \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Delay
      \\ qpat_x_assum ‘force_rel NONE y2 _’ $ irule_at Any
      \\ irule_at Any thunk_case_projProofTheory.compile_rel_Delay
      \\ first_x_assum $ irule_at $ Pos hd
      \\ fs []
      \\ irule_at Any thunk_unthunkProofTheory.delay_force_Delay \\ fs [])
    \\ fs [cexp_wf_def,SF SFY_ss,exp_of'_def]
    \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Var
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Force
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Var
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Delay
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Force
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Var
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Delay
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Force
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Var
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Delat_Force_Var
    \\ fs [])
  >~ [‘Apps’] >-
   (pop_assum kall_tac
    \\ rpt $ pop_assum mp_tac
    \\ qid_spec_tac ‘x’
    \\ qid_spec_tac ‘y1’
    \\ qid_spec_tac ‘y2’
    \\ qid_spec_tac ‘y3’
    \\ qid_spec_tac ‘y4’
    \\ qid_spec_tac ‘y’
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    >- (fs [pure_expTheory.Apps_def] \\ metis_tac [])
    \\ rw [] \\ gvs []
    \\ fs [pure_expTheory.Apps_def]
    \\ rename [‘App (exp_of x5) (exp_of h5)’]
    \\ qpat_x_assum ‘exp_rel x x5’ assume_tac
    \\ drule exp_rel_App
    \\ disch_then $ qspecl_then [‘ARB’,‘[h]’,‘[h5]’] mp_tac
    \\ impl_tac >- (fs [] \\ strip_tac \\ gvs [SF SFY_ss])
    \\ strip_tac
    \\ first_x_assum $ drule
    \\ fs [GSYM PULL_EXISTS]
    \\ rename [‘LIST_REL _ xs ys’]
    \\ disch_then $ qspec_then ‘ys’ mp_tac
    \\ fs [pure_expTheory.Apps_def,exp_of'_def]
    \\ disch_then irule
    \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_App
    \\ qpat_x_assum ‘to_thunk (exp_of' _) _’ $ irule_at Any
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_App
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_App
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_App
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_App
    \\ qpat_x_assum ‘LIST_REL _ _ _’ kall_tac
    \\ qpat_x_assum ‘(∀c z. h = Var c z ⇒ h5 ≠ Var z) ⇒ _’ mp_tac
    \\ disch_then (assume_tac o ONCE_REWRITE_RULE [IMP_DISJ_THM])
    \\ reverse $ gvs []
    >-
     (qpat_x_assum ‘to_thunk (exp_of' _) _’ $ irule_at Any
      \\ qpat_x_assum ‘lift_rel y1 _’ $ irule_at Any
      \\ qpat_x_assum ‘force_rel NONE y2 _’ $ irule_at Any
      \\ first_x_assum $ irule_at $ Pos hd
      \\ irule_at Any thunk_unthunkProofTheory.delay_force_Delay
      \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
      \\ first_x_assum $ irule_at $ Pos hd
      \\ first_x_assum $ irule_at $ Pos hd \\ fs []
      \\ irule_at Any thunk_case_projProofTheory.compile_rel_Delay
      \\ first_x_assum $ irule_at $ Pos hd \\ fs []
      \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Delay
      \\ fs [cexp_wf_def,SF SFY_ss])
    \\ first_x_assum $ irule_at $ Pos hd
    \\ fs [cexp_wf_def,SF SFY_ss,exp_of'_def]
    \\ qpat_x_assum ‘proj_rel _ y4’ $ irule_at Any
    \\ qpat_x_assum ‘lift_rel y1 _’ $ irule_at Any \\ gvs []
    \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Var
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Force
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Var
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Delay
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Force
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Var
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Delay
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Force
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Var
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Delat_Force_Var)
  >~ [‘AtomOp’] >-
   (irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Prim \\ fs []
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Prim
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Prim
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Prim \\ fs []
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Prim \\ fs []
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
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
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Lam \\ fs []
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Lam
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Lam \\ fs []
    \\ rpt $ first_assum $ irule_at Any)
  >~ [‘Letrec’] >-
   (qpat_x_assum ‘_ ≠ []’ kall_tac
    \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Letrec \\ fs []
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Letrec \\ fs []
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Letrec \\ fs []
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Letrec
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Letrec \\ fs []
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
    \\ irule_at Any thunk_unthunkProofTheory.delay_force_Delay
    \\ irule_at Any thunk_case_projProofTheory.compile_rel_Delay
    \\ irule_at Any thunk_let_forceProofTheory.exp_rel_Delay
    \\ rpt $ first_assum $ irule_at Any
    \\ EVAL_TAC \\ fs []) >>
  gvs[num_args_ok_def, pure_configTheory.num_monad_args_def] >>
  gvs[LENGTH_EQ_NUM_compute] >>
  simp[to_thunk_cases, PULL_EXISTS, pure_configTheory.monad_cns_def,
       mop_rel_cases, mop_ret_rel_cases, mop_delay_rel_cases]
  >~ [`Ret`]
  >- (
    simp[lift_cases, force_cases, proj_cases, delay_force_cases, PULL_EXISTS] >>
    last_x_assum $ mp_tac o ONCE_REWRITE_RULE [IMP_DISJ_THM] >> rw[] >> gvs[]
    >- (
      simp[exp_of'_def, to_thunk_cases, PULL_EXISTS] >>
      ntac 3 $ simp[lift_cases, force_cases, proj_cases, delay_force_cases, PULL_EXISTS]
      ) >>
    simp[lift_cases, force_cases, proj_cases, delay_force_cases, PULL_EXISTS] >>
    rpt $ goal_assum drule
    )
  >~ [`Raise`]
  >- (
    simp[lift_cases, force_cases, proj_cases, delay_force_cases, PULL_EXISTS] >>
    last_x_assum $ mp_tac o ONCE_REWRITE_RULE [IMP_DISJ_THM] >> rw[] >> gvs[]
    >- (
      simp[exp_of'_def, to_thunk_cases, PULL_EXISTS] >>
      ntac 3 $ simp[lift_cases, force_cases, proj_cases, delay_force_cases, PULL_EXISTS]
      ) >>
    simp[lift_cases, force_cases, proj_cases, delay_force_cases, PULL_EXISTS] >>
    rpt $ goal_assum drule
    )
  >~ [`Bind`]
  >- (
    simp[lift_cases, force_cases, proj_cases, delay_force_cases, PULL_EXISTS] >>
    rpt $ goal_assum drule
    )
  >~ [`Handle`]
  >- (
    simp[lift_cases, force_cases, proj_cases, delay_force_cases, PULL_EXISTS] >>
    rpt $ goal_assum $ drule
    )
  >~ [`Act`]
  >- (
    simp[lift_cases, force_cases, proj_cases, delay_force_cases, PULL_EXISTS] >>
    goal_assum drule >> simp[lift_cases, PULL_EXISTS] >>
    goal_assum drule >> ntac 4 $ simp[lift_cases, PULL_EXISTS] >>
    simp[force_cases, PULL_EXISTS] >> goal_assum drule >>
    ntac 4 $ simp[force_cases, PULL_EXISTS] >>
    simp[proj_cases, PULL_EXISTS] >> goal_assum drule >>
    ntac 4 $ simp[proj_cases, PULL_EXISTS] >>
    ntac 5 $ simp[delay_force_cases]
    )
  >~ [`Length`]
  >- (
    simp[lift_cases, force_cases, proj_cases, delay_force_cases, PULL_EXISTS] >>
    goal_assum drule >> simp[lift_cases, PULL_EXISTS] >>
    goal_assum drule >> ntac 4 $ simp[lift_cases, PULL_EXISTS] >>
    simp[force_cases, PULL_EXISTS] >> goal_assum drule >>
    ntac 4 $ simp[force_cases, PULL_EXISTS] >>
    simp[proj_cases, PULL_EXISTS] >> goal_assum drule >>
    ntac 4 $ simp[proj_cases, PULL_EXISTS] >>
    ntac 5 $ simp[delay_force_cases]
    )
  >~ [`Alloc`] (* Delay (Force (Var _)) case *)
  >- (
    simp[lift_cases, force_cases, proj_cases, delay_force_cases, PULL_EXISTS] >>
    goal_assum drule >> simp[exp_of'_def, to_thunk_cases, PULL_EXISTS] >>
    simp[LUPDATE_DEF] >> simp[lift_cases, PULL_EXISTS] >> goal_assum drule >>
    ntac 7 $ simp[lift_cases, PULL_EXISTS] >> simp[force_cases, PULL_EXISTS] >>
    goal_assum drule >> ntac 7 $ simp[force_cases, PULL_EXISTS] >>
    simp[proj_cases, PULL_EXISTS] >> goal_assum drule >>
    ntac 7 $ simp[proj_cases, PULL_EXISTS] >> ntac 6 $ simp[delay_force_cases]
    )
  >~ [`Alloc`]
  >- (
    simp[LUPDATE_DEF] >>
    ntac 2 $ simp[lift_cases, PULL_EXISTS] >> rpt $ goal_assum drule >>
    simp[lift_cases, PULL_EXISTS] >> goal_assum drule >>
    ntac 7 $ simp[lift_cases, PULL_EXISTS] >>
    ntac 2 $ simp[force_cases, PULL_EXISTS] >> goal_assum drule >>
    simp[force_cases, PULL_EXISTS] >> goal_assum drule >>
    ntac 7 $ simp[force_cases, PULL_EXISTS] >>
    ntac 2 $ simp[proj_cases, PULL_EXISTS] >> goal_assum drule >>
    simp[proj_cases, PULL_EXISTS] >> goal_assum drule >>
    ntac 7 $ simp[proj_cases, PULL_EXISTS] >>
    ntac 7 $ simp[delay_force_cases, PULL_EXISTS]
    )
  >~ [`Deref`]
  >- (
    ntac 2 $ simp[lift_cases, PULL_EXISTS] >> rpt $ goal_assum drule >>
    ntac 4 $ simp[lift_cases, PULL_EXISTS] >>
    ntac 2 $ simp[force_cases, PULL_EXISTS] >> rpt $ goal_assum drule >>
    ntac 4 $ simp[force_cases, PULL_EXISTS] >>
    ntac 2 $ simp[proj_cases, PULL_EXISTS] >> rpt $ goal_assum drule >>
    ntac 4 $ simp[proj_cases, PULL_EXISTS] >>
    ntac 2 $ simp[delay_force_cases, PULL_EXISTS] >> rpt $ goal_assum drule >>
    ntac 4 $ simp[delay_force_cases, PULL_EXISTS]
    )
  >~ [`Update`] (* Delay (Force (Var _)) case *)
  >- (
    simp[LUPDATE_DEF, exp_of'_def] >> rpt $ goal_assum drule >>
    simp[to_thunk_cases, PULL_EXISTS] >>
    ntac 3 $ simp[lift_cases, PULL_EXISTS] >> rpt $ goal_assum drule >>
    ntac 11 $ simp[lift_cases, PULL_EXISTS] >>
    ntac 3 $ simp[force_cases, PULL_EXISTS] >> rpt $ goal_assum drule >>
    ntac 11 $ simp[force_cases, PULL_EXISTS] >>
    ntac 3 $ simp[proj_cases, PULL_EXISTS] >> rpt $ goal_assum drule >>
    ntac 11 $ simp[proj_cases, PULL_EXISTS] >>
    ntac 12 $ simp[Once delay_force_cases]
    )
  >~ [`Update`]
  >- (
    simp[LUPDATE_DEF, exp_of'_def] >> rpt $ goal_assum drule >>
    ntac 3 $ simp[lift_cases, PULL_EXISTS] >> rpt $ goal_assum drule >>
    simp[lift_cases, PULL_EXISTS] >> goal_assum drule >>
    ntac 11 $ simp[lift_cases, PULL_EXISTS] >>
    ntac 3 $ simp[force_cases, PULL_EXISTS] >> rpt $ goal_assum drule >>
    simp[force_cases, PULL_EXISTS] >> goal_assum drule >>
    ntac 11 $ simp[force_cases, PULL_EXISTS] >>
    ntac 3 $ simp[proj_cases, PULL_EXISTS] >> rpt $ goal_assum drule >>
    simp[proj_cases, PULL_EXISTS] >> goal_assum drule >>
    ntac 11 $ simp[proj_cases, PULL_EXISTS] >>
    ntac 12 $ simp[Once delay_force_cases]
    )
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
  \\ drule_at (Pos $ el 2) compile_case_proj_semantics
  \\ impl_keep_tac
  >- (drule exp_rel_NONE_freevars \\ fs [closed_def])
  \\ strip_tac
  \\ drule thunk_unthunkProofTheory.delay_force_semantics
  \\ impl_keep_tac
  >- (imp_res_tac compile_rel_closed \\ gvs [])
  \\ strip_tac \\ fs []
  \\ drule_all delay_force_closed \\ fs []
QED

val _ = export_theory ();
