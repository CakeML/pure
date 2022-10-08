(*
  Proof of correctness for the pure_to_thunk compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     pure_semanticsTheory thunk_semanticsTheory pure_evalTheory
     thunkLang_primitivesTheory pure_exp_lemmasTheory pure_miscTheory
     pure_to_thunk_1ProofTheory pure_cexpTheory pureLangTheory
     thunk_case_liftProofTheory
     thunk_case_d2bProofTheory
     expof_caseProofTheory;

val _ = new_theory "pure_to_thunkProof";

val _ = set_grammar_ancestry ["pure_to_thunk_1Proof", "pure_cexp",
                              "thunkLang", "pureLang", "expof_caseProof"];

(*
  cexp = Var 'a vname                         (* variable                 *)
       | Prim 'a cop (cexp list)              (* primitive operations     *)
       | App 'a cexp (cexp list)              (* function application     *)
       | Lam 'a (vname list) cexp             (* lambda                   *)
       | Let 'a vname cexp cexp               (* let                      *)
       | Letrec 'a ((vname # cexp) list) cexp (* mutually recursive exps  *)
       | Case 'a cexp vname ((vname # vname list # cexp) list) (* case of *)
       | NestedCase 'a cexp vname cepat cexp ((cepat # cexp) list)
                                     (* case w/non-empty pattern-exp list *)
*)

Definition Lams_def:
  Lams [] x = x ∧
  Lams (v::vs) x = thunkLang$Lam v (Lams vs x)
End

Definition Apps_def:
  Apps x [] = x ∧
  Apps x (y::ys) = Apps (thunkLang$App x y) ys
End

Definition lets_for_def:
  lets_for l cn v [] b = b ∧
  lets_for l cn v ((n,w)::ws) b =
    Let NONE (If (Prim (IsEq cn l T) [Force (Var v)]) Unit Fail) $
      Let (SOME w) (Delay $ Force $ Prim (Proj cn n) [Force $ Var v]) $
        lets_for l cn v ws b
End

Definition rows_of_def:
  (rows_of v k [] =
    case k of
      NONE => Fail
    | SOME e => e) ∧
  rows_of v k ((cn,vs,b)::rest) =
   If (Prim (IsEq cn (LENGTH vs) T) [Force (Var v)])
      (lets_for (LENGTH vs) cn v (MAPi (λi v. (i,v)) vs) b)
      (rows_of v k rest)
End

(*
       | Prim 'a cop (cexp list)                 (* primitive operations     *)
*)

Inductive exp_rel:
[~Var:]
  (∀(n:mlstring).
     exp_rel (pure_cexp$Var i n)
             (thunkLang$Force (Var (explode n)))) ∧
[~Lam:]
  (∀(s:mlstring list) x y.
     exp_rel x y ⇒
       exp_rel (pure_cexp$Lam i s x) (Lams (MAP explode s) y)) ∧
[~Let:]
  (∀s x y.
     exp_rel x x1 ∧ exp_rel y y1 ⇒
       exp_rel (Let i s x y) (Let (SOME (explode s)) (Delay x1) y1)) ∧
[~Letrec:]
  (∀i xs xs1 y y1.
     LIST_REL (λ(n,x) (m,x1). explode n = m ∧
                              ∃y. exp_rel x y ∧ x1 = Delay y) xs xs1 ∧ exp_rel y y1 ⇒
       exp_rel (Letrec i xs y) (Letrec xs1 y1)) ∧
[~App:]
  (∀f g xs ys.
     exp_rel f g ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (App i f xs) (Apps g (MAP Delay ys))) ∧
[~Case:]
  (∀i x v xs ys fresh.
     ~MEM v (FLAT (MAP (FST ∘ SND) xs)) ∧ xs ≠ [] ∧
     LIST_REL (λ(x1,x2,x3) (y1,y2,y3).
       explode x1 = y1 ∧ MAP explode x2 = y2 ∧
       exp_rel x3 y3 ∧ fresh ∉ freevars (exp_of' x3)) xs ys ∧
     (∀x. eopt = SOME x ⇒ fresh ∉ freevars (exp_of' x)) ∧
     exp_rel x a_exp ∧ fresh ≠ explode v ∧
     OPTREL exp_rel eopt yopt ⇒
       exp_rel (Case i x v xs eopt)
         (Let (SOME fresh) a_exp $
          Let (SOME (explode v)) (Box (Var fresh)) $
            rows_of (explode v) yopt ys))
End

Overload to_thunk = “pure_to_thunk_1Proof$compile_rel”
Overload lift_rel = “thunk_case_liftProof$compile_rel”
Overload d2b_rel = “thunk_case_d2bProof$exp_rel”

Theorem LIST_REL_combined_IMP:
  ∀xs ys.
    LIST_REL (λx y.
      exp_rel x y ∧
      (cexp_wf x ⇒
       ∃y1 y2. to_thunk (exp_of x) y1 ∧ lift_rel y1 y2 ∧ d2b_rel y2 y)) xs ys ∧
    EVERY (λa. cexp_wf a) xs ⇒
    ∃ts1 ts2.
      LIST_REL (λx y. to_thunk (exp_of x) y) xs ts1 ∧
      LIST_REL lift_rel ts1 ts2 ∧
      LIST_REL d2b_rel ts2 ys
Proof
  Induct \\ Cases_on ‘ys’ \\ fs [] \\ rw []
  \\ first_x_assum drule \\ fs [] \\ rw [PULL_EXISTS]
  \\ metis_tac []
QED

Theorem to_thunk_Apps:
  ∀xs ys x y.
    to_thunk x y ∧ LIST_REL to_thunk xs ys ⇒
    to_thunk (Apps x xs) (Apps y (MAP Delay ys))
Proof
  Induct \\ Cases_on ‘ys’ \\ fs [pure_expTheory.Apps_def,Apps_def]
  \\ rw [] \\ first_x_assum $ irule
  \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases]
QED

Theorem lift_rel_Apps:
  ∀xs ys x y.
    lift_rel x y ∧ LIST_REL lift_rel xs ys ⇒
    lift_rel (Apps x (MAP Delay xs)) (Apps y (MAP Delay ys))
Proof
  Induct \\ Cases_on ‘ys’ \\ fs [pure_expTheory.Apps_def,Apps_def]
  \\ rw [] \\ first_x_assum $ irule \\ fs []
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_App \\ fs []
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay \\ fs []
QED

Theorem d2b_rel_Apps:
  ∀xs ys x y.
    d2b_rel x y ∧ LIST_REL d2b_rel xs ys ⇒
    d2b_rel (Apps x (MAP Delay xs)) (Apps y (MAP Delay ys))
Proof
  Induct \\ Cases_on ‘ys’ \\ fs [pure_expTheory.Apps_def,Apps_def]
  \\ rw [] \\ first_x_assum $ irule \\ fs []
  \\ irule_at Any thunk_case_d2bProofTheory.exp_rel_App \\ fs []
  \\ irule_at Any thunk_case_d2bProofTheory.exp_rel_Delay \\ fs []
QED

Theorem to_thunk_lets_for:
  ∀ws. to_thunk rhs rhs' ⇒
       to_thunk (lets_for' n r0 v ws rhs)
                (lets_for n r0 v ws rhs')
Proof
  Induct \\ fs [lets_for_def,lets_for'_def]
  \\ PairCases \\ fs [lets_for_def,lets_for'_def] \\ rw [] \\ fs []
  \\ rpt $ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases]
QED

Theorem d2b_lets_for:
  ∀ws. d2b_rel rhs rhs' ⇒
       d2b_rel (lets_for n r0 v ws rhs)
               (lets_for n r0 v ws rhs')
Proof
  Induct \\ fs [lets_for_def,lets_for'_def]
  \\ PairCases \\ fs [lets_for_def,lets_for'_def] \\ rw [] \\ fs []
  \\ rpt $ simp [Once thunk_case_d2bProofTheory.exp_rel_cases]
QED

Theorem lift_lets_for:
  ∀ws. lift_rel rhs rhs' ⇒
       lift_rel (lets_for n r0 v ws rhs)
                (lets_for n r0 v ws rhs')
Proof
  Induct \\ fs [lets_for_def,lets_for'_def]
  \\ PairCases \\ fs [lets_for_def,lets_for'_def] \\ rw [] \\ fs []
  \\ rpt $ simp [Once thunk_case_liftProofTheory.compile_rel_cases]
QED

Triviality not_freevars_lets_for:
  fresh ∉ freevars rhs ∧ fresh ≠ y ⇒
  fresh ∉ freevars (lets_for n x y ws rhs)
Proof
  Induct_on ‘ws’ \\ fs [lets_for_def,FORALL_PROD]
  \\ fs [thunkLangTheory.freevars_def]
QED

Triviality not_treevars_rows_of:
  fresh ≠ v ∧
  EVERY (λ(n,vs,b). fresh ∉ freevars b) rows ∧
  (∀x. opt = SOME x ⇒ fresh ∉ freevars x) ⇒
  fresh ∉ freevars (rows_of v opt rows)
Proof
  Induct_on ‘rows’ \\ fs [rows_of_def,FORALL_PROD]
  >- (CASE_TAC \\ fs [freevars_def])
  \\ rw [freevars_def]
  \\ irule not_freevars_lets_for \\ fs []
QED

Theorem d2b_rows_of:
  ∀rows rows1.
    LIST_REL (λ(x1,x2,x3) (y1,y2,y3). x1 = y1 ∧ x2 = y2 ∧ d2b_rel x3 y3)
       rows rows1 ∧ OPTREL d2b_rel opt opt1 ⇒
    d2b_rel (rows_of v opt rows) (rows_of v opt1 rows1)
Proof
  Induct \\ fs [rows_of_def]
  >-
   (Cases_on ‘opt’ \\ Cases_on ‘opt1’ \\ fs []
    \\ rpt $ simp [Once thunk_case_d2bProofTheory.exp_rel_cases])
  \\ fs [PULL_EXISTS]
  \\ PairCases
  \\ PairCases
  \\ fs [] \\ rw []
  \\ fs [rows_of_def]
  \\ simp [Once thunk_case_d2bProofTheory.exp_rel_cases]
  \\ irule_at Any d2b_lets_for \\ fs []
  \\ rpt $ simp [Once thunk_case_d2bProofTheory.exp_rel_cases]
QED

Theorem lift_rows_of:
  ∀rows rows1.
    LIST_REL (λ(x1,x2,x3) (y1,y2,y3). x1 = y1 ∧ x2 = y2 ∧ lift_rel x3 y3)
       rows rows1 ∧ OPTREL lift_rel opt opt1 ⇒
    lift_rel (rows_of v opt rows) (rows_of v opt1 rows1)
Proof
  Induct \\ fs [rows_of_def]
  >-
   (Cases_on ‘opt’ \\ Cases_on ‘opt1’ \\ fs []
    \\ rpt $ simp [Once thunk_case_liftProofTheory.compile_rel_cases])
  \\ fs [PULL_EXISTS]
  \\ PairCases
  \\ PairCases
  \\ fs [] \\ rw []
  \\ fs [rows_of_def]
  \\ simp [Once thunk_case_liftProofTheory.compile_rel_cases]
  \\ irule_at Any lift_lets_for \\ fs []
  \\ rpt $ simp [Once thunk_case_liftProofTheory.compile_rel_cases]
QED

Theorem OPTREL_SIMP:
  (OPTREL P (SOME x) m ⇔ ∃y. m = SOME y ∧ P x y) ∧
  (OPTREL P n (SOME y) ⇔ ∃x. n = SOME x ∧ P x y) ∧
  (OPTREL P NONE m ⇔ m = NONE) ∧
  (OPTREL P n NONE ⇔ n = NONE)
Proof
  Cases_on ‘n’ \\ Cases_on ‘m’ \\ fs []
QED

Theorem to_thunk_rows_of:
  ∀xs ys.
    LIST_REL (λ(x1,x2,x3) (y1,y2,y3).
        explode x1 = y1 ∧ MAP explode x2 = y2 ∧
        to_thunk (exp_of' x3) y3)
      xs ys ∧
    OPTREL (λe1 e2. to_thunk (exp_of' e1) e2) eopt opt ⇒
    to_thunk (rows_of' v
               (case eopt of NONE => Fail | SOME e => exp_of' e)
               (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of' x')) xs))
             (rows_of v opt ys)
Proof
  Induct \\ fs [PULL_EXISTS]
  >-
   (rw [rows_of'_def,rows_of_def]
    \\ CASE_TAC \\ gvs [OPTREL_SIMP]
    \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases])
  \\ fs [UNCURRY] \\ rw [] \\ res_tac
  \\ rename [‘explode (FST xx) = FST yy’]
  \\ PairCases_on ‘xx’ \\ PairCases_on ‘yy’ \\ gvs []
  \\ rw [rows_of'_def,rows_of_def]
  \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases]
  \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases]
  \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases]
  \\ irule to_thunk_lets_for \\ fs []
QED

val to_thunk_freevars = pure_to_thunk_1ProofTheory.compile_rel_freevars;

Theorem exp_rel_imp_combined:
  ∀x y.
    exp_rel x y ∧ cexp_wf x ⇒
    ∃y1 y2.
      to_thunk (exp_of' x) y1 ∧
      lift_rel y1 y2 ∧
      d2b_rel y2 y
Proof
  Induct_on ‘exp_rel’ \\ rw [exp_of'_def,cexp_wf_def] \\ fs []
  >~ [‘Var n’] >-
   (simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases]
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Force
    \\ irule_at Any thunk_case_d2bProofTheory.exp_rel_Force
    \\ irule_at Any thunk_case_d2bProofTheory.exp_rel_Var
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Var)
  >~ [‘Lams s’] >-
   (qid_spec_tac ‘s’ \\ Induct
    \\ fs [Lams_def,pure_expTheory.Lams_def]
    >- metis_tac []
    \\ rw []
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Lam
    \\ irule_at Any thunk_case_d2bProofTheory.exp_rel_Lam
    \\ first_x_assum $ irule_at Any
    \\ first_x_assum $ irule_at Any
    \\ simp [Once pure_to_thunk_1ProofTheory.compile_rel_cases])
  >~ [‘Let’] >-
   (irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Let
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Let
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any thunk_case_d2bProofTheory.exp_rel_Let
    \\ irule_at Any thunk_case_d2bProofTheory.exp_rel_Delay \\ fs [])
  >~ [‘Letrec’] >-
   (irule_at Any thunk_case_d2bProofTheory.exp_rel_Letrec
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Letrec
    \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Letrec
    \\ rpt $ first_assum $ irule_at Any
    \\ last_x_assum mp_tac
    \\ rename [‘LIST_REL _ xs ys’]
    \\ qpat_x_assum ‘EVERY _ _’ mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS,EXISTS_PROD,FORALL_PROD]
    \\ rw [] \\ res_tac
    \\ irule_at Any thunk_case_d2bProofTheory.exp_rel_Delay \\ fs []
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
    \\ rpt $ first_assum $ irule_at Any)
  >~ [‘Apps’] >-
   (irule_at Any lift_rel_Apps \\ fs []
    \\ irule_at Any d2b_rel_Apps \\ fs []
    \\ irule_at Any to_thunk_Apps \\ simp [listTheory.LIST_REL_MAP1]
    \\ rpt $ first_assum $ irule_at Any
    \\ qpat_x_assum ‘LIST_REL _ xs ys’ mp_tac
    \\ qpat_x_assum ‘EVERY _ _’ mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS,EXISTS_PROD,FORALL_PROD]
    \\ rw [] \\ gvs []
    \\ res_tac
    \\ rpt $ first_assum $ irule_at Any)
  >~ [‘rows_of’] (* i.e. Case *)
  \\ Cases_on ‘xs’ >- fs [] \\ gvs []
  \\ rename [‘MEM v (FST (SND r))’] \\ PairCases_on ‘r’ \\ gvs []
  \\ rename [‘LIST_REL _ xs ys’]
  \\ gvs [UNCURRY]
  \\ rename [‘exp_rel r2 (SND (SND q))’] \\ PairCases_on ‘q’ \\ gvs []
  \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Let
  \\ gvs [rows_of'_def]
  \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_If \\ fs []
  \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Prim \\ fs [PULL_EXISTS]
  \\ irule_at Any pure_to_thunk_1ProofTheory.compile_rel_Var \\ fs []
  \\ qpat_x_assum ‘to_thunk (exp_of' x) _’ $ irule_at Any
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Let
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
  \\ qpat_x_assum ‘lift_rel y1 y2’ $ irule_at Any
  \\ irule_at (Pos $ hd) thunk_case_liftProofTheory.compile_rel_Lift
  \\ gvs [thunkLangTheory.freevars_def]
  \\ irule_at (Pos $ last) thunk_case_d2bProofTheory.exp_rel_D2B \\ fs [rows_of_def]
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Force
  \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Var
  \\ irule_at (Pos $ hd) thunk_case_d2bProofTheory.exp_rel_If \\ fs []
  \\ irule_at (Pos $ hd) thunk_case_d2bProofTheory.exp_rel_Prim \\ fs []
  \\ irule_at (Pos $ hd) thunk_case_d2bProofTheory.exp_rel_Force \\ fs []
  \\ irule_at (Pos $ hd) thunk_case_d2bProofTheory.exp_rel_Var \\ fs []
  \\ irule_at Any to_thunk_lets_for
  \\ first_assum $ irule_at $ Pos hd
  \\ irule_at Any d2b_lets_for
  \\ irule_at Any lift_lets_for
  \\ first_assum $ irule_at $ Pos hd
  \\ first_assum $ irule_at $ Pos hd
  \\ irule_at Any not_freevars_lets_for
  \\ irule_at Any d2b_rows_of \\ fs []
  \\ irule_at Any lift_rows_of \\ fs []
  \\ irule_at Any not_treevars_rows_of \\ fs []
  \\ irule_at Any to_thunk_rows_of
  \\ ‘∃ys1 ys2.
         EVERY (λ(n,vs,b). fresh ∉ freevars b) ys1 ∧
         LIST_REL
            (λ(x1,x2,x3) (y1,y2,y3).
                 explode x1 = y1 ∧ MAP explode x2 = y2 ∧
                 to_thunk (exp_of' x3) y3) xs ys1 ∧
         LIST_REL
            (λ(x1,x2,x3) (y1,y2,y3).
                 x1 = y1 ∧ x2 = y2 ∧ lift_rel x3 y3) ys1 ys2 ∧
         LIST_REL
            (λ(x1,x2,x3) (y1,y2,y3). x1 = y1 ∧ x2 = y2 ∧ d2b_rel x3 y3) ys2 ys’ by
   (qpat_x_assum ‘LIST_REL _ xs ys’ mp_tac
    \\ qpat_x_assum ‘EVERY _ (MAP _ xs)’ mp_tac
    \\ qid_spec_tac ‘ys’ \\ qid_spec_tac ‘xs’
    \\ rpt $ pop_assum kall_tac
    \\ Induct \\ fs [PULL_EXISTS,UNCURRY,PULL_FORALL,EXISTS_PROD]
    \\ rw [] \\ last_x_assum drule_all \\ rw []
    \\ rpt $ first_assum $ irule_at Any
    \\ imp_res_tac to_thunk_freevars \\ fs [])
  \\ pop_assum $ irule_at Any
  \\ pop_assum $ irule_at Any
  \\ pop_assum $ irule_at Any
  \\ pop_assum $ irule_at Any
  \\ imp_res_tac to_thunk_freevars \\ fs []
  \\ Cases_on ‘eopt’ \\ gvs [OPTREL_SIMP,PULL_EXISTS]
  \\ rpt $ first_assum $ irule_at Any
  \\ imp_res_tac to_thunk_freevars \\ fs []
QED

(*

TODO:
 - make thunk_case_inl usable

thunk_case_lift:    If IsEq --> Let If IsEq       -- has cheat
thunk_case_d2b:     Let Delay Force --> Let Box
thunk_case_inl:     (Var v) --> (Box (Var v))     -- needs to be able to stop rec
thunk_case_unbox:   (Force (Box (Var v))) --> (Tick (Var v)))   -- needs removal of Tick
thunk_case_proj:    Let (SOME w) (Tick (Delay (Force (Proj s i (Var v))))) x --> Let (SOME w) (MkTick (Proj s i (Var v))) y -- remove Tick, MkTick

*)

val _ = export_theory ();
