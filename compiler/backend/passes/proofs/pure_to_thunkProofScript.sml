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
     thunk_case_d2bProofTheory;

val _ = new_theory "pure_to_thunkProof";

val _ = set_grammar_ancestry ["pure_to_thunk_1Proof", "pure_cexp",
                              "thunkLang", "pureLang"];

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
  lets_for cn v [] b = b ∧
  lets_for cn v ((n,w)::ws) b =
    Let (SOME w) (Delay $ Force $ Prim (Proj cn n) [Force $ Var v]) $
      lets_for cn v ws b
End

Definition rows_of_def:
  rows_of v [] = Prim (AtomOp Add) [] ∧
  rows_of v ((cn,vs,b)::rest) =
    If (Prim (IsEq cn (LENGTH vs) T) [Force (Var v)])
      (lets_for cn v (MAPi (λi v. (i,v)) vs) b)
      (rows_of v rest)
End

Inductive exp_rel:
[~Var:]
  (∀(n:string).
     exp_rel (pure_cexp$Var i n)
             (thunkLang$Force (Var n))) ∧
[~Lam:]
  (∀(s:string list) x y.
     exp_rel x y ⇒
       exp_rel (pure_cexp$Lam i s x) (Lams s y)) ∧
[~Let:]
  (∀s x y.
     exp_rel x x1 ∧ exp_rel y y1 ⇒
       exp_rel (Let i s x y) (Let (SOME s) (Delay x1) y1)) ∧
[~App:]
  (∀f g xs ys.
     exp_rel f g ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (App i f xs) (Apps g (MAP Delay ys))) ∧
[~Case:]
  (∀i x v xs ys.
     ~MEM v (FLAT (MAP (FST ∘ SND) xs)) ∧ xs ≠ [] ∧
     MAP FST xs = MAP FST ys ∧
     MAP (FST o SND) xs = MAP (FST o SND) ys ∧
     LIST_REL exp_rel (MAP (SND o SND) xs) (MAP (SND o SND) ys) ⇒
       exp_rel (Case i x v xs)
         (Let (SOME fresh) a_exp $
          Let (SOME v) (Box (Var fresh)) $
            rows_of fresh ys))
End

Overload to_thunk = “pure_to_thunk_1Proof$compile_rel”
Overload lift_rel = “thunk_case_liftProof$compile_rel”
Overload d2b_rel = “thunk_case_d2bProof$exp_rel”

Theorem LIST_REL_combined_IMP:
  ∀xs ys.
    LIST_REL (λx y.
      exp_rel x y ∧
      ∃y1 y2. to_thunk (exp_of x) y1 ∧ lift_rel y1 y2 ∧ d2b_rel y2 y) xs ys ⇒
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

Theorem exp_rel_imp_combined:
  ∀x y.
    exp_rel x y ⇒
    ∃y1 y2.
      to_thunk (exp_of x) y1 ∧
      lift_rel y1 y2 ∧
      d2b_rel y2 y
Proof

  Induct_on ‘exp_rel’ \\ rw [pureLangTheory.exp_of_def]
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
   (irule_at Any pure_to_thunk_1ProofTheory.compile_rel__Let
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Let
    \\ irule_at Any thunk_case_liftProofTheory.compile_rel_Delay
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any thunk_case_d2bProofTheory.exp_rel_Let
    \\ irule_at Any thunk_case_d2bProofTheory.exp_rel_Delay \\ fs [])
  >~ [‘Apps’] >-
   (drule LIST_REL_combined_IMP \\ strip_tac
    \\ qexists_tac ‘Apps y1 (MAP Delay ts1)’
    \\ qexists_tac ‘Apps y2 (MAP Delay ts2)’
    \\ irule_at Any to_thunk_Apps \\ simp [listTheory.LIST_REL_MAP1]
    \\ fs [combinTheory.o_DEF,SF ETA_ss]
    \\ irule_at Any lift_rel_Apps \\ fs []
    \\ irule_at Any d2b_rel_Apps \\ fs [])
  >~ [‘rows_of’] (* i.e. Case *)

  \\ cheat
QED

(*

TODO:
 - remove closed from Letrec in pure_to_thunk_1Proof
 - make thunk_case_inl usable

*)

val _ = export_theory ();
