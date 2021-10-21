(*
  An alternative version of the exp_of-embedding made to fit with
  the pure2thunk Case compilation.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory dep_rewrite
     relationTheory;
open pure_miscTheory pure_evalTheory pure_expTheory pure_exp_relTheory
     pure_congruenceTheory pure_cexpTheory pure_exp_lemmasTheory;

val _ = new_theory "expof_caseProof";

(* TODO move to pure_exp? *)
Overload Unit = “Prim (Cons "") []”;

Definition lets_for'_def:
  lets_for' m cn v [] b = b ∧
  lets_for' m cn v ((n,w)::ws) b =
    Seq (If (IsEq cn m (Var v)) Unit Fail)
        (Let w (Proj cn n (Var v))
               (lets_for' m cn v ws b))
End

Definition rows_of'_def:
  rows_of' v [] = Fail ∧
  rows_of' v ((cn,vs,b)::rest) =
    Tick (If (IsEq cn (LENGTH vs) (Var v))
             (lets_for' (LENGTH vs) cn v (MAPi (λi v. (i,v)) vs) b)
             (rows_of' v rest))
End

Definition exp_of'_def:
  exp_of' (Var d n) =
    ((Var n):exp) ∧
  exp_of' (Prim d p xs) =
    Prim (op_of p) (MAP exp_of' xs) ∧
  exp_of' (Let d v x y) =
    Let v (exp_of' x) (exp_of' y) ∧
  exp_of' (App _ f xs) =
    Apps (exp_of' f) (MAP Tick (MAP exp_of' xs)) ∧
  exp_of' (Lam d vs x) =
    Lams vs (exp_of' x) ∧
  exp_of' (Letrec d rs x) =
    Letrec (MAP (λ(n,x). (n,exp_of' x)) rs) (exp_of' x) ∧
  exp_of' (Case d x v rs) =
    (let caseexp =
       Let v (exp_of' x) (rows_of' v (MAP (λ(c,vs,x). (c,vs,exp_of' x)) rs))
     in if MEM v (FLAT (MAP (FST o SND) rs)) then
       Seq Fail caseexp
     else
       caseexp)
Termination
  WF_REL_TAC ‘measure (cexp_size (K 0))’ \\ rw []
  \\ imp_res_tac cexp_size_lemma
  \\ first_x_assum (qspec_then ‘K 0’ mp_tac) \\ fs []
End

(* TODO pure_cexp_lemmas? *)
Theorem exp_eq_Apps_cong:
  ∀xs ys x y.
    x ≅ y ∧
    LIST_REL $≅ xs ys ⇒
      Apps x xs ≅ Apps y ys
Proof
  Induct \\ rw [] \\ gs [Apps_def]
  \\ first_x_assum irule \\ gs []
  \\ irule exp_eq_App_cong \\ gs []
QED

(* TODO pure_cexp_lemmas? *)
Theorem exp_eq_Lams_cong:
  x ≅ y ⇒
    Lams vs x ≅ Lams vs y
Proof
  Induct_on ‘vs’
  \\ rw [] \\ gs [Lams_def]
  \\ irule exp_eq_Lam_cong \\ gs []
QED

(* TODO pure_cexp_lemmas? *)
Theorem exp_eq_Let_cong:
  a ≅ c ∧
  b ≅ d ⇒
    Let v a b ≅ Let v c d
Proof
  strip_tac
  \\ irule exp_eq_App_cong
  \\ irule_at Any exp_eq_Lam_cong
  \\ gs []
QED

(* TODO pure_cexp_lemmas? *)
Theorem exp_eq_If_cong:
  a ≅ d ∧ b ≅ e ∧ c ≅ f ⇒
    If a b c ≅ If d e f
Proof
  strip_tac
  \\ irule exp_eq_Prim_cong
  \\ gs []
QED

Theorem exp_eq_IsEq_Proj[local]:
  w ≠ v ⇒
    If (IsEq cn m (Var v))
       (Let w (Proj cn n (Var v)) a) b ≅
    If (IsEq cn m (Var v))
       (Let w (Proj cn n (Var v))
              (If (IsEq cn m (Var v)) a Fail)) b
Proof
  strip_tac
  \\ irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, bind_def]
  \\ ‘∃u. FLOOKUP f v = SOME u’
    by (Cases_on ‘FLOOKUP f v’ \\ gs [flookup_thm])
  \\ gs [DOMSUB_FLOOKUP_THM]
  \\ simp [eval_wh_thm, subst_def, bind_def, FLOOKUP_UPDATE]
  \\ rw [] \\ gs [subst_def, eval_wh_thm]
QED

Theorem exp_eq_IsEq_Seq_Proj[local]:
  w ≠ v ⇒
    If (IsEq cn n (Var v))
       (Seq (If (IsEq cn n (Var v)) Unit Fail)
            (Let w (Proj cn m (Var v)) x)) a ≅
    If (IsEq cn n (Var v))
       (Seq (If (IsEq cn n (Var v)) Unit Fail)
            (Let w (Proj cn m (Var v))
                   (If (IsEq cn n (Var v)) x Fail))) a
Proof
  strip_tac
  \\ irule eval_wh_IMP_exp_eq \\ rw []
  \\ ‘∃u. FLOOKUP f v = SOME u’
    by (Cases_on ‘FLOOKUP f v’ \\ gs [flookup_thm])
  \\ res_tac
  \\ simp [subst_def, DOMSUB_FLOOKUP_THM, eval_wh_thm, bind_def,
           FLOOKUP_UPDATE]
QED

Theorem exp_eq_lets_of_cong:
  ∀n cn v ws x y a b.
   x ≅ y ∧
   a ≅ b ∧
   ¬MEM v (MAP SND ws) ∧
   (∀m. MEM m (MAP FST ws) ⇒ m ≤ n) ⇒
     If (IsEq cn n (Var v)) (lets_for' n cn v ws x) a ≅
     If (IsEq cn n (Var v)) (lets_for cn v ws y) b
Proof
  ho_match_mp_tac lets_for'_ind
  \\ rw [] \\ gs [lets_for'_def, lets_for_def]
  >- (
    irule exp_eq_Prim_cong
    \\ simp [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ irule_at (Pos last) (iffLR exp_eq_sym)
  \\ irule_at (Pos hd) exp_eq_IsEq_Proj \\ simp []
  \\ irule exp_eq_trans
  \\ irule_at Any exp_eq_IsEq_Seq_Proj \\ simp []
  \\ ‘Fail ≅ Fail’ by gs [exp_eq_refl]
  \\ gs [SF DNF_ss]
  \\ first_x_assum (drule_all_then assume_tac)
  \\ once_rewrite_tac [exp_eq_sym]
  \\ irule exp_eq_trans
  \\ irule_at Any exp_eq_If_cong
  \\ irule_at Any exp_eq_refl
  \\ irule_at Any exp_eq_Let_cong
  \\ irule_at Any exp_eq_refl
  \\ first_x_assum (irule_at Any o ONCE_REWRITE_RULE [exp_eq_sym])
  \\ first_assum (irule_at Any o ONCE_REWRITE_RULE [exp_eq_sym])
  \\ rename1 ‘Seq _ X’
  \\ irule eval_wh_IMP_exp_eq \\ rw []
  \\ ‘∃u. FLOOKUP f v = SOME u’
    by (Cases_on ‘FLOOKUP f v’ \\ gs [flookup_thm])
  \\ res_tac
  \\ simp [subst_def, eval_wh_thm]
QED

Theorem exp_eq_rows_of_cong:
  ∀v xs ys.
    ¬MEM v (FLAT (MAP (FST o SND) xs)) ∧
    LIST_REL (λ(a,vs,x) (b,ws,y). a = b ∧ vs = ws ∧ x ≅ y) xs ys ⇒
      rows_of' v xs ≅ rows_of v ys
Proof
  ho_match_mp_tac rows_of'_ind
  \\ simp [rows_of'_def, rows_of_def, exp_eq_refl]
  \\ rw [] \\ pairarg_tac \\ gvs []
  \\ simp [rows_of_def]
  \\ irule exp_eq_Tick_cong
  \\ irule exp_eq_lets_of_cong
  \\ rw [indexedListsTheory.MEM_MAPi]
  \\ gs [MEM_EL]
QED

Theorem exp_of_exp_eq:
  ∀x. exp_of' x ≅ exp_of x
Proof
  ho_match_mp_tac exp_of'_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- ((* Var *)
    simp [exp_of_def, exp_of'_def, exp_eq_refl])
  >- ((* Prim *)
    strip_tac
    \\ simp [exp_of_def, exp_of'_def]
    \\ irule exp_eq_Prim_cong
    \\ gs [EVERY2_MAP, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS])
  >- ((* Let *)
    strip_tac
    \\ simp [exp_of_def, exp_of'_def]
    \\ irule exp_eq_App_cong
    \\ irule_at Any exp_eq_Lam_cong
    \\ gs [])
  >- ((* App *)
    strip_tac
    \\ simp [exp_of_def, exp_of'_def]
    \\ irule exp_eq_Apps_cong
    \\ gs [EVERY2_MAP, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS] \\ rw []
    \\ irule exp_eq_Tick_cong \\ gs [])
  >- ((* Lam *)
    strip_tac
    \\ simp [exp_of_def, exp_of'_def]
    \\ irule exp_eq_Lams_cong \\ gs [])
  >- ((* Letrec *)
    strip_tac
    \\ simp [exp_of_def, exp_of'_def]
    \\ irule exp_eq_Letrec_cong
    \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, EVERY2_MAP,
           LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
    \\ rw [ELIM_UNCURRY]
    \\ first_x_assum irule
    \\ first_assum (irule_at Any)
    \\ irule_at Any PAIR)
  >- ((* Case *)
    strip_tac
    \\ simp [exp_of_def, exp_of'_def]
    \\ IF_CASES_TAC \\ gs [exp_eq_refl]
    >- (
      irule eval_wh_IMP_exp_eq
      \\ simp [eval_wh_thm, subst_def])
    \\ irule exp_eq_Let_cong \\ gs []
    \\ irule exp_eq_rows_of_cong
    \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, EVERY2_MAP,
           LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
    \\ rw [ELIM_UNCURRY]
    \\ first_x_assum irule
    \\ first_assum (irule_at Any)
    \\ Cases_on ‘EL n rs’ \\ gs []
    \\ irule_at Any PAIR)
QED

val _ = export_theory ();

