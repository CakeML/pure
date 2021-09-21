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

Overload Assert = “λp x. If p x Fail”;

Definition lets_for'_def:
  lets_for' cn v [] b = b ∧
  lets_for' cn v ((n,w)::ws) b =
    Seq (Proj cn n (Var v))
        (Let w (Proj cn n (Var v))
               (lets_for' cn v ws b))
End

Definition rows_of'_def:
  rows_of' v [] = Fail ∧
  rows_of' v ((cn,vs,b)::rest) =
    Tick (If (IsEq cn (LENGTH vs) (Var v))
             (lets_for' cn v (MAPi (λi v. (i,v)) vs) b)
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
    (if MEM v (FLAT (MAP (FST o SND) rs)) then
       Fail
     else
       Let v (exp_of' x)
             (rows_of v (MAP (λ(c,vs,x). (c,vs,exp_of' x)) rs)))
Termination
  WF_REL_TAC ‘measure (cexp_size (K 0))’ \\ rw []
  \\ imp_res_tac cexp_size_lemma
  \\ first_x_assum (qspec_then ‘K 0’ mp_tac) \\ fs []
End

Theorem Assert_exp_eq:
  v ∉ freevars p ⇒
    If p (Let v y x) e ≅
    If p (Let v y (Assert p x)) e
Proof
  strip_tac
  \\ irule eval_wh_IMP_exp_eq
  \\ strip_tac
  \\ strip_tac \\ gs []
  \\ simp [subst_def, eval_wh_thm, bind_def, FLOOKUP_UPDATE]
  \\ IF_CASES_TAC \\ gs []
  \\ IF_CASES_TAC \\ gs []
  \\ IF_CASES_TAC \\ gs []
  \\ drule_then (qspec_then ‘f’ (assume_tac o SYM)) subst_fdomsub \\ gs []
  \\ simp [subst_def, eval_wh_thm, bind_def, FLOOKUP_UPDATE]
  \\ ‘subst1 v (subst f y) (subst f p) = subst f p’ suffices_by gs []
  \\ irule subst_ignore
  \\ simp [freevars_subst, IN_FRANGE, flookup_thm, SF SFY_ss]
QED

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

Theorem exp_eq_Lams_cong:
  x ≅ y ⇒
    Lams vs x ≅ Lams vs y
Proof
  Induct_on ‘vs’
  \\ rw [] \\ gs [Lams_def]
  \\ irule exp_eq_Lam_cong \\ gs []
QED

Theorem exp_eq_Tick:
  Tick x ≅ x
Proof
  irule eval_wh_IMP_exp_eq
  \\ rw [eval_wh_thm, subst_def, subst_funs_def, bind_def, FUPDATE_LIST_THM]
QED

Theorem exp_eq_lets_for_cong:
  ∀v s vs x y.
    x ≅ y ⇒
      lets_for v s vs x ≅ lets_for v s vs y
Proof
  ho_match_mp_tac lets_for_ind
  \\ simp [lets_for_def] \\ rw []
  \\ irule exp_eq_App_cong
  \\ irule_at Any exp_eq_Lam_cong
  \\ irule_at Any exp_eq_Prim_cong
  \\ gs [exp_eq_refl]
QED

Theorem exp_eq_rows_of_cong:
  ∀v xs ys.
    LIST_REL (λ(a,vs,x) (b,ws,y). a = b ∧ vs = ws ∧ x ≅ y) xs ys ⇒
      rows_of v xs ≅ rows_of v ys
Proof
  ho_match_mp_tac rows_of_ind
  \\ simp [rows_of_def, exp_eq_refl]
  \\ rw [] \\ pairarg_tac \\ gvs []
  \\ simp [rows_of_def]
  \\ irule exp_eq_Prim_cong \\ simp []
  \\ irule_at Any exp_eq_Prim_cong
  \\ simp [exp_eq_refl]
  \\ irule exp_eq_lets_for_cong \\ gs []
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
    \\ irule exp_eq_trans
    \\ irule_at Any exp_eq_Tick \\ gs [])
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
    \\ irule exp_eq_App_cong
    \\ irule_at Any exp_eq_Lam_cong \\ gs []
    \\ irule exp_eq_rows_of_cong
    \\ gs [EVERY2_MAP, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, ELIM_UNCURRY]
    \\ rw []
    \\ first_x_assum irule
    \\ first_assum (irule_at Any)
    \\ Cases_on ‘EL n rs’ \\ gs []
    \\ irule_at Any PAIR)
QED

val _ = export_theory ();

