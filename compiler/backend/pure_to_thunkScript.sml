(*
   A compiler from pureLang to the substitution-based version of
   thunkLang.

 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open listTheory rich_listTheory;
open pure_expTheory thunkLang_substTheory;

val _ = new_theory "pure_to_thunk";

(* TODO:
 * Force needs to be inserted somewhere. One possible candidate is at operator
 * application (when the value of an operation on primitives is requested, we
 * need to evaluate all its arguments fully).
 *)

(*
Definition compile_exp_def:
  compile_exp (Var n : pure_exp$exp) = thunkLang_subst$Var n ∧
  compile_exp (Prim op xs) =
    (if op = If ∧ LENGTH xs = 3 then
       If (compile_exp (EL 0 xs))
          (compile_exp (EL 1 xs))
          (compile_exp (EL 2 xs))
     else
       Prim op (MAP (λx. Force (compile_exp x)) xs)) ∧
  compile_exp (App x y) = App (compile_exp x) (Delay T (compile_exp y)) ∧
  compile_exp (Lam v x) = Lam v (compile_exp x) ∧
  compile_exp (Letrec funs x) =
    Letrec (MAP (λ(fn, x). case x of
                             Lam v bod => (fn, v, compile_exp bod)
                           | _ => ("", "", Var "")) funs)
           (compile_exp x)
Termination
  WF_REL_TAC ‘measure exp_size’
  \\ dsimp [pure_expTheory.exp_size_def, LENGTH_EQ_NUM_compute]
  \\ rw []
  \\ (drule (CONJUNCT2 exp_size_lemma) ORELSE
      drule (CONJUNCT1 exp_size_lemma))
  \\ simp [pure_expTheory.exp_size_def]
End

Definition No_Value_def:
  No_Value (Var v) = T ∧
  No_Value (Prim op xs) = EVERY No_Value xs ∧
  No_Value (App x y) = (No_Value x ∧ No_Value y) ∧
  No_Value (Lam v x) = No_Value x ∧
  No_Value (Letrec f x) = (EVERY No_Value (MAP (SND o SND) f) ∧ No_Value x) ∧
  No_Value (If x y z) = (No_Value x ∧ No_Value y ∧ No_Value z) ∧
  No_Value (Delay T x) = No_Value x ∧
  No_Value (Force x) = No_Value x ∧
  No_Value (Value v) = F
Termination
  WF_REL_TAC ‘measure exp_size’ \\ rw []
  \\ fs [pairTheory.LAMBDA_PROD, MEM_MAP, pairTheory.EXISTS_PROD]
  \\ rename1 ‘MEM _ xs’
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [thunkLang_substTheory.exp_size_def]
End

Theorem compile_exp_No_Value:
  ∀x. No_Value (compile_exp x)
Proof
  ho_match_mp_tac compile_exp_ind
  \\ simp [compile_exp_def, No_Value_def]
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ strip_tac
  >- (
    rw [No_Value_def, EVERY_MAP, EVERY_MEM]
    \\ fs [])
  >- (
    simp [EVERY_MEM]
    \\ simp [MAP_MAP_o, MEM_MAP, pairTheory.EXISTS_PROD, PULL_EXISTS]
    \\ rpt gen_tac
    \\ CASE_TAC \\ fs [No_Value_def]
    \\ strip_tac
    \\ res_tac)
QED
 *)
val _ = export_theory ();

