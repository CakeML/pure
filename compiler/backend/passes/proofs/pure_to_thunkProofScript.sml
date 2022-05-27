(*
  Proof of correctness for the pure_to_thunk compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     pure_semanticsTheory thunk_semanticsTheory pure_evalTheory
     thunkLang_primitivesTheory pure_exp_lemmasTheory pure_miscTheory
     pure_to_thunk_1ProofTheory pure_cexpTheory
     thunk_case_liftProofTheory
     thunk_case_d2bProofTheory;

val _ = new_theory "pure_to_thunkProof";

val _ = set_grammar_ancestry ["pure_to_thunk_1Proof","pure_cexp","thunkLang"];

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
     MAP FST xs = MAP FST ys ∧
     MAP (FST o SND) xs = MAP (FST o SND) ys ∧
     LIST_REL exp_rel (MAP (SND o SND) xs) (MAP (SND o SND) ys) ⇒
       exp_rel (Case i x v xs)
         (Let (SOME fresh) a_exp $
          Let (SOME v) (Box (Var fresh)) $
            rows_of fresh ys))
End

Overload to_thunk = “pure_to_thunk_1Proof$exp_rel”
Overload lift_rel = “thunk_case_liftProof$exp_rel”

(*
Theorem exp_rel_imp_combined:
  ∀x y.
    exp_rel x y ⇒
    ∃x1 y1 y2.
      tick_rel (exp_of x) x1 ∧
      to_thunk x1 y1 ∧
      thunk_tick_rel y1 y2 ∧
      lift_rel y2 y3
      thunk_tick_rel y3 y4 ∧
      ARB
Proof
  cheat
QED
*)

(*

TODO:
 - remove ticks from pure_to_thunk_1Proof
 - remove closed from Letrec in pure_to_thunk_1Proof
 - remove ticks from thunk_case_liftProof

*)

val _ = export_theory ();
