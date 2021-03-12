(*
   This file defines expressions for pure_lang as the compiler sees them.
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory;

val _ = new_theory "pure_cexp";

Datatype:
  cop = Cons string        (* datatype constructor                     *)
      | AtomOp atom_op     (* primitive parametric operator over Atoms *)
      | Seq                (* diverges if arg1 does, else same as arg2 *)
End

Datatype:
  cexp = Var 'a vname                         (* variable                 *)
       | Prim 'a cop (cexp list)              (* primitive operations     *)
       | App 'a cexp (cexp list)              (* function application     *)
       | Lam 'a (vname list) cexp             (* lambda                   *)
       | Let 'a vname cexp cexp               (* let                      *)
       | Letrec 'a ((vname # cexp) list) cexp (* mutually recursive exps  *)
       | Case 'a cexp vname ((vname # vname list # cexp) list) (* case of *)
End

Theorem cexp_size_lemma:
  (∀xs a. MEM a xs ⇒ cexp_size f a < cexp6_size f xs) ∧
  (∀xs a1 a. MEM (a1,a) xs ⇒ cexp_size f a < cexp4_size f xs) ∧
  (∀xs a1 a2 a. MEM (a1,a2,a) xs ⇒ cexp_size f a < cexp1_size f xs)
Proof
  rpt conj_tac
  \\ Induct \\ rw [] \\ fs [fetch "-" "cexp_size_def"] \\ res_tac \\ fs []
QED

Definition op_of_def:
  op_of (Cons s) = Cons s ∧
  op_of (AtomOp p) = AtomOp p ∧
  op_of (Seq:cop) = (Seq:op)
End

Definition lets_for_def:
  lets_for cn v [] b = b ∧
  lets_for cn v ((n,w)::ws) b = Let w (Proj cn n (Var v)) (lets_for cn v ws b)
End

Definition rows_of_def:
  rows_of v [] = Fail ∧
  rows_of v ((cn,vs,b)::rest) =
    If (IsEq cn (LENGTH vs) (Var v))
      (lets_for cn v (MAPi (λi v. (i,v)) vs) b) (rows_of v rest)
End

Definition exp_of_def:
  exp_of (Var d n)       = ((Var n):exp) ∧
  exp_of (Prim d p xs)   = Prim (op_of p) (MAP exp_of xs) ∧
  exp_of (Let d v x y)   = Let v (exp_of x) (exp_of y) ∧
  exp_of (App _ f xs)    = Apps (exp_of f) (MAP exp_of xs) ∧
  exp_of (Lam d vs x)    = Lams vs (exp_of x) ∧
  exp_of (Letrec d rs x) = Letrec (MAP (λ(n,x). (n,exp_of x)) rs) (exp_of x) ∧
  exp_of (Case d x v rs) = Let v (exp_of x)
                             (rows_of v (MAP (λ(c,vs,x). (c,vs,exp_of x)) rs))
Termination
  WF_REL_TAC ‘measure (cexp_size (K 0))’ \\ rw []
  \\ imp_res_tac cexp_size_lemma
  \\ first_x_assum (qspec_then ‘K 0’ mp_tac) \\ fs []
End

val _ = export_theory();
