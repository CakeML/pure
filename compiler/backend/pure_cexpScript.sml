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
    If (IsEq cn (LENGTH vs) T (Var v))
      (lets_for cn v (MAPi (λi v. (i,v)) vs) b) (rows_of v rest)
End

Definition exp_of_def:
  exp_of (Var d n)       = ((Var n):exp) ∧
  exp_of (Prim d p xs)   = Prim (op_of p) (MAP exp_of xs) ∧
  exp_of (Let d v x y)   = Let v (exp_of x) (exp_of y) ∧
  exp_of (App _ f xs)    = Apps (exp_of f) (MAP exp_of xs) ∧
  exp_of (Lam d vs x)    = Lams vs (exp_of x) ∧
  exp_of (Letrec d rs x) = Letrec (MAP (λ(n,x). (n,exp_of x)) rs) (exp_of x) ∧
  exp_of (Case d x v rs) =
    (let caseexp =
       Let v (exp_of x) (rows_of v (MAP (λ(c,vs,x). (c,vs,exp_of x)) rs))
     in if MEM v (FLAT (MAP (FST o SND) rs)) then
       Seq Fail caseexp
     else
       caseexp)
Termination
  WF_REL_TAC ‘measure (cexp_size (K 0))’ \\ rw []
  \\ imp_res_tac cexp_size_lemma
  \\ first_x_assum (qspec_then ‘K 0’ mp_tac) \\ fs []
End

Definition freevars_cexp_def[simp]:
  freevars_cexp (Var c v) = {v} ∧
  freevars_cexp (Prim c op es) = BIGUNION (set (MAP freevars_cexp es)) ∧
  freevars_cexp (App c e es) =
    freevars_cexp e ∪ BIGUNION (set (MAP freevars_cexp es)) ∧
  freevars_cexp (Lam c vs e) = freevars_cexp e DIFF set vs ∧
  freevars_cexp (Let c v e1 e2) = freevars_cexp e1 ∪ (freevars_cexp e2 DELETE v) ∧
  freevars_cexp (Letrec c fns e) =
    freevars_cexp e ∪ BIGUNION (set (MAP (λ(fn,e). freevars_cexp e) fns))
      DIFF set (MAP FST fns) ∧
  freevars_cexp (Case c e v css) = freevars_cexp e ∪
    (BIGUNION (set (MAP (λ(_,vs,ec). freevars_cexp ec DIFF set vs) css)) DELETE v)
Termination
  WF_REL_TAC `measure (cexp_size (K 0))` >> rw [] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[fetch "-" "cexp_size_def"]
End

Definition freevars_cexp_l_def[simp]:
  freevars_cexp_l (Var c v) = [v] ∧
  freevars_cexp_l (Prim c op es) = FLAT (MAP freevars_cexp_l es) ∧
  freevars_cexp_l (App c e es) =
    freevars_cexp_l e ++ FLAT (MAP freevars_cexp_l es) ∧
  freevars_cexp_l (Lam c vs e) = FILTER (λv. ¬MEM v vs) (freevars_cexp_l e) ∧
  freevars_cexp_l (Let c v e1 e2) =
    freevars_cexp_l e1 ++ (FILTER ($≠ v) (freevars_cexp_l e2)) ∧
  freevars_cexp_l (Letrec c fns e) =
    FILTER (λv. ¬MEM v (MAP FST fns))
      (freevars_cexp_l e ++ FLAT (MAP (λ(fn,e). freevars_cexp_l e) fns)) ∧
  freevars_cexp_l (Case c e v css) = freevars_cexp_l e ++
    FILTER ($≠ v)
      (FLAT (MAP (λ(_,vs,ec). FILTER (λv. ¬MEM v vs) (freevars_cexp_l ec)) css))
Termination
  WF_REL_TAC `measure (cexp_size (K 0))` >> rw [] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[fetch "-" "cexp_size_def"]
End

Definition substc_def:
  substc f (Var c v) = (case FLOOKUP f v of SOME e => e | NONE => Var c v) ∧
  substc f (Prim c op es) = Prim c op (MAP (substc f) es) ∧
  substc f (App c e es) = App c (substc f e) (MAP (substc f) es) ∧
  substc f (Lam c vs e) = Lam c vs (substc (FDIFF f (set vs)) e) ∧
  substc f (Let c v e1 e2) = Let c v (substc f e1) (substc (f \\ v) e2) ∧
  substc f (Letrec c fns e) =
    Letrec c
      (MAP (λ(fn,e). (fn, substc (FDIFF f (set (MAP FST fns))) e)) fns)
      (substc (FDIFF f (set (MAP FST fns))) e) ∧
  substc f (Case c e v css) =
    Case c (substc f e) v
      (MAP (λ(cn,vs,e). (cn,vs, substc (FDIFF f (v INSERT set vs)) e)) css)
Termination
  WF_REL_TAC `measure (cexp_size (K 0) o  SND)` >> rw [] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[fetch "-" "cexp_size_def"]
End

Overload substc1 = ``λname v e. substc (FEMPTY |+ (name,v)) e``;

Definition get_info_def:
  get_info (Var c _) = c ∧
  get_info (Prim c _ _) = c ∧
  get_info (App c _ _) = c ∧
  get_info (Lam c _ _) = c ∧
  get_info (Let c _ _ _) = c ∧
  get_info (Letrec c _ _) = c ∧
  get_info (Case c _ _ _) = c
End

Definition cexp_wf_def:
  cexp_wf (Var _ v) = T ∧
  cexp_wf (Prim _ op es) = EVERY cexp_wf es ∧
  cexp_wf (App _ e es) = (cexp_wf e ∧ EVERY cexp_wf es ∧ es ≠ []) ∧
  cexp_wf (Lam _ vs e) = (cexp_wf e ∧ vs ≠ []) ∧
  cexp_wf (Let _ v e1 e2) = (cexp_wf e1 ∧ cexp_wf e2) ∧
  cexp_wf (Letrec _ fns e) = (EVERY cexp_wf $ MAP SND fns ∧ cexp_wf e ∧ fns ≠ []) ∧
  cexp_wf (Case _ e v css) = (
    cexp_wf e ∧ EVERY cexp_wf $ MAP (SND o SND) css ∧ css ≠ [] ∧
    ¬ MEM v (FLAT $ MAP (FST o SND) css))
Termination
  WF_REL_TAC `measure $ cexp_size (K 0)` >> rw[fetch "-" "cexp_size_def"] >>
  gvs[MEM_MAP, EXISTS_PROD] >>
  rename1 `MEM _ es` >> Induct_on `es` >> rw[] >> gvs[fetch "-" "cexp_size_def"]
End

Definition cexp_eq_def:
  cexp_eq (Var _ v1) (Var _ v2) = (v1 = v2) ∧
  cexp_eq (Prim _ op1 es1) (Prim _ op2 es2) = (
    op1 = op2 ∧ LIST_REL (λe1 e2. cexp_eq e1 e2) es1 es2) ∧
  cexp_eq (App _ e1 es1) (App _ e2 es2) = (
    cexp_eq e1 e2 ∧ LIST_REL (λe1 e2. cexp_eq e1 e2) es1 es2) ∧
  cexp_eq (Lam _ vs1 e1) (Lam _ vs2 e2) = (vs1 = vs2 ∧ cexp_eq e1 e2) ∧
  cexp_eq (Let _ v1 e11 e12) (Let _ v2 e21 e22) = (
    v1 = v2 ∧ cexp_eq e11 e21 ∧ cexp_eq e12 e22) ∧
  cexp_eq (Letrec _ fns1 e1) (Letrec _ fns2 e2) = (cexp_eq e1 e2 ∧
    LIST_REL (λ(fn1,e1) (fn2,e2). fn1 = fn2 ∧ cexp_eq e1 e2) fns1 fns2) ∧
  cexp_eq (Case _ e1 v1 css1) (Case _ e2 v2 css2) = (
    cexp_eq e1 e2 ∧ v1 = v2 ∧
    LIST_REL (λ(cn1,vs1,e1) (cn2,vs2,e2). cn1 = cn2 ∧ vs1 = vs2 ∧ cexp_eq e1 e2)
      css1 css2)
Termination
  WF_REL_TAC `measure $ cexp_size (K 0) o SND` >> rw[fetch "-" "cexp_size_def"] >>
  rename1 `MEM _ es` >> Induct_on `es` >> rw[] >> gvs[fetch "-" "cexp_size_def"]
End

val _ = export_theory();
