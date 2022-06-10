(*
   This file defines expressions for pure_lang as the type system sees them.
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open arithmeticTheory listTheory rich_listTheory alistTheory stringTheory
     optionTheory pairTheory pred_setTheory finite_mapTheory;
open pure_cexpTheory pure_cexp_lemmasTheory pure_expTheory pure_evalTheory
     pure_exp_lemmasTheory pure_exp_relTheory pure_congruenceTheory;

val _ = new_theory "pure_tcexp";

Datatype:
  tcexp = Var vname                           (* variable                 *)
        | Prim cop (tcexp list)               (* primitive operations     *)
        | App tcexp (tcexp list)              (* function application     *)
        | Lam (vname list) tcexp              (* lambda                   *)
        | Let vname tcexp tcexp               (* let                      *)
        | Letrec ((vname # tcexp) list) tcexp (* mutually recursive exps  *)
        | Case tcexp vname ((vname # vname list # tcexp) list) (* case of *)
        | SafeProj vname num num tcexp        (* typesafe projection      *)
End

Definition lets_for_def:
  lets_for cn a v [] b = b ∧
  lets_for cn a v ((n,w)::ws) b =
    Let w (If (IsEq cn a T (Var v)) (Proj cn n (Var v)) Bottom) (lets_for cn a v ws b)
End

Definition rows_of_def:
  rows_of v [] = Fail ∧
  rows_of v ((cn,vs,b)::rest) =
    If (IsEq cn (LENGTH vs) T (Var v))
      (lets_for cn (LENGTH vs) v (MAPi (λi v. (i,v)) vs) b) (rows_of v rest)
End

Definition exp_of_def:
  exp_of (Var n)       = ((Var n):exp) ∧
  exp_of (Prim p xs)   = Prim (op_of p) (MAP exp_of xs) ∧
  exp_of (Let v x y)   = Let v (exp_of x) (exp_of y) ∧
  exp_of (App f xs)    = Apps (exp_of f) (MAP exp_of xs) ∧
  exp_of (Lam vs x)    = Lams vs (exp_of x) ∧
  exp_of (Letrec rs x) = Letrec (MAP (λ(n,x). (n,exp_of x)) rs) (exp_of x) ∧
  exp_of (Case x v rs) = Let v (exp_of x)
                          (rows_of v (MAP (λ(c,vs,x). (c,vs,exp_of x)) rs)) ∧
  exp_of (SafeProj cn ar i e) =
    If (IsEq cn ar T (exp_of e)) (Proj cn i (exp_of e)) Bottom
Termination
  WF_REL_TAC `measure tcexp_size` \\ rw [fetch "-" "tcexp_size_def"] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[fetch "-" "tcexp_size_def"]
End

Definition tcexp_of_def:
  tcexp_of (Var d n : 'a cexp) = (Var n : tcexp) ∧
  tcexp_of (Prim d p xs)   = Prim p (MAP tcexp_of xs) ∧
  tcexp_of (Let d v x y)   = Let v (tcexp_of x) (tcexp_of y) ∧
  tcexp_of (App d f xs)    = App (tcexp_of f) (MAP tcexp_of xs) ∧
  tcexp_of (Lam d vs x)    = Lam vs (tcexp_of x) ∧
  tcexp_of (Letrec d rs x) = Letrec (MAP (λ(n,x). (n,tcexp_of x)) rs) (tcexp_of x) ∧
  tcexp_of (Case d x v rs) = Case (tcexp_of x) v
                                (MAP ( λ(c,vs,x). (c,vs,tcexp_of x)) rs) ∧
  tcexp_of _               = Lam [] ARB
Termination
  WF_REL_TAC `measure $ cexp_size $ K 0` \\ rw [cexp_size_def] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[cexp_size_def]
End

Definition freevars_tcexp_def[simp]:
  freevars_tcexp (Var v) = {v} ∧
  freevars_tcexp (Prim op es) = BIGUNION (set (MAP freevars_tcexp es)) ∧
  freevars_tcexp (App e es) =
    freevars_tcexp e ∪ BIGUNION (set (MAP freevars_tcexp es)) ∧
  freevars_tcexp (Lam vs e) = freevars_tcexp e DIFF set vs ∧
  freevars_tcexp (Let v e1 e2) = freevars_tcexp e1 ∪ (freevars_tcexp e2 DELETE v) ∧
  freevars_tcexp (Letrec fns e) =
    freevars_tcexp e ∪ BIGUNION (set (MAP (λ(fn,e). freevars_tcexp e) fns))
      DIFF set (MAP FST fns) ∧
  freevars_tcexp (Case e v css) = freevars_tcexp e ∪
    (BIGUNION (set (MAP (λ(_,vs,ec). freevars_tcexp ec DIFF set vs) css)) DELETE v) ∧
  freevars_tcexp (SafeProj cn ar i e) = freevars_tcexp e
Termination
  WF_REL_TAC `measure tcexp_size` >> rw [] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[fetch "-" "tcexp_size_def"]
End

Definition subst_tc_def:
  subst_tc f (Var v) = (case FLOOKUP f v of SOME e => e | NONE => Var v) ∧
  subst_tc f (Prim op es) = Prim op (MAP (subst_tc f) es) ∧
  subst_tc f (App e es) = App (subst_tc f e) (MAP (subst_tc f) es) ∧
  subst_tc f (Lam vs e) = Lam vs (subst_tc (FDIFF f (set vs)) e) ∧
  subst_tc f (Let v e1 e2) = Let v (subst_tc f e1) (subst_tc (f \\ v) e2) ∧
  subst_tc f (Letrec fns e) =
    Letrec
      (MAP (λ(fn,e). (fn, subst_tc (FDIFF f (set (MAP FST fns))) e)) fns)
      (subst_tc (FDIFF f (set (MAP FST fns))) e) ∧
  subst_tc f (Case e v css) =
    Case (subst_tc f e) v
      (MAP (λ(cn,vs,e). (cn,vs, subst_tc (FDIFF f (v INSERT set vs)) e)) css) ∧
  subst_tc f (SafeProj cn ar i e) = SafeProj cn ar i (subst_tc f e)
Termination
  WF_REL_TAC `measure (tcexp_size o SND)` >> rw [] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[fetch "-" "tcexp_size_def"]
End

Overload subst_tc1 = ``λname v e. subst_tc (FEMPTY |+ (name,v)) e``;

Definition tcexp_wf_def:
  tcexp_wf (Var v) = T ∧
  tcexp_wf (Prim op es) = (num_args_ok op (LENGTH es) ∧ EVERY tcexp_wf es) ∧
  tcexp_wf (App e es) = (tcexp_wf e ∧ EVERY tcexp_wf es ∧ es ≠ []) ∧
  tcexp_wf (Lam vs e) = (tcexp_wf e ∧ vs ≠ []) ∧
  tcexp_wf (Let v e1 e2) = (tcexp_wf e1 ∧ tcexp_wf e2) ∧
  tcexp_wf (Letrec fns e) = (EVERY tcexp_wf $ MAP SND fns ∧ tcexp_wf e ∧ fns ≠ []) ∧
  tcexp_wf (Case e v css) = (
    tcexp_wf e ∧ EVERY tcexp_wf $ MAP (SND o SND) css ∧
    css ≠ [] ∧ ¬ MEM v (FLAT $ MAP (FST o SND) css) ∧
    ∀cn. MEM cn (MAP FST css) ⇒ cn ∉ monad_cns) ∧
  tcexp_wf (SafeProj cn ar i e) = (tcexp_wf e ∧ i < ar)
Termination
  WF_REL_TAC `measure tcexp_size` >> rw[fetch "-" "tcexp_size_def"] >>
  gvs[MEM_MAP, EXISTS_PROD] >>
  rename1 `MEM _ es` >> Induct_on `es` >> rw[] >> gvs[fetch "-" "tcexp_size_def"]
End


val _ = export_theory();
