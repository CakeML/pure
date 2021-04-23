(*
  Expressions for thunkLang as seen by the compiler
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory pred_setTheory rich_listTheory finite_mapTheory;
open thunkLangTheory;

val _ = new_theory "thunkLang_cexp";

Datatype:
  cop = Cons string
      | AtomOp atom_op
End

Datatype:
  cexp = Var 'a vname
       | Prim 'a cop (cexp list)
       | App 'a cexp (cexp list)
       | Lam 'a (vname list) cexp
       | Letrec 'a ((vname # cexp) list) cexp
       | Let 'a (vname option) cexp cexp
       | If 'a cexp cexp cexp
       | Delay 'a cexp
       | Box 'a cexp
       | Force 'a cexp
       | Case 'a cexp vname ((vname # (vname list) # cexp) list)
End

Definition op_of_def:
  op_of (Cons s) : op = Cons s ∧
  op_of (AtomOp aop) = AtomOp aop
End

Definition Lams_def:
  Lams [] e = e ∧
  Lams (x::xs) e = Lam x (Lams xs e)
End

Definition Apps_def:
  Apps e [] = e ∧
  Apps e (x::xs) = Apps (App e x) xs
End

Definition lets_for_def:
  lets_for cn v [] b = b ∧
  lets_for cn v ((n,w)::ws) b =
    Let (SOME w) (Prim (Proj cn n) [Var v]) (lets_for cn v ws b)
End

Definition rows_of_def:
  rows_of v [] = Prim If [] ∧
  rows_of v ((cn,vs,b)::rest) =
    If (Prim (IsEq cn (LENGTH vs)) [Var v])
      (lets_for cn v (MAPi (λi v. (i,v)) vs) b) (rows_of v rest)
End

Definition exp_of_def:
  exp_of (Var c n) : exp  = Var n ∧
  exp_of (Prim c cop es)  = Prim (op_of cop) (MAP exp_of es) ∧
  exp_of (App c e es)     = Apps (exp_of e) (MAP exp_of es) ∧
  exp_of (Lam c xs e)     = Lams xs (exp_of e) ∧
  exp_of (Letrec c fns e) = Letrec (MAP (λ(f,x). (f, exp_of x)) fns) (exp_of e) ∧
  exp_of (Let c x e1 e2)  = Let x (exp_of e1) (exp_of e2) ∧
  exp_of (If c e e1 e2)   = If (exp_of e) (exp_of e1) (exp_of e2) ∧
  exp_of (Delay c e)      = Delay (exp_of e) ∧
  exp_of (Box c e)        = Box (exp_of e) ∧
  exp_of (Force c e)      = Force (exp_of e) ∧
  exp_of (Case c e v css) = Let (SOME v) (exp_of e)
                              (rows_of v (MAP (λ(cn,vs,e). (cn, vs, exp_of e)) css))
Termination
  WF_REL_TAC `measure $ cexp_size $ K 0` >>
  rw[fetch "-" "cexp_size_def"] >> gvs[] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[fetch "-" "cexp_size_def"]
End

Definition freevars_cexp_def[simp]:
  freevars_cexp (Var c v) = {v} ∧
  freevars_cexp (Prim c op es) = BIGUNION (set (MAP freevars_cexp es)) ∧
  freevars_cexp (App c e es) =
    freevars_cexp e ∪ BIGUNION (set (MAP freevars_cexp es)) ∧
  freevars_cexp (Lam c vs e) = freevars_cexp e DIFF set vs ∧
  freevars_cexp (Letrec c fns e) =
    freevars_cexp e ∪ BIGUNION (set (MAP (λ(fn,e). freevars_cexp e) fns))
      DIFF set (MAP FST fns) ∧
  freevars_cexp (Let c NONE e1 e2) = freevars_cexp e1 ∪ freevars_cexp e2 ∧
  freevars_cexp (Let c (SOME v) e1 e2) = freevars_cexp e1 ∪ (freevars_cexp e2 DELETE v) ∧
  freevars_cexp (If c e e1 e2) =
    freevars_cexp e ∪ freevars_cexp e1 ∪ freevars_cexp e2 ∧
  freevars_cexp (Delay c e) = freevars_cexp e ∧
  freevars_cexp (Box c e) = freevars_cexp e ∧
  freevars_cexp (Force c e) = freevars_cexp e ∧
  freevars_cexp (Case c e v css) = freevars_cexp e ∪
    (BIGUNION (set (MAP (λ(_,vs,ec). freevars_cexp ec DIFF set vs) css)) DELETE v)
Termination
  WF_REL_TAC `measure (cexp_size (K 0))` >> rw [] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[fetch "-" "cexp_size_def"]
End

Definition get_info_def:
  get_info (Var c _) = c ∧
  get_info (Prim c _ _) = c ∧
  get_info (App c _ _) = c ∧
  get_info (Lam c _ _) = c ∧
  get_info (Letrec c _ _) = c ∧
  get_info (Let c _ _ _) = c ∧
  get_info (If c _ _ _) = c ∧
  get_info (Delay c _) = c ∧
  get_info (Box c _ ) = c ∧
  get_info (Force c _ ) = c ∧
  get_info (Case c _ _ _) = c
End

val _ = export_theory();

