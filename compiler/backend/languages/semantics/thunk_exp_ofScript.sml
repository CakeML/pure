(*
  Definition of cexp -> exp function for thunkLang
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory combinTheory
     thunkLangTheory thunk_cexpTheory;

val _ = new_theory "thunk_exp_of";

val _ = set_grammar_ancestry ["thunkLang", "thunk_cexp"];

Definition lets_for_def:
  lets_for l cn v [] b = (b:thunkLang$exp) ∧
  lets_for l cn v ((n,w)::ws) b =
    Seq (If (IsEq cn l T (Var v)) Unit Fail) $
      Let (SOME w) (Proj cn n (Var v)) $
        lets_for l cn v ws b
End

Overload True[local] = “Prim (Cons "True") []”;
Overload False[local] = “Prim (Cons "False") []”;

Definition Disj_def:
  Disj v [] = False ∧
  Disj v ((cn,l)::xs) = If (IsEq cn l T (Var v)) True (Disj v xs)
End

Definition rows_of_def:
  rows_of v [] k =
    (case k of
     | NONE => Prim (AtomOp Add) []
     | SOME (alts,e) => If (Disj v alts) e Fail) ∧
  rows_of v ((cn,vs,b)::rest) k =
    If (IsEq cn (LENGTH vs) T (Var v))
      (lets_for (LENGTH vs) cn v (MAPi (λi v. (i,v)) vs) b) (rows_of v rest k)
End

Definition op_of_def[simp]:
  op_of (Cons m) = Cons (explode m) ∧
  op_of (AtomOp a) = AtomOp a
End

Definition exp_of_def[simp]:
  exp_of (Var n)         = Var (explode n):thunkLang$exp ∧
  exp_of (Prim p xs)     = Prim (op_of p) (MAP exp_of xs) ∧
  exp_of (Let w x y)     = Let (OPTION_MAP explode w) (exp_of x) (exp_of y) ∧
  exp_of (App f xs)      = Apps (exp_of f) (MAP exp_of xs) ∧
  exp_of (Lam vs x)      = Lams (MAP explode vs) (exp_of x) ∧
  exp_of (Letrec rs x)   = Letrec (MAP (λ(n,x). (explode n,exp_of x)) rs) (exp_of x) ∧
  exp_of (Case v rs d) =
      rows_of
        (explode v)
        (MAP (λ(c,vs,x). (explode c,MAP explode vs,exp_of x)) rs)
        (OPTION_MAP (λ(a,e). (MAP (explode ## I) a, exp_of e)) d) ∧
  exp_of (Force x)       = Force (exp_of x) ∧
  exp_of (Delay x)       = Delay (exp_of x) ∧
  exp_of (Box x)         = Box (exp_of x)
Termination
  WF_REL_TAC ‘measure cexp_size’ >> rw [cexp_size_eq]
End

Definition args_ok_def:
  args_ok (thunk_cexp$AtomOp aop) es =
    (num_atomop_args_ok aop (LENGTH es) ∧
     ∀s1 s2. aop ≠ Lit (Msg s1 s2) ∧ ∀l. aop ≠ Lit (Loc l)) ∧
  args_ok (Cons cn) es =
    if cn = «Ret» ∨ cn = «Raise» then
      (∃e0. es = [e0])
    else if cn = «Length» ∨ cn = «Act» then
      (∃e0. es = [Delay e0])
    else if cn = «Bind» ∨ cn = «Handle» ∨ cn = «Alloc» ∨ cn = «Deref» then
      (∃e0 e1. es = [Delay e0; Delay e1])
    else if cn = «Update» then
      (∃e0 e1 e2. es = [Delay e0; Delay e1; Delay e2])
    else T
End

Definition cexp_ok_bind_def:
  (cexp_ok_bind (Delay _ : cexp) = T) ∧
  (cexp_ok_bind (Lam _ _) = T) ∧
  (cexp_ok_bind _ = F)
End

Definition cexp_wf_def:
  cexp_wf (Var v) = T ∧
  cexp_wf (Prim op es) = (args_ok op es ∧ EVERY cexp_wf es) ∧
  cexp_wf (App e es) = (cexp_wf e ∧ EVERY cexp_wf es ∧ es ≠ []) ∧
  cexp_wf (Force e) = cexp_wf e ∧
  cexp_wf (Delay e) = cexp_wf e ∧
  cexp_wf (Box e) = cexp_wf e ∧
  cexp_wf (Lam vs e) = (cexp_wf e ∧ vs ≠ []) ∧
  cexp_wf (Let v e1 e2) = (cexp_wf e1 ∧ cexp_wf e2) ∧
  cexp_wf (Letrec fns e) = (EVERY (λ(_,x). cexp_ok_bind x ∧ cexp_wf x) fns ∧ cexp_wf e
                            ∧ fns ≠ [] ∧ ALL_DISTINCT (MAP FST fns)) ∧
  cexp_wf (Case v css eopt) = (
    EVERY (λ(_,_,x). cexp_wf x) css ∧
    (eopt = NONE ⇒ css ≠ []) ∧
    ¬ MEM v (FLAT $ MAP (FST o SND) css) ∧
    OPTION_ALL (λ(_,e). cexp_wf e) eopt ∧
    (∀cn. MEM cn (MAP FST css) ⇒ explode cn ∉ monad_cns))
Termination
  WF_REL_TAC ‘measure cexp_size’
End

Definition is_Delay_def:
  (is_Delay (Delay _ : cexp) = T) ∧
  (is_Delay _ = F)
End

val _ = export_theory ();
