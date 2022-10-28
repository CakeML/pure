
open HolKernel Parse boolLib bossLib term_tactic;
open stringTheory optionTheory pairTheory listTheory
     finite_mapTheory pred_setTheory pure_configTheory;

val _ = new_theory "pure_exp";

(* AST for a small functional language *)

Type vname = “:string”  (* variable name *)

Datatype:
  op = If                    (* if-expression                             *)
     | Cons string           (* datatype constructor                      *)
     | IsEq string num bool  (* compare cons tag and num of args (strict) *)
     | Proj string num       (* reading a field of a constructor          *)
     | AtomOp atom_op        (* primitive parametric operator over Atoms  *)
     | Seq                   (* diverges if arg1 does, else same as arg2  *)
End

Datatype:
  exp = Var vname                         (* variable                 *)
      | Prim op (exp list)                (* primitive operations     *)
      | App exp exp                       (* function application     *)
      | Lam vname exp                     (* lambda                   *)
      | Letrec ((vname # exp) list) exp   (* mutually recursive exps  *)
End

(* some abbreviations *)
Overload Let  = “λs x y. App (Lam s y) x”         (* let-expression    *)
Overload If   = “λx y z. Prim If [x; y; z]”       (* If   at exp level *)
Overload Cons = “λs. Prim (Cons s)”               (* Cons at exp level *)
Overload IsEq = “λs n t x. Prim (IsEq s n t) [x]” (* IsEq at exp level *)
Overload Proj = “λs i x. Prim (Proj s i) [x]”     (* Proj at exp level *)
Overload Seq  = “λx y. Prim Seq [x; y]”           (* Seq  at exp level *)
Overload Fail = “Prim (AtomOp Add) []”            (* causes Error      *)
Overload Lit  = “λl. Prim (AtomOp (Lit l)) []”    (* Lit at exp level  *)
Overload Tick = “λx. Letrec [] x”

Definition Apps_def:
  Apps x [] = x ∧
  Apps x (a::as) = Apps (App x a) as
End

Definition Lams_def:
  Lams [] b = b ∧
  Lams (v::vs) b = Lam v (Lams vs b)
End

Definition Bottom_def:
  Bottom = Letrec [("bot",Var "bot")] (Var "bot")
End

Definition freevars_def[simp]:
  freevars (Var n)        = {n} ∧
  freevars (Prim op es)   = BIGUNION (set (MAP freevars es)) ∧
  freevars (App e1 e2)    = freevars e1 ∪ freevars e2 ∧
  freevars (Lam n e)      = freevars e DELETE n ∧
  freevars (Letrec lcs e) =
    freevars e ∪ BIGUNION (set (MAP (λ(fn,e). freevars e) lcs))
      DIFF set (MAP FST lcs)
Termination
  WF_REL_TAC `measure exp_size` >> rw[] >> gvs[] >>
  rename1 `MEM _ l` >>
  Induct_on `l` >> rw[] >> gvs[fetch "-" "exp_size_def"]
End

Definition freevars_l_def[simp]:
  freevars_l (Var n)     = [n]                              ∧
  freevars_l (Prim _ es) = (FLAT (MAP freevars_l es))       ∧
  freevars_l (App e1 e2) = (freevars_l e1 ⧺ freevars_l e2)  ∧
  freevars_l (Lam n e)   = (FILTER ($≠ n) (freevars_l e))   ∧
  freevars_l (Letrec lcs e) =
    FILTER (\n. ¬ MEM n (MAP FST lcs))
           (freevars_l e ⧺ FLAT (MAP (λ(fn,e). freevars_l e) lcs))
Termination
  WF_REL_TAC `measure exp_size` >> rw[] >> gvs[] >>
  rename1 `MEM _ l` >>
  Induct_on `l` >> rw[] >> gvs[fetch "-" "exp_size_def"]
End

Definition boundvars_def[simp]:
  boundvars (Var n)        = ∅ ∧
  boundvars (Prim op es)   = BIGUNION (set (MAP boundvars es)) ∧
  boundvars (App e1 e2)    = boundvars e1 ∪ boundvars e2 ∧
  boundvars (Lam n e)      = n INSERT boundvars e ∧
  boundvars (Letrec lcs e) =
    boundvars e ∪ set (MAP FST lcs) ∪ BIGUNION (set (MAP (λ(fn,e). boundvars e) lcs))
Termination
  WF_REL_TAC `measure exp_size` >> rw[] >> gvs[] >>
  rename1 `MEM _ l` >>
  Induct_on `l` >> rw[] >> gvs[fetch "-" "exp_size_def"]
End

Definition boundvars_l_def[simp]:
  boundvars_l (Var n)     = []                                ∧
  boundvars_l (Prim _ es) = FLAT (MAP boundvars_l es)         ∧
  boundvars_l (App e1 e2) = (boundvars_l e1 ⧺ boundvars_l e2) ∧
  boundvars_l (Lam n e)   = n::boundvars_l e                  ∧
  boundvars_l (Letrec lcs e) =
    MAP FST lcs ++ FLAT (MAP (λ(v,e). boundvars_l e) lcs) ++ boundvars_l e
Termination
  WF_REL_TAC `measure exp_size` >> rw[] >> gvs[] >>
  rename1 `MEM _ l` >>
  Induct_on `l` >> rw[] >> gvs[fetch "-" "exp_size_def"]
End

Definition closed_def:
  closed e = (freevars e = {})
End

Theorem exp_size_lemma:
  (∀xs     a. MEM      a  xs ⇒ exp_size a < exp3_size xs) ∧
  (∀xs x   a. MEM   (x,a) xs ⇒ exp_size a < exp1_size xs)
Proof
  conj_tac \\ TRY conj_tac \\ Induct \\ rw []
  \\ res_tac \\ fs [fetch "-" "exp_size_def"]
QED

Definition subst_def:
  subst m (Var s) =
    (case FLOOKUP m s of
     | NONE => Var s
     | SOME x => x) ∧
  subst m (Prim op xs) = Prim op (MAP (subst m) xs) ∧
  subst m (App x y) = App (subst m x) (subst m y) ∧
  subst m (Lam s x) = Lam s (subst (m \\ s) x) ∧
  subst m (Letrec f x) =
    let m1 = FDIFF m (set (MAP FST f)) in
      Letrec (MAP (λ(f,e). (f,subst m1 e)) f) (subst m1 x)
Termination
  WF_REL_TAC `measure (exp_size o SND)` \\ rw []
  \\ imp_res_tac exp_size_lemma \\ fs []
End

Overload subst1 = ``λname v e. subst (FEMPTY |+ (name,v)) e``;

Definition bind_def:
  bind m e =
    if (∀n v. FLOOKUP m n = SOME v ⇒ closed v) then subst m e else Fail
End

Overload bind1 = ``λname v e. bind (FEMPTY |+ (name,v)) e``;

Definition subst_funs_def:
  subst_funs f = bind (FEMPTY |++ (MAP (λ(g,x). (g,Letrec f x)) f))
End

Definition expandLets_def:
   expandLets i cn nm ([]) cs = cs ∧
   expandLets i cn nm (v::vs) cs = Let v (Proj cn i (Var nm))
                                         (expandLets (i+1) cn nm vs cs)
End

Definition expandRows_def:
   expandRows nm [] = Fail ∧
   expandRows nm ((cn,vs,cs)::css) = If (IsEq cn (LENGTH vs) T (Var nm))
                                        (expandLets 0 cn nm vs cs)
                                        (expandRows nm css)
End

Definition expandCases_def:
   expandCases x nm css = (Let nm x (expandRows nm css))
End

Overload Case = “λx nm css. expandCases x nm css”

val _ = export_theory ();
