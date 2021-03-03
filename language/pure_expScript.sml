
open HolKernel Parse boolLib bossLib term_tactic;
open stringTheory optionTheory pairTheory listTheory
     finite_mapTheory pred_setTheory pure_configTheory;

val _ = new_theory "pure_exp";

(* AST for a small functional language *)

Type vname = “:string”  (* variable name *)

Datatype:
  op = If                 (* if-expression                            *)
     | Cons string        (* datatype constructor                     *)
     | IsEq string num    (* compare cons tag and num of args         *)
     | Proj string num    (* reading a field of a constructor         *)
     | AtomOp atom_op     (* primitive parametric operator over Atoms *)
     | Seq                (* diverges if arg1 does, else same as arg2 *)
End

Datatype:
  exp = Var vname                         (* variable                 *)
      | Prim op (exp list)                (* primitive operations     *)
      | App exp exp                       (* function application     *)
      | Lam vname exp                     (* lambda                   *)
      | Letrec ((vname # exp) list) exp   (* mutually recursive exps  *)
End

(* some abbreviations *)
Overload Let  = “λs x y. App (Lam s y) x”      (* let-expression    *)
Overload If   = “λx y z. Prim If [x; y; z]”    (* If   at exp level *)
Overload Cons = “λs. Prim (Cons s)”            (* Cons at exp level *)
Overload IsEq = “λs n x. Prim (IsEq s n) [x]”  (* IsEq at exp level *)
Overload Proj = “λs i x. Prim (Proj s i) [x]”  (* Proj at exp level *)
Overload Seq  = “λx y. Prim Seq [x; y]”        (* Seq  at exp level *)
Overload Fail = “Prim If []”                   (* causes Error      *)

Definition Bottom_def:
  Bottom = Letrec [("bot",Var "bot")] (Var "bot")
End

Definition freevars_def[simp]:
  freevars (Var n)     = [n]                               ∧
  freevars (Prim _ es) = (FLAT (MAP freevars es))          ∧
  freevars (App e1 e2) = (freevars e1 ⧺ freevars e2)       ∧
  freevars (Lam n e)   = (FILTER ($≠ n) (freevars e))      ∧
  freevars (Letrec lcs e) =
    FILTER (\n. ¬ MEM n (MAP FST lcs))
           (freevars e ⧺ FLAT (MAP (λ(fn,e). freevars e) lcs))
Termination
  WF_REL_TAC ‘measure exp_size’ \\ fs[]
  \\ conj_tac \\ TRY conj_tac
  \\ TRY (Induct_on ‘lcs’)
  \\ TRY (Induct_on ‘css’)
  \\ TRY (Induct_on ‘es’)
  \\ rw [] \\ fs [fetch "-" "exp_size_def"] \\ res_tac \\ fs[]
  \\ pop_assum (assume_tac o SPEC_ALL) \\ fs[]
End

Overload freevars = “λe. set (freevars e)”

Theorem freevars_set_def[simp]:
  (∀n.     freevars (Var n)        = {n}) ∧
  (∀op es. freevars (Prim op es)   = BIGUNION (set (MAP freevars es))) ∧
  (∀e1 e2. freevars (App e1 e2)    = freevars e1 ∪ freevars e2) ∧
  (∀n e.   freevars (Lam n e)      = freevars e DELETE n) ∧
  (∀lcs e. freevars (Letrec lcs e) =
    freevars e ∪ BIGUNION (set (MAP (λ(fn,e). freevars e) lcs))
      DIFF set (MAP FST lcs))
Proof
  rw[freevars_def, LIST_TO_SET_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  rw[LIST_TO_SET_FILTER, DELETE_DEF, EXTENSION] >>
  fs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  eq_tac >> rw[] >> fs[] >>
  DISJ2_TAC >> qexists_tac `y` >> fs[] >>
  PairCases_on `y` >> fs[]
QED

Definition boundvars_def[simp]:
  boundvars (Var n)     = []                                ∧
  boundvars (Prim _ es) = FLAT (MAP boundvars es)           ∧
  boundvars (App e1 e2) = (boundvars e1 ⧺ boundvars e2)     ∧
  boundvars (Lam n e)   = n::boundvars e                    ∧
  boundvars (Letrec lcs e) =
    FLAT (MAP (λ(v,e). v::boundvars e) lcs) ++ boundvars e
Termination
  WF_REL_TAC ‘measure exp_size’ \\ fs[]
  \\ conj_tac
  \\ TRY (Induct_on ‘lcs’)
  \\ TRY (Induct_on ‘es’)
  \\ rw[] \\ fs [fetch "-" "exp_size_def"] \\ res_tac \\ fs[]
  \\ pop_assum (assume_tac o SPEC_ALL) \\ fs[]
End

Overload boundvars = “λe. set (boundvars e)”

Theorem boundvars_set_def[simp]:
  (∀n.     boundvars (Var n)        = ∅) ∧
  (∀op es. boundvars (Prim op es)   = BIGUNION (set (MAP boundvars es))) ∧
  (∀e1 e2. boundvars (App e1 e2)    = boundvars e1 ∪ boundvars e2) ∧
  (∀n e.   boundvars (Lam n e)      = n INSERT boundvars e) ∧
  (∀lcs e. boundvars (Letrec lcs e) =
    boundvars e ∪ BIGUNION (set (MAP (λ(fn,e). fn INSERT boundvars e) lcs)) )
Proof
  rw[boundvars_def, LIST_TO_SET_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  rw[LIST_TO_SET_FILTER, DELETE_DEF, EXTENSION] >>
  fs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  eq_tac >> rw[] >> fs[]
  >- ( DISJ2_TAC >> qexists_tac ‘x'’ >> Cases_on ‘x'’ >> fs[])
  >>   DISJ1_TAC >> qexists_tac ‘y’  >> Cases_on ‘y’  >> fs[]
QED

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

Overload subst = ``λname v e. subst (FEMPTY |+ (name,v)) e``;

Definition bind_def:
  bind m e =
    if (∀n v. FLOOKUP m n = SOME v ⇒ closed v) then subst m e else Fail
End

Overload bind = ``λname v e. bind (FEMPTY |+ (name,v)) e``;

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
   expandRows nm ((cn,vs,cs)::css) = If (IsEq cn (LENGTH vs) (Var nm))
                                        (expandLets 0 cn nm vs cs)
                                        (expandRows nm css)
End

Definition expandCases_def:
   expandCases x nm css = (Let nm x (expandRows nm css))
End

Overload Case = “λx nm css. expandCases x nm css”

val _ = export_theory ();
