
open HolKernel Parse boolLib bossLib term_tactic;
open stringTheory optionTheory configTheory pairTheory listTheory
     finite_mapTheory pred_setTheory;

val _ = new_theory "exp";

(* AST for a small functional language *)

Type vname = “:string”  (* variable name *)

Datatype:
  op = If                 (* if-expression                            *)
     | Cons string        (* datatype constructor                     *)
     | IsEq string num    (* compare cons tag and num of args         *)
     | Proj string num    (* reading a field of a constructor         *)
     | AtomOp atom_op     (* primitive parametric operator over Atoms *)
     | Lit lit            (* parametric literal Atom                  *)
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
Overload Lit  = “λa. Prim (Lit a) []”          (* Lit  at exp level *)
Overload Cons = “λs. Prim (Cons s)”            (* Cons at exp level *)
Overload IsEq = “λs n x. Prim (IsEq s n) [x]”  (* IsEq at exp level *)
Overload Proj = “λs i x. Prim (Proj s i) [x]”  (* Proj at exp level *)
Overload Fail = “Prim (Lit ARB) [Prim (Lit ARB)[]]” (* causes Error *)

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

Definition bind_def:
  bind m e =
    if (∀n v. FLOOKUP m n = SOME v ⇒ closed v) then subst m e else Fail
End

Theorem subst_ignore:
  ∀m e. DISJOINT (freevars e) (FDOM m) ⇒ subst m e = e
Proof
  ho_match_mp_tac subst_ind \\ rw [] \\ fs [subst_def] \\ rw[]
  >- fs[FLOOKUP_DEF]
  >- (Induct_on `xs` >> fs[])
  >- (
    first_x_assum irule >>
    fs[DISJOINT_DEF, EXTENSION] >>
    metis_tac[]
    )
  >- (
    rw[LIST_EQ_REWRITE] >> fs[MEM_EL, PULL_EXISTS, EL_MAP] >>
    Cases_on `EL x f` >> fs[] >> rename1 `(fn_name, fn_body)` >>
    first_x_assum drule >> fs[] >> disch_then irule >>
    fs[DISJOINT_DEF, EXTENSION] >> rw[] >> rename1 `var ∉ _` >>
    first_assum (qspec_then `var` assume_tac) >> fs[] >>
    first_x_assum (qspec_then `freevars fn_body` assume_tac) >> gvs[] >>
    pop_assum mp_tac >> simp[MEM_MAP] >> strip_tac >>
    pop_assum (qspec_then `(fn_name,fn_body)` assume_tac) >> gvs[MEM_EL] >>
    pop_assum mp_tac >> simp[MEM_EL] >> strip_tac >>
    pop_assum (qspec_then `x` assume_tac) >> gvs[]
    )
  >- (
    first_x_assum irule >>
    fs[DISJOINT_DEF, EXTENSION] >> rw[] >>
    first_x_assum (qspec_then `x` assume_tac) >> fs[]
    )
QED

Theorem closed_subst[simp]:
  ∀m e. closed e ⇒ subst m e = e
Proof
  rw [] \\ match_mp_tac subst_ignore \\ fs [closed_def]
QED

Theorem subst_subst:
  ∀m1 e m2.
    DISJOINT (FDOM m1) (FDOM m2) ∧
    (∀v1. v1 ∈ FRANGE m1 ⇒ closed v1) ∧
    (∀v2. v2 ∈ FRANGE m2 ⇒ closed v2)
  ⇒ subst m1 (subst m2 e) = subst m2 (subst m1 e)
Proof
  ho_match_mp_tac subst_ind >> rw[subst_def] >> gvs[]
  >- (
    fs[DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >>
    last_assum (qspec_then `s` assume_tac) >> fs[]
    >- (
      IF_CASES_TAC >> gvs[subst_def, FLOOKUP_DEF, IN_FRANGE] >>
      irule closed_subst >> first_x_assum irule >>
      goal_assum drule >> fs[]
      )
    >- (
      IF_CASES_TAC >> gvs[subst_def, FLOOKUP_DEF, IN_FRANGE] >>
      irule (GSYM closed_subst) >> last_x_assum irule >>
      goal_assum drule >> fs[]
      )
    )
  >- (
    fs[MAP_MAP_o, combinTheory.o_DEF] >>
    rw[MAP_EQ_f] >> first_x_assum irule >> fs[]
    )
  >- (first_x_assum irule >> fs[])
  >- (first_x_assum irule >> fs[])
  >- (
    first_x_assum irule >> fs[] >>
    gvs[IN_FRANGE, PULL_EXISTS, DOMSUB_FAPPLY_THM, DISJOINT_DEF, EXTENSION] >>
    rw[] >> Cases_on `x = s` >> fs[]
    )
  >- (
    rw[LIST_EQ_REWRITE] >> gvs[MEM_EL, PULL_EXISTS, EL_MAP] >>
    Cases_on `EL x f` >> rename1 `(fn_name, fn_body)` >> gvs[] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >>
    first_x_assum irule >>
    gvs[IN_FRANGE, PULL_EXISTS] >>
    simp[FDIFF_def, DRESTRICT_DEF, GSYM CONJ_ASSOC] >>
    goal_assum drule >> fs[] >>
    fs[DISJOINT_DEF, EXTENSION] >> rw[] >> rename1 `foo ∉ _` >>
    Cases_on `MEM foo (MAP FST f)` >> fs[]
    )
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >>
    first_x_assum irule >>
    gvs[IN_FRANGE, PULL_EXISTS] >>
    simp[FDIFF_def, DRESTRICT_DEF] >>
    fs[DISJOINT_DEF, EXTENSION] >> rw[] >> rename1 `foo ∉ _` >>
    Cases_on `MEM foo (MAP FST f)` >> fs[]
    )
QED

Theorem FDIFF_FUNION:
  ∀fm1 fm2 s. FDIFF (fm1 ⊌ fm2) s = (FDIFF fm1 s) ⊌ (FDIFF fm2 s)
Proof
  rw[FDIFF_def, DRESTRICTED_FUNION] >>
  rw[fmap_eq_flookup] >>
  rw[FLOOKUP_DRESTRICT, FLOOKUP_FUNION] >> fs[] >>
  rw[FLOOKUP_DEF]
QED

Theorem subst_subst_FUNION:
  ∀m1 e m2.
    (∀v. v ∈ FRANGE m2 ⇒ closed v)
  ⇒ subst m1 (subst m2 e) = subst (m2 ⊌ m1) e
Proof
  ho_match_mp_tac subst_ind >> rw[subst_def] >> gvs[FRANGE_FLOOKUP, PULL_EXISTS]
  >- (
    gvs[FLOOKUP_FUNION] >>
    reverse CASE_TAC >> gvs[subst_def]
    >- (irule closed_subst >> res_tac)
    )
  >- (
    fs[MAP_MAP_o, combinTheory.o_DEF] >>
    rw[MAP_EQ_f] >>
    first_x_assum irule >> simp[] >> gvs[]
    )
  >- (
    gvs[DOMSUB_FUNION] >>
    first_x_assum irule >>
    gvs[DOMSUB_FLOOKUP_THM] >> rw[] >>
    res_tac
    )
  >- (
    fs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >>
    rw[MAP_EQ_f] >> rename1 `MEM fn f` >> PairCases_on `fn` >> gvs[] >>
    rw[FDIFF_FUNION] >>
    first_x_assum irule >>
    gvs[FDIFF_def, FLOOKUP_DRESTRICT] >> rw[] >> res_tac >>
    goal_assum drule
    )
  >- (
    rw[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >>
    rw[FDIFF_FUNION] >>
    first_x_assum irule >>
    gvs[FDIFF_def, FLOOKUP_DRESTRICT] >> rw[] >> res_tac
    )
QED

Theorem subst_subst_single:
  ∀m e n v.
    closed v ⇒
    subst (m |+ (n,v)) e = subst m (subst (FEMPTY |+ (n,v)) e)
Proof
  rw[] >>
  simp[Once FUPDATE_EQ_FUNION] >>
  irule (GSYM subst_subst_FUNION) >>
  fs[FRANGE_FLOOKUP, FLOOKUP_UPDATE, PULL_EXISTS]
QED

Theorem bind_bind_single:
  ∀m e n v.
    closed v ∧ n ∉ FDOM m ⇒
    bind (m |+ (n,v)) e = bind m (bind (FEMPTY |+ (n,v)) e)
Proof
  rw[] >> fs[bind_def] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >>
    gvs[FLOOKUP_UPDATE] >>
    rename1 `if n1 = n2 then _ else _` >>
    Cases_on `n1 = n2` >> gvs[] >>
    res_tac
    ) >>
  reverse (IF_CASES_TAC) >> gvs[]
  >- (
    gvs[FLOOKUP_UPDATE] >>
    rename1 `FLOOKUP _ n2` >> rename1 `n1 ∉ _` >>
    `n1 ≠ n2` by (gvs[flookup_thm] >> CCONTR_TAC >> gvs[]) >>
    first_assum (qspec_then `n2` assume_tac) >> gvs[]
    ) >>
  IF_CASES_TAC >> gvs[FLOOKUP_UPDATE] >>
  fs[Once subst_subst_single]
QED

Theorem bind_bind:
  ∀m1 m2 e.
    (∀v. v ∈ FRANGE m1 ⇒ closed v) ∧ DISJOINT (FDOM m1) (FDOM m2)
  ⇒ bind m1 (bind m2 e) = bind (m2 ⊌ m1) e
Proof
  rw[] >> fs[bind_def, FRANGE_FLOOKUP, PULL_EXISTS, DISJOINT_DEF, EXTENSION] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    IF_CASES_TAC >> gvs[] >>
    gvs[FLOOKUP_FUNION] >>
    imp_res_tac flookup_thm >> res_tac
    ) >>
  reverse (IF_CASES_TAC) >> gvs[FLOOKUP_FUNION]
  >- (
    IF_CASES_TAC >> gvs[subst_def] >>
    pop_assum (qspec_then `n` assume_tac) >> gvs[]
    ) >>
  reverse (IF_CASES_TAC) >> gvs[]
  >- (Cases_on `FLOOKUP m2 n` >> gvs[] >> res_tac) >>
  irule subst_subst_FUNION >> gvs[FRANGE_FLOOKUP, PULL_EXISTS]
QED

Theorem subst_FEMPTY:
  ∀e. subst FEMPTY e = e
Proof
  rw[] >> irule subst_ignore >> fs[]
QED

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
