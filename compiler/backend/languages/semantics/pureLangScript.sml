(*
  Conversion of ``:cexp`` from pure_cexpTheory to ``:exp``
*)
open HolKernel Parse boolLib bossLib;
open pairTheory listTheory pred_setTheory combinTheory pure_expTheory pure_cexpTheory;

val _ = new_theory "pureLang";

Overload True[local] = “Prim (Cons "True") []”;
Overload False[local] = “Prim (Cons "False") []”;

Definition Disj_def:
  Disj v [] = False ∧
  Disj v ((cn,l)::xs) = If (IsEq cn l T (Var v)) True (Disj v xs)
End

Definition lets_for_def:
  lets_for cn v [] b = b ∧
  lets_for cn v ((n,w)::ws) b = Let w (Proj cn n (Var v)) (lets_for cn v ws b)
End

Definition rows_of_def:
  rows_of v k [] = k ∧
  rows_of v k ((cn,vs,b)::rest) =
    If (IsEq cn (LENGTH vs) T (Var v))
      (lets_for cn v (MAPi (λi v. (i,v)) vs) b) (rows_of v k rest)
End

Definition patguards_def:
  patguards [] = (Prim (Cons "True") [], []) ∧
  patguards (ep::eps) =
  case ep of
  | (e, cepatVar v) => (I ## CONS (v,e)) (patguards eps)
  | (e, cepatUScore) => patguards eps
  | (e, cepatCons cnm ps) =>
      let
        cnml = explode cnm ;
        (gd, binds) = patguards (MAPi (λi p. (Proj cnml i e, p)) ps ++ eps) ;
      in
        (If (IsEq cnml (LENGTH ps) T e) gd (Prim (Cons "False") []),
         binds)
Termination
  WF_REL_TAC ‘measure (list_size cepat_size o MAP SND)’ >>
  simp[listTheory.list_size_def, cepat_size_def, combinTheory.o_DEF,
       listTheory.list_size_append, cepat_size_eq]
End

Definition nested_rows_def[simp]:
  nested_rows v [] = Fail ∧
  nested_rows v (pe :: pes) =
  let (gd, binds) = patguards [(v,FST pe)]
  in
    If gd
       (FOLDR (λ(u,e) A. Let (explode u) e A) (SND pe) binds)
       (nested_rows v pes)
End

Definition IfDisj_def:
  IfDisj v a e =
    If (Disj (explode v) (MAP (explode ## I) a)) e Fail
End

Definition exp_of_def:
  exp_of (Var d n)       = Var (explode n):exp ∧
  exp_of (Prim d p xs)   = Prim (op_of p) (MAP exp_of xs) ∧
  exp_of (Let d v x y)   = Let (explode v) (exp_of x) (exp_of y) ∧
  exp_of (App _ f xs)    = Apps (exp_of f) (MAP exp_of xs) ∧
  exp_of (Lam d vs x)    = Lams (MAP explode vs) (exp_of x) ∧
  exp_of (Letrec d rs x) =
    Letrec (MAP (λ(n,x). (explode n,exp_of x)) rs) (exp_of x) ∧
  exp_of (Case d x v rs eopt) =
    (let
       k = (case eopt of
            | NONE => Fail
            | SOME (a,e) => IfDisj v a (exp_of e)) ;
       caseexp =
       Let (explode v) (exp_of x)
           (rows_of (explode v) k
            (MAP (λ(c,vs,x). (explode c,MAP explode vs,exp_of x)) rs))
     in if MEM v (FLAT (MAP (FST o SND) rs)) then
       Seq Fail caseexp
     else
       caseexp) ∧
  exp_of (NestedCase d g gv p e pes) =
  Let (explode gv) (exp_of g)
      (nested_rows (Var (explode gv))
       (MAP (λ(p,e). (p, exp_of e)) ((p,e)::pes)))
Termination
  WF_REL_TAC ‘measure (cexp_size (K 0))’ >> rw [cexp_size_eq] >>
  simp[] >>
  FIRST (map (drule_then $ qspec_then ‘K 0’ assume_tac) $
         CONJUNCTS cexp_size_lemma) >>
  gs[cexp_size_eq]
End

Definition allvars_of_def[simp]:
  allvars_of (pure_cexp$Var c v) =
    {explode v} ∧
  allvars_of (Lam c ns x) =
    set (MAP explode ns) UNION allvars_of x ∧
  allvars_of (Letrec c xs y) =
    set (MAP (explode o FST) xs) UNION
    BIGUNION (set (MAP (allvars_of o SND) xs)) UNION
    allvars_of y ∧
  allvars_of (Prim c p xs) =
    BIGUNION (set (MAP allvars_of xs)) ∧
  allvars_of (App c x ys) =
    allvars_of x UNION
    BIGUNION (set (MAP allvars_of ys)) ∧
  allvars_of (Let c n x y) =
    {explode n} UNION allvars_of x UNION allvars_of y ∧
  allvars_of (Case c x n ys eopt) =
    {explode n} UNION
    BIGUNION (set (MAP (set o MAP explode o FST o SND) ys)) UNION
    BIGUNION (set (MAP (allvars_of o SND o SND) ys)) UNION
    allvars_of x UNION
      (case eopt of
       | NONE => {}
       | SOME (a,e) => allvars_of e) ∧
  allvars_of (NestedCase c g gv p e pes) =
    {explode gv} UNION
    BIGUNION (set (MAP (allvars_of o SND) pes)) UNION
    allvars_of e UNION allvars_of g
Termination
  WF_REL_TAC `measure $ cexp_size (K 0)`
End

Theorem allvars_Lams:
  ∀vs x. allvars (Lams vs x) = set vs UNION allvars x
Proof
  Induct \\ fs [Lams_def,EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
QED

Theorem allvars_Apps:
  ∀xs x. allvars (Apps x xs) = BIGUNION (set (MAP allvars xs)) UNION allvars x
Proof
  Induct \\ fs [Apps_def,EXTENSION] \\ metis_tac []
QED

Theorem allvars_IfDisj:
  allvars (IfDisj v a e) = if a = [] then allvars e else explode v INSERT allvars e
Proof
  simp[IfDisj_def] >> Induct_on `a` >> rw[Disj_def] >>
  PairCases_on `h` >> rw[Disj_def] >>
  rewrite_tac[GSYM UNION_ASSOC] >> pop_assum SUBST_ALL_TAC >>
  rw[EXTENSION] >> eq_tac >> rw[] >> simp[]
QED

Theorem allvars_lets_for:
  allvars (lets_for cn v ws b) =
    (if ws = [] then {} else {v}) ∪ set (MAP SND ws) ∪ allvars b
Proof
  Induct_on `ws` >> rw[lets_for_def, allvars_def] >>
  PairCases_on `h` >> rw[lets_for_def, EXTENSION] >> eq_tac >> rw[] >> gvs[]
QED

Theorem allvars_rows_of:
  allvars (rows_of v k css) =
    (if css = [] then {} else {v}) ∪
    allvars k ∪
    BIGUNION (set (MAP (λ(cn,vs,b). set vs ∪ allvars b) css))
Proof
  Induct_on `css` >> rw[rows_of_def] >> PairCases_on `h` >> rw[rows_of_def] >>
  simp[allvars_lets_for, combinTheory.o_DEF] >>
  Cases_on `h1` >> gvs[] >> rw[EXTENSION] >> eq_tac >> rw[] >>
  gvs[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> metis_tac[]
QED

Theorem allvars_of:
  ∀x. NestedCase_free x ∧ cexp_wf x ⇒ allvars_of x = allvars (exp_of x)
Proof
  recInduct allvars_of_ind >> rw[] >>
  gvs[exp_of_def, allvars_Lams, allvars_Apps] >>
  gvs[cexp_wf_def, MAP_MAP_o, o_DEF, UNCURRY, COND_RAND] >>
  gvs[GSYM INSERT_SING_UNION, AC UNION_ASSOC UNION_COMM]
  >- (ntac 4 AP_TERM_TAC >> rw[MAP_EQ_f] >> gvs[EVERY_MEM, MEM_MAP] >> metis_tac[])
  >- (ntac 2 AP_TERM_TAC >> rw[MAP_EQ_f] >> gvs[EVERY_MEM, MEM_MAP] >> metis_tac[])
  >- (ntac 3 AP_TERM_TAC >> rw[MAP_EQ_f] >> gvs[EVERY_MEM, MEM_MAP] >> metis_tac[])
  >- (rw[EXTENSION] >> eq_tac >> rw[] >> gvs[]) >>
  qmatch_goalsub_abbrev_tac `_ INSERT allvars foo` >>
  qmatch_goalsub_abbrev_tac `_ INSERT _ ∪ bar` >>
  qsuff_tac `allvars foo = explode n INSERT bar`
  >- (rw[EXTENSION] >> eq_tac >> rw[] >> gvs[]) >>
  unabbrev_all_tac >> simp[allvars_rows_of] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  Cases_on `eopt` >> gvs[GSYM INSERT_SING_UNION]
  >- (
    AP_TERM_TAC >> qpat_x_assum `_ ≠ []` kall_tac >>
    Induct_on `ys` >> rw[] >> gvs[] >> pairarg_tac >> gvs[FORALL_PROD] >>
    simp[AC UNION_ASSOC UNION_COMM]
    )
  >- (
    pairarg_tac >> gvs[] >> simp[allvars_IfDisj] >>
    simp[INSERT_UNION_EQ, AC UNION_ASSOC UNION_COMM] >> rpt AP_TERM_TAC >>
    rpt $ qpat_x_assum `_ ≠ []` kall_tac >>
    Induct_on `ys` >> rw[] >> gvs[] >> pairarg_tac >> gvs[FORALL_PROD] >>
    simp[AC UNION_ASSOC UNION_COMM]
    )
QED

Theorem Apps_append:
  ∀xs ys x. Apps x (xs ++ ys) = Apps (Apps x xs) ys
Proof
  Induct \\ fs [Apps_def]
QED

Theorem exp_of_SmartLam[simp]:
  exp_of (SmartLam a vs x) = exp_of (Lam a vs x)
Proof
  rw [SmartLam_def,exp_of_def,NULL_EQ,Lams_def]
  \\ Cases_on ‘dest_Lam x’ \\ fs [exp_of_def]
  \\ CASE_TAC \\ fs [] \\ rw [exp_of_def]
  \\ Cases_on ‘x’ \\ gvs [dest_Lam_def,exp_of_def]
  \\ qid_spec_tac ‘vs’ \\ Induct \\ fs [Lams_def]
QED

Theorem exp_of_SmartApp[simp]:
  exp_of (SmartApp a x xs) = exp_of (App a x xs)
Proof
  rw [SmartApp_def,exp_of_def,NULL_EQ,Apps_def]
  \\ Cases_on ‘dest_App x’ \\ fs [exp_of_def]
  \\ CASE_TAC \\ fs [] \\ rw [exp_of_def]
  \\ Cases_on ‘x’ \\ gvs [dest_App_def,exp_of_def,SF ETA_ss,Apps_append]
QED

val _ = export_theory();
