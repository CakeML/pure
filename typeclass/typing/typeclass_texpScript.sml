(*
   This file defines expressions for typeclass_lang as the type system sees them.
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open arithmeticTheory listTheory rich_listTheory alistTheory stringTheory
     optionTheory pairTheory pred_setTheory mlmapTheory;
open pure_cexpTheory;
open typeclass_typesTheory typeclass_kindCheckTheory;
val _ = new_theory "typeclass_texp";

(* We associate a poly-type to variable.
* This is needed for type elaboration.
* It can be provided by the user as well. *)
(* 'a can be instantiated to Kind list or num *)
Type annot_cvname = ``:(cvname # ('a # PredType) option)``;
Type class_constr = ``:(cvname # type)``;

Datatype:
  (* The first argument for each constructor is the type of the whole expression *)
  (* So the user can do something like ``show ((read x)::Int)`` *)
  texp = Var (class_constr list) cvname                    (* variable                 *)
        | Prim cop (texp list)                        (* primitive operations     *)
        | App texp (texp list)                       (* function application     *)
        | Lam ((cvname # (type option)) list) texp    (* lambda                   *)
        | Let ('a annot_cvname) texp texp                 (* let                      *)
        | Letrec (('a annot_cvname # texp) list) texp   (* mutually recursive exps  *)
        | UserAnnot type texp                         (* user type annotation     *)
        | NestedCase texp cvname cepat texp
            ((cepat # texp) list)                     (* case of                  *)
End

(* top level declarations *)
Datatype:
  tcdecl = FuncDecl PredType ('a texp) (* enforce top level declarations *)
End

Definition freevars_texp_def[simp]:
  freevars_texp ((Var c v): 'a texp) = {v} /\
  freevars_texp (Prim op es) = BIGUNION (set (MAP (λa. freevars_texp a) es)) /\
  freevars_texp (App e es) =
    freevars_texp e ∪ BIGUNION (set (MAP freevars_texp es)) ∧
  freevars_texp (Lam vs e) = freevars_texp e DIFF set (MAP FST vs) ∧
  freevars_texp (Let v e1 e2) =
    freevars_texp e1 ∪ (freevars_texp e2 DELETE (FST v)) ∧
  freevars_texp (Letrec fns e) =
    freevars_texp e ∪ BIGUNION (set (MAP (λ(v,e). freevars_texp e) fns))
      DIFF set (MAP (FST o FST) fns) ∧
  freevars_texp (NestedCase g gv p e pes) =
    freevars_texp g ∪
    (((freevars_texp e DIFF cepat_vars p) ∪
      BIGUNION (set (MAP (λ(p,e). freevars_texp e DIFF cepat_vars p) pes)))
    DELETE gv) ∧
  freevars_texp (UserAnnot t e) = freevars_texp e
Termination
  WF_REL_TAC `measure $ texp_size (K 1)` >> rw []
End

Definition texp_wf_def[nocompute]:
  texp_wf (Var _ v) = T ∧
  texp_wf (Prim op es) = (
    num_args_ok op (LENGTH es) ∧ EVERY texp_wf es) ∧
  texp_wf (App e es) = (texp_wf e ∧ EVERY texp_wf es ∧ es ≠ []) ∧
  texp_wf (Lam vs e) = (texp_wf e ∧ vs ≠ []) ∧
  texp_wf (Let v e1 e2) = (texp_wf e1 ∧ texp_wf e2) ∧
  texp_wf (Letrec fns e) = (EVERY texp_wf $ MAP (λx. SND x) fns ∧
    texp_wf e ∧ fns ≠ []) ∧
  texp_wf (NestedCase g gv p e pes) = (
    texp_wf g ∧ texp_wf e ∧ EVERY texp_wf $ MAP SND pes ∧
    ¬ MEM gv (FLAT $ MAP (cepat_vars_l o FST) ((p,e) :: pes))) ∧
  texp_wf (UserAnnot _ e) = texp_wf e
Termination
  WF_REL_TAC `measure $ texp_size (K 1)` >> rw[fetch "-" "texp_size_def"] >>
  gvs[MEM_MAP, EXISTS_PROD] >>
  rename1 `MEM _ es` >> Induct_on `es` >> rw[] >> gvs[fetch "-" "texp_size_def"]
End

val texp_size_eq = fetch "-" "texp_size_eq";

Theorem texp_size_lemma:
  (∀xs v e f. MEM (v,e) xs ⇒ texp_size f e < texp1_size f xs) ∧
  (∀xs p e f. MEM (p,e) xs ⇒ texp_size f e < texp3_size f xs) ∧
  (∀xs a f. MEM a xs ⇒ texp_size f a < texp5_size f xs)
Proof
  rpt conj_tac
  \\ Induct \\ rw [] \\ fs [fetch "-" "texp_size_def"] \\ res_tac \\ fs []
  \\ irule LESS_LESS_EQ_TRANS
  \\ first_assum $ irule_at (Pos hd) \\ fs[]
QED

Theorem better_texp_induction =
        TypeBase.induction_of “:'a texp”
          |> Q.SPECL [‘P’,
                      ‘λxs. ∀v e. MEM (v,e) xs ⇒ P e’,
                      ‘λ(v,e). P e’,
                      ‘λlbs. ∀pat e. MEM (pat, e) lbs ⇒ P e’,
                      ‘λ(nm,e). P e’,
                      ‘λes. ∀e. MEM e es ⇒ P e’]
          |> CONV_RULE (LAND_CONV (SCONV [DISJ_IMP_THM, FORALL_AND_THM,
                                          pairTheory.FORALL_PROD,
                                          DECIDE “(p ∧ q ⇒ q) ⇔ T”]))
          |> UNDISCH |> CONJUNCTS |> hd |> DISCH_ALL

val _ = TypeBase.update_induction better_texp_induction

Definition every_texp_def[simp]:
  every_texp (p:'a texp -> bool) (Var cs v) = p (Var cs v) ∧
  every_texp p (Prim x es) =
    (p (Prim x es) ∧ EVERY (every_texp p) es) ∧
  every_texp p (App e es) =
    (p (App e es) ∧ every_texp p e ∧ EVERY (every_texp p) es) ∧
  every_texp p (Lam vs e) =
    (p (Lam vs e) ∧ every_texp p e) ∧
  every_texp p (Let v e1 e2) =
    (p (Let v e1 e2) ∧ every_texp p e1 ∧ every_texp p e2) ∧
  every_texp p (Letrec fns e) =
    (p (Letrec fns e) ∧
     every_texp p e ∧ EVERY (every_texp p) $ MAP (λx. SND x) fns) ∧
  every_texp p (NestedCase e1 v pat e2 rows) =
    (p (NestedCase e1 v pat e2 rows) ∧
     every_texp p e1 ∧ every_texp p e2 ∧
     EVERY (every_texp p) $ MAP SND rows) ∧
  every_texp p (UserAnnot t e) = (p (UserAnnot t e) ∧ every_texp p e)
Termination
  WF_REL_TAC ‘measure $ texp_size (K 1) o SND’ >>
  simp[texp_size_eq, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
  rename [‘MEM _ list’] >> Induct_on ‘list’ >>
  simp[FORALL_PROD, listTheory.list_size_def, basicSizeTheory.pair_size_def] >>
  rw[] >> gs[]
End

Triviality MAX_SET_LE:
  FINITE s ∧ (∀y. y ∈ s ⇒ y ≤ x) ⇒
  MAX_SET s ≤ x
Proof
  strip_tac >>
  simp[GSYM GREATER_EQ] >>
  ho_match_mp_tac MAX_SET_ELIM >>
  simp[GREATER_EQ]
QED

Triviality MAX_SET_LT:
  FINITE s ∧ (∀y. y ∈ s ⇒ y < x) ∧ 0 < x ⇒
  MAX_SET s < x
Proof
  strip_tac >>
  simp[GSYM GREATER_DEF] >>
  ho_match_mp_tac MAX_SET_ELIM >>
  simp[GREATER_DEF]
QED

(* similar to freevars_texp, but it collects every
* binder variable, the x and y in λx y. ...  *)
Definition lambda_vars_def:
  lambda_vars (Var _ _) = {} ∧
  lambda_vars (Prim _ es) = lambda_varsl es ∧
  lambda_vars (App f es) = lambda_vars f ∪ lambda_varsl es ∧
  lambda_vars (Lam vs e) = set (MAP FST vs) ∪ lambda_vars e ∧
  lambda_vars (Let v e e') =
    FST v INSERT lambda_vars e ∪ lambda_vars e' ∧
  lambda_vars (Letrec fns e') =
    set (MAP (FST o FST) fns) ∪
    lambda_varsl (MAP SND fns) ∪
    lambda_vars e' ∧
  lambda_vars (UserAnnot _ e) = lambda_vars e ∧
  lambda_vars (NestedCase g gv p e pes) =
    gv INSERT lambda_vars g ∪ cepat_vars p ∪ lambda_vars e ∪
    BIGUNION (set (MAP (cepat_vars o FST) pes)) ∪
    lambda_varsl (MAP SND pes) ∧
  lambda_varsl [] = {} ∧
  lambda_varsl (e::es) = lambda_vars e ∪ lambda_varsl es
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (λe. case e of
    | INR es => (MAX_SET (set (MAP (texp_size (K 1)) es)),LENGTH es + 1)
    | INL e => (texp_size (K 1) e,0))` >>
  rw[]
  >- (
    irule MAX_SET_LT >>
    rw[MEM_MAP] >>
    irule LESS_TRANS >>
    drule_then (irule_at (Pos hd)) $ cj 3 texp_size_lemma >>
    simp[]
  )
  >- (
    simp[GSYM LE_LT] >>
    irule in_max_set >>
    simp[]
  )
  >- (
    irule MAX_SET_LT >>
    rw[MEM_MAP] >>
    irule LESS_TRANS >>
    Cases_on `y''` >>
    simp[] >>
    drule_then (irule_at (Pos hd)) $ cj 2 texp_size_lemma >>
    simp[]
  )
  >- (
    irule MAX_SET_LT >>
    rw[MEM_MAP] >>
    irule LESS_TRANS >>
    Cases_on `y''` >>
    simp[] >>
    drule_then (irule_at (Pos hd)) $ cj 1 texp_size_lemma >>
    simp[]
  )
  >- (
    irule MAX_SET_LT >>
    rw[MEM_MAP] >>
    irule LESS_TRANS >>
    drule_then (irule_at (Pos hd)) $ cj 3 texp_size_lemma >>
    simp[]
  )
  >- (
    simp[GSYM LE_LT] >>
    irule MAX_SET_LE >>
    rw[MEM_MAP,PULL_EXISTS] >>
    irule in_max_set >>
    simp[MEM_MAP] >>
    metis_tac[]
  )
End

Theorem lambda_varsl_def:
  lambda_varsl es = BIGUNION (set (MAP lambda_vars es))
Proof
  Induct_on `es` >>
  simp[lambda_vars_def]
QED

Theorem lambda_vars_FINITE[simp]:
  (∀(e:'a texp). FINITE (lambda_vars e)) ∧
  ∀(es:'a texp list). FINITE (lambda_varsl es)
Proof
  ho_match_mp_tac lambda_vars_ind >>
  rw[lambda_vars_def,lambda_varsl_def,MEM_MAP,PULL_EXISTS,
    GSYM pure_cexpTheory.cepat_vars_l_correct]
QED

val _ = export_theory();
