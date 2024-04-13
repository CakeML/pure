(*
   This file defines expressions for typeclass_lang as the type system sees them.
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open arithmeticTheory listTheory rich_listTheory alistTheory stringTheory
     optionTheory pairTheory pred_setTheory mlmapTheory;
open pure_cexpTheory;
open typeclass_typesTheory typeclass_kindCheckTheory;
val _ = new_theory "typeclass_tcexp";

(* We associate a poly-type to variable.
* This is needed for type elaboration.
* It can be provided by the user as well. *)
Type annot_cvname = ``:(cvname # (num # PredType) option)``;
Type class_constr = ``:(cvname # type)``;

Datatype:
  (* The first argument for each constructor is the type of the whole expression *)
  (* So the user can do something like ``show ((read x)::Int)`` *)
  tcexp = Var (class_constr list) cvname                    (* variable                 *)
        | Prim cop (tcexp list)                        (* primitive operations     *)
        | App tcexp (tcexp list)                       (* function application     *)
        | Lam ((cvname # (type option)) list) tcexp    (* lambda                   *)
        | Let annot_cvname tcexp tcexp                 (* let                      *)
        | Letrec ((annot_cvname # tcexp) list) tcexp   (* mutually recursive exps  *)
        | UserAnnot type tcexp                         (* user type annotation     *)
        | NestedCase tcexp cvname cepat tcexp
            ((cepat # tcexp) list)                     (* case of                  *)
End

(* top level declarations *)
Datatype:
  tcdecl = FuncDecl PredType tcexp (* enforce top level declarations *)
End

Definition freevars_tcexp_def[simp]:
  freevars_tcexp ((Var c v): tcexp) = {v} /\
  freevars_tcexp (Prim op es) = BIGUNION (set (MAP (λa. freevars_tcexp a) es)) /\
  freevars_tcexp (App e es) =
    freevars_tcexp e ∪ BIGUNION (set (MAP freevars_tcexp es)) ∧
  freevars_tcexp (Lam vs e) = freevars_tcexp e DIFF set (MAP FST vs) ∧
  freevars_tcexp (Let v e1 e2) =
    freevars_tcexp e1 ∪ (freevars_tcexp e2 DELETE (FST v)) ∧
  freevars_tcexp (Letrec fns e) =
    freevars_tcexp e ∪ BIGUNION (set (MAP (λ(v,e). freevars_tcexp e) fns))
      DIFF set (MAP (FST o FST) fns) ∧
  freevars_tcexp (NestedCase g gv p e pes) =
    freevars_tcexp g ∪
    (((freevars_tcexp e DIFF cepat_vars p) ∪
      BIGUNION (set (MAP (λ(p,e). freevars_tcexp e DIFF cepat_vars p) pes)))
    DELETE gv) ∧
  freevars_tcexp (UserAnnot t e) = freevars_tcexp e
Termination
  WF_REL_TAC `measure tcexp_size` >> rw []
End

Definition tcexp_wf_def[nocompute]:
  tcexp_wf (Var _ v) = T ∧
  tcexp_wf (Prim op es) = (
    num_args_ok op (LENGTH es) ∧ EVERY tcexp_wf es ∧
    (∀l. op = AtomOp (Lit l) ⇒ isInt l ∨ isStr l) ∧
    (∀m. op = AtomOp (Message m) ⇒ m ≠ "")) ∧
  tcexp_wf (App e es) = (tcexp_wf e ∧ EVERY tcexp_wf es ∧ es ≠ []) ∧
  tcexp_wf (Lam vs e) = (tcexp_wf e ∧ vs ≠ []) ∧
  tcexp_wf (Let v e1 e2) = (tcexp_wf e1 ∧ tcexp_wf e2) ∧
  tcexp_wf (Letrec fns e) = (EVERY tcexp_wf $ MAP (λx. SND x) fns ∧
    tcexp_wf e ∧ fns ≠ []) ∧
  tcexp_wf (NestedCase g gv p e pes) = (
    tcexp_wf g ∧ tcexp_wf e ∧ EVERY tcexp_wf $ MAP SND pes ∧
    ¬ MEM gv (FLAT $ MAP (cepat_vars_l o FST) ((p,e) :: pes))) ∧
  tcexp_wf (UserAnnot _ e) = tcexp_wf e
Termination
  WF_REL_TAC `measure tcexp_size` >> rw[fetch "-" "tcexp_size_def"] >>
  gvs[MEM_MAP, EXISTS_PROD] >>
  rename1 `MEM _ es` >> Induct_on `es` >> rw[] >> gvs[fetch "-" "tcexp_size_def"]
End

val tcexp_size_eq = fetch "-" "tcexp_size_eq";

Theorem tcexp_size_lemma:
  (∀xs v e. MEM (v,e) xs ⇒ tcexp_size e < tcexp1_size xs) ∧
  (∀xs p e. MEM (p,e) xs ⇒ tcexp_size e < tcexp3_size xs) ∧
  (∀xs a. MEM a xs ⇒ tcexp_size a < tcexp5_size xs)
Proof
  rpt conj_tac
  \\ Induct \\ rw [] \\ fs [fetch "-" "tcexp_size_def"] \\ res_tac \\ fs []
QED

Theorem better_tcexp_induction =
        TypeBase.induction_of “:tcexp”
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

val _ = TypeBase.update_induction better_tcexp_induction

Definition every_tcexp_def[simp]:
  every_tcexp (p:tcexp -> bool) (Var cs v) = p (Var cs v) ∧
  every_tcexp p (Prim x es) =
    (p (Prim x es) ∧ EVERY (every_tcexp p) es) ∧
  every_tcexp p (App e es) =
    (p (App e es) ∧ every_tcexp p e ∧ EVERY (every_tcexp p) es) ∧
  every_tcexp p (Lam vs e) =
    (p (Lam vs e) ∧ every_tcexp p e) ∧
  every_tcexp p (Let v e1 e2) =
    (p (Let v e1 e2) ∧ every_tcexp p e1 ∧ every_tcexp p e2) ∧
  every_tcexp p (Letrec fns e) =
    (p (Letrec fns e) ∧
     every_tcexp p e ∧ EVERY (every_tcexp p) $ MAP (λx. SND x) fns) ∧
  every_tcexp p (NestedCase e1 v pat e2 rows) =
    (p (NestedCase e1 v pat e2 rows) ∧
     every_tcexp p e1 ∧ every_tcexp p e2 ∧
     EVERY (every_tcexp p) $ MAP SND rows) ∧
  every_tcexp p (UserAnnot t e) = (p (UserAnnot t e) ∧ every_tcexp p e)
Termination
  WF_REL_TAC ‘measure $ tcexp_size o SND’ >>
  simp[tcexp_size_eq, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
  rename [‘MEM _ list’] >> Induct_on ‘list’ >>
  simp[FORALL_PROD, listTheory.list_size_def, basicSizeTheory.pair_size_def] >>
  rw[] >> gs[]
End

val _ = export_theory();
