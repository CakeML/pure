(*
   This file defines expressions for pure_lang as the type system sees them.
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open arithmeticTheory listTheory rich_listTheory alistTheory stringTheory
     optionTheory pairTheory pred_setTheory mlmapTheory;
open pure_cexpTheory pure_cexp_lemmasTheory pure_expTheory pure_evalTheory
     pure_exp_lemmasTheory pure_exp_relTheory pure_congruenceTheory;
open pure_typesTheory pure_kindCheckTheory;
val _ = new_theory "pure_tcexp";

Datatype:
  (* The first argument for each constructor is the type of the whole expression *)
  tcexp = Var (PredType option) cvname                            (* variable                 *)
          (* the first type is the type for the whole expression,
          *  and the second type is the type for the operator *)
        | Prim (PredType option) cop (tcexp list)                 (* primitive operations     *)
        | App (PredType option) tcexp (tcexp list)                (* function application     *)
          (* the types inside the list are the types assigned for
          * the corresponding variables *)
        | Lam (PredType option) ((PredType option # cvname) list)
            tcexp                                                 (* lambda                   *)
          (* the type scheme is the polymorphic type for
          *  the binding expression. Used for inferencing *)
        | Let (PredType option)
             (PredType_scheme option) cvname tcexp tcexp          (* let                      *)
        | Letrec (PredType option)
            (((PredType_scheme option) # cvname # tcexp) list)
            tcexp                                                 (* mutually recursive exps  *)
        | NestedCase (PredType option) tcexp cvname cepat tcexp
            ((cepat # tcexp) list)                                (* case of                  *)
End

(* top level declarations *)
Datatype:
  tcdecl = FuncDecl PredType tcexp (* enforce top level declarations *)
End

Type minImplAST = ``:(mlstring list) list``; (* DNF of function names*)

Datatype:
  classinfo =
    <| super : mlstring list
     ; kind : Kind option
     ; methodsig : cvname |-> PredType
     ; minImp : minImplAST
     ; defaults : cvname |-> tcexp |>
End

Inductive super_reachable:
  (!src dst sup.
    cdb src = SOME c /\ MEM sup c.super /\
    super_reachable cdb sup dst ==>
      super_reachable cdb src dst) /\
  (!src sup.
    cdb src = SOME c /\ MEM sup c.super ==>
      super_reachable cdb src sup)
End

Definition super_ok_def:
  super_ok cdb =
    !x c. FLOOKUP cdb x = SOME c ==>
      ~(super_reachable (FLOOKUP cdb) x x)
End

Datatype:
  instinfo =
    <| cstr : (mlstring # 'b) list (* class and type variable*)
     (* ; class : mlstring *)
     (* ; insttype : type *)
     ; impl : cvname |-> tcexp |> (* function name and its expression *)
End

Definition instinfo_constraint_ok_def:
  instinfo_constraint_ok inst insttype =
    !x. MEM x inst.cstr ==>
      (* everything in the left must be in used in the right *)
      SND x IN collect_type_vars insttype /\
      (* everything in the left must be smaller than the type in the right *)
      (* since we only allow a single type variable on the right now,
      * so the following check should suffice *)
      TypeVar (SND x) <> insttype
End

Definition instinfo_impl_ok:
  instinfo_impl_ok cdb inst class <=>
  ?c. FLOOKUP cdb class = SOME c /\
    (!meth ty. FLOOKUP c.methodsig meth = SOME ty ==>
      ?exp.
       (FLOOKUP inst.impl meth = SOME exp
       (* /\ TODO: check if the tcexp has the correct instantiated type *)) \/
       FLOOKUP c.defaults meth = SOME exp) /\
    (?minimpl. !m.
      MEM minimpl c.minImp /\ MEM m minimpl ==>
        ?exp. FLOOKUP inst.impl m = SOME exp)
End

Definition freevars_tcexp_def[simp]:
  freevars_tcexp (Var c v) = {v} /\
  freevars_tcexp (Prim c op es) = BIGUNION (set (MAP (λa. freevars_tcexp a) es)) /\
  freevars_tcexp (App c e es) =
    freevars_tcexp e ∪ BIGUNION (set (MAP freevars_tcexp es)) ∧
  freevars_tcexp (Lam c vs e) = freevars_tcexp e DIFF set (MAP SND vs) ∧
  freevars_tcexp (Let c s v e1 e2) = freevars_tcexp e1 ∪ (freevars_tcexp e2 DELETE v) ∧
  freevars_tcexp (Letrec c fns e) =
    freevars_tcexp e ∪ BIGUNION (set (MAP (λ(s,fn,e). freevars_tcexp e) fns))
      DIFF set (MAP (FST o SND) fns) ∧
  freevars_tcexp (NestedCase c g gv p e pes) =
    freevars_tcexp g ∪
    (((freevars_tcexp e DIFF cepat_vars p) ∪
      BIGUNION (set (MAP (λ(p,e). freevars_tcexp e DIFF cepat_vars p) pes)))
    DELETE gv)
Termination
  WF_REL_TAC `measure tcexp_size` >> rw []
End

Definition tcexp_wf_def[nocompute]:
  tcexp_wf (Var _ v) = T ∧
  tcexp_wf (Prim _ op es) = (
    num_args_ok op (LENGTH es) ∧ EVERY tcexp_wf es ∧
    (∀l. op = AtomOp (Lit l) ⇒ isInt l ∨ isStr l) ∧
    (∀m. op = AtomOp (Message m) ⇒ m ≠ "")) ∧
  tcexp_wf (App _ e es) = (tcexp_wf e ∧ EVERY tcexp_wf es ∧ es ≠ []) ∧
  tcexp_wf (Lam _ vs e) = (tcexp_wf e ∧ vs ≠ []) ∧
  tcexp_wf (Let _ _ v e1 e2) = (tcexp_wf e1 ∧ tcexp_wf e2) ∧
  tcexp_wf (Letrec _ fns e) = (EVERY tcexp_wf $ MAP (λx. SND (SND x)) fns ∧
    tcexp_wf e ∧ fns ≠ []) ∧
  tcexp_wf (NestedCase _ g gv p e pes) = (
    tcexp_wf g ∧ tcexp_wf e ∧ EVERY tcexp_wf $ MAP SND pes ∧
    ¬ MEM gv (FLAT $ MAP (cepat_vars_l o FST) ((p,e) :: pes))
  )
Termination
  WF_REL_TAC `measure tcexp_size` >> rw[fetch "-" "tcexp_size_def"] >>
  gvs[MEM_MAP, EXISTS_PROD] >>
  rename1 `MEM _ es` >> Induct_on `es` >> rw[] >> gvs[fetch "-" "tcexp_size_def"]
End

val tcexp_size_eq = fetch "-" "tcexp_size_eq";

Theorem tcexp_size_lemma:
  (∀xs s v e. MEM (s,v,e) xs ⇒ tcexp_size e < tcexp1_size xs) ∧
  (∀xs p e. MEM (p,e) xs ⇒ tcexp_size e < tcexp3_size xs) ∧
  (∀xs a. MEM a xs ⇒ tcexp_size a < tcexp6_size xs)
Proof
  rpt conj_tac
  \\ Induct \\ rw [] \\ fs [fetch "-" "tcexp_size_def"] \\ res_tac \\ fs []
QED

Theorem better_tcexp_induction =
        TypeBase.induction_of “:tcexp”
          |> Q.SPECL [‘P’,
                      ‘λxs. ∀s v e. MEM (s,v,e) xs ⇒ P e’,
                      ‘λ(x,v,e). P e’,
                      ‘λlbs. ∀pat e. MEM (pat, e) lbs ⇒ P e’,
                      ‘λ(nm,e). P e’,
                      ‘λ(p,e). P e’,
                      ‘λes. ∀e. MEM e es ⇒ P e’]
          |> CONV_RULE (LAND_CONV (SCONV [DISJ_IMP_THM, FORALL_AND_THM,
                                          pairTheory.FORALL_PROD,
                                          DECIDE “(p ∧ q ⇒ q) ⇔ T”]))
          |> UNDISCH |> CONJUNCTS |> hd |> DISCH_ALL

val _ = TypeBase.update_induction better_tcexp_induction

Definition every_tcexp_def[simp]:
  every_tcexp (p:tcexp -> bool) (Var a v) = p (Var a v) ∧
  every_tcexp p (Prim a x es) =
    (p (Prim a x es) ∧ EVERY (every_tcexp p) es) ∧
  every_tcexp p (App a e es) =
    (p (App a e es) ∧ every_tcexp p e ∧ EVERY (every_tcexp p) es) ∧
  every_tcexp p (Lam a vs e) =
    (p (Lam a vs e) ∧ every_tcexp p e) ∧
  every_tcexp p (Let a s v e1 e2) =
    (p (Let a s v e1 e2) ∧ every_tcexp p e1 ∧ every_tcexp p e2) ∧
  every_tcexp p (Letrec a fns e) =
    (p (Letrec a fns e) ∧
     every_tcexp p e ∧ EVERY (every_tcexp p) $ MAP (λx. SND (SND x)) fns) ∧
  every_tcexp p (NestedCase a e1 v pat e2 rows) =
    (p (NestedCase a e1 v pat e2 rows) ∧
     every_tcexp p e1 ∧ every_tcexp p e2 ∧
     EVERY (every_tcexp p) $ MAP SND rows)
Termination
  WF_REL_TAC ‘measure $ tcexp_size o SND’ >>
  simp[tcexp_size_eq, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
  rename [‘MEM _ list’] >> Induct_on ‘list’ >>
  simp[FORALL_PROD, listTheory.list_size_def, basicSizeTheory.pair_size_def] >>
  rw[] >> gs[]
End

val _ = export_theory();
