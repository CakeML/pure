(*
   This file defines expressions for pure_lang as the compiler sees them.
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory;

val _ = new_theory "pure_cexp";

Datatype:
  cop = Cons string        (* datatype constructor                     *)
      | AtomOp atom_op     (* primitive parametric operator over Atoms *)
      | Seq                (* diverges if arg1 does, else same as arg2 *)
End

(* no 'a (info) fields *)
Datatype:
  cepat = cepatVar string
        | cepatUScore
        | cepatCons string (cepat list)
End

Theorem cepat_ind_alt:
  ∀P.
    P cepatUScore ∧
    (∀s. P (cepatVar s)) ∧
    (∀s ps. (∀p. MEM p ps ⇒ P p) ⇒ P (cepatCons s ps)) ⇒
    ∀p. P p
Proof
  gen_tac >> strip_tac >>
  ‘(∀p. P p) ∧ (∀ps p. MEM p ps ⇒ P p)’ suffices_by simp[] >>
  Induct >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

val _ = TypeBase.update_induction cepat_ind_alt

Definition cepat_vars_def[simp]:
  cepat_vars cepatUScore = ∅ ∧
  cepat_vars (cepatVar v) = {v} ∧
  cepat_vars (cepatCons s ps) = BIGUNION (set (MAP cepat_vars ps))
Termination
  WF_REL_TAC ‘measure cepat_size’
End

Definition cepat_vars_l_def[simp]:
  cepat_vars_l cepatUScore = [] ∧
  cepat_vars_l (cepatVar s) = [s] ∧
  cepat_vars_l (cepatCons s ps) = FLAT (MAP cepat_vars_l ps)
Termination
  WF_REL_TAC ‘measure cepat_size’
End

Theorem cepat_vars_l_correct:
  set (cepat_vars_l p) = cepat_vars p
Proof
  Induct_on ‘p’ >>
  simp[LIST_TO_SET_FLAT, MAP_MAP_o, combinTheory.o_DEF, Cong MAP_CONG] >>
  simp[SF ETA_ss]
QED

Datatype:
  cexp = Var 'a vname                         (* variable                 *)
       | Prim 'a cop (cexp list)              (* primitive operations     *)
       | App 'a cexp (cexp list)              (* function application     *)
       | Lam 'a (vname list) cexp             (* lambda                   *)
       | Let 'a vname cexp cexp               (* let                      *)
       | Letrec 'a ((vname # cexp) list) cexp (* mutually recursive exps  *)
       | Case 'a cexp vname ((vname # vname list # cexp) list) (* case of *)
       | NestedCase 'a cexp vname cepat cexp ((cepat # cexp) list)
                                     (* case w/non-empty pattern-exp list *)
End

Theorem cexp_size_lemma:
  (∀xs a. MEM a xs ⇒ cexp_size f a < cexp8_size f xs) ∧
  (∀xs p e. MEM (p,e) xs ⇒ cexp_size f e < cexp6_size f xs) ∧
  (∀xs a1 a. MEM (a1,a) xs ⇒ cexp_size f a < cexp4_size f xs) ∧
  (∀xs a1 a2 a. MEM (a1,a2,a) xs ⇒ cexp_size f a < cexp1_size f xs)
Proof
  rpt conj_tac
  \\ Induct \\ rw [] \\ fs [fetch "-" "cexp_size_def"] \\ res_tac \\ fs []
QED

Theorem better_cexp_induction =
        TypeBase.induction_of “:α cexp”
          |> Q.SPECL [‘P’, ‘λrows. ∀c arg e. MEM (c,arg,e) rows ⇒ P e’,
                      ‘λ(c,arg,e). P e’, ‘λ(nm,e). P e’,
                      ‘λlbs. ∀nm e. MEM (nm, e) lbs ⇒ P e’,
                      ‘λ(s,e). P e’,
                      ‘λpes. ∀p e. MEM (p,e) pes ⇒ P e’,
                      ‘λ(p,e). P e’, ‘λes. ∀e. MEM e es ⇒ P e’
                     ]
          |> CONV_RULE (LAND_CONV (SCONV [DISJ_IMP_THM, FORALL_AND_THM,
                                          pairTheory.FORALL_PROD,
                                          DECIDE “(p ∧ q ⇒ q) ⇔ T”]))
          |> UNDISCH |> CONJUNCTS |> hd |> DISCH_ALL

val _ = TypeBase.update_induction better_cexp_induction

Definition dest_var_def[simp]:
  dest_var (Var _ vnm) = SOME vnm ∧
  dest_var _ = NONE
End

Definition dest_nestedcase_def[simp]:
  dest_nestedcase (NestedCase _ g gv p e pes) = SOME (g, gv, (p,e)::pes) ∧
  dest_nestedcase _ = NONE
End

Definition gencexp_recurse_def:
  gencexp_recurse f (pure_cexp$Letrec c xs y) =
    f (pure_cexp$Letrec c (MAP (λ(n,x). (n, gencexp_recurse f x)) xs)
       (gencexp_recurse f y)) ∧
  gencexp_recurse f (Lam c ns x) = f (Lam c ns (gencexp_recurse f x))  ∧
  gencexp_recurse f (Prim c p xs) = f (Prim c p (MAP (gencexp_recurse f) xs)) ∧
  gencexp_recurse f (App c x ys) =
    f (App c (gencexp_recurse f x) (MAP (gencexp_recurse f) ys))  ∧
  gencexp_recurse f (Var c v) = f (Var c v) ∧
  gencexp_recurse f (Let c n x y) =
    f (Let c n (gencexp_recurse f x) (gencexp_recurse f y)) ∧
  gencexp_recurse f (Case c x n ys) =
    f (Case c (gencexp_recurse f x) n
       (MAP (λ(n,ns,e). (n,ns,gencexp_recurse f e)) ys)) ∧
  gencexp_recurse f (NestedCase c g gv p e pes) =
    f (NestedCase c (gencexp_recurse f g) gv p (gencexp_recurse f e)
       (MAP (λ(p,e). (p, gencexp_recurse f e)) pes))
Termination
  WF_REL_TAC ‘measure (cexp_size (K 0) o SND)’
End

Definition op_of_def:
  op_of (Cons s) = Cons s ∧
  op_of (AtomOp p) = AtomOp p ∧
  op_of (Seq:cop) = (Seq:op)
End

Definition freevars_cexp_def[simp]:
  freevars_cexp (Var c v) = {v} ∧
  freevars_cexp (Prim c op es) = BIGUNION (set (MAP freevars_cexp es)) ∧
  freevars_cexp (App c e es) =
    freevars_cexp e ∪ BIGUNION (set (MAP freevars_cexp es)) ∧
  freevars_cexp (Lam c vs e) = freevars_cexp e DIFF set vs ∧
  freevars_cexp (Let c v e1 e2) = freevars_cexp e1 ∪ (freevars_cexp e2 DELETE v) ∧
  freevars_cexp (Letrec c fns e) =
    freevars_cexp e ∪ BIGUNION (set (MAP (λ(fn,e). freevars_cexp e) fns))
      DIFF set (MAP FST fns) ∧
  freevars_cexp (Case c e v css) = freevars_cexp e ∪
    (BIGUNION (set (MAP (λ(_,vs,ec). freevars_cexp ec DIFF set vs) css))
     DELETE v) ∧
  freevars_cexp (NestedCase c g gv p e pes) =
    freevars_cexp g ∪
    (((freevars_cexp e DIFF cepat_vars p) ∪
      BIGUNION (set (MAP (λ(p,e). freevars_cexp e DIFF cepat_vars p) pes)))
    DELETE gv)
Termination
  WF_REL_TAC `measure (cexp_size (K 0))` >> rw []
End

Definition freevars_cexp_l_def[simp]:
  freevars_cexp_l (Var c v) = [v] ∧
  freevars_cexp_l (Prim c op es) = FLAT (MAP freevars_cexp_l es) ∧
  freevars_cexp_l (App c e es) =
    freevars_cexp_l e ++ FLAT (MAP freevars_cexp_l es) ∧
  freevars_cexp_l (Lam c vs e) = FILTER (λv. ¬MEM v vs) (freevars_cexp_l e) ∧
  freevars_cexp_l (Let c v e1 e2) =
    freevars_cexp_l e1 ++ (FILTER ($≠ v) (freevars_cexp_l e2)) ∧
  freevars_cexp_l (Letrec c fns e) =
    FILTER (λv. ¬MEM v (MAP FST fns))
      (freevars_cexp_l e ++ FLAT (MAP (λ(fn,e). freevars_cexp_l e) fns)) ∧
  freevars_cexp_l (Case c e v css) = freevars_cexp_l e ++
    FILTER ($≠ v)
      (FLAT
        (MAP (λ(_,vs,ec). FILTER (λv. ¬MEM v vs) (freevars_cexp_l ec)) css)) ∧
  freevars_cexp_l (NestedCase c g gv p e pes) =
    freevars_cexp_l g ++
    FLAT
      (FILTER (λv. v ≠ gv ∧ ¬MEM v (cepat_vars_l p)) (freevars_cexp_l e) ::
       MAP (λ(p, e). FILTER (λv. v ≠ gv ∧ ¬MEM v (cepat_vars_l p))
                            (freevars_cexp_l e))
       pes)
Termination
  WF_REL_TAC `measure (cexp_size (K 0))` >> rw []
End

Definition substc_def:
  substc f (Var c v) = (case FLOOKUP f v of SOME e => e | NONE => Var c v) ∧
  substc f (Prim c op es) = Prim c op (MAP (substc f) es) ∧
  substc f (App c e es) = App c (substc f e) (MAP (substc f) es) ∧
  substc f (Lam c vs e) = Lam c vs (substc (FDIFF f (set vs)) e) ∧
  substc f (Let c v e1 e2) = Let c v (substc f e1) (substc (f \\ v) e2) ∧
  substc f (Letrec c fns e) =
    Letrec c
      (MAP (λ(fn,e). (fn, substc (FDIFF f (set (MAP FST fns))) e)) fns)
      (substc (FDIFF f (set (MAP FST fns))) e) ∧
  substc f (Case c e v css) =
    Case c (substc f e) v
      (MAP (λ(cn,vs,e). (cn,vs, substc (FDIFF f (v INSERT set vs)) e)) css) ∧
  substc f (NestedCase c g gv p e pes) =
  NestedCase
    c
    (substc f g)
    gv
    p
    (substc (FDIFF f (gv INSERT cepat_vars p)) e)
    (MAP (λ(p,e). (p, substc (FDIFF f (gv INSERT cepat_vars p)) e)) pes)
Termination
  WF_REL_TAC `measure (cexp_size (K 0) o  SND)` >> rw []
End

Overload substc1 = ``λname v e. substc (FEMPTY |+ (name,v)) e``;

Definition get_info_def:
  get_info (Var c _) = c ∧
  get_info (Prim c _ _) = c ∧
  get_info (App c _ _) = c ∧
  get_info (Lam c _ _) = c ∧
  get_info (Let c _ _ _) = c ∧
  get_info (Letrec c _ _) = c ∧
  get_info (Case c _ _ _) = c ∧
  get_info (NestedCase c _ _ _ _ _) = c
End

Definition cexp_wf_def:
  cexp_wf (Var _ v) = T ∧
  cexp_wf (Prim _ op es) = EVERY cexp_wf es ∧
  cexp_wf (App _ e es) = (cexp_wf e ∧ EVERY cexp_wf es ∧ es ≠ []) ∧
  cexp_wf (Lam _ vs e) = (cexp_wf e ∧ vs ≠ []) ∧
  cexp_wf (Let _ v e1 e2) = (cexp_wf e1 ∧ cexp_wf e2) ∧
  cexp_wf (Letrec _ fns e) = (EVERY cexp_wf $ MAP SND fns ∧ cexp_wf e ∧ fns ≠ []) ∧
  cexp_wf (Case _ e v css) = (
    cexp_wf e ∧ EVERY cexp_wf $ MAP (SND o SND) css ∧ css ≠ [] ∧
    ¬ MEM v (FLAT $ MAP (FST o SND) css)) ∧
  cexp_wf (NestedCase _ g gv p e pes) = (
    cexp_wf g ∧ cexp_wf e ∧ EVERY cexp_wf $ MAP SND pes ∧
    ¬ MEM gv (FLAT $ MAP (cepat_vars_l o FST) ((p,e) :: pes))
  )
Termination
  WF_REL_TAC `measure $ cexp_size (K 0)` >> rw[fetch "-" "cexp_size_def"] >>
  gvs[MEM_MAP, EXISTS_PROD] >>
  rename1 `MEM _ es` >> Induct_on `es` >> rw[] >> gvs[fetch "-" "cexp_size_def"]
End

Definition NestedCase_free_def[simp]:
  NestedCase_free (Var _ _) = T ∧
  NestedCase_free (Prim _ _ es) = EVERY NestedCase_free es ∧
  NestedCase_free (App _ e es) = (NestedCase_free e ∧ EVERY NestedCase_free es)∧
  NestedCase_free (Lam _ vs e) = NestedCase_free e ∧
  NestedCase_free (Let _ _ e1 e2) = (NestedCase_free e1 ∧ NestedCase_free e2) ∧
  NestedCase_free (Letrec _ fns e) = (
    NestedCase_free e ∧ EVERY NestedCase_free $ MAP SND fns
  ) ∧
  NestedCase_free (Case _ e _ css) = (
    NestedCase_free e ∧ EVERY NestedCase_free $ MAP (SND o SND) css
  ) ∧
  NestedCase_free (NestedCase _ _ _ _ _ _) = F
Termination
  WF_REL_TAC ‘measure $ cexp_size (K 0)’ >>
  simp[fetch "-" "cexp_size_eq", MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
  rename [‘MEM _ list’] >> Induct_on ‘list’ >>
  simp[FORALL_PROD, listTheory.list_size_def, basicSizeTheory.pair_size_def] >>
  rw[] >> gs[]
End

Definition cexp_eq_def:
  cexp_eq (Var _ v1) (Var _ v2) = (v1 = v2) ∧
  cexp_eq (Prim _ op1 es1) (Prim _ op2 es2) = (
    op1 = op2 ∧ LIST_REL (λe1 e2. cexp_eq e1 e2) es1 es2) ∧
  cexp_eq (App _ e1 es1) (App _ e2 es2) = (
    cexp_eq e1 e2 ∧ LIST_REL (λe1 e2. cexp_eq e1 e2) es1 es2) ∧
  cexp_eq (Lam _ vs1 e1) (Lam _ vs2 e2) = (vs1 = vs2 ∧ cexp_eq e1 e2) ∧
  cexp_eq (Let _ v1 e11 e12) (Let _ v2 e21 e22) = (
    v1 = v2 ∧ cexp_eq e11 e21 ∧ cexp_eq e12 e22) ∧
  cexp_eq (Letrec _ fns1 e1) (Letrec _ fns2 e2) = (cexp_eq e1 e2 ∧
    LIST_REL (λ(fn1,e1) (fn2,e2). fn1 = fn2 ∧ cexp_eq e1 e2) fns1 fns2) ∧
  cexp_eq (Case _ e1 v1 css1) (Case _ e2 v2 css2) = (
    cexp_eq e1 e2 ∧ v1 = v2 ∧
    LIST_REL (λ(cn1,vs1,e1) (cn2,vs2,e2). cn1 = cn2 ∧ vs1 = vs2 ∧ cexp_eq e1 e2)
      css1 css2) ∧
  (cexp_eq (NestedCase _ g1 gv1 p1 e1 pes1) (NestedCase _ g2 gv2 p2 e2 pes2) ⇔
     cexp_eq g1 g2 ∧ gv1 = gv2 ∧ p1 = p2 ∧ cexp_eq e1 e2 ∧
     LIST_REL (λ(p1,e1) (p2,e2). p1 = p2 ∧ cexp_eq e1 e2) pes1 pes2) ∧
  (cexp_eq _ _ ⇔ F)
Termination
  WF_REL_TAC `measure $ cexp_size (K 0) o SND` >> rw[]
End

val _ = export_theory();
