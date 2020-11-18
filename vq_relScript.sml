
open bossLib boolLib;
open HolKernel pure_langTheory valueTheory quotient_llistTheory listTheory
     llistTheory quotient_ltreeTheory quotientLib;

val _ = new_theory "vq_rel";

Definition empty_conf_def:
  empty_conf = ARB : ('a, 'b) conf
End

Definition vq_rel_def:
  vq_rel = v_rel empty_conf
End

Theorem vq_rel_refl:
  ∀x. vq_rel x x
Proof
  simp [vq_rel_def, v_rel_refl]
QED

Theorem vq_rel_sym:
  ∀x y. vq_rel x y ⇔ vq_rel y x
Proof
  simp [vq_rel_def, v_rel_sym]
QED

Theorem vq_rel_trans:
  ∀x y z. vq_rel x y ∧ vq_rel y z ⇒ vq_rel x z
Proof
  metis_tac [vq_rel_def, v_rel_trans]
QED

Theorem vq_rel_EQUIV:
  EQUIV vq_rel
Proof
  simp [EQUIV_def, FUN_EQ_THM]
  \\ metis_tac [vq_rel_sym, vq_rel_trans, vq_rel_refl]
QED

Theorem v_rel_eqns:
  (∀b1 b2.
     b1 = b2 ⇒
       v_rel c (Atom b1) (Atom b2)) ∧
  (∀n1 x1 n2 x2.
     (∀z. v_rel c (eval c (bind [(n1, z)] x1)) (eval c (bind [(n2, z)] x2))) ⇒
       v_rel c (Closure n1 x1) (Closure n2 x2)) ∧
  (∀n1 x1 n2 x2.
     n1 = n2 ∧
     LIST_REL (v_rel c) x1 x2 ⇒
       v_rel c (Constructor n1 x1) (Constructor n2 x2)) ∧
  v_rel c Diverge Diverge ∧
  v_rel c Error Error
Proof
  simp [v_rel_def]
  \\ rpt conj_tac
  >- (* Atom *)
   (gen_tac
    \\ Cases \\ simp [v_rel'_def])
  >- (* Closure *)
   (simp [PULL_FORALL]
    \\ ntac 4 gen_tac
    \\ Cases
    \\ rw [v_rel'_def, DISJ_EQ_IMP])
  >- (* Constructor *)
   (simp [PULL_FORALL]
    \\ ntac 3 gen_tac
    \\ Cases
    \\ rw [v_rel'_def, DISJ_EQ_IMP]
    \\ fs[LIST_REL_EL_EQN, v_rel_def])
     (* Constants *)
  \\ Cases \\ simp [v_rel'_def]
QED

Triviality v_rel'_refl:
  ∀n c x . v_rel' c n x x
Proof
  Induct >> rw[v_rel'_def]
  \\ CASE_TAC \\ fs []
  \\ rw [LIST_REL_EL_EQN]
QED

Theorem v_rel_eq_simps:
  (∀b x. v_rel c (Atom b) x ⇔ x = Atom b) ∧
  (∀n x y. v_rel c (Constructor n x) y ⇔
    ∃x'.
      y = Constructor n x' ∧
      LIST_REL (v_rel c) x x') ∧
  (∀s x y. v_rel c (Closure s x) y ⇔
    ∃s' x'.
      y = Closure s' x' ∧
      ∀z. exp_rel c (bind [(s,z)] x) (bind [(s',z)] x')) ∧
  (∀x. v_rel c Diverge x ⇔ x = Diverge) ∧
  (∀x. v_rel c Error x ⇔ x = Error)
Proof
  rw[v_rel_def]
  >- ( (* Atom *)
    EQ_TAC >> strip_tac
    >- (
      first_x_assum (qspec_then `SUC 0` assume_tac) >>
      gvs[v_rel'_def]
      ) >>
    gvs[v_rel'_refl]
    )
  >- ( (* Constructor *)
    reverse EQ_TAC >> strip_tac
    >- (
      gvs[] >>
      Cases >> gvs[v_rel'_def] >>
      fs[LIST_REL_EL_EQN, v_rel_def]
      ) >>
    first_assum (qspec_then `SUC 0` assume_tac) >>
    Cases_on `y` >> gvs[v_rel'_def] >>
    first_assum (qspec_then `SUC 0` assume_tac) >>
    fs[v_rel'_def] >> gvs[] >>
    fs[LIST_REL_EL_EQN] >> rw[v_rel_def] >>
    rename1 `m < _` >> rename1 `v_rel' _ step _ _` >>
    last_x_assum (qspec_then `SUC step` assume_tac) >> gvs[v_rel'_def] >>
    fs[LIST_REL_EL_EQN, v_rel'_refl]
    )
  >- ( (* Closure *)
    reverse EQ_TAC >> strip_tac
    >- (
      gvs[] >>
      Cases >> gvs[v_rel'_def] >>
      fs[exp_rel_def, v_rel_def]
      ) >>
    first_assum (qspec_then `SUC 0` assume_tac) >>
    Cases_on `y` >> gvs[v_rel'_def, exp_rel_def, v_rel_def] >>
    first_assum (qspec_then `SUC 0` assume_tac) >>
    fs[v_rel'_def] >> rw[] >> gvs[v_rel'_refl] >>
    first_x_assum (qspec_then `SUC n'` assume_tac) >>
    gvs[v_rel'_def, v_rel'_refl]
    )
  >> ( (* Diverge, Error *)
    EQ_TAC >> rw[v_rel'_refl] >>
    pop_assum (qspec_then `SUC 0` assume_tac) >>
    gvs[v_rel'_def]
    )
QED

(*
 * Re-definitions for eval:
 *)

Theorem eval_thm:
  eval c Fail = Error ∧
  eval c (Var s) = Error ∧
  eval c (Cons s xs) =
    Constructor s (MAP (eval c) xs) ∧
  eval c (IsEq s n x) = is_eq c s n (eval c x) ∧
  eval c (Proj s i x) = el s i (eval c x) ∧
  eval c (Let s x y) = eval c (bind [(s,x)] y) ∧
  eval c (If x y z) =
   (if v_rel c (eval c x) Diverge then Diverge
    else if v_rel c (eval c x) True then eval c y
    else if v_rel c (eval c x) False then eval c z
    else Error) ∧
  eval c (Lam s x) = Closure s x ∧
  eval c (Letrec f x) = eval c (subst_funs f x) ∧
  eval c (App x y) =
    (let v = eval c x in
       if v_rel c v Diverge then Diverge
       else case dest_Closure v of
              NONE => Error
            | SOME (s,body) => eval c (bind [(s,y)] body)) ∧
  eval c (Case x nm css) = eval c (expandCases x nm css)
Proof
  gs [eval_thm, v_rel_eq_simps,
      v_rel_eq_simps |> PURE_ONCE_REWRITE_RULE [v_rel_sym]]
QED

Definition vq_eval_def:
  vq_eval = eval empty_conf
End

Theorem vq_eval_thm =
  eval_thm
  |> Q.INST [‘c’|->‘empty_conf’]
  |> REWRITE_RULE [
    GSYM vq_rel_def,
    GSYM vq_eval_def];

(*
 * Some constructor theorems about the v type. Anything vq_rel
 * (or higher-order equiv. rels. with vq_rel) will be lifted to
 * equality in the new type.
 *
 * (This particular theorem will look like the theorem [Constructor_11] above).
 *)

Theorem Constructor_vq_11:
  vq_rel (Constructor n x) (Constructor m y) ⇔
    n = m ∧
    LIST_REL vq_rel x y
Proof
  reverse eq_tac >>
  simp[vq_rel_def, v_rel_def] >> strip_tac
  >- (
    Cases >> simp[v_rel'_def] >>
    fs[LIST_REL_EL_EQN, vq_rel_def, v_rel_def]
    )
  >- (
    first_assum (qspec_then `SUC 0` assume_tac) >> fs[v_rel'_def] >> gvs[] >>
    fs[LIST_REL_EL_EQN, v_rel_def] >> rw[] >>
    rename1 `v_rel' _ k _ _` >>
    last_x_assum (qspec_then `SUC k` assume_tac) >>
    gvs[v_rel'_def, v_rel'_refl, LIST_REL_EL_EQN]
    )
QED

(*
 * This theorem is more interesting because the results of evaluating
 * both closures will be equal (as the closures are equal in the new type.)
 *)

Theorem Closure_vq_11:
  vq_rel (Closure n e1) (Closure m e2) ⇔
    ∀z. vq_rel (vq_eval (bind [(n, z)] e1)) (vq_eval (bind [(m, z)] e2))
Proof
  simp [vq_rel_def, vq_eval_def]
  \\ reverse eq_tac
  >- simp [v_rel_eqns]
  \\ strip_tac
  \\ gvs[v_rel_eq_simps, exp_rel_def, Closure_11]
QED

(*
 * Respectfulness theorems for the lifting.
 *)

Theorem Constructor_rsp:
  x1 = y1 ∧
  LIST_REL vq_rel x2 y2 ⇒
    vq_rel (Constructor x1 x2) (Constructor y1 y2)
Proof
  rw [vq_rel_def]
  \\ irule (el 3 (CONJUNCTS v_rel_eqns))
  \\ fs []
QED

Theorem vq_eval_rsp:
  x1 = x2 ⇒
    vq_rel (vq_eval x1) (vq_eval x2)
Proof
  metis_tac [vq_rel_EQUIV, EQUIV_def]
QED

Theorem is_eq_rsp:
  c1 = c2 ∧
  x1 = y1 ∧
  n1 = n2 ∧
  vq_rel x2 y2 ⇒
    vq_rel (is_eq c1 x1 n1 x2) (is_eq c2 y1 n2 y2)
Proof
  strip_tac
  \\ simp [is_eq_def] \\ rw []
  \\ fs [vq_rel_refl, v_rel_eqns, v_rel_eq_simps, vq_rel_def, v_rel_sym]
  \\ rpt CASE_TAC \\ fs []
  \\ fs [vq_rel_refl, v_rel_eqns, v_rel_eq_simps, vq_rel_def, v_rel_sym]
  \\ gvs [v_rel'_def, LIST_REL_EL_EQN, v_rel'_refl]
QED

Theorem el_rsp:
  x1 = y1 ∧
  x2 = y2 ∧
  vq_rel x3 y3 ⇒
    vq_rel (el x1 x2 x3) (el y1 y2 y3)
Proof
  rw [el_def] >>
  fs[vq_rel_def, v_rel_def, v_rel_eq_simps]
  >- (
    rename1 `x ≠ Diverge` >>
    pop_assum (qspec_then `SUC 0` assume_tac) >>
    Cases_on `x` >> fs[v_rel'_def]
    ) >>
  strip_tac >>
  rename1 `∀n. v_rel' _ n x y` >>
  rpt CASE_TAC >> fs [] >>
  first_assum (qspec_then `SUC 0` assume_tac) >>
  fs[LNTH_fromList, v_rel'_def, v_rel'_refl,
     LIST_REL_EL_EQN] >>
  gvs[] >>
  first_x_assum (qspec_then `SUC n` assume_tac) >>
  gvs[v_rel'_def, v_rel'_refl, LIST_REL_EL_EQN]
QED

Theorem isClos_rsp:
  ∀x y. vq_rel x y ⇒ isClos x = isClos y
Proof
  Cases \\ Cases \\ simp [vq_rel_def, v_rel_eq_simps, isClos_def]
QED

(*
 * Not many conjuncts survive (yet):
 *)

Theorem vq_progress_lemma =
  progress_lemma
  |> Q.INST [‘c’|->‘empty_conf’]
  |> REWRITE_RULE [
       exp_rel_def,
       GSYM vq_rel_def,
       GSYM vq_eval_def];

Theorem isClos_is_Closure:
  ∀v. isClos v ⇔ ∃s x. vq_rel v (Closure s x)
Proof
  Cases
  \\ rw [isClos_def, vq_rel_def, v_rel_eq_simps, exp_rel_def]
  \\ Q.LIST_EXISTS_TAC [‘n’, ‘x’]
  \\ simp [v_rel_refl]
QED

(*
 * Perform lifting.
 *)

val thms = define_quotient_types_full {
  types =
    [{equiv = vq_rel_EQUIV,
      name  = "vq"
     }
    ],
  defs = [
    (* Constructors *)
    {def_name = "Atom_vq_def",
     fname    = "Atom_vq",
     func     = “Atom”,
     fixity   = NONE},
    {def_name = "Constructor_vq_def",
     fname    = "Constructor_vq",
     func     = “Constructor”,
     fixity   = NONE},
    {def_name = "Closure_vq_def",
     fname    = "Closure_vq",
     func       = “Closure”,
     fixity     = NONE},
    {def_name = "Diverge_vq_def",
     fname    = "Diverge_vq",
     func     = “Diverge”,
     fixity   = NONE},
    {def_name = "Error_vq_def",
     fname    = "Error_vq",
     func     = “Error”,
     fixity   = NONE},
    (* Functions *)
    {def_name = "eval_vq_def",
     fname    = "eval_vq",
     func     = “vq_eval”,
     fixity   = NONE },
    {def_name = "isClos_vq_def",
     fname    = "is_Clos_vq",
     func     = “isClos”,
     fixity   = NONE},
    {def_name = "is_eq_vq_def",
     fname    = "is_eq_vq",
     func     = “is_eq”,
     fixity   = NONE
    },
    {def_name = "el_vq_def",
     fname    = "el_vq",
     func     = “el”,
     fixity   = NONE
    }
    ],
  tyop_equivs = [],
  tyop_quotients = [],
  tyop_simps = [],
  respects = [
    Constructor_rsp,
    el_rsp,
    is_eq_rsp,
    isClos_rsp
    ],
  poly_preserves = [],
  poly_respects = [
  ],
  old_thms = [
    Constructor_vq_11,
    Closure_vq_11,
    (* dest_Closure is an issue: *)
    vq_eval_thm |> CONJUNCTS |> C (curry List.take) 9 |> LIST_CONJ,
    vq_progress_lemma,
    isClos_is_Closure
    ]
  };

Theorem progress_vq =
  SIMP_RULE std_ss [el 5 thms, PULL_EXISTS] (el 4 thms);

val _ = export_theory ();

