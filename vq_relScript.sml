
open bossLib boolLib;
open HolKernel pure_langTheory quotient_llistTheory
     quotient_ltreeTheory quotientLib;

val _ = new_theory "vq_rel";

val _ = Parse.thytype_abbrev (
  {Name = "v", Thy = "pure_lang"},
  “:('a, 'b) v_prefix ltree”,
  true);

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

(*
 * Re-definitions for :v constructors.
 * (These are just overrides in the [pure_lang] theory, and that confuses
 * the quotient package.)
 *)

val _ = Parse.clear_overloads_on "Atom";
val _ = Parse.clear_overloads_on "Constructor";
val _ = Parse.clear_overloads_on "Closure";
val _ = Parse.clear_overloads_on "Diverge";
val _ = Parse.clear_overloads_on "Error";
val _ = Parse.clear_overloads_on "True";
val _ = Parse.clear_overloads_on "False";

Definition Atom_def:
  Atom b = Branch (Atom' b) LNIL
End

Definition Constructor_def:
  Constructor n ts = Branch (Constructor' n) (fromList ts)
End

Definition Closure_def:
  Closure s x = Branch (Closure' s x) LNIL
End

Definition Diverge_def:
  Diverge = Branch Diverge' LNIL
End

Definition Error_def:
  Error = Branch Error' LNIL
End

Overload True = “Constructor "True" []”;

Overload False = “Constructor "False" []”;

(*
 * Theorems about :v.
 *)

Theorem v_distinct:
  ALL_DISTINCT [
    Atom b;
    Closure s x;
    Constructor n y;
    Diverge;
    Error]
Proof
  rw [Atom_def, Constructor_def, Closure_def, Diverge_def, Error_def]
QED

Theorem v_distinct = SIMP_RULE list_ss [] v_distinct;

Theorem Atom_11:
  Atom x1 = Atom x2 ⇔ x1 = x2
Proof
  rw [Atom_def]
QED

Theorem Constructor_11:
  Constructor x1 y1 = Constructor x2 y2 ⇔ x1 = x2 ∧ y1 = y2
Proof
  rw [Constructor_def]
QED

Theorem Closure_11:
  Closure x1 y1 = Closure x2 y2 ⇔ x1 = x2 ∧ y1 = y2
Proof
  rw [Closure_def]
QED

(*
 * TODO
 * - Re-prove when v_rel relies on finite-breadth values.
 *)

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
    \\ rw [v_rel'_def, Closure_def, DISJ_EQ_IMP])
  >- (* Constructor *)
   (simp [PULL_FORALL]
    \\ ntac 3 gen_tac
    \\ Cases
    \\ rw [v_rel'_def, Constructor_def, DISJ_EQ_IMP]
    \\ fs[listTheory.LIST_REL_EL_EQN, v_rel_def])
     (* Constants *)
  \\ Cases \\ simp [v_rel'_def]
QED

Triviality v_rel'_refl:
  ∀ n c x . v_rel' c n x x
Proof
  Cases >> rw[v_rel'_def]
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
      gvs[v_rel'_def, Atom_def]
      ) >>
    gvs[v_rel'_refl]
    )
  >- ( (* Constructor *)
    reverse EQ_TAC >> strip_tac
    >- (
      gvs[] >>
      Cases >> gvs[v_rel'_def, Constructor_def] >>
      DISJ2_TAC >>
      fs[listTheory.LIST_REL_EL_EQN, v_rel_def]
      ) >>
    first_assum (qspec_then `SUC 0` assume_tac) >>
    Cases_on `y` >> gvs[v_rel'_def, Constructor_def] >>
    first_assum (qspec_then `SUC 0` assume_tac) >>
    Cases_on `a` >> fs[v_rel'_def, Constructor_def] >> gvs[]
    >- (irule listTheory.EVERY2_refl >> rw[] >> fs[v_rel_refl]) >>
    fs[listTheory.LIST_REL_EL_EQN] >> rw[v_rel_def] >>
    rename1 `m < _` >> rename1 `v_rel' _ step _ _` >>
    last_x_assum (qspec_then `SUC step` assume_tac) >> gvs[v_rel'_def] >>
    fs[listTheory.LIST_REL_EL_EQN, v_rel'_refl]
    )
  >- ( (* Closure *)
    reverse EQ_TAC >> strip_tac
    >- (
      gvs[] >>
      Cases >> gvs[v_rel'_def, Closure_def] >>
      fs[exp_rel_def, v_rel_def]
      ) >>
    first_assum (qspec_then `SUC 0` assume_tac) >>
    Cases_on `y` >> gvs[v_rel'_def, Closure_def, exp_rel_def, v_rel_def] >>
    first_assum (qspec_then `SUC 0` assume_tac) >>
    Cases_on `a` >> fs[v_rel'_def, Closure_def] >> rw[] >> gvs[v_rel'_refl] >>
    first_x_assum (qspec_then `SUC n` assume_tac) >>
    gvs[v_rel'_def, v_rel'_refl]
    )
  >> ( (* Diverge, Error *)
    EQ_TAC >> rw[v_rel'_refl] >>
    pop_assum (qspec_then `SUC 0` assume_tac) >>
    gvs[v_rel'_def, Diverge_def, Error_def]
    )
QED

(*
 * Re-definitions for eval:
 * TODO:
 * - Adjust/specialize for finite-breadth values
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
   (if eval c x = Diverge then Diverge
    else if eval c x = True then eval c y
    else if eval c x = False then eval c z
    else Error) ∧
  eval c (Lam s x) = Closure s x ∧
  eval c (Letrec f x) = eval c (subst_funs f x) ∧
  eval c (App x y) =
    (let v = eval c x in
       if v = Diverge then Diverge
       else case dest_Closure v of
              NONE => Error
            | SOME (s,body) => eval c (bind [(s,y)] body)) ∧
  eval c (Case x nm css) = eval c (expandCases x nm css)
Proof
  simp [eval_thm, Constructor_def, Error_def, Diverge_def, Closure_def,
        llistTheory.LMAP_fromList]
QED

Definition vq_eval_def:
  vq_eval = eval empty_conf
End

Theorem vq_eval_thm =
  eval_thm
  |> Q.INST [‘c’|->‘empty_conf’]
  |> REWRITE_RULE [GSYM vq_eval_def];

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
  simp[vq_rel_def, v_rel_def, Constructor_def] >> strip_tac
  >- (
    Cases >> simp[v_rel'_def] >>
    fs[listTheory.LIST_REL_EL_EQN, vq_rel_def, v_rel_def]
    )
  >- (
    first_assum (qspec_then `SUC 0` assume_tac) >> fs[v_rel'_def] >> gvs[]
    >- (irule listTheory.EVERY2_refl >> fs[v_rel_refl]) >>
    fs[listTheory.LIST_REL_EL_EQN, v_rel_def] >> rw[] >>
    rename1 `v_rel' _ k _ _` >>
    last_x_assum (qspec_then `SUC k` assume_tac) >>
    gvs[v_rel'_def, v_rel'_refl, listTheory.LIST_REL_EL_EQN]
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

Theorem Atom_rsp:
  x1 = x2 ⇒
    vq_rel (Atom x1) (Atom x2)
Proof
  rw [vq_rel_def, v_rel_refl]
QED

Theorem Constructor_rsp:
  x1 = y1 ∧
  LIST_REL vq_rel x2 y2 ⇒
    vq_rel (Constructor x1 x2) (Constructor y1 y2)
Proof
  rw [vq_rel_def]
  \\ irule (el 3 (CONJUNCTS v_rel_eqns))
  \\ fs []
QED

(*
  finite_branching t ⇔
    ∀a ts. Branch a ts ∈ subtrees t ⇒ LFINITE ts

  v_rel c x y = ... ∧
                finite_branching x ∧
                finite_branching y
*)

Theorem dest_Closure_rsp:
  vq_rel x1 x2 ⇒
    OPTREL (λ(n1, x1) (n2, x2). ∀z.
      vq_rel (vq_eval (bind [(n1,z)] x1)) (vq_eval (bind [(n2,z)] x2)))
      (dest_Closure x1)
      (dest_Closure x2)
Proof
  rw [dest_Closure_def]
  \\ rpt CASE_TAC \\ fs []
  \\ fs [GSYM Atom_def,
         GSYM Closure_def,
         GSYM Constructor_def,
         GSYM Diverge_def,
         GSYM Error_def]
  \\ fs [Closure_vq_11, vq_rel_def, v_rel_eq_simps, v_distinct, Closure_11]
  \\ fs [Closure_def, v_rel_def]
  \\ pop_assum (qspec_then ‘SUC 0’ assume_tac)
  \\ fs [v_rel'_def]
QED

Theorem vq_eval_rsp:
  x1 = x2 ⇒
    vq_rel (vq_eval x1) (vq_eval x2)
Proof
  metis_tac [vq_rel_EQUIV, EQUIV_def]
QED

(*
Definition vq_is_eq_def:
  vq_is_eq s x =
    if x = Diverge then Diverge else
      case some (t, xs). x = Constructor t xs of
        NONE => Error
      | SOME (t, xs) => if s = t then True else False
End

Theorem vq_is_eq_thm:
  ∀c. vq_is_eq = is_eq c
Proof
  rw [FUN_EQ_THM, vq_is_eq_def, is_eq_def, Diverge_def, Constructor_def,
      Error_def]
  \\ DEEP_INTRO_TAC optionTheory.some_intro
  \\ simp [pairTheory.UNCURRY, pairTheory.FORALL_PROD]
  \\ rw []
  \\ rpt CASE_TAC \\ fs []
QED
*)

Theorem is_eq_rsp:
  c1 = c2 ∧
  x1 = y1 ∧
  n1 = n2 ∧
  vq_rel x2 y2 ⇒
    vq_rel (is_eq c1 x1 n1 x2) (is_eq c2 y1 n2 y2)
Proof
  strip_tac
  \\ simp [is_eq_def] \\ rw []
  \\ fs [GSYM Diverge_def, GSYM Constructor_def, GSYM Error_def]
  \\ fs [vq_rel_refl, v_rel_eqns, v_rel_eq_simps, vq_rel_def, v_rel_sym]
  \\ rpt CASE_TAC \\ fs []
  \\ fs [vq_rel_refl, v_rel_eqns, v_rel_eq_simps, vq_rel_def, v_rel_sym]
  \\ fs [Constructor_def, Diverge_def, Error_def, Atom_def] \\ rw []
  \\ fs [v_rel_def]
  \\ first_x_assum (qspec_then ‘SUC 0’ assume_tac)
  \\ gvs [v_rel'_def, listTheory.LIST_REL_EL_EQN, v_rel'_refl]
QED

(*
 * TODO: Same issue as above.
 * TODO: Also, its slightly false.
 *)

Theorem vq_el_rsp:
  x1 = y1 ∧
  x2 = y2 ∧
  vq_rel x3 y3 ⇒
    vq_rel (el x1 x2 x3) (el y1 y2 y3)
Proof
  rw [el_def] >>
  fs[vq_rel_def, v_rel_def, GSYM Diverge_def, v_rel_eq_simps]
  >- (
    rename1 `x ≠ Diverge` >>
    pop_assum (qspec_then `SUC 0` assume_tac) >>
    Cases_on `x` >> fs[v_rel'_def, Diverge_def]
    ) >>
  strip_tac >>
  rename1 `∀n. v_rel' _ n x y` >>
  fs[Diverge_def] >>

  Cases_on `x` >> Cases_on `y` >>
  first_assum (qspec_then `SUC 0` assume_tac) >>
  fs[llistTheory.LNTH_fromList, v_rel'_def, v_rel'_refl,
     listTheory.LIST_REL_EL_EQN] >>
  gvs[] >>
  Cases_on `x1 = m` >> gvs[v_rel'_refl] >>
  CASE_TAC >> gvs[v_rel'_refl] >>
  first_x_assum (qspec_then `SUC n` assume_tac) >>
  gvs[v_rel'_def, v_rel'_refl, listTheory.LIST_REL_EL_EQN]
QED

Theorem isClos_rsp:
  ∀x y. vq_rel x y ⇒ isClos x = isClos y
Proof
  metis_tac [isClos_def, vq_rel_def, v_rel_def, v_rel'_def]
QED

(*
 * Not many conjuncts survive (yet):
 *)

Theorem vq_eval_thm =
  vq_eval_thm
  |> CONJUNCTS
  |> C (curry List.take) 2
  |> LIST_CONJ;

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
  \\ Cases_on ‘a’ \\ Cases_on ‘ts’
  \\ rw [Closure_def, isClos_def, vq_rel_def, v_rel_def]
  \\ TRY
    (Q.REFINE_EXISTS_TAC ‘SUC n’
     \\ simp [v_rel'_def])
  \\ Q.LIST_EXISTS_TAC [‘s’, ‘e’]
  \\ simp [GSYM v_rel_def, v_rel_refl] (* Meh. *)
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
    {def_name = "dest_Closure_vq_def",
     fname    = "dest_Closure_vq",
     func     = “dest_Closure”,
     fixity   = NONE},
    {
     def_name = "isClos_vq_def",
     fname    = "is_Clos_vq",
     func     = “isClos”,
     fixity   = NONE}
    (*
    {def_name = "is_eq_vq_def",
     fname    = "is_eq_vq",
     func     = “vq_is_eq”,
     fixity   = NONE
    },
    {def_name = "el_vq_def",
     fname    = "el_vq",
     func     = “vq_el”,
     fixity   = NONE
    } *)
    ],
  tyop_equivs = [],
  tyop_quotients = [llist_QUOTIENT],
  tyop_simps = [llist_rel_equality, llist_map_I],
  respects = [
    Constructor_rsp,
    dest_Closure_rsp,
    isClos_rsp
    ],
  poly_preserves = [],
  poly_respects = [
  ],
  old_thms = [
    Constructor_vq_11,
    Closure_vq_11,
    vq_eval_thm,
    vq_progress_lemma,
    isClos_is_Closure
    ]
  };

Theorem progress_vq =
  SIMP_RULE std_ss [el 5 thms, PULL_EXISTS] (el 4 thms);

val _ = export_theory ();

