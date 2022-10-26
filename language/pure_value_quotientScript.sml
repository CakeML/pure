
open bossLib boolLib;
open HolKernel pure_eval_oldTheory pure_valueTheory quotient_llistTheory listTheory
     llistTheory quotient_ltreeTheory quotientLib;

val _ = new_theory "pure_value_quotient";

Theorem v_rel_EQUIV:
  EQUIV v_rel
Proof
  simp [EQUIV_def, FUN_EQ_THM]
  \\ metis_tac [v_rel_sym, v_rel_trans, v_rel_refl]
QED

Theorem isClos_is_Closure:
  ∀v. isClos v ⇔ ∃s x. v_rel v (Closure s x)
Proof
  Cases
  \\ rw [isClos_def, v_rel_cases, exp_rel_def]
  \\ Q.LIST_EXISTS_TAC [‘n’, ‘x’]
  \\ simp [v_rel_refl]
QED

(*
 * The eval_thm theorem adapted for lifting.
 *)

Theorem eval_lift:
  eval (Var s) = Error ∧
  eval (Cons s xs) = Constructor s (MAP eval xs) ∧
  eval (IsEq s n a x) = is_eq s n (eval x) ∧
  eval (Proj s i x) = el s i (eval x) ∧
  eval (Let s x y) = eval (bind1 s x y) ∧
  eval (If x y z) =
    (if v_rel (eval x) Diverge then Diverge
     else if v_rel (eval x) True then eval y
     else if v_rel (eval x) False then eval z
     else Error) ∧
  eval (Lam s x) = Closure s x ∧
  eval (Letrec f x) = eval (subst_funs f x) ∧
  eval (Case x nm css) = eval (expandCases x nm css)
Proof
  simp [eval_thm, v_rel_cases,
        PURE_ONCE_REWRITE_RULE [v_rel_sym] v_rel_cases]
QED

(*
 * Some constructor theorems about the v type. Anything vq_rel
 * (or higher-order equiv. rels. with vq_rel) will be lifted to
 * equality in the new type.
 *)

Theorem Atom_vq_11:
  v_rel (Atom x) (Atom y) ⇔
    x = y
Proof
  rw [v_rel_cases, EQ_SYM_EQ]
QED

Theorem Constructor_vq_11:
  v_rel (Constructor n x) (Constructor m y) ⇔
    n = m ∧
    LIST_REL v_rel x y
Proof
  rw [v_rel_cases, EQ_SYM_EQ]
QED

Theorem Closure_vq_11:
  v_rel (Closure n e1) (Closure m e2) ⇔
    ∀z. v_rel (eval (bind1 n z e1)) (eval (bind1 m z e2))
Proof
  rw [v_rel_cases, exp_rel_def]
QED

(*
 * Respectfulness theorems for the lifting.
 *)

Theorem Constructor_rsp:
  x1 = y1 ∧
  LIST_REL v_rel x2 y2 ⇒
    v_rel (Constructor x1 x2) (Constructor y1 y2)
Proof
  rw [Constructor_vq_11]
QED

Theorem vq_eval_rsp:
  x1 = x2 ⇒
    v_rel (eval x1) (eval x2)
Proof
  simp [v_rel_refl]
QED

Theorem is_eq_rsp:
  v_rel x y ⇒
    v_rel (is_eq s n x) (is_eq s n y)
Proof
  rw [is_eq_def]
  \\ fs [v_rel_refl, v_rel_cases]
  \\ rpt CASE_TAC \\ gs [v_rel_cases, LIST_REL_EL_EQN]
QED

Theorem el_rsp:
  v_rel x y ⇒
    v_rel (el s n x) (el s n y)
Proof
  rw [el_def]
  \\ fs [v_rel_cases]
  \\ rpt CASE_TAC \\ gs [v_rel_cases, LIST_REL_EL_EQN]
QED

Theorem isClos_rsp:
  ∀x y. v_rel x y ⇒ isClos x = isClos y
Proof
  Cases \\ Cases \\ simp [v_rel_cases, isClos_def]
QED

(*
 * Perform lifting.
 *)

type def = {
    def_name: string,
    fixity: Parse.fixity option,
    fname: string,
    func: term
  };

val defs_Constructors : def list = [
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
     fixity   = NONE}
  ];

val defs_Functions : def list = [
    {def_name = "eval_vq_def",
     fname    = "eval_vq",
     func     = “eval”,
     fixity   = NONE},
    {def_name = "isClos_vq_def",
     fname    = "is_Clos_vq",
     func     = “isClos”,
     fixity   = NONE},
    {def_name = "is_eq_vq_def",
     fname    = "is_eq_vq",
     func     = “is_eq”,
     fixity   = NONE},
    {def_name = "el_vq_def",
     fname    = "el_vq",
     func     = “el”,
     fixity   = NONE}
  ];

val [
    Constructor_vq_11,
    Closure_vq_11,
    eval_vq_thm,
    progress_vq_thm,
    isClos_vq_is_Closure,
    exp_rel_thm
  ] = define_quotient_types_full {
  types =
    [{equiv = v_rel_EQUIV,
      name  = "vq"}
    ],
  defs = defs_Constructors @
         defs_Functions,
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
    eval_lift,
    progress_lemma,
    isClos_is_Closure,
    exp_rel_def
    ]
  };

Theorem progress_vq_def =
  progress_def
  |> Q.SPEC ‘empty_conf’
  |> REWRITE_RULE [
    exp_rel_thm];

Theorem progress_vq_thm =
  progress_vq_thm
  |> REWRITE_RULE [progress_vq_def];

val _ = export_theory ();
