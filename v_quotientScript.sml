
open bossLib boolLib;
open HolKernel pure_langTheory valueTheory quotient_llistTheory listTheory
     llistTheory quotient_ltreeTheory quotientLib;

val _ = new_theory "v_quotient";

(*
 * We won't be able to use `v_rel c` with `c` free as the relation
 * for our quotient type, so we make up a dummy value in place of c,
 * and define a new relation `vq_rel`.
 *)

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

Definition vq_eval_def:
  vq_eval = eval empty_conf
End

Definition vq_exp_rel_def:
  vq_exp_rel x y = exp_rel empty_conf x y
End

Theorem vq_exp_rel = vq_exp_rel_def;

(*
 * Adapt theorems about v_rel to vq_rel.
 *)

Theorem vq_rel_rules =
  v_rel_rules
  |> CONJUNCTS
  |> map (Q.SPEC ‘empty_conf’)
  |> LIST_CONJ
  |> REWRITE_RULE [
    GSYM vq_rel_def,
    GSYM vq_eval_def];

Theorem vq_rel_rules' =
  v_rel_rules'
  |> CONJUNCTS
  |> map (Q.SPEC ‘empty_conf’)
  |> LIST_CONJ
  |> REWRITE_RULE [
    GSYM vq_rel_def,
    GSYM vq_eval_def];

Theorem vq_rel_cases =
  v_rel_cases
  |> CONJUNCTS
  |> map (Q.SPEC ‘empty_conf’)
  |> LIST_CONJ
  |> REWRITE_RULE [
    GSYM vq_rel_def,
    GSYM vq_eval_def,
    GSYM vq_exp_rel_def];

Theorem vq_exp_rel_def:
  vq_exp_rel x y = vq_rel (vq_eval x) (vq_eval y)
Proof
  rw [vq_exp_rel_def, vq_rel_def, vq_eval_def, exp_rel_def]
QED

(*
 * Adapt theorems about eval to vq_eval.
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
  eval c (Case x nm css) = eval c (expandCases x nm css)
Proof
  gs [eval_thm, v_rel_cases, PURE_ONCE_REWRITE_RULE [v_rel_sym] v_rel_cases]
QED

Theorem vq_eval_thm =
  eval_thm
  |> Q.INST [‘c’|->‘empty_conf’]
  |> REWRITE_RULE [
    GSYM vq_rel_def,
    GSYM vq_eval_def];

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
  \\ rw [isClos_def, vq_rel_cases, vq_exp_rel_def]
  \\ Q.LIST_EXISTS_TAC [‘n’, ‘x’]
  \\ simp [vq_rel_refl]
QED

(*
 * Some constructor theorems about the v type. Anything vq_rel
 * (or higher-order equiv. rels. with vq_rel) will be lifted to
 * equality in the new type.
 *)

Theorem Atom_vq_11:
  vq_rel (Atom x) (Atom y) ⇔
    x = y
Proof
  rw [vq_rel_cases, EQ_SYM_EQ]
QED

Theorem Constructor_vq_11:
  vq_rel (Constructor n x) (Constructor m y) ⇔
    n = m ∧
    LIST_REL vq_rel x y
Proof
  rw [vq_rel_cases, EQ_SYM_EQ]
QED

Theorem Closure_vq_11:
  vq_rel (Closure n e1) (Closure m e2) ⇔
    ∀z. vq_rel (vq_eval (bind [(n, z)] e1)) (vq_eval (bind [(m, z)] e2))
Proof
  rw [vq_rel_cases, vq_exp_rel_def]
QED

(*
 * Respectfulness theorems for the lifting.
 *)

Theorem Constructor_rsp:
  x1 = y1 ∧
  LIST_REL vq_rel x2 y2 ⇒
    vq_rel (Constructor x1 x2) (Constructor y1 y2)
Proof
  rw [Constructor_vq_11]
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
  rw [is_eq_def]
  \\ fs [vq_rel_refl, vq_rel_cases]
  \\ rpt CASE_TAC \\ gs [vq_rel_cases, LIST_REL_EL_EQN]
QED

Theorem el_rsp:
  x1 = y1 ∧
  x2 = y2 ∧
  vq_rel x3 y3 ⇒
    vq_rel (el x1 x2 x3) (el y1 y2 y3)
Proof
  rw [el_def]
  \\ fs [vq_rel_cases]
  \\ rpt CASE_TAC \\ gs [vq_rel_cases, LIST_REL_EL_EQN]
QED

Theorem isClos_rsp:
  ∀x y. vq_rel x y ⇒ isClos x = isClos y
Proof
  Cases \\ Cases \\ simp [vq_rel_def, v_rel_cases, isClos_def]
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
     func     = “vq_eval”,
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
    vq_isClos_is_Closure,
    vq_exp_rel_thm
  ] = define_quotient_types_full {
  types =
    [{equiv = vq_rel_EQUIV,
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
    vq_eval_thm,
    vq_progress_lemma,
    isClos_is_Closure,
    vq_exp_rel_def
    ]
  };

Theorem progress_vq_def =
  progress_def
  |> Q.SPEC ‘empty_conf’
  |> REWRITE_RULE [
    GSYM vq_exp_rel,
    vq_exp_rel_thm];

Theorem progress_vq_thm =
  progress_vq_thm
  |> REWRITE_RULE [progress_vq_def];

val _ = export_theory ();

