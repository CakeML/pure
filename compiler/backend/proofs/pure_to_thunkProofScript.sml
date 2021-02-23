(*
  Proof of correctness for the pure_to_thunk compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLang_substTheory
     pure_evalTheory thunkLang_primitivesTheory;

val _ = new_theory "pure_to_thunkProof";

val _ = numLib.prefer_num ();

(* TODO: Move to pure_to_thunk

   Some variables point to computations that have been
   suspended by a lambda on the thunkLang side. These variables
   need to be forced, and are thus tagged with ‘Suspended’.
 *)

Datatype:
  vmode = Raw | Suspended
End

(*
  NOTES ON COMPILING PURELANG TO THUNKLANG:

  thunkLang_subst-pureLang simulation.

  As pureLang is lazy it allows non-functional value declarations that are
  mutually recursive, and lazy value declarations. All such computations are
  suspended behind a “Delay T (Closure «fresh_var»  «defn»)” thunkLang-side.
  We keep track of which variables are suspended and which are not using a
  context.

  * [Var]
    - ‘Suspended’ variables are forced thunkLang-side.
    - ‘Raw’ variables are evaluated as-is.
  * [Lam]
    - Lambdas are already lazy. The bound variable is treated as ‘Raw’.
  * [App]
    - The function argument is evaluated in the same way on both sides, but
      the function argument computation is suspended thunkLang-side by wrapping
      it in a “Delay T (Closure ...)”-thing (using a fresh variable).
  * [Prim]
    - ‘If’ receives special treatment because we need it to retain its laziness
      in thunkLang (Why isn't it possible to suspend the branches by wrapping
      them in ‘Delay’? Because the way the semantics is set up, a ‘Delay’
      produces a “Thunk” value that can only be dealt with by the semantics of
      ‘Force’. But if we wrap both branches with ‘Force’ then suspension is
      essentially a no-op).
    - ‘Cons’ arguments are suspended in application, as if it were a n-ary
      ‘App’.
    - ‘Force’ is applied to ‘Proj’ to put it in weak head normal form (this
      corresponds to the additional evaluate performed in the pureLang
      semantics).
    - The rest of the operations naturally produce results in weak head normal
      form, so we don't do anything special about these
  * [Letrec]
    - TODO

  Various TODO:
    - thunkLang subst or thunkLang freevars (I don't know which) makes a
      mistake with Letrecs
    - thunkLang subst should check whether the expression is closed and fail
      when pureLang subst fails
 *)

Inductive exp_rel:
[exp_rel_Var_Suspended:]
  (∀ctxt n.
     ALOOKUP ctxt n = SOME Suspended ⇒
       exp_rel ctxt (Var n) (Force (Var n))) ∧
[exp_rel_Var_Raw:]
  (∀ctxt n.
     ALOOKUP ctxt n = SOME Raw ⇒
       exp_rel ctxt (Var n) (Var n)) ∧
[exp_rel_Lam:]
  (∀ctxt s (x: pure_exp$exp) (x': thunkLang_subst$exp).
     exp_rel ((s, Raw)::ctxt) x x' ⇒
       exp_rel ctxt (Lam s x) (Lam s x')) ∧
[exp_rel_App:]
  (∀ctxt x x' y y' s.
     exp_rel ctxt x x' ∧
     exp_rel ctxt y y' ∧
     s ∉ freevars y ⇒
       exp_rel ctxt (App x y) (App x' (Delay F (Lam s y')))) ∧
[exp_rel_If:]
  (∀ctxt xs x y z.
     LENGTH xs = 3 ∧
     exp_rel ctxt (EL 0 xs) x ∧
     exp_rel ctxt (EL 1 xs) y ∧
     exp_rel ctxt (EL 2 xs) z ⇒
       exp_rel ctxt (Prim If xs) (If x y z)) ∧
[exp_rel_Cons:]
  (∀ctxt n m ss xs ys.
     LIST_REL (exp_rel ctxt) xs ys ∧
     LIST_REL (λs y. s ∉ freevars y) ss ys ∧
     n = m ⇒
       exp_rel ctxt (Prim (Cons n) xs)
                    (Prim (Cons m) (MAP2 (λs y. Delay F (Lam s y)) ss ys))) ∧
[exp_rel_Proj:]
  (∀ctxt s i xs ys.
     LIST_REL (exp_rel ctxt) xs ys ⇒
       exp_rel ctxt (Prim (Proj s i) xs) (Force (Prim (Proj s i) ys))) ∧
[exp_rel_Prim:]
  (∀ctxt op xs ys.
     op ≠ If ∧
     (∀n. op ≠ Cons n) ∧
     (∀s i. op ≠ Proj s i) ∧
     LIST_REL (exp_rel ctxt) xs ys ⇒
       exp_rel ctxt (Prim op xs) (Prim op ys)) ∧
[exp_rel_Letrec:]
  (∀ctxt f f' x x'.
     exp_rel ctxt (Letrec f x) (Letrec f' x'))
     (* FIXME This bit will involve more context-fiddling *)
End

Theorem exp_rel_def[local]:
  (∀n.
     exp_rel ctxt (Var n) y ⇔
       (ALOOKUP ctxt n = SOME Suspended ∧
        y = Force (Var n)) ∨
       (ALOOKUP ctxt n = SOME Raw ∧
        y = Var n)) ∧
  (∀s x.
     exp_rel ctxt (Lam s x) y ⇔
       ∃z. y = Lam s z ∧
           exp_rel ((s, Raw)::ctxt) x z) ∧
  (∀op xs.
     exp_rel ctxt (Prim op xs) y ⇔
       (∃x1 x2 x3.
          y = If x1 x2 x3 ∧
          op = If ∧
          LENGTH xs = 3 ∧
          exp_rel ctxt (EL 0 xs) x1 ∧
          exp_rel ctxt (EL 1 xs) x2 ∧
          exp_rel ctxt (EL 2 xs) x3) ∨
       (∃ss n ys.
          op = Cons n ∧
          y = Prim op (MAP2 (λs y. Delay F (Lam s y)) ss ys) ∧
          LIST_REL (exp_rel ctxt) xs ys ∧
          LIST_REL (λs y. s ∉ freevars y) ss ys) ∨
       (∃ss s i ys.
          op = Proj s i ∧
          y = Force (Prim op ys) ∧
          LIST_REL (exp_rel ctxt) xs ys) ∨
       (∃ss ys.
          op ≠ If ∧
          (∀n. op ≠ Cons n) ∧
          (∀s i. op ≠ Proj s i) ∧
          y = Prim op ys ∧
          LIST_REL (exp_rel ctxt) xs ys)) ∧
  (∀f x.
     exp_rel ctxt (App f x) y ⇔
       ∃g z s.
         y = App g (Delay F (Lam s z)) ∧
         s ∉ freevars x ∧
         exp_rel ctxt f g ∧
         exp_rel ctxt x z)
Proof
  rw []
  \\ simp [Once exp_rel_cases]
  \\ eq_tac
  \\ rw [] \\ gs []
  \\ irule_at Any EQ_REFL \\ fs []
QED

Inductive thunk_rel:
[thunk_rel_Suspended:]
  (∀ctxt x s y.
     s ∉ freevars y ∧
     exp_rel ctxt x y ⇒
       thunk_rel ctxt x (Thunk F (Closure s y))) ∧
[thunk_rel_Raw:]
  (∀ctxt x y v.
    exp_rel ctxt x y ∧
    eval_to 0 y = INR v ⇒
      thunk_rel ctxt x (Thunk T v))
End

Definition v_rel_def:
  v_rel ctxt wh_Error (INL Type_error) = T ∧
  v_rel ctxt wh_Diverge (INL Diverge) = T ∧
  v_rel ctxt (wh_Closure s x) (INR (Closure t y)) =
    (s = t ∧ exp_rel ((s, Raw)::ctxt) x y) ∧
  v_rel ctxt (wh_Constructor s xs) (INR (Constructor t ys)) =
    (s = t ∧ LIST_REL (thunk_rel ctxt) xs ys) ∧
  v_rel ctxt (wh_Atom a) (INR (Atom b)) = (a = b) ∧
  v_rel ctxt _ _ = F
End

Theorem v_rel_rev[local]:
  v_rel ctxt x (INL err) =
    ((x = wh_Error ∧ err = Type_error) ∨
     (x = wh_Diverge ∧ err = Diverge)) ∧
  v_rel ctxt x (INR (Closure s y)) =
    (∃b.
       x = wh_Closure s b ∧
       exp_rel ((s, Raw)::ctxt) b y) ∧
  v_rel ctxt x (INR (Constructor s ys)) =
    (∃xs.
       x = wh_Constructor s xs ∧
       LIST_REL (thunk_rel ctxt) xs ys) ∧
  v_rel ctxt x (INR (Atom l)) =
    (x = wh_Atom l)
Proof
  Cases_on ‘x’ \\ rw [v_rel_def, EQ_IMP_THM] \\ fs []
  \\ Cases_on ‘err’ \\ fs [v_rel_def]
QED

Theorem subst_fresh[local]:
  ∀m bod.
    EVERY (λ(v, x). v ∉ freevars bod) m ⇒
      subst m bod = bod
Proof
  ho_match_mp_tac subst_ind \\ rw []
  >- ((* Var *)
    fs [subst_def, EVERY_MEM, freevars_def, ELIM_UNCURRY]
    \\ CASE_TAC \\ fs []
    \\ drule_then assume_tac ALOOKUP_MEM
    \\ gs [FORALL_PROD])
  >- ((* Prim *)
    fs [subst_def, EVERY_MEM, freevars_def, ELIM_UNCURRY]
    \\ irule pure_miscTheory.MAP_ID_ON \\ rw []
    \\ first_x_assum irule
    \\ gs [DISJ_EQ_IMP, MEM_MAP]
    \\ CCONTR_TAC
    \\ qpat_x_assum ‘MEM _ _’ mp_tac \\ simp []
    \\ fs [ELIM_UNCURRY]
    \\ first_assum irule
    \\ first_assum (irule_at Any) \\ fs [])
  >- ((* If *)
    fs [subst_def, EVERY_MEM, freevars_def, ELIM_UNCURRY])
  >- ((* App *)
    fs [subst_def, EVERY_MEM, freevars_def, ELIM_UNCURRY])
  >- ((* Lam *)
    fs [subst_def, EVERY_MEM, freevars_def, ELIM_UNCURRY]
    \\ first_x_assum irule
    \\ rw [MEM_FILTER]
    \\ first_x_assum drule \\ fs [])
  >- ((* Letrec *)
    cheat (* TODO subst_def is broken *))
  >- ((* Delay *)
    fs [subst_def, freevars_def])
  >- ((* Force *)
    fs [subst_def, freevars_def])
  >- ((* Value *)
    fs [subst_def, freevars_def])
QED

Theorem subst1_fresh[local]:
  v ∉ freevars bod ⇒
    subst1 v x bod = bod
Proof
  strip_tac
  \\ irule_at Any subst_fresh \\ fs []
QED

Theorem bind1_fresh[local]:
  v ∉ freevars bod ⇒
  bind1 v x bod = bod
Proof
  strip_tac
  \\ simp [bind_def, subst1_fresh]
QED

(* TODO Not useful now but might become useful later *)
Theorem eval_to_Force_Delay_F:
  var ∉ freevars bod ⇒
  eval_to k (Force (Delay F (Lam var bod))) ≠ INL Diverge ⇒
    eval_to k (Force (Delay F (Lam var bod))) = eval_to (k - 1) bod
Proof
  rw [eval_to_def, dest_Thunk_def, dest_anyClosure_def,
      thunkLang_substTheory.dest_Closure_def, bind1_fresh]
QED

(* TODO Not useful now but might become useful later *)
Theorem eval_to_Force_Delay_T:
  eval_to k (Force (Delay T x)) = eval_to k x
Proof
  rw [eval_to_def]
  \\ Cases_on ‘eval_to k x’ \\ fs [dest_Thunk_def]
QED

Theorem eval_to_subst_mono_le[local]:
  ∀k x j. eval_to k x ≠ INL Diverge ∧ k ≤ j ⇒ eval_to j x = eval_to k x
Proof
  dsimp [arithmeticTheory.LESS_OR_EQ, eval_to_subst_mono]
QED

Theorem exp_rel_eval_to:
  ∀k x res y ctxt.
    eval_wh_to k x = res ∧
    exp_rel ctxt x y ⇒
      v_rel ctxt res (eval_to k y)
Proof
  ho_match_mp_tac eval_wh_to_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- ((* Var *)
    rw [eval_wh_to_def, eval_to_def]
    \\ fs [exp_rel_def, v_rel_def, eval_to_def])
  >- ((* Lam *)
    rw [eval_wh_to_def, exp_rel_def]
    \\ simp [eval_to_def, v_rel_def])
  >- ((* App *)
    strip_tac
    \\ rpt gen_tac
    \\ simp [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    >- ((* pure sem diverges *)
      rw [exp_rel_def]
      \\ simp [eval_to_def]
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to k g’ \\ fs [v_rel_def])
    \\ rw [exp_rel_def]
    \\ first_x_assum (drule_then assume_tac)
    \\ rw [eval_to_def]
    \\ Cases_on ‘eval_wh_to k x = wh_Error’ \\ fs []
    >- ((* pure sem errors *)
      simp [eval_to_def]
      \\ Cases_on ‘eval_to k g’ \\ fs [v_rel_def])
    \\ ‘∃res. eval_to k g = INR res’
      by (Cases_on ‘eval_to k g’ \\ fs []
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ fs [v_rel_rev])
    \\ simp []
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k x)’ \\ fs []
    >- ((* not a pureLang closure: thunk sem must also error *)
      Cases_on ‘eval_wh_to k x’ \\ Cases_on ‘res’ \\ gvs [v_rel_def]
      \\ simp [thunkLang_substTheory.dest_anyClosure_def,
               thunkLang_substTheory.dest_Closure_def,
               thunkLang_substTheory.dest_Recclosure_def,
               v_rel_def])
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ Cases_on ‘eval_wh_to k x’ \\ gvs [dest_wh_Closure_def]
    \\ Cases_on ‘res’ \\ gvs [dest_anyClosure_def,
                              thunkLang_substTheory.dest_Closure_def,
                              v_rel_def]
    \\ IF_CASES_TAC \\ fs [v_rel_def]
    \\ first_x_assum irule
    \\ simp [pure_expTheory.bind_def, FLOOKUP_UPDATE]
    \\ cheat
      (* TODO
           lemma about exp_rel and bound thunk stuff.
           we need for substitution to fail on both sides unless
           the expression (body) is closed.
       *))
  >- ((* Letrec *)
    cheat (* TODO Not done *))
  >- ((* Prim *)
    rename1 ‘Prim op xs’
    \\ rw [exp_rel_def]
    >- ((* If *)
      simp [eval_to_def, eval_wh_to_def]
      \\ IF_CASES_TAC \\ fs [v_rel_def]
      \\ gvs [LENGTH_EQ_NUM_compute]
      \\ fsrw_tac [boolSimps.DNF_ss] []
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ rename1 ‘exp_rel ctxt y1 x1’
      \\ CASE_TAC \\ Cases_on ‘eval_to (k - 1) x1’ \\ fs [v_rel_def]
      \\ rename1 ‘INR res’ \\ Cases_on ‘res’ \\ gvs [v_rel_def]
      \\ IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs [v_rel_def])
    >- ((* Cons *)
      simp [eval_wh_to_def, eval_to_def]
      \\ IF_CASES_TAC \\ fs [v_rel_def]
      \\ qmatch_goalsub_abbrev_tac ‘map f (MAP2 g _ _)’
      \\ ‘∃res. map f (MAP2 g ss ys) = INR res’
        by (Cases_on ‘map f (MAP2 g ss ys)’ \\ fs []
            \\ gvs [map_INL, Abbr ‘f’, Abbr ‘g’, EL_MAP2, eval_to_def])
      \\ simp [Abbr ‘f’, Abbr ‘g’, v_rel_def]
      \\ drule map_INR
      \\ gvs [LIST_REL_EL_EQN, EL_MAP2, eval_to_def]
      \\ disch_then (assume_tac o GSYM)
      \\ drule_then assume_tac map_LENGTH \\ gvs []
      \\ rw [thunk_rel_cases])
    >- ((* Proj *)
      simp [eval_wh_to_def, eval_to_def]
      \\ IF_CASES_TAC \\ fs [v_rel_def]
      \\ gvs [LIST_REL_EL_EQN, eval_to_def]
      \\ IF_CASES_TAC \\ fs [v_rel_def]
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel _ x y’
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) y’ \\ fs [v_rel_rev]
      \\ rename1 ‘dest_Constructor v’
      \\ Cases_on ‘dest_Constructor v’
      >- (
        Cases_on ‘eval_wh_to (k - 1) x’ \\ Cases_on ‘v’
        \\ gvs [v_rel_def, dest_Constructor_def])
      \\ Cases_on ‘v’ \\ gvs [dest_Constructor_def, v_rel_rev]
      \\ fs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gvs [v_rel_def]
      \\ first_x_assum (drule_then assume_tac)
      \\ fs [thunk_rel_cases, dest_Thunk_def, dest_anyClosure_def,
             thunkLang_substTheory.dest_Closure_def, bind1_fresh]
      \\ rename1 ‘eval_to 0 z’
      \\ ‘v_rel ctxt (eval_wh_to (k - 1) (EL i xs)) (eval_to 0 z)’
        suffices_by gs []
      \\ ‘0 ≤ k - 1’ by fs []
      \\ ‘eval_to 0 z ≠ INL Diverge’ by (strip_tac \\ fs [])
      \\ drule_all_then assume_tac eval_to_subst_mono_le
      \\ pop_assum (assume_tac o SYM) \\ gs [])
    >- ((* {IsEq, AtomOp, Lit} *)
      simp [eval_wh_to_def, eval_to_def]
      \\ IF_CASES_TAC \\ fs [v_rel_def]
      \\ gvs [LIST_REL_EL_EQN, eval_to_def]
      \\ Cases_on ‘op’ \\ fs [dest_Thunk_def]
      >- ((* IsEq *)
        IF_CASES_TAC \\ fs [v_rel_def]
        \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
        \\ rename1 ‘exp_rel _ x y’
        \\ first_x_assum (drule_then assume_tac)
        \\ Cases_on ‘eval_to (k - 1) y’ \\ fs [v_rel_rev]
        \\ rename1 ‘dest_Constructor v’
        \\ Cases_on ‘dest_Constructor v’ \\ fs []
        >- (
          Cases_on ‘eval_to (k - 1) y’ \\ Cases_on ‘eval_wh_to (k - 1) x’
          \\ Cases_on ‘v’ \\ gvs [dest_Constructor_def, v_rel_def])
        \\ pairarg_tac \\ gvs []
        \\ Cases_on ‘v’ \\ gvs [dest_Constructor_def, v_rel_rev]
        \\ drule_then assume_tac LIST_REL_LENGTH
        \\ IF_CASES_TAC \\ gvs [v_rel_def, dest_Thunk_def]
        \\ IF_CASES_TAC \\ gvs [v_rel_def, dest_Thunk_def])
      >- ((* AtomOp *)
        qmatch_goalsub_abbrev_tac ‘map f ys’
        \\ CASE_TAC \\ fs []
        >- (
          gvs [get_atoms_NONE_eq, EL_MAP]
          \\ Cases_on ‘map f ys’ \\ fs [Abbr ‘f’, v_rel_rev, v_rel_def]
          >- (
            gvs [map_INL]
            \\ rename1 ‘m < LENGTH ys’
            \\ Cases_on ‘m < n’ \\ gs []
            >- (
              first_x_assum (drule_then strip_assume_tac)
              \\ ‘exp_rel ctxt (EL m xs) (EL m ys) ∧ MEM (EL m xs) xs’
                by fs [EL_MEM]
              \\ last_x_assum (drule_all_then assume_tac)
              \\ gvs [AllCaseEqs (), v_rel_def])
            \\ Cases_on ‘n < m’ \\ gs []
            >- (
              first_x_assum drule
              \\ CASE_TAC \\ fs []
              \\ CASE_TAC \\ fs []
              \\ ‘exp_rel ctxt (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
                by fs [EL_MEM]
              \\ last_x_assum (drule_all_then assume_tac)
              \\ gvs [AllCaseEqs (), v_rel_def, v_rel_rev])
            \\ ‘m = n’ by fs []
            \\ pop_assum SUBST_ALL_TAC \\ gvs []
            \\ ‘exp_rel ctxt (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
              by fs [EL_MEM]
            \\ last_x_assum (drule_all_then assume_tac)
            \\ gvs [AllCaseEqs (), v_rel_def, v_rel_rev])
          \\ drule_then assume_tac map_LENGTH
          \\ dxrule_then drule_all map_INR \\ fs []
          \\ CASE_TAC \\ fs []
          \\ CASE_TAC \\ fs [] \\ rw []
          \\ ‘exp_rel ctxt (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
            by fs [EL_MEM]
          \\ last_x_assum (drule_all_then assume_tac)
          \\ gs [v_rel_def])
        \\ CASE_TAC \\ fs []
        >- (
          gvs [get_atoms_SOME_NONE_eq, EL_MAP]
          \\ Cases_on ‘map f ys’ \\ fs [Abbr ‘f’, v_rel_rev, v_rel_def]
          >- (
            gvs [map_INL]
            \\ rename1 ‘m < LENGTH ys’
            \\ Cases_on ‘m ≤ n’ \\ gs []
            >- (
              ‘exp_rel ctxt (EL m xs) (EL m ys) ∧ MEM (EL m xs) xs’
                by fs [EL_MEM]
              \\ last_x_assum (drule_all_then assume_tac)
              \\ gvs [AllCaseEqs (), v_rel_def, v_rel_rev])
            \\ fs [arithmeticTheory.NOT_LESS_EQUAL]
            \\ first_x_assum drule
            \\ CASE_TAC \\ fs []
            \\ CASE_TAC \\ fs []
            \\ ‘exp_rel ctxt (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
              by fs [EL_MEM]
            \\ last_x_assum (drule_all_then assume_tac) \\ gs [v_rel_rev])
          \\ drule_then assume_tac map_LENGTH
          \\ dxrule_then drule_all map_INR \\ fs []
          \\ CASE_TAC \\ fs []
          \\ CASE_TAC \\ fs [] \\ rw []
          \\ ‘exp_rel ctxt (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
            by fs [EL_MEM]
          \\ last_x_assum (drule_all_then assume_tac)
          \\ gs [v_rel_rev])
        \\ gvs [get_atoms_SOME_SOME_eq, LIST_REL_EL_EQN, EL_MAP]
        \\ Cases_on ‘map f ys’ \\ fs [Abbr ‘f’]
        >- (
          gvs [map_INL]
          \\ ‘exp_rel ctxt (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
            by fs [EL_MEM]
          \\ last_x_assum (drule_all_then assume_tac)
          \\ gs [v_rel_def, AllCaseEqs ()])
        \\ rename1 ‘LENGTH ys = LENGTH zs’
        \\ qsuff_tac ‘y = zs’
        >- (
          rw []
          \\ CASE_TAC \\ fs [v_rel_def])
        \\ drule_then assume_tac map_LENGTH
        \\ irule LIST_EQ \\ rw [] \\ gvs []
        \\ ‘x < LENGTH ys’ by fs []
        \\ dxrule_then drule map_INR \\ simp []
        \\ CASE_TAC \\ fs []
        \\ CASE_TAC \\ fs [] \\ rw []
        \\ ‘exp_rel ctxt (EL x xs) (EL x ys) ∧ MEM (EL x xs) xs’
          by fs [EL_MEM]
        \\ last_x_assum (drule_all_then assume_tac)
        \\ gvs [v_rel_rev])
      >- ((* Lit *)
        IF_CASES_TAC \\ fs [v_rel_def]
        \\ IF_CASES_TAC \\ fs [v_rel_def])))
QED

val _ = export_theory ();

