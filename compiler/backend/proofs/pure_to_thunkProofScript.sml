(*
  Proof of correctness for the pure_to_thunk compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLang_substTheory
     pure_evalTheory thunkLang_primitivesTheory
open pure_exp_lemmasTheory pure_miscTheory;

val _ = new_theory "pure_to_thunkProof";

val _ = numLib.prefer_num ();

(* TODO
   - All variables are suspended. Update notes.
   - Are they though?
 *)

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

Overload Suspend[local] = “λx. Force (Value (Thunk (INR x)))”;

Overload Raw[local] = “λv. Force (Value (Thunk (INL v)))”;

Overload Rec[local] = “λf n. Force (Value (Recclosure f n))”;

Overload Tick[local] = “λx. Letrec [] (x: pure_exp$exp)”;

Theorem eval_Tick[local]:
  k ≠ 0 ⇒ eval_wh_to k (Tick x) = eval_wh_to (k - 1) x
Proof
  rw [eval_wh_to_def]
  \\ simp [pure_expTheory.subst_funs_def, pure_expTheory.bind_def,
           flookup_fupdate_list, subst_ignore, FDOM_FUPDATE_LIST]
QED

Inductive exp_rel:
[exp_rel_Value_Rec:]
  (∀f g x y n.
     LIST_REL (\(fn, x) (gn, y). fn = gn ∧ closed x ∧ exp_rel x y) f g ∧
     ALOOKUP (REVERSE f) n = SOME x ∧
     ALOOKUP (REVERSE g) n = SOME y ⇒
       exp_rel (Letrec f x) (Rec (MAP (λ(gn, y). (gn, Delay y)) g) n)) ∧
[exp_rel_Value_Suspend:]
  (∀x y.
     exp_rel x y ∧
     closed x ⇒
       exp_rel (Tick x) (Suspend y)) ∧
[exp_rel_Var:]
  (∀n.
     exp_rel (Var n) (Force (Var n))) ∧
[exp_rel_Lam:]
  (∀s x y.
     exp_rel x y ⇒
       exp_rel (Lam s x) (Lam s y)) ∧
[exp_rel_App:]
  (∀f g x y.
     exp_rel f g ∧
     exp_rel x y ⇒
       exp_rel (App f (Tick x)) (App g (Delay y))) ∧
[exp_rel_If:]
  (∀x1 y1 z1 x2 y2 z2.
     LIST_REL exp_rel [x1; y1; z1] [x2; y2; z2] ⇒
       exp_rel (If x1 y1 z1) (If x2 y2 z2)) ∧
[exp_rel_Cons:]
  (∀n xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Cons n xs) (Prim (Cons n) (MAP Delay ys))) ∧
[exp_rel_Proj:]
  (∀s i xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim (Proj s i) xs) (Force (Prim (Proj s i) ys))) ∧
[exp_rel_Prim:]
  (∀op xs ys.
     op ≠ If ∧
     (∀n. op ≠ Cons n) ∧
     (∀s i. op ≠ Proj s i) ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim op xs) (Prim op ys)) ∧
[exp_rel_Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn, x) (gn, y). fn = gn ∧ closed x ∧ exp_rel x y) f g ∧
     exp_rel x y ⇒
       exp_rel (Letrec f x) (Letrec (MAP (λ(gn, x). (gn, Delay x)) g) y))
End

Definition thunk_rel_def:
  thunk_rel x v ⇔
    ∃y. v = Thunk (INR y) ∧
        exp_rel x y
End

Definition v_rel_def[simp]:
  v_rel wh_Error (INL Type_error) = T ∧
  v_rel wh_Diverge (INL Diverge) = T ∧
  v_rel (wh_Closure s x) (INR (Closure t y)) =
    (s = t ∧ exp_rel x y) ∧
  v_rel (wh_Constructor s xs) (INR (Constructor t ys)) =
    (s = t ∧ LIST_REL thunk_rel xs ys) ∧
  v_rel (wh_Atom a) (INR (Atom b)) = (a = b) ∧
  v_rel _ _ = F
End

Theorem v_rel_rev[local,simp]:
  v_rel x (INL err) =
    ((x = wh_Error ∧ err = Type_error) ∨
     (x = wh_Diverge ∧ err = Diverge)) ∧
  v_rel x (INR (Closure s y)) =
    (∃b.
       x = wh_Closure s b ∧
       exp_rel b y) ∧
  v_rel x (INR (Constructor s ys)) =
    (∃xs.
       x = wh_Constructor s xs ∧
       LIST_REL thunk_rel xs ys) ∧
  v_rel x (INR (Atom l)) =
    (x = wh_Atom l)
Proof
  Cases_on ‘x’ \\ rw [v_rel_def, EQ_IMP_THM] \\ fs []
  \\ Cases_on ‘err’ \\ fs [v_rel_def]
QED

(* TODO Move to thunkLang_subst *)
Theorem eval_to_subst_mono_le[local]:
  ∀k x j. eval_to k x ≠ INL Diverge ∧ k ≤ j ⇒ eval_to j x = eval_to k x
Proof
  dsimp [arithmeticTheory.LESS_OR_EQ, eval_to_subst_mono]
QED

Theorem MAP_EQ_EL[local]:
  ∀xs ys.
    MAP f xs = MAP g ys ⇒
      ∀n. n < LENGTH xs ⇒ f (EL n xs) = g (EL n ys)
Proof
  Induct \\ Cases_on ‘ys’ \\ simp [PULL_FORALL]
  \\ Cases_on ‘n’ \\ simp []
QED

Theorem exp_ind_alt[local]:
 ∀P.
   (∀n. P (Var n: pure_exp$exp)) ∧
   (∀v0 es. (∀a. MEM a es ⇒ P a) ⇒ P (Prim v0 es)) ∧
   (∀e1 e2. (∀e3. exp_size e3 ≤ exp_size e2 ⇒ P e3) ∧ P e1 ⇒ P (App e1 e2)) ∧
   (∀n e. P e ⇒ P (Lam n e)) ∧
   (∀lcs e. (∀fn e'. MEM (fn,e') lcs ⇒ P e') ∧ P e ⇒ P (Letrec lcs e)) ⇒
     ∀v. P v
Proof
  gen_tac
  \\ strip_tac
  \\ gen_tac
  \\ completeInduct_on ‘exp_size v’ \\ rw []
  \\ fs [PULL_FORALL]
  \\ Cases_on ‘v’ \\ fs []
  \\ last_x_assum irule \\ rw []
  \\ first_x_assum irule
  \\ fs [pure_expTheory.exp_size_def]
  \\ imp_res_tac pure_expTheory.exp_size_lemma \\ fs []
QED

Theorem exp_rel_subst:
  ∀x y a b n s.
    exp_rel x y ∧
    exp_rel a b ∧
    closed a ⇒
      exp_rel (subst n (Tick a) x)
              (subst1 n (Thunk (INR b)) y)
Proof
  ho_match_mp_tac exp_ind_alt \\ rw []
  >- ((* Var *)
    simp [subst_single_def]
    \\ ‘y = Force (Var n)’ by fs [Once exp_rel_cases]
    \\ IF_CASES_TAC \\ gvs [subst1_def, exp_rel_rules])
  >- ((* Prim *)
    rename1 ‘exp_rel (Prim op xs)’
    \\ qpat_x_assum ‘exp_rel (Prim op xs) _’ mp_tac
    \\ rw [Once exp_rel_cases]
    >- ((* If *)
      simp [subst_single_def, subst1_def]
      \\ rw [Once exp_rel_cases])
    >- ((* Cons *)
      simp [subst_single_def, subst1_def]
      \\ rw [Once exp_rel_cases]
      \\ qmatch_goalsub_abbrev_tac ‘MAP f (MAP g _)’
      \\ qexists_tac ‘MAP f ys’
      \\ unabbrev_all_tac
      \\ simp [EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, subst1_def]
      \\ fs [LIST_REL_EL_EQN] \\ rw []
      \\ first_x_assum irule \\ fs [MEM_EL]
      \\ irule_at Any EQ_REFL \\ fs [])
    >- ((* Proj *)
      simp [subst_single_def, subst1_def]
      \\ simp [Once exp_rel_cases, EVERY2_MAP]
      \\ gvs [LIST_REL_EL_EQN] \\ rw []
      \\ first_x_assum irule \\ fs [MEM_EL]
      \\ irule_at Any EQ_REFL \\ fs [])
    >- ((* Others *)
      simp [subst_single_def, subst1_def]
      \\ rw [Once exp_rel_cases, EVERY2_MAP]
      \\ gvs [LIST_REL_EL_EQN] \\ rw []
      \\ first_x_assum irule \\ fs [MEM_EL]
      \\ irule_at Any EQ_REFL \\ fs []))
  >- ((* App *)
    qpat_x_assum ‘exp_rel (App _ _) _’ mp_tac
    \\ rw [Once exp_rel_cases]
    \\ qmatch_asmsub_rename_tac ‘exp_rel f g’
    \\ qmatch_asmsub_rename_tac ‘exp_rel x y’
    \\ simp [subst_single_def, subst1_def]
    \\ irule exp_rel_App \\ fs []
    \\ first_x_assum irule
    \\ fs [pure_expTheory.exp_size_def])
  >- ((* Lam *)
    qpat_x_assum ‘exp_rel (Lam n x) _’ mp_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [subst_single_def, subst1_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ irule exp_rel_Lam \\ fs [])
  >- ((* Letrec *)
    qpat_x_assum ‘exp_rel (Letrec _ _) _’ mp_tac
    \\ rw [Once exp_rel_cases]
    >- ((* Rec *)
      fs [subst_single_def, subst1_def]
      \\ IF_CASES_TAC \\ fs []
      \\ irule exp_rel_Value_Rec \\ fs []
      \\ simp [GSYM MAP_REVERSE, ALOOKUP_MAP, EVERY2_MAP]
      \\ gvs [LIST_REL_EL_EQN] \\ rw []
      \\ rpt (pairarg_tac \\ gvs [])
      \\ first_x_assum (drule_then assume_tac) \\ gs [])
    >- ((* Suspend *)
      fs [subst_single_def, subst1_def]
      \\ irule exp_rel_Value_Suspend \\ fs [])
    \\ simp [subst_single_def, subst1_def]
    \\ ‘MAP FST g = MAP FST lcs’
      by (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘g’
          \\ Induct_on ‘lcs’ \\ Cases_on ‘g’ \\ simp [ELIM_UNCURRY])
    \\ simp [Once MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
             GSYM pure_miscTheory.FST_THM]
    \\ IF_CASES_TAC \\ fs [exp_rel_Letrec]
    \\ rw [subst1_def, Once exp_rel_cases]
    \\ qmatch_goalsub_abbrev_tac ‘MAP G (MAP H g)’
    \\ ‘MAP G (MAP H g) = MAP H (MAP G g)’
      by simp [Abbr ‘G’, Abbr ‘H’, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
               subst1_def]
    \\ first_assum (irule_at Any)
    \\ gvs [EVERY2_MAP, Abbr ‘G’, Abbr ‘H’, LIST_REL_EL_EQN] \\ rw []
    \\ rpt (pairarg_tac \\ gvs [])
    \\ first_x_assum (irule_at Any) \\ fs [MEM_EL]
    \\ first_assum (irule_at Any) \\ fs []
    \\ first_x_assum (drule_all_then assume_tac)
    \\ pairarg_tac \\ gvs [])
QED

Theorem exp_rel_freevars:
  ∀x y. exp_rel x y ⇒ freevars x = freevars y
Proof
  ho_match_mp_tac exp_rel_ind \\ rw []
  \\ fs [freevars_def, pure_expTheory.closed_def, DELETE_DEF,
         AC UNION_COMM UNION_ASSOC, MAP_MAP_o, combinTheory.o_DEF]
  >- (
    ‘freevars x = EMPTY’
      by (drule_then (qspec_then ‘REVERSE f’ mp_tac) ALOOKUP_SOME_EL_2
          \\ impl_tac
          >- (
            last_x_assum mp_tac
            \\ rpt (pop_assum kall_tac)
            \\ qid_spec_tac ‘g’
            \\ Induct_on ‘f’ \\ Cases_on ‘g’ \\ simp [ELIM_UNCURRY])
          \\ rw [] \\ gvs [EL_REVERSE, LIST_REL_EL_EQN]
          \\ qmatch_asmsub_abbrev_tac ‘EL m f’
          \\ ‘m < LENGTH g’ by fs [Abbr ‘m’]
          \\ first_x_assum (drule_then assume_tac) \\ gs [])
    \\ fs []
    \\ qsuff_tac ‘∀x. x ∈ set (MAP (λ(fn,e). freevars e) f) ⇒ x = EMPTY’
    >- (
      rw [EXTENSION]
      \\ fs [MEM_MAP, PULL_EXISTS]
      \\ rw [DISJ_EQ_IMP]
      \\ pairarg_tac \\ gvs [])
    \\ simp [MEM_MAP, MEM_EL]
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ rw [] \\ pairarg_tac \\ gvs []
    \\ gvs [LIST_REL_EL_EQN]
    \\ first_x_assum (drule_then assume_tac)
    \\ pairarg_tac \\ gvs []
    \\ pairarg_tac \\ gvs [])
  >- (
    pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ Induct_on ‘xs’ \\ Cases_on ‘ys’ \\ simp [] \\ rw []
    \\ res_tac \\ fs [])
  >- (
    pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ Induct_on ‘xs’ \\ Cases_on ‘ys’ \\ simp [] \\ rw []
    \\ res_tac \\ fs [])
  >- (
    pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ Induct_on ‘xs’ \\ Cases_on ‘ys’ \\ simp [] \\ rw []
    \\ res_tac \\ fs [])
  >- (
    ‘MAP FST f = MAP FST g’
      by (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘g’
          \\ Induct_on ‘f’ \\ Cases_on ‘g’ \\ simp [ELIM_UNCURRY])
    \\ fs []
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, freevars_def,
             GSYM pure_miscTheory.FST_THM]
    \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
    \\ last_x_assum mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ qid_spec_tac ‘g’
    \\ Induct_on ‘f’ \\ Cases_on ‘g’ \\ fs [ELIM_UNCURRY])
QED

Theorem exp_rel_closed:
  exp_rel x y ⇒ closed x = closed y
Proof
  metis_tac [closed_def, pure_expTheory.closed_def, exp_rel_freevars,
             pure_miscTheory.NIL_iff_NOT_MEM]
QED

Theorem closed_Delay[local,simp]:
  closed (Delay x) = closed x
Proof
  rw [closed_def, freevars_def]
QED

Theorem FDIFF_EMPTY[simp]:
  ∀m. FDIFF m EMPTY = m
Proof
  Induct \\ rw [FDIFF_def]
QED

(* TODO:
   - Maybe, with some fixes.
 *)

Theorem exp_rel_subst_funs[local]:
  ∀x f g y.
    LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ closed x ∧ exp_rel x y) f g ∧
    exp_rel x y ⇒
      exp_rel (subst_funs f x) (subst_funs (MAP (λ(gn, x). (gn, Delay x)) g) y)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ simp [subst_funs_def, bind_def, pure_expTheory.subst_funs_def,
           pure_expTheory.bind_def]
  \\ reverse IF_CASES_TAC \\ fs []
  >- ((* FIXME blergh: *)
    ‘F’ suffices_by rw []
    \\ pop_assum mp_tac \\ simp []
    \\ fs [flookup_fupdate_list]
    \\ ‘LIST_REL exp_rel (MAP SND f) (MAP SND g) ∧ MAP FST f = MAP FST g’
      by (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘g’
          \\ Induct_on ‘f’ \\ Cases_on ‘g’ \\ fs [ELIM_UNCURRY])
    \\ drule_then (qspec_then ‘n’ assume_tac) LIST_REL_imp_OPTREL_ALOOKUP
    \\ gs [CaseEq "option", OPTREL_def]
    \\ imp_res_tac ALOOKUP_SOME
    \\ fs [MAP_REVERSE, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
           GSYM FST_THM, ALOOKUP_NONE]
    \\ imp_res_tac ALOOKUP_MEM \\ fs [MEM_REVERSE, MEM_MAP]
    \\ pairarg_tac \\ gvs []
    \\ pop_assum mp_tac
    \\ simp [MEM_EL, Once EQ_SYM_EQ]
    \\ strip_tac \\ gvs []
    \\ gvs [LIST_REL_EL_EQN]
    \\ ‘freevars (SND (EL n f)) = EMPTY’
      by fs [pure_expTheory.closed_def, ELIM_UNCURRY]
    \\ gvs []
    \\ ‘EVERY (λe. freevars e ⊆ set (MAP FST f)) (MAP SND f)’ suffices_by rw []
    \\ rw [EVERY_EL]
    \\ last_x_assum drule
    \\ simp [EL_MAP, pure_expTheory.closed_def, ELIM_UNCURRY])
  \\ pop_assum kall_tac
  \\ rpt (pop_assum mp_tac)
  \\ map_every qid_spec_tac [‘g’, ‘f’, ‘y’, ‘x’]
  \\ ho_match_mp_tac exp_ind_alt \\ rw []
  >- ((* Var *)
    ‘y = Force (Var n)’ by fs [Once exp_rel_cases]
    \\ simp [pure_expTheory.subst_def, flookup_fupdate_list, subst_def,
             MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
    \\ qmatch_goalsub_abbrev_tac ‘ALOOKUP (REVERSE (MAP f1 f))’
    \\ qmatch_goalsub_abbrev_tac ‘ALOOKUP (REVERSE (MAP g1 g))’
    \\ ‘MAP FST (MAP f1 f) = MAP FST (MAP g1 g)’
      by (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
          \\ unabbrev_all_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘g’
          \\ Induct_on ‘f’ \\ Cases_on ‘g’ \\ fs []
          \\ fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FORALL_PROD,
                 GSYM FST_THM]
          \\ fs [ELIM_UNCURRY])
    \\ ‘ALOOKUP (REVERSE (MAP f1 f)) n = NONE ⇔
        ALOOKUP (REVERSE (MAP g1 g)) n = NONE’
      by rw [Abbr ‘f1’, Abbr ‘g1’, ALOOKUP_NONE, MAP_REVERSE]
    \\ CASE_TAC \\ fs []
    \\ CASE_TAC \\ fs []
    \\ unabbrev_all_tac
    \\ qmatch_asmsub_abbrev_tac ‘ALOOKUP (REVERSE f1) n = SOME x’
    \\ drule_then (qspec_then ‘REVERSE f1’ mp_tac) ALOOKUP_SOME_EL_2
    \\ rw [Abbr ‘f1’, MAP_REVERSE]
    \\ gvs [EL_REVERSE, EL_MAP, LIST_REL_EL_EQN]
    \\ pairarg_tac \\ gvs []
    \\ pairarg_tac \\ gvs []
    \\ qmatch_asmsub_abbrev_tac ‘EL m f’
    \\ rename1 ‘EL m f = (fn, x)’
    \\ rename1 ‘EL m g = (fn, y)’
    \\ ‘m < LENGTH g’ by fs [Abbr ‘m’]
    \\ ‘closed x ∧ exp_rel x y’
      by (first_x_assum (drule_then assume_tac)
          \\ pairarg_tac \\ gvs [])
    \\ gvs []
    \\ irule exp_rel_Value_Rec
    \\ simp [GSYM MAP_REVERSE, ALOOKUP_MAP]
    \\ ‘MAP FST (REVERSE f) = MAP FST (REVERSE g)’
      by (last_x_assum mp_tac
          \\ qpat_x_assum ‘LENGTH f = _’ mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘g’
          \\ Induct_on ‘f’ \\ Cases_on ‘g’ \\ simp []
          \\ rw []
          >- (
            first_x_assum drule
            \\ impl_tac \\ fs []
            \\ rw []
            \\ pairarg_tac \\ gvs []
            \\ pairarg_tac \\ gvs []
            \\ first_x_assum (qspec_then ‘SUC n’ assume_tac) \\ gs [])
          \\ first_x_assum (qspec_then ‘0’ assume_tac)
          \\ pairarg_tac \\ gvs []
          \\ pairarg_tac \\ gvs [])
    \\ conj_asm1_tac
    >- (
      fs [GSYM MAP_REVERSE, ALOOKUP_MAP])
    \\ conj_tac
    >- (
      CCONTR_TAC \\ fs []
      \\ Cases_on ‘ALOOKUP (REVERSE g) fn’ \\ gs []
      \\ imp_res_tac ALOOKUP_SOME
      \\ gs [MAP_REVERSE, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
             GSYM FST_THM, ALOOKUP_NONE])
    \\ fs [LIST_REL_EL_EQN])
  >- ((* Prim *)
    pop_assum mp_tac
    \\ rw [Once exp_rel_cases]
    \\ rw [subst_def, pure_expTheory.subst_def]
    >- simp [exp_rel_If]
    >- ((* Cons *)
      qmatch_goalsub_abbrev_tac ‘MAP f1 (MAP f2 ys)’
      \\ ‘MAP f1 (MAP f2 ys) = MAP f2 (MAP f1 ys)’
        by (unabbrev_all_tac
            \\ rw [MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, subst_def])
      \\ pop_assum SUBST1_TAC
      \\ unabbrev_all_tac
      \\ irule exp_rel_Cons
      \\ fs [EVERY2_MAP, LIST_REL_EL_EQN]
      \\ rw [] \\ gvs [EL_MEM])
    >- ((* Proj *)
      irule exp_rel_Proj
      \\ fs [EVERY2_MAP, LIST_REL_EL_EQN]
      \\ rw [] \\ gvs [EL_MEM])
    \\ irule exp_rel_Prim
    \\ fs [EVERY2_MAP, LIST_REL_EL_EQN]
    \\ rw [] \\ gvs [EL_MEM])
  >- ((* App *)
    pop_assum mp_tac
    \\ rw [Once exp_rel_cases]
    \\ rw [subst_def, pure_expTheory.subst_def]
    \\ irule exp_rel_App \\ fs []
    \\ first_x_assum irule
    \\ fs [pure_expTheory.exp_size_def])
  >- ((* Lam *)
    pop_assum mp_tac
    \\ rw [Once exp_rel_cases]
    \\ rw [subst_def, pure_expTheory.subst_def]
    \\ irule exp_rel_Lam
    \\ cheat (* something about fdomsub and FILTER *))
  >- ((* Letrec *)
    pop_assum mp_tac
    \\ rw [Once exp_rel_cases]
    \\ rw [subst_def, pure_expTheory.subst_def, exp_rel_Value_Suspend]
    >- ((* Rec *)
      irule exp_rel_Value_Rec \\ fs []
      \\ simp [GSYM MAP_REVERSE, ALOOKUP_MAP]
      \\ fs [EVERY2_MAP, LAMBDA_PROD, LIST_REL_EL_EQN] \\ rw []
      \\ rpt (pairarg_tac \\ gvs [])
      \\ rename1 ‘EL m lcs’
      \\ ‘MEM (EL m lcs) lcs’ by fs [EL_MEM]
      \\ first_x_assum (drule_all_then assume_tac) \\ gs [])
    \\ qmatch_goalsub_abbrev_tac
      ‘exp_rel (Letrec ff xx) (Letrec (MAP f1 (MAP f2 gg)) yy)’
    \\ ‘MAP f1 (MAP f2 gg) = MAP f2 (MAP f1 gg)’
      by (unabbrev_all_tac
          \\ simp [MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, LAMBDA_PROD,
                   FORALL_PROD, subst_def])
    \\ pop_assum SUBST1_TAC
    \\ unabbrev_all_tac
    \\ irule exp_rel_Letrec \\ fs []
    \\ cheat (* TODO maybe *))
QED

Theorem exp_rel_eval_to:
  ∀k x res y.
    eval_wh_to k x = res ∧
    exp_rel x y ⇒
      v_rel res (eval_to k y)
Proof
  ho_match_mp_tac eval_wh_to_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- ((* Var *)
    rw [eval_wh_to_def]
    \\ fs [Once exp_rel_cases, eval_to_def])
  >- ((* Lam *)
    rw [eval_wh_to_def, Once exp_rel_cases]
    \\ simp [eval_to_def])
  >- ((* App *)
    strip_tac
    \\ rpt gen_tac
    \\ simp [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    >- ((* pure sem diverges *)
      rw [Once exp_rel_cases]
      \\ fs [eval_wh_to_def]
      \\ simp [eval_to_def]
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to k g’ \\ fs [])
    \\ rw [Once exp_rel_cases]
    \\ first_x_assum (drule_then assume_tac)
    \\ simp [eval_to_def]
    \\ Cases_on ‘eval_wh_to k x = wh_Error’ \\ fs []
    >- ((* pure sem errors *)
      Cases_on ‘eval_to k g’ \\ fs [])
    \\ ‘∃res. eval_to k g = INR res’
      by (Cases_on ‘eval_to k g’ \\ fs [v_rel_rev])
    \\ simp []
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k x)’ \\ fs []
    >- ((* not a pureLang closure: thunk sem must also error *)
      Cases_on ‘eval_wh_to k x’ \\ Cases_on ‘res’ \\ gvs [dest_anyClosure_def])
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ Cases_on ‘eval_wh_to k x’ \\ gvs [dest_wh_Closure_def]
    \\ Cases_on ‘res’ \\ gvs [dest_anyClosure_def]
    \\ IF_CASES_TAC \\ fs []
    \\ rename1 ‘Tick z1’
    \\ rename1 ‘exp_rel z1 z2’
    \\ imp_res_tac exp_rel_closed \\ gvs []
    \\ fs [pure_expTheory.bind_def, FLOOKUP_UPDATE, bind_def, closed_def,
           pure_expTheory.closed_def]
    \\ ‘∀k. eval_wh_to k Fail = wh_Error’ by cheat (* TODO Fix in pure_eval *)
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum irule
    \\ irule exp_rel_subst
    \\ fs [pure_expTheory.closed_def])
  >- ((* Letrec *)
    rw []
    \\ pop_assum mp_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_wh_to_def, eval_to_def]
    >- ((* Rec *)
      imp_res_tac ALOOKUP_SOME \\ fs [dest_anyThunk_def]
      \\ simp [GSYM MAP_REVERSE, ALOOKUP_MAP]
      \\ IF_CASES_TAC \\ fs []
      \\ first_x_assum irule
      \\ irule exp_rel_subst_funs \\ fs []
      \\ drule_then (qspec_then ‘REVERSE f’ mp_tac) ALOOKUP_SOME_EL_2
      \\ impl_tac
      >- (
        last_x_assum mp_tac
        \\ rpt (pop_assum kall_tac)
        \\ qid_spec_tac ‘g’
        \\ Induct_on ‘f’ \\ Cases_on ‘g’ \\ simp [ELIM_UNCURRY])
      \\ rw [] \\ gvs [LIST_REL_EL_EQN, EL_REVERSE]
      \\ qmatch_asmsub_abbrev_tac ‘EL m f’
      \\ ‘m < LENGTH g’ by gvs [Abbr ‘m’]
      \\ first_x_assum (drule_then assume_tac) \\ gs [])
    >- ((* Tick *)
      IF_CASES_TAC \\ fs [dest_anyThunk_def]
      \\ first_x_assum irule
      \\ fs [pure_expTheory.subst_funs_def, pure_expTheory.bind_def,
             flookup_fupdate_list, FDOM_FUPDATE_LIST, subst_ignore,
             subst_funs_def, bind_def])
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum irule
    \\ irule exp_rel_subst_funs \\ fs [])
  >- ((* Prim *)
    rename1 ‘Prim op xs’
    \\ rw []
    \\ pop_assum mp_tac
    \\ rw [Once exp_rel_cases]
    >- ((* If *)
      simp [eval_to_def, eval_wh_to_def]
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LENGTH_EQ_NUM_compute]
      \\ fsrw_tac [boolSimps.DNF_ss] []
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ CASE_TAC \\ Cases_on ‘eval_to (k - 1) x2’ \\ fs []
      \\ rename1 ‘INR res’ \\ Cases_on ‘res’ \\ gvs []
      \\ IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs [])
    >- ((* Cons *)
      simp [eval_wh_to_def, eval_to_def]
      \\ IF_CASES_TAC \\ fs []
      \\ qmatch_goalsub_abbrev_tac ‘map f _’
      \\ ‘∃res. map f (MAP Delay ys) = INR res’
        by (Cases_on ‘map f (MAP Delay ys)’ \\ fs []
            \\ gvs [map_INL, Abbr ‘f’, EL_MAP, eval_to_def])
      \\ simp [Abbr ‘f’]
      \\ drule map_INR
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, eval_to_def]
      \\ disch_then (assume_tac o GSYM)
      \\ drule_then assume_tac map_LENGTH \\ gvs []
      \\ rw [thunk_rel_def])
    >- ((* Proj *)
      simp [eval_wh_to_def, eval_to_def]
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LIST_REL_EL_EQN, eval_to_def]
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) y’ \\ fs [v_rel_rev]
      \\ rename1 ‘dest_Constructor v’
      \\ Cases_on ‘dest_Constructor v’
      >- (
        Cases_on ‘eval_wh_to (k - 1) x’ \\ Cases_on ‘v’ \\ gvs [])
      \\ Cases_on ‘v’ \\ gvs [v_rel_rev]
      \\ fs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gvs []
      \\ first_x_assum (drule_then assume_tac)
      \\ fs [thunk_rel_def, dest_anyThunk_def, subst_funs_def, bind_def])
    >- ((* {IsEq, AtomOp, Lit} *)
      simp [eval_wh_to_def, eval_to_def]
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LIST_REL_EL_EQN, eval_to_def]
      \\ Cases_on ‘op’ \\ fs []
      >- ((* IsEq *)
        IF_CASES_TAC \\ fs []
        \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
        \\ rename1 ‘exp_rel x y’
        \\ first_x_assum (drule_then assume_tac)
        \\ Cases_on ‘eval_to (k - 1) y’ \\ fs [v_rel_rev]
        \\ rename1 ‘dest_Constructor v’
        \\ Cases_on ‘dest_Constructor v’ \\ fs []
        >- (
          Cases_on ‘eval_to (k - 1) y’ \\ Cases_on ‘eval_wh_to (k - 1) x’
          \\ Cases_on ‘v’ \\ gvs [])
        \\ pairarg_tac \\ gvs []
        \\ Cases_on ‘v’ \\ gvs [v_rel_rev]
        \\ drule_then assume_tac LIST_REL_LENGTH
        \\ IF_CASES_TAC \\ gvs []
        \\ IF_CASES_TAC \\ gvs [])
      >- ((* AtomOp *)
        qmatch_goalsub_abbrev_tac ‘map f ys’
        \\ CASE_TAC \\ fs []
        >- (
          gvs [get_atoms_NONE_eq, EL_MAP]
          \\ Cases_on ‘map f ys’ \\ fs [Abbr ‘f’, v_rel_rev]
          >- (
            gvs [map_INL]
            \\ rename1 ‘m < LENGTH ys’
            \\ Cases_on ‘m < n’ \\ gs []
            >- (
              first_x_assum (drule_then strip_assume_tac)
              \\ ‘exp_rel (EL m xs) (EL m ys) ∧ MEM (EL m xs) xs’
                by fs [EL_MEM]
              \\ last_x_assum (drule_all_then assume_tac)
              \\ gvs [AllCaseEqs ()])
            \\ Cases_on ‘n < m’ \\ gs []
            >- (
              first_x_assum drule
              \\ CASE_TAC \\ fs []
              \\ CASE_TAC \\ fs []
              \\ ‘exp_rel (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
                by fs [EL_MEM]
              \\ last_x_assum (drule_all_then assume_tac)
              \\ gvs [AllCaseEqs (), v_rel_rev])
            \\ ‘m = n’ by fs []
            \\ pop_assum SUBST_ALL_TAC \\ gvs []
            \\ ‘exp_rel (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
              by fs [EL_MEM]
            \\ last_x_assum (drule_all_then assume_tac)
            \\ gvs [AllCaseEqs (), v_rel_rev])
          \\ drule_then assume_tac map_LENGTH
          \\ dxrule_then drule_all map_INR \\ fs []
          \\ CASE_TAC \\ fs []
          \\ CASE_TAC \\ fs [] \\ rw []
          \\ ‘exp_rel (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
            by fs [EL_MEM]
          \\ last_x_assum (drule_all_then assume_tac)
          \\ gs [])
        \\ CASE_TAC \\ fs []
        >- (
          gvs [get_atoms_SOME_NONE_eq, EL_MAP]
          \\ Cases_on ‘map f ys’ \\ fs [Abbr ‘f’, v_rel_rev]
          >- (
            gvs [map_INL]
            \\ rename1 ‘m < LENGTH ys’
            \\ Cases_on ‘m ≤ n’ \\ gs []
            >- (
              ‘exp_rel (EL m xs) (EL m ys) ∧ MEM (EL m xs) xs’
                by fs [EL_MEM]
              \\ last_x_assum (drule_all_then assume_tac)
              \\ gvs [AllCaseEqs (), v_rel_rev])
            \\ fs [arithmeticTheory.NOT_LESS_EQUAL]
            \\ first_x_assum drule
            \\ CASE_TAC \\ fs []
            \\ CASE_TAC \\ fs []
            \\ ‘exp_rel (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
              by fs [EL_MEM]
            \\ last_x_assum (drule_all_then assume_tac) \\ gs [v_rel_rev])
          \\ drule_then assume_tac map_LENGTH
          \\ dxrule_then drule_all map_INR \\ fs []
          \\ CASE_TAC \\ fs []
          \\ CASE_TAC \\ fs [] \\ rw []
          \\ ‘exp_rel (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
            by fs [EL_MEM]
          \\ last_x_assum (drule_all_then assume_tac)
          \\ gs [v_rel_rev])
        \\ gvs [get_atoms_SOME_SOME_eq, LIST_REL_EL_EQN, EL_MAP]
        \\ Cases_on ‘map f ys’ \\ fs [Abbr ‘f’]
        >- (
          gvs [map_INL]
          \\ ‘exp_rel (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
            by fs [EL_MEM]
          \\ last_x_assum (drule_all_then assume_tac)
          \\ gs [AllCaseEqs ()])
        \\ rename1 ‘LENGTH ys = LENGTH zs’
        \\ qsuff_tac ‘y = zs’
        >- (
          rw []
          \\ CASE_TAC \\ fs [])
        \\ drule_then assume_tac map_LENGTH
        \\ irule LIST_EQ \\ rw [] \\ gvs []
        \\ ‘x < LENGTH ys’ by fs []
        \\ dxrule_then drule map_INR \\ simp []
        \\ CASE_TAC \\ fs []
        \\ CASE_TAC \\ fs [] \\ rw []
        \\ ‘exp_rel (EL x xs) (EL x ys) ∧ MEM (EL x xs) xs’
          by fs [EL_MEM]
        \\ last_x_assum (drule_all_then assume_tac)
        \\ gvs [])
      >- ((* Lit *)
        IF_CASES_TAC \\ fs []
        \\ IF_CASES_TAC \\ fs [])))
QED

val _ = export_theory ();

