(*
  Proof of correctness for the pure_to_thunk compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax dep_rewrite
     intLib;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     pure_semanticsTheory thunk_semanticsTheory pure_evalTheory
     thunkLang_primitivesTheory pure_exp_lemmasTheory pure_miscTheory;

val _ = new_theory "pure_to_thunkProof";

val _ = set_grammar_ancestry ["finite_map", "pred_set", "rich_list",
                              "pure_semantics", "thunk_semantics",
                              "pure_exp_lemmas", "pure_misc"];

val _ = numLib.prefer_num ();

(*
  NOTES ON COMPILING PURELANG TO THUNKLANG:

  thunkLang-pureLang simulation.

  As pureLang is lazy it allows non-functional value declarations that are
  mutually recursive, and lazy value declarations. All such computations are
  suspended thunkLang-side by Lam, Box or Delay. This relation (exp_rel) acts as
  if the compiler inserted Delay everywhere, but the compiler can insert Box
  for things that do not require a thunk to be allocated, such as a lambda.

  * [Var]
    - All variables are wrapped in ‘Force’ as if they were suspended either by
      a Thunk or a Recclosure.
  * [Lam]
    - Lambdas are already lazy.
  * [App]
    - The function expression is evaluated in the same way on both sides, but
      the computation of the argument to the function computation is suspended
      thunkLang-side by wrapping it in a Delay expression.
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
    - The remainder of the operations already produce results in weak head
      normal form, so we don't do anything special to them.
    - The first argument to ‘Seq’ is forced.
  * [Letrec]
    - We expect all expressions in the list of bindings to be suspended by
      something (either Lam or Delay or Box), so we insert Delay everywhere.
 *)

Overload Suspend[local] = “λx. Force (Value (Thunk (INR x)))”;

Overload Rec[local] = “λf n. Force (Value (Recclosure f n))”;

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
     exp_rel (pure_exp$Var n) (Force (Var n))) ∧
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
[exp_rel_Seq:]
  (∀x1 x2 y1 y2.
     LIST_REL exp_rel [x1; y1] [x2; y2] ∧
     closed x1 ⇒
       exp_rel (Seq x1 y1) (Let NONE x2 y2)) ∧
[exp_rel_Prim:]
  (∀op xs ys.
     op ≠ If ∧
     op ≠ Seq ∧
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
        exp_rel x y ∧
        closed x
End

Definition v_rel_def[simp]:
  v_rel wh_Error (INL Type_error) = T ∧
  v_rel wh_Diverge (INL Diverge) = T ∧
  v_rel (wh_Closure s x) (INR (Closure t y)) =
    (s = t ∧ exp_rel x y ∧ freevars x ⊆ {s}) ∧
  v_rel (wh_Constructor s xs) (INR (Constructor t ys)) =
    (s = t ∧ LIST_REL thunk_rel xs ys ∧ EVERY closed xs) ∧
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
       freevars b ⊆ {s} ∧
       exp_rel b y) ∧
  v_rel x (INR (Constructor s ys)) =
    (∃xs.
       x = wh_Constructor s xs ∧
       EVERY closed xs ∧
       LIST_REL thunk_rel xs ys) ∧
  v_rel x (INR (Atom l)) =
    (x = wh_Atom l)
Proof
  Cases_on ‘x’ \\ rw [v_rel_def, EQ_IMP_THM] \\ fs []
  \\ Cases_on ‘err’ \\ fs [v_rel_def]
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

Theorem exp_rel_freevars:
  ∀x y. exp_rel x y ⇒ freevars x = freevars y
Proof
  ho_match_mp_tac exp_rel_ind \\ rw []
  \\ fs [freevars_def, pure_expTheory.closed_def, DELETE_DEF,
         AC UNION_COMM UNION_ASSOC, MAP_MAP_o, combinTheory.o_DEF]
  >- (
    ‘freevars x = EMPTY’
      by (imp_res_tac ALOOKUP_SOME_EL
          \\ gvs [LIST_REL_EL_EQN, EL_REVERSE, ELIM_UNCURRY]
          \\ qmatch_asmsub_abbrev_tac ‘EL m f’
          \\ ‘m < LENGTH g’ by gvs [Abbr ‘m’]
          \\ first_x_assum (drule_then assume_tac) \\ gs [])
    \\ fs []
    \\ qsuff_tac ‘∀x. x ∈ set (MAP (λ(f,x). freevars x) f) ⇒ x = EMPTY’
    >- (
      rw [EXTENSION] \\ fs [MEM_MAP]
      \\ rw [DISJ_EQ_IMP] \\ fs []
      \\ pairarg_tac \\ gvs []
      \\ res_tac \\ gvs [FORALL_PROD])
    \\ rw [EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP]
    \\ gvs [MEM_EL, LIST_REL_EL_EQN, EL_MAP]
    \\ first_x_assum (drule_then assume_tac)
    \\ rpt (pairarg_tac \\ gvs []))
  >- (
    AP_TERM_TAC \\ AP_TERM_TAC
    \\ irule LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP])
  >- (
    AP_TERM_TAC \\ AP_TERM_TAC
    \\ irule LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP])
  >- (
    AP_TERM_TAC \\ AP_TERM_TAC
    \\ irule LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP])
  >- (
    gvs [LIST_REL_CONJ, ELIM_UNCURRY, SF ETA_ss]
    \\ ‘MAP FST f = MAP FST g’
      by (irule LIST_EQ
          \\ gs [LIST_REL_EL_EQN, EL_MAP])
    \\ gvs [freevars_def]
    \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
    \\ irule LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP])
QED

Theorem exp_rel_closed:
  exp_rel x y ⇒ closed x = closed y
Proof
  rw [closed_def, pure_expTheory.closed_def]
  \\ drule exp_rel_freevars \\ simp []
QED

Theorem subst_single_def[local] = pure_exp_lemmasTheory.subst1_def;
Theorem subst1_def[local] = thunkLangTheory.subst1_def;

Theorem exp_rel_subst:
  ∀x y a b n s.
    exp_rel x y ∧
    exp_rel a b ∧
    closed a ⇒
      exp_rel (subst1 n (Tick a) x)
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
    >- ((* Seq *)
      simp [subst_single_def, subst1_def]
      \\ irule exp_rel_Seq \\ fs []
      \\ fs [SF DNF_ss]
      \\ last_x_assum (irule_at Any) \\ fs []
      \\ last_assum (irule_at Any) \\ fs [])
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

Theorem closed_Delay[local,simp]:
  closed (Delay x) = closed x
Proof
  rw [closed_def, freevars_def]
QED

(* TODO Move to pure_misc? *)
Theorem FDIFF_EMPTY[simp]:
  ∀m. FDIFF m EMPTY = m
Proof
  Induct \\ rw [FDIFF_def]
QED

Theorem exp_rel_subst_list[local]:
  ∀x f g y ks.
    LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ closed x ∧ exp_rel x y) f g ∧
    exp_rel x y ⇒
      exp_rel
        (subst
           (FEMPTY |++
            MAP (λ(g,x). (g,Letrec f x))
              (FILTER (λ(n,x). n ∉ ks) f)) x)
        (subst
           (MAP
              (λ(gn,x).(gn, Recclosure (MAP (λ(gn,x). (gn,Delay x)) g) gn))
              (FILTER (λ(n,x). n ∉ ks) (MAP (λ(gn,x). (gn,Delay x)) g))) y)
Proof
  ho_match_mp_tac exp_ind_alt \\ rw []
  >- ((* Var *)
    ‘y = Force (Var n)’ by fs [Once exp_rel_cases]
    \\ simp [pure_expTheory.subst_def, flookup_fupdate_list, subst_def,
             MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
    \\ simp [GSYM MAP_REVERSE, ALOOKUP_MAP, GSYM FILTER_REVERSE, ALOOKUP_FILTER,
             ALOOKUP_MAP_2]
    \\ IF_CASES_TAC \\ fs []
    \\ ‘MAP FST f = MAP FST g’
      by (last_x_assum mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘g’
          \\ Induct_on ‘f’ \\ Cases_on ‘g’ \\ fs [ELIM_UNCURRY])
    \\ CASE_TAC \\ CASE_TAC \\ fs []
    \\ imp_res_tac ALOOKUP_SOME \\ gvs [ALOOKUP_NONE, MAP_REVERSE]
    \\ irule exp_rel_Value_Rec \\ fs [])
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
    >- ((* Seq *)
      irule exp_rel_Seq \\ fs [SF DNF_ss]
      \\ first_x_assum irule \\ fs []
      \\ first_assum (irule_at Any))
    \\ irule exp_rel_Prim \\ fs [EVERY2_MAP]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw [])
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
    \\ qmatch_goalsub_abbrev_tac ‘MAP f1 (FILTER _ gg)’
    \\ ‘(FEMPTY |++ MAP f1 (FILTER (λ(m,x). m ∉ ks) gg)) \\ n =
        FEMPTY |++ MAP f1 (FILTER (λ(m,x). m ∉ ks ∪ {n}) gg)’
      by (fs [DOMSUB_FUPDATE_LIST, combinTheory.o_DEF, FILTER_MAP, LAMBDA_PROD,
              FILTER_FILTER, Abbr ‘f1’]
          \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
          \\ rw [FUN_EQ_THM, EQ_IMP_THM])
    \\ pop_assum SUBST_ALL_TAC
    \\ unabbrev_all_tac
    \\ qmatch_goalsub_abbrev_tac ‘FILTER _ (MAP f2 (FILTER _ gg))’
    \\ ‘FILTER (λ(m,x). m ≠ n) (MAP f2 (FILTER (λ(m,x). m ∉ ks) gg)) =
        MAP f2 (FILTER (λ(m, x). m ∉ ks ∪ {n}) gg)’
      by (simp [FILTER_MAP, combinTheory.o_DEF, FILTER_FILTER, LAMBDA_PROD,
                Abbr ‘f2’]
          \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
          \\ rw [FUN_EQ_THM, EQ_IMP_THM])
    \\ pop_assum SUBST_ALL_TAC
    \\ unabbrev_all_tac
    \\ first_x_assum irule \\ fs [])
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
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    \\ qmatch_goalsub_abbrev_tac ‘MAP f1 (FILTER _ gg)’
    \\ ‘FDIFF (FEMPTY |++ MAP f1 (FILTER (λ(m,x). m ∉ ks) gg))
              (set (MAP FST lcs)) =
        FEMPTY |++ MAP f1 (FILTER (λ(m,x). m ∉ ks ∪ set (MAP FST lcs)) gg)’
      by (‘∀x. (λ(m,x). m ∉ ks) (f1 x) = (λ(m,x). m ∉ ks) x’
            by rw [Abbr ‘f1’, ELIM_UNCURRY]
          \\ ‘∀x. (λ(m,x). m ∉ ks ∪ set (MAP FST lcs)) (f1 x) =
                  (λ(m,x). m ∉ ks ∪ set (MAP FST lcs)) x’
            by rw [Abbr ‘f1’, ELIM_UNCURRY]
          \\ simp [MAP_FILTER]
          \\ unabbrev_all_tac
          \\ rename1 ‘FDIFF (_ |++ FILTER _ xs) zs’
          \\ rpt (pop_assum kall_tac)
          \\ simp [fmap_EXT]
          \\ conj_tac
          >- (
            rw [EXTENSION, FDOM_FDIFF, FDOM_FUPDATE_LIST, MEM_MAP, MEM_FILTER,
                LAMBDA_PROD, EXISTS_PROD, EQ_IMP_THM]
            \\ fs [SF SFY_ss])
          \\ rw [FDOM_FUPDATE_LIST, MEM_MAP, MEM_FILTER, LAMBDA_PROD,
                 EXISTS_PROD, FDIFF_def, DRESTRICT_DEF,
                 FUPDATE_LIST_EQ_APPEND_REVERSE]
          \\ qmatch_goalsub_abbrev_tac ‘alist_to_fmap al’
          \\ Cases_on ‘ALOOKUP al x’
          \\ gs [ALOOKUP_NONE, Abbr ‘al’, MAP_REVERSE, MEM_MAP, MEM_FILTER,
                 LAMBDA_PROD, EXISTS_PROD, FDOM_FUPDATE_LIST,
                 GSYM FILTER_REVERSE, ALOOKUP_FILTER])
    \\ pop_assum SUBST1_TAC
    \\ unabbrev_all_tac
    \\ qmatch_goalsub_abbrev_tac ‘FILTER _ (MAP f2 (FILTER _ gg))’
    \\ ‘FILTER (λ(m,x). ¬MEM m (MAP FST g'))
               (MAP f2 (FILTER (λ(m,x). m ∉ ks) gg)) =
        MAP f2 (FILTER (λ(m, x). m ∉ ks ∪ set (MAP FST g')) gg)’
      by (simp [FILTER_MAP, combinTheory.o_DEF, FILTER_FILTER, LAMBDA_PROD,
                Abbr ‘f2’]
          \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
          \\ rw [FUN_EQ_THM, EQ_IMP_THM])
    \\ pop_assum SUBST1_TAC
    \\ unabbrev_all_tac
    \\ rename1 ‘LIST_REL _ f1 g1’
    \\ ‘MAP FST g1 = MAP FST f1’
      by (qpat_x_assum ‘LIST_REL _ f1 _’ mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘g1’
          \\ Induct_on ‘f1’ \\ Cases_on ‘g1’ \\ simp []
          \\ rw [] \\ fs [ELIM_UNCURRY])
    \\ pop_assum SUBST_ALL_TAC
    \\ first_x_assum (irule_at Any) \\ fs []
    \\ simp [EVERY2_MAP, LAMBDA_PROD]
    \\ simp [LIST_REL_EL_EQN]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ rw [] \\ gvs []
    \\ pairarg_tac \\ gvs []
    \\ pairarg_tac \\ gvs []
    \\ rename1 ‘EL n f1 = (v1, b1)’
    \\ ‘MEM (v1, b1) f1’
      by (rw [MEM_EL, Once EQ_SYM_EQ]
          \\ first_assum (irule_at Any) \\ fs [])
    \\ first_x_assum drule
    \\ qpat_x_assum ‘LIST_REL _ f _’ assume_tac
    \\ disch_then drule
    \\ gvs [LIST_REL_EL_EQN]
    \\ first_x_assum (drule_then assume_tac)
    \\ pairarg_tac \\ gvs []
    \\ disch_then (drule_then (qspec_then ‘ks ∪ set (MAP FST f1)’ mp_tac))
    \\ qmatch_goalsub_abbrev_tac ‘subst s1’ \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac ‘subst s2’
    \\ ‘s1 = s2’ suffices_by (rw [] \\ fs [])
    \\ unabbrev_all_tac
    \\ simp [FILTER_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
QED

Theorem exp_rel_subst_funs:
  ∀x f g y ks.
    LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ closed x ∧ exp_rel x y) f g ∧
    exp_rel x y ⇒
      exp_rel (subst_funs f x)
              (subst_funs (MAP (λ(gn, x). (gn, Delay x)) g) y)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ simp [subst_funs_def, pure_expTheory.subst_funs_def,
           pure_expTheory.bind_def]
  \\ reverse IF_CASES_TAC \\ fs []
  >- (
    ‘F’ suffices_by rw []
    \\ pop_assum mp_tac \\ simp []
    \\ fs [flookup_fupdate_list, FILTER_MAP, GSYM MAP_REVERSE, ALOOKUP_MAP,
           CaseEq "option"]
    \\ simp [EVERY_MAP, LAMBDA_PROD, EVERY_FILTER]
    \\ ‘MAP FST f = MAP FST g’
      by (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘g’
          \\ Induct_on ‘f’ \\ Cases_on ‘g’ \\ fs [ELIM_UNCURRY])
    \\ imp_res_tac ALOOKUP_MEM \\ fs [MEM_REVERSE, MEM_MAP, MEM_FILTER]
    \\ pop_assum mp_tac
    \\ simp [MEM_EL, Once EQ_SYM_EQ]
    \\ strip_tac \\ gvs []
    \\ gvs [LIST_REL_EL_EQN]
    \\ rename1 ‘m < LENGTH g’
    \\ ‘freevars (SND (EL m f)) = EMPTY’
      by fs [pure_expTheory.closed_def, ELIM_UNCURRY]
    \\ gvs [EVERY_EL] \\ rw []
    \\ pairarg_tac \\ gvs []
    \\ first_x_assum (drule_then assume_tac)
    \\ pairarg_tac \\ gvs []
    \\ pairarg_tac \\ gvs []
    \\ gs [pure_expTheory.closed_def])
  \\ drule_all_then (qspec_then ‘EMPTY’ mp_tac) exp_rel_subst_list
  \\ simp [FILTER_T, GSYM LAMBDA_PROD]
QED

Theorem subst1_fresh:
  ∀x s v.
    s ∉ freevars x ⇒ subst1 s v x = x
Proof
  ho_match_mp_tac freevars_ind \\ rw []
  \\ fs [freevars_def, subst1_def]
  >- (
    irule MAP_ID_ON \\ rw []
    \\ first_x_assum irule
    \\ gs [MEM_MAP, Once DISJ_COMM, DISJ_EQ_IMP, PULL_EXISTS])
  \\ IF_CASES_TAC \\ fs []
  \\ irule MAP_ID_ON \\ simp [FORALL_PROD]
  \\ qx_genl_tac [‘k’, ‘y’] \\ strip_tac
  \\ fs [MEM_MAP, FORALL_PROD, Once DISJ_COMM, DISJ_EQ_IMP, EXISTS_PROD,
         PULL_EXISTS]
  \\ first_x_assum irule
  \\ first_assum (irule_at Any)
  \\ first_assum (irule_at Any)
  \\ first_assum (irule_at Any)
QED

(* TODO move *)
Theorem result_map_MAP:
  result_map f (MAP g xs) = result_map (f o g) xs
Proof
  simp [result_map_def, MEM_MAP, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem exp_rel_eval_to:
  ∀k x res y.
    eval_wh_to k x = res ∧
    res ≠ wh_Error ∧
    exp_rel x y ∧
    closed x ⇒
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
    \\ simp [eval_to_def]
    \\ Cases_on ‘eval_wh_to k x = wh_Error’ \\ fs []
    \\ first_x_assum (drule_then assume_tac)
    \\ ‘∃res. eval_to k g = INR res’
      by (Cases_on ‘eval_to k g’ \\ gs [])
    \\ simp []
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k x)’ \\ fs []
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ Cases_on ‘eval_wh_to k x’ \\ gvs [dest_wh_Closure_def]
    \\ Cases_on ‘res’ \\ gvs [dest_anyClosure_def]
    \\ IF_CASES_TAC \\ fs []
    \\ imp_res_tac exp_rel_closed \\ gvs []
    \\ first_x_assum irule
    \\ fs [pure_expTheory.bind_def, FLOOKUP_UPDATE]
    \\ irule_at Any exp_rel_subst \\ fs []
    \\ irule_at Any closed_freevars_subst1
    \\ fs [pure_expTheory.closed_def])
  >- ((* Letrec *)
    rw []
    \\ qpat_x_assum ‘exp_rel (Letrec f y) _’ mp_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_wh_to_def, Once eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- ((* Rec *)
      CONV_TAC (PATH_CONV "rl" (SIMP_CONV (srw_ss()) [eval_to_def])) \\ gs []
      \\ imp_res_tac ALOOKUP_SOME \\ fs [dest_anyThunk_def]
      \\ simp [GSYM MAP_REVERSE, ALOOKUP_MAP]
      \\ first_x_assum irule
      \\ irule_at Any exp_rel_subst_funs \\ fs []
      \\ drule_then (qspec_then ‘REVERSE f’ mp_tac) ALOOKUP_SOME_EL_2
      \\ impl_tac
      >- (
        simp [MAP_REVERSE]
        \\ irule LIST_EQ
        \\ gvs [EL_MAP, LIST_REL_EL_EQN]
        \\ rw []
        \\ first_x_assum (drule_then assume_tac)
        \\ gs [ELIM_UNCURRY])
      \\ strip_tac
      \\ gvs [LIST_REL_EL_EQN, EL_REVERSE]
      \\ qmatch_asmsub_abbrev_tac ‘EL m f’
      \\ ‘m < LENGTH g’ by gvs [Abbr ‘m’]
      \\ first_x_assum (drule_then assume_tac) \\ gs []
      \\ gs [eval_wh_to_def, pure_expTheory.subst_funs_def,
             pure_expTheory.bind_def, flookup_fupdate_list, GSYM MAP_REVERSE,
             ALOOKUP_MAP_2]
      \\ rw [])
    >- ((* Tick *)
      CONV_TAC (PATH_CONV "rl" (SIMP_CONV (srw_ss()) [eval_to_def]))
      \\ gs [dest_anyThunk_def]
      \\ first_x_assum irule
      \\ fs [pure_expTheory.subst_funs_def, pure_expTheory.bind_def,
             flookup_fupdate_list, FDOM_FUPDATE_LIST, subst_ignore,
             subst_funs_def, eval_wh_to_def])
    \\ first_x_assum irule
    \\ irule_at Any exp_rel_subst_funs \\ fs []
    \\ gs [pure_expTheory.subst_funs_def, pure_expTheory.bind_def,
           flookup_fupdate_list, GSYM MAP_REVERSE, ALOOKUP_MAP_2,
           eval_wh_to_def]
    \\ rw []
    \\ irule_at Any IMP_closed_subst
    \\ simp [FDOM_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
             GSYM FST_THM]
    \\ simp [IN_FRANGE_FLOOKUP, PULL_EXISTS, flookup_fupdate_list,
             GSYM MAP_REVERSE, ALOOKUP_MAP_2, SF SFY_ss])
  >- ((* Prim *)
    rename1 ‘Prim op xs’
    \\ rw [] \\ qpat_x_assum ‘exp_rel (Prim op xs) _’ mp_tac
    >- ((* k = 0 *)
      rw [Once exp_rel_cases]
      \\ simp [Once eval_to_def, eval_wh_to_def, result_map_MAP,
               combinTheory.o_DEF]
      >- (
        simp [eval_to_def]
        \\ qmatch_goalsub_abbrev_tac ‘result_map f ys’
        \\ Cases_on ‘result_map f ys’ \\ fs [Abbr ‘f’]
        \\ gvs [result_map_def, MEM_MAP, MAP_MAP_o, combinTheory.o_DEF,
                LIST_REL_EL_EQN]
        \\ rw [] \\ gvs [EL_MAP]
        \\ gs [thunk_rel_def, EVERY_EL])
      >- (
        gvs [eval_to_def, eval_wh_to_def, LIST_REL_EL_EQN]
        \\ IF_CASES_TAC \\ gs []
        \\ gvs [LENGTH_EQ_NUM_compute])
      \\ Cases_on ‘op’ \\ fs [LIST_REL_EL_EQN]
      >- (
        IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute])
      \\ simp [result_map_def, MEM_MAP]
      \\ Cases_on ‘xs = []’ \\ gs []
      >- (
        simp [get_atoms_def]
        \\ CASE_TAC \\ fs []
        \\ CASE_TAC \\ fs []
        \\ IF_CASES_TAC \\ fs [])
      \\ ‘ys ≠ []’ by (strip_tac \\ fs [])
      \\ simp [get_atoms_MAP_Diverge]
      \\ gs [NIL_iff_NOT_MEM]
      \\ rw [] \\ gs [])
    \\ rw [Once exp_rel_cases]
    >- ((* If *)
      simp [eval_to_def, eval_wh_to_def]
      \\ gvs [LENGTH_EQ_NUM_compute, SF DNF_ss]
      \\ ‘eval_wh_to (k - 1) x1 ≠ wh_Error’
        by (gs [eval_wh_to_def, AllCaseEqs ()])
      \\ first_assum drule_all
      \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
      \\ rename1 ‘INR res’
      \\ CASE_TAC \\ Cases_on ‘res’ \\ gvs []
      \\ strip_tac \\ gvs []
      \\ IF_CASES_TAC \\ gvs []
      >- (
        first_x_assum irule
        \\ gs [eval_wh_to_def])
      \\ IF_CASES_TAC \\ gvs []
      >- (
        first_x_assum irule
        \\ gs [eval_wh_to_def])
      \\ IF_CASES_TAC \\ gvs []
      \\ IF_CASES_TAC \\ gvs [])
    >- ((* Cons *)
      simp [eval_wh_to_def, eval_to_def, result_map_MAP, combinTheory.o_DEF,
            result_map_def, MEM_MAP, MAP_MAP_o, EVERY2_MAP, thunk_rel_def,
            SF ETA_ss]
      \\ gs [LIST_REL_EL_EQN, EVERY_EL])
    >- ((* Proj *)
      simp [eval_wh_to_def, Once eval_to_def]
      \\ simp [Once eval_to_def]
      \\ IF_CASES_TAC \\ gvs [LIST_REL_EL_EQN]
      \\ gvs [Once eval_to_def, LENGTH_EQ_NUM_compute,
              DECIDE “∀n. n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ ‘eval_wh_to (k - 1) x ≠ wh_Error’
        by (strip_tac
            \\ gs [eval_wh_to_def])
      \\ first_assum (drule_all_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) y’ \\ fs []
      \\ rename1 ‘dest_Constructor v’
      \\ Cases_on ‘dest_Constructor v’
      >- (
        Cases_on ‘eval_wh_to (k - 1) x’ \\ Cases_on ‘v’ \\ gvs [])
      \\ Cases_on ‘v’ \\ gvs []
      \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gvs []
      \\ first_x_assum (drule_all_then assume_tac)
      \\ fs [thunk_rel_def, dest_anyThunk_def, subst_funs_def,
             EVERY_EL]
      \\ first_x_assum irule \\ gs []
      \\ strip_tac
      \\ gs [eval_wh_to_def])
    >- ((* Seq *)
      simp [eval_wh_to_def, eval_to_def]
      \\ fs [SF DNF_ss]
      \\ ‘eval_wh_to (k - 1) x1 ≠ wh_Error’
        by (strip_tac \\ gs [eval_wh_to_def])
      \\ first_assum (drule_all_then assume_tac) \\ fs []
      \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs [eval_wh_to_def]
      \\ IF_CASES_TAC \\ gvs [])
    >- ((* {IsEq, AtomOp, Lit} *)
      simp [eval_wh_to_def, eval_to_def]
      \\ gvs [LIST_REL_EL_EQN, eval_to_def]
      \\ Cases_on ‘op’ \\ fs []
      >- ((* IsEq *)
        IF_CASES_TAC \\ fs []
        \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
        \\ rename1 ‘exp_rel x y’
        \\ ‘eval_wh_to (k - 1) x ≠ wh_Error’
          by (strip_tac \\ gs [eval_wh_to_def])
        \\ first_assum (drule_all_then assume_tac)
        \\ Cases_on ‘eval_to (k - 1) y’ \\ fs []
        \\ rename1 ‘dest_Constructor v’
        \\ Cases_on ‘dest_Constructor v’ \\ fs []
        >- (
          Cases_on ‘eval_to (k - 1) y’ \\ Cases_on ‘eval_wh_to (k - 1) x’
          \\ Cases_on ‘v’ \\ gvs [])
        \\ pairarg_tac \\ gvs []
        \\ Cases_on ‘v’ \\ gvs []
        \\ drule_then assume_tac LIST_REL_LENGTH
        \\ IF_CASES_TAC \\ gvs []
        \\ IF_CASES_TAC \\ gvs [])
      >- ((* AtomOp *)
        qmatch_goalsub_abbrev_tac ‘result_map f ys’
        \\ gs [MEM_EL, PULL_EXISTS, EVERY_EL, eval_wh_to_def]
        \\ CASE_TAC \\ fs []
        >- (
          gvs [get_atoms_NONE_eq, EVERY_MAP, MEM_MAP, EVERY_MEM, MEM_EL,
               PULL_EXISTS]
          \\ ‘result_map f ys = INL Diverge’
            suffices_by rw []
          \\ gvs [result_map_def, MEM_MAP, MEM_EL, PULL_EXISTS, CaseEq "bool"]
          \\ simp [RIGHT_EXISTS_AND_THM]
          \\ reverse conj_tac
          >- (
            first_assum (irule_at Any)
            \\ first_x_assum (drule_then assume_tac)
            \\ ‘eval_wh_to (k - 1) (EL n xs) ≠ wh_Error’
              by (strip_tac \\ gs [])
            \\ first_x_assum (drule_all_then assume_tac)
            \\ first_x_assum (drule_all_then assume_tac)
            \\ first_x_assum (drule_all_then assume_tac)
            \\ unabbrev_all_tac \\ gs []
            \\ CASE_TAC \\ gs [])
          \\ qx_gen_tac ‘m’
          \\ rw [DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”]
          \\ first_x_assum (drule_then assume_tac)
          \\ ‘eval_wh_to (k - 1) (EL m xs) ≠ wh_Error’
            by (strip_tac \\ gs [])
          \\ first_x_assum (drule_all_then assume_tac)
          \\ first_x_assum (drule_all_then assume_tac)
          \\ first_x_assum (drule_all_then assume_tac)
          \\ unabbrev_all_tac \\ gs []
          \\ CASE_TAC \\ gs []
          \\ Cases_on ‘eval_wh_to (k - 1) (EL m xs)’ \\ gs []
          \\ CASE_TAC \\ gs [])
        \\ CASE_TAC \\ gs []
        \\ gvs [get_atoms_SOME_SOME_eq, EVERY2_MAP]
        \\ Cases_on ‘result_map f ys’ \\ gs []
        >- (
          gs [result_map_def, CaseEq "bool", MEM_MAP, MEM_EL, PULL_EXISTS]
          \\ unabbrev_all_tac \\ gs []
          \\ gvs [CaseEqs ["sum", "thunkLang$v"], LIST_REL_EL_EQN]
          \\ first_x_assum (drule_then assume_tac)
          \\ ‘eval_wh_to (k - 1) (EL n xs) ≠ wh_Error’ by gs []
          \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs [])
        \\ rename1 ‘eval_op a z’
        \\ qsuff_tac ‘z = y’
        >- (
          rw []
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs []
          \\ IF_CASES_TAC \\ gs [])
        \\ irule LIST_EQ
        \\ gvs [result_map_def, CaseEq "bool", MEM_MAP, MEM_EL, PULL_EXISTS,
                MAP_MAP_o, combinTheory.o_DEF, EL_MAP, LIST_REL_EL_EQN]
        \\ rw []
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ unabbrev_all_tac \\ gs []
        \\ ‘eval_wh_to (k - 1) (EL x xs) ≠ wh_Error’ by gs []
        \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs []
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [])))
QED

Theorem v_rel_mono:
  x ≠ wh_Diverge ∧
  v_rel x (eval_to k y) ⇒
    ∀j. k ≤ j ⇒ v_rel x (eval_to j y)
Proof
  rw []
  \\ ‘eval_to k y ≠ INL Diverge’ by (strip_tac \\ fs [])
  \\ Cases_on ‘k = j’ \\ fs []
  \\ ‘k < j’ by fs []
  \\ drule_all_then assume_tac eval_to_mono \\ fs []
QED

Theorem exp_rel_eval:
  eval_wh x ≠ wh_Error ∧
  exp_rel x y ∧
  closed x ⇒
    v_rel (eval_wh x) (eval y)
Proof
  strip_tac
  \\ qpat_x_assum ‘eval_wh _ ≠ _’ mp_tac
  \\ simp [eval_wh_def, thunkLangTheory.eval_def]
  \\ DEEP_INTRO_TAC some_intro \\ fs []
  \\ DEEP_INTRO_TAC some_intro \\ fs []
  \\ rw []
  >- (
    rename1 ‘eval_to k’
    \\ rename1 ‘eval_wh_to j’
    \\ Cases_on ‘j ≤ k’ \\ fs []
    >- (
      irule v_rel_mono \\ fs []
      \\ first_assum (irule_at Any)
      \\ irule_at Any exp_rel_eval_to
      \\ first_assum (irule_at Any) \\ fs []
      \\ first_assum (irule_at Any) \\ fs [])
    \\ ‘k ≤ j’ by fs []
    \\ drule_all_then assume_tac eval_to_mono
    \\ pop_assum (SUBST_ALL_TAC o SYM)
    \\ irule exp_rel_eval_to
    \\ first_assum (irule_at Any) \\ fs []
    \\ first_assum (irule_at Any) \\ fs [])
  >- (
    irule exp_rel_eval_to
    \\ first_assum (irule_at Any) \\ fs [])
  \\ CCONTR_TAC
  \\ rename1 ‘eval_wh_to j’
  \\ ‘∃res. eval_wh_to j x = res ∧ res ≠ wh_Error’
    by gs []
  \\ drule_all_then assume_tac exp_rel_eval_to \\ gs []
QED

Definition cont_rel_def[simp]:
  cont_rel Done Done = T ∧
  cont_rel (BC x c) (BC v d) = (closed x ∧ thunk_rel x v ∧ cont_rel c d) ∧
  cont_rel (HC x c) (HC v d) = (closed x ∧ thunk_rel x v ∧ cont_rel c d) ∧
  cont_rel _ _ = F
End

Definition state_rel_def:
  state_rel = LIST_REL (LIST_REL thunk_rel)
End

Definition next_rel_def[simp]:
  next_rel Ret Ret = T ∧
  next_rel Div Div = T ∧
  next_rel Err Err = T ∧
  next_rel (Act a c s) (Act b d t) = (a = b ∧ cont_rel c d ∧ state_rel s t) ∧
  next_rel _ _ = F
End

(* -------------------------------------------------------------------------
 * Alternative top-level semantics with Tick'd applications
 * ------------------------------------------------------------------------- *)

Definition apply_closure'_def:
  apply_closure' f arg cont =
    if eval_wh f = wh_Diverge then Div else
      case dest_wh_Closure (eval_wh f) of
        NONE => pure_semantics$Err
      | SOME (n,e) => cont (eval_wh (bind1 n (Tick arg) e))
End

Definition next'_def:
  next' (k:num) v stack state =
    case v of
    | wh_Constructor s es =>
       (if s = "Ret" ∧ LENGTH es = 1 then
          (case stack of
           | Done => Ret
           | BC f fs =>
             apply_closure' f (HD es)
               (λw. if k = 0 then Div else next' (k-1) w fs state)
           | HC f fs => if k = 0 then Div else next' (k-1) v fs state)
        else if s = "Raise" ∧ LENGTH es = 1 then
          (case stack of
           | Done => Ret
           | BC f fs => if k = 0 then Div else next' (k-1) v fs state
           | HC f fs =>
               apply_closure' f (HD es)
                 (λw. if k = 0 then Div else next' (k-1) w fs state))
        else if s = "Bind" ∧ LENGTH es = 2 then
          (let m = EL 0 es in
           let f = EL 1 es in
             if k = 0 then Div else next' (k-1) (eval_wh m) (BC f stack) state)
        else if s = "Handle" ∧ LENGTH es = 2 then
          (let m = EL 0 es in
           let f = EL 1 es in
             if k = 0 then Div else next' (k-1) (eval_wh m) (HC f stack) state)
        else if s = "Act" ∧ LENGTH es = 1 then
          (with_atom es (λa.
             case a of
             | Msg channel content => Act (channel, content) stack state
             | _ => Err))
        else if s = "Alloc" ∧ LENGTH es = 2 then
          (with_atom [HD es] (λa.
             case a of
             | Int len =>
                 (let n = if len < 0 then 0 else Num len in
                  let new_state = state ++ [REPLICATE n (EL 1 es)] in
                    if k = 0 then Div else
                    next' (k-1)
                      (wh_Constructor "Ret" [Lit (Loc (LENGTH state))])
                      stack new_state)
             | _ => Err))
        else if s = "Length" ∧ LENGTH es = 1 then
          (with_atom es (λa.
             case a of
             | Loc n =>
                 (if LENGTH state ≤ n then Err else
                  if k = 0 then Div else
                  next' (k-1)
                    (wh_Constructor "Ret" [Lit (Int (& (LENGTH (EL n state))))])
                    stack state)
             | _ => Err))
        else if s = "Deref" ∧ LENGTH es = 2 then
          (with_atom2 es (λa a'.
             case (a, a') of
             | (Loc n, Int i) =>
                 (if LENGTH state ≤ n then Err else
                  if 0 ≤ i ∧ i < & LENGTH (EL n state) then
                  if k = 0 then Div else
                    next' (k-1) (wh_Constructor "Ret" [EL (Num i) (EL n state)])
                          stack state
                  else if k = 0 then Div else
                    next' (k-1) (wh_Constructor "Raise" [Cons "Subscript" []])
                          stack state)
             | _ => Err))
        else if s = "Update" ∧ LENGTH es = 3 then
          (with_atom2 [EL 0 es; EL 1 es] (λa a'.
             case (a, a') of
             | (Loc n, Int i) =>
                 (if LENGTH state ≤ n then Err else
                  if 0 ≤ i ∧ i < & LENGTH (EL n state) then
                    if k = 0 then Div else
                      next' (k-1) (wh_Constructor "Ret" [Cons "" []]) stack
                            (LUPDATE (LUPDATE (EL 2 es) (Num i)
                                              (EL n state)) n state)
                  else if k = 0 then Div else
                    next' (k-1) (wh_Constructor "Raise" [Cons "Subscript" []])
                          stack state)
             | _ => Err))
        else Err)
    | wh_Diverge => Div
    | _ => Err
End

Definition next_action'_def:
  next_action' wh stack state =
    case some k. next' k wh stack state ≠ Div of
    | NONE => Div
    | SOME k => next' k wh stack state
End

Inductive tick_rel:
[~Var:]
  (∀n. tick_rel (pure_exp$Var n) (Var n)) ∧
[~Prim:]
  (∀op xs ys.
     LIST_REL tick_rel xs ys ⇒
       tick_rel (Prim op xs) (Prim op ys)) ∧
[~App:]
  (∀f g x y.
     tick_rel f g ∧
     tick_rel x y ⇒
       tick_rel (App f x) (App g y)) ∧
[~Lam:]
  (∀s x y.
     tick_rel x y ⇒
       tick_rel (Lam s x) (Lam s y)) ∧
[~Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ tick_rel x y) f g ∧
     tick_rel x y ⇒
       tick_rel (Letrec f x) (Letrec g y)) ∧
[~Tick:]
  (∀x. tick_rel x (Tick x))
End

Definition tcont_rel_def[simp]:
  tcont_rel Done Done = T ∧
  tcont_rel (BC x c) (BC y d) = (tick_rel x y ∧ tcont_rel c d) ∧
  tcont_rel (HC x c) (HC y d) = (tick_rel x y ∧ tcont_rel c d) ∧
  tcont_rel _ _ = F
End

Definition tstate_rel_def:
  tstate_rel = LIST_REL (LIST_REL tick_rel)
End

Definition tnext_rel_def[simp]:
  tnext_rel Ret Ret = T ∧
  tnext_rel Div Div = T ∧
  tnext_rel Err Err = T ∧
  tnext_rel (Act a c s) (Act b d t) = (a = b ∧ tcont_rel c d ∧ tstate_rel s t) ∧
  tnext_rel _ _ = F
End

Definition tick_wh_rel_def[simp]:
  tick_wh_rel (wh_Constructor s x) (wh_Constructor t y) =
    (s = t ∧ LIST_REL tick_rel x y) ∧
  tick_wh_rel (wh_Closure s x) (wh_Closure t y) =
    (s = t ∧ tick_rel x y) ∧
  tick_wh_rel (wh_Atom x) (wh_Atom y) = (x = y) ∧
  tick_wh_rel wh_Error wh_Error =  T ∧
  tick_wh_rel wh_Diverge wh_Diverge =  T ∧
  tick_wh_rel _ _ = F
End

Theorem tick_rel_thm[simp]:
  (∀s x z.
    tick_wh_rel (wh_Constructor s x) z =
    ∃y. z = wh_Constructor s y ∧ LIST_REL tick_rel x y) ∧
  (∀s x z.
    tick_wh_rel (wh_Closure s x) z =
    ∃y. z = wh_Closure s y ∧ tick_rel x y) ∧
  (∀x z.
   tick_wh_rel (wh_Atom x) z = (z = wh_Atom x)) ∧
  (∀z. tick_wh_rel wh_Error z =  (z = wh_Error)) ∧
  (∀z. tick_wh_rel wh_Diverge z = (z = wh_Diverge))
Proof
 rpt conj_tac \\ Cases_on ‘z’ \\ rw [tick_wh_rel_def, EQ_IMP_THM]
QED

Theorem tick_rel_refl:
  ∀x. tick_rel x x
Proof
  ho_match_mp_tac exp_ind_alt \\ rw []
  \\ rw [Once tick_rel_cases]
  \\ gs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
  \\ disj1_tac \\ rw []
  \\ first_x_assum drule
  \\ Cases_on ‘EL n lcs’ \\ gs []
QED

Theorem tick_wh_rel_refl:
  ∀x. tick_wh_rel x x
Proof
  Cases \\ rw [tick_rel_refl, LIST_REL_EL_EQN]
QED

Theorem tstate_rel_refl:
  tstate_rel s s
Proof
  rw [tstate_rel_def, LIST_REL_EL_EQN, tick_rel_refl]
QED

Theorem tcont_rel_refl:
  ∀x. tcont_rel x x
Proof
  Induct \\ rw [tick_rel_refl]
QED

Theorem tnext_rel_refl:
  ∀x. tnext_rel x x
Proof
  Cases \\ rw [tnext_rel_def, tcont_rel_refl, tstate_rel_refl]
QED

Theorem tick_rel_eval_wh_to:
  ∀x y.
    tick_rel x y ⇒
      ∀k. ∃j. tick_wh_rel (eval_wh_to k x) (eval_wh_to (k + j) y)
Proof
  ho_match_mp_tac tick_rel_strongind \\ rw []
  >~ [‘Var n’] >- (
    rw [eval_wh_to_def])
  >~ [‘Lam s x’] >- (
    rw [eval_wh_to_def])
  >~ [‘Tick x’] >- (
    qexists_tac ‘1’
    \\ rw [eval_wh_to_def, pure_expTheory.subst_funs_def,
           pure_expTheory.bind_def, FUPDATE_LIST_THM]
    \\ irule tick_wh_rel_refl)
  >~ [‘_ _ (App f x)’, ‘_ (_ + _) (App g y)’] >- (
    last_x_assum (qspec_then ‘k’ (qx_choose_then ‘j’ assume_tac)) \\ gs []
    \\ rw [eval_wh_to_def]
    >- (
      qexists_tac ‘j’
      \\ Cases_on ‘eval_wh_to (j + k ) g’ \\ gs [])
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k f)’ \\ gs []
    >- (
      qexists_tac ‘j’
      \\ Cases_on ‘eval_wh_to k f’ \\ Cases_on ‘eval_wh_to (j + k) g’ \\ gs [])
    \\ BasicProvers.TOP_CASE_TAC
    \\ IF_CASES_TAC \\ gs []
    >- (
      Cases_on ‘eval_wh_to 0 g = wh_Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘eval_wh_to j g = eval_wh_to 0 g’
        by (irule eval_wh_inc \\ gs [])
      \\ qexists_tac ‘0’ \\ simp []
      \\ Cases_on ‘eval_wh_to 0 f’ \\ Cases_on ‘eval_wh_to 0 g’ \\ gs [])
    \\ ‘eval_wh_to (j + k) g ≠ wh_Diverge’
      by (strip_tac \\ Cases_on ‘eval_wh_to k f’ \\ gs [])
    \\ last_x_assum (qspec_then ‘k’ (qx_choose_then ‘j1’ assume_tac)) \\ gs []
    \\ cheat)
  >~ [‘Letrec f x’] >- (
    first_x_assum (qspec_then ‘k’ (qx_choose_then ‘j’ assume_tac)) \\ gs []
    \\ rw [eval_wh_to_def]
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ rw [pure_expTheory.subst_funs_def]
    \\ qexists_tac ‘0’
    \\ cheat)
  >~ [‘Prim op xs’] >- (
    cheat)
QED

Theorem tick_rel_eval_wh:
  tick_rel x y ⇒ tick_wh_rel (eval_wh x) (eval_wh y)
Proof
  rw [eval_wh_def]
  \\ cheat
QED

Theorem next'_thm:
  ∀k v c s w d t.
    tick_wh_rel v w ∧
    tstate_rel s t ∧
    tcont_rel c d ⇒
      tnext_rel (next' k v c s) (next k w d t)
Proof
  ho_match_mp_tac next'_ind \\ rw []
  \\ simp [Once next'_def]
  \\ Cases_on ‘v = wh_Error ∨
               v = wh_Diverge ∨
               (∃x. v = wh_Atom x) ∨
               (∃s x. v = wh_Closure s x)’
  >- ((* Error *)
    rgs [Once pure_semanticsTheory.next_def]
    \\ simp [Once pure_semanticsTheory.next_def])
  \\ ‘∃n xs. v = wh_Constructor n xs’
    by (Cases_on ‘v’ \\ gs [])
  \\ gvs []
  \\ drule_then assume_tac LIST_REL_LENGTH
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once pure_semanticsTheory.next_def]
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘c’ \\ Cases_on ‘d’
    \\ gvs [apply_closure'_def, pure_semanticsTheory.apply_closure_def]
    >- (
      rename1 ‘tick_rel x y’
      \\ drule_then assume_tac tick_rel_eval_wh
      \\ Cases_on ‘eval_wh x’ \\ Cases_on ‘eval_wh y’ \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ first_x_assum irule \\ gs []
      \\ irule tick_rel_eval_wh
      \\ cheat (* subst theorem *))
    \\ IF_CASES_TAC \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once pure_semanticsTheory.next_def]
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘c’ \\ Cases_on ‘d’
    \\ gvs [apply_closure'_def, pure_semanticsTheory.apply_closure_def]
    >- (
      IF_CASES_TAC \\ gs [])
    \\ rename1 ‘tick_rel x y’
    \\ drule_then assume_tac tick_rel_eval_wh
    \\ Cases_on ‘eval_wh x’ \\ Cases_on ‘eval_wh y’ \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule \\ gs []
    \\ irule tick_rel_eval_wh
    \\ cheat (* subst theorem *))
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once pure_semanticsTheory.next_def]
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule \\ gs []
    \\ irule tick_rel_eval_wh \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once pure_semanticsTheory.next_def]
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule \\ gs []
    \\ irule tick_rel_eval_wh \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once pure_semanticsTheory.next_def]
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ simp [with_atom_def, pure_semanticsTheory.with_atoms_def]
    \\ rename1 ‘tick_rel x y’
    \\ drule_then assume_tac tick_rel_eval_wh
    \\ Cases_on ‘eval_wh x’ \\ Cases_on ‘eval_wh y’
    \\ gs [pure_semanticsTheory.get_atoms_def]
    \\ CASE_TAC \\ gvs [])
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once pure_semanticsTheory.next_def]
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ rename1 ‘with_atom [x1]’
    \\ rename1 ‘tick_rel x1 y1’
    \\ rename1 ‘tick_rel x2 y2’
    \\ simp [with_atom_def, pure_semanticsTheory.with_atoms_def]
    \\ qpat_x_assum ‘tick_rel x1 _’ assume_tac
    \\ drule_then assume_tac tick_rel_eval_wh
    \\ qpat_x_assum ‘tick_rel x2 _’ assume_tac
    \\ drule_then assume_tac tick_rel_eval_wh
    \\ Cases_on ‘eval_wh x1’ \\ Cases_on ‘eval_wh y1’
    \\ gs [pure_semanticsTheory.get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ simp [Once tick_rel_cases]
    \\ gs [tstate_rel_def, LIST_REL_EL_EQN] \\ rw []
    \\ gs [EL_REPLICATE])
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once pure_semanticsTheory.next_def]
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ rename1 ‘tick_rel x y’
    \\ simp [with_atom_def, pure_semanticsTheory.with_atoms_def]
    \\ drule_then assume_tac tick_rel_eval_wh
    \\ Cases_on ‘eval_wh x’ \\ Cases_on ‘eval_wh y’
    \\ gs [pure_semanticsTheory.get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ ‘LENGTH s = LENGTH t’
      by gvs [tstate_rel_def, LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ simp [Once tick_rel_cases]
    \\ gs [tstate_rel_def, LIST_REL_EL_EQN] \\ rw [])
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once pure_semanticsTheory.next_def]
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ rename1 ‘with_atom2 [x1; x2]’
    \\ rename1 ‘tick_rel x1 y1’
    \\ rename1 ‘tick_rel x2 y2’
    \\ simp [with_atom2_def, pure_semanticsTheory.with_atoms_def]
    \\ qpat_x_assum ‘tick_rel x1 _’ assume_tac
    \\ drule_then assume_tac tick_rel_eval_wh
    \\ qpat_x_assum ‘tick_rel x2 _’ assume_tac
    \\ drule_then assume_tac tick_rel_eval_wh
    \\ Cases_on ‘eval_wh x1’ \\ Cases_on ‘eval_wh y1’
    \\ Cases_on ‘eval_wh x2’ \\ Cases_on ‘eval_wh y2’
    \\ gs [pure_semanticsTheory.get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ ‘LENGTH s = LENGTH t’
      by gvs [tstate_rel_def, LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ gs []
    \\ ‘LENGTH (EL n s) = LENGTH (EL n t)’
      by gvs [tstate_rel_def, LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ gs []
    >- (
      IF_CASES_TAC \\ gs []
      \\ first_x_assum irule \\ gs [tstate_rel_def, LIST_REL_EL_EQN]
      \\ gvs [arithmeticTheory.LESS_OR_EQ, arithmeticTheory.NOT_LESS]
      \\ first_x_assum drule \\ rw []
      \\ first_x_assum irule
      \\ intLib.ARITH_TAC)
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule \\ gs [tstate_rel_def, LIST_REL_EL_EQN]
    \\ gvs [arithmeticTheory.LESS_OR_EQ, arithmeticTheory.NOT_LESS]
    \\ simp [Once tick_rel_cases]
    \\ qexists_tac ‘i’ \\ gs []
    \\ qexists_tac ‘n’ \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once pure_semanticsTheory.next_def]
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ rename1 ‘with_atom2 [x1; x2]’
    \\ rename1 ‘tick_rel x1 y1’
    \\ rename1 ‘tick_rel x2 y2’
    \\ simp [with_atom2_def, pure_semanticsTheory.with_atoms_def]
    \\ qpat_x_assum ‘tick_rel x1 _’ assume_tac
    \\ drule_then assume_tac tick_rel_eval_wh
    \\ qpat_x_assum ‘tick_rel x2 _’ assume_tac
    \\ drule_then assume_tac tick_rel_eval_wh
    \\ Cases_on ‘eval_wh x1’ \\ Cases_on ‘eval_wh y1’
    \\ Cases_on ‘eval_wh x2’ \\ Cases_on ‘eval_wh y2’
    \\ gs [pure_semanticsTheory.get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ ‘LENGTH s = LENGTH t’
      by gvs [tstate_rel_def, LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ gs []
    \\ ‘LENGTH (EL n s) = LENGTH (EL n t)’
      by gvs [tstate_rel_def, LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ gs []
    >- (
      IF_CASES_TAC \\ gs []
      \\ first_x_assum irule \\ gs [tstate_rel_def, LIST_REL_EL_EQN]
      \\ simp [Once tick_rel_cases]
      \\ rw [EL_LUPDATE] \\ rw [])
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule \\ gs [tstate_rel_def, LIST_REL_EL_EQN]
    \\ simp [Once tick_rel_cases]
    \\ first_assum (irule_at Any)
    \\ qexists_tac ‘i’ \\ gs [])
  \\ rw [Once pure_semanticsTheory.next_def]
QED

Theorem next'_less_eq:
  ∀k1 x fs st.
    next' k1 x fs st ≠ Div ⇒
    ∀k2. k1 ≤ k2 ⇒
      next' k1 x fs st = next' k2 x fs st
Proof
  ho_match_mp_tac next'_ind \\ rw []
  \\ qpat_x_assum ‘next' _ _ _ _ ≠ _’ mp_tac
  \\ once_rewrite_tac [next'_def]
  \\ Cases_on ‘x’ \\ fs [apply_closure'_def]
  \\ Cases_on ‘s = "Bind"’ THEN1 (fs [] \\ rw [])
  \\ Cases_on ‘s = "Handle"’ THEN1 (fs [] \\ rw [])
  \\ Cases_on ‘s = "Act"’ THEN1 (fs [] \\ rw [])
  \\ Cases_on ‘s = "Raise"’
  THEN1
   (fs [] \\ rw [] \\ Cases_on ‘fs’ \\ fs []
    \\ Cases_on ‘dest_wh_Closure (eval_wh e)’ \\ fs []
    \\ rw [] \\ fs [] \\ PairCases_on ‘x’ \\ gvs [] \\ rw [] \\ fs [])
  \\ Cases_on ‘s = "Ret"’
  THEN1
   (fs [] \\ rw [] \\ Cases_on ‘fs’ \\ fs []
    \\ Cases_on ‘dest_wh_Closure (eval_wh e)’ \\ fs []
    \\ rw [] \\ fs [] \\ PairCases_on ‘x’ \\ gvs [] \\ rw [] \\ fs [])
  \\ Cases_on ‘s = "Alloc"’ THEN1
   (fs [] \\ rw [with_atom_def,pure_semanticsTheory.with_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘eval_wh h’ \\ gvs [get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ fs [])
  \\ Cases_on ‘s = "Length"’ THEN1
   (fs [] \\ rw [with_atom_def,pure_semanticsTheory.with_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘eval_wh h’ \\ gvs [get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ fs [] \\ IF_CASES_TAC \\ fs [])
  \\ Cases_on ‘s = "Deref"’ THEN1
   (fs [] \\ rw [with_atom2_def,pure_semanticsTheory.with_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘eval_wh h’ \\ gvs [get_atoms_def]
    \\ Cases_on ‘eval_wh h'’ \\ gvs [get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gvs [LENGTH_EQ_NUM_compute]
    \\ BasicProvers.TOP_CASE_TAC \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ fs [] \\ IF_CASES_TAC \\ fs []
    \\ fs [AllCaseEqs()]
    \\ first_x_assum irule \\ fs []
    \\ metis_tac [])
  \\ Cases_on ‘s = "Update"’ THEN1
   (fs [] \\ rw [with_atom2_def,pure_semanticsTheory.with_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘eval_wh h’ \\ gvs [get_atoms_def]
    \\ Cases_on ‘eval_wh h'’ \\ gvs [get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gvs [LENGTH_EQ_NUM_compute]
    \\ BasicProvers.TOP_CASE_TAC \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ fs [] \\ IF_CASES_TAC \\ fs []
    \\ fs [AllCaseEqs()]
    \\ first_x_assum irule \\ fs []
    \\ metis_tac [])
  \\ rw [] \\ fs []
QED

Theorem next'_next':
  next' k1 x fs st ≠ Div ∧ next' k2 x fs st ≠ Div ⇒
  next' k1 x fs st = next' k2 x fs st
Proof
  metis_tac [LESS_EQ_CASES, next'_less_eq]
QED

Theorem next_action'_thm:
  tick_wh_rel v w ∧
  tstate_rel s t ∧
  tcont_rel c d ⇒
    tnext_rel (next_action' v c s) (next_action w d t)
Proof
  rw [next_action'_def, pure_semanticsTheory.next_action_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ simp [PULL_FORALL]
  \\ qx_gen_tac ‘i’
  \\ qx_gen_tac ‘j’
  \\ qx_gen_tac ‘k’
  \\ rw []
  >- (
    drule_all_then assume_tac next'_thm
    \\ drule_then (qspec_then ‘i + j’ assume_tac)
                  pure_semanticsTheory.next_less_eq
    \\ drule_then (qspec_then ‘i + j’ assume_tac) next'_less_eq
    \\ gs [])
  \\ drule_all_then assume_tac next'_thm \\ gs []
QED

Definition interp'_alt_def:
  interp'_alt =
    io_unfold_err
      (λ(v,stack,state).
        case next_action' v stack state of
        | Ret => Ret' Termination
        | Err => Ret' Error
        | Div => Div'
        | Act a new_stack new_state =>
            Vis' a (λy. (wh_Constructor "Ret" [Lit (Str y)],
                    new_stack, new_state)))
      ((λ_ ret. STRLEN ret ≤ max_FFI_return_size),
       FinalFFI,
       λs. FinalFFI s FFI_failure)
End

Definition interp_alt:
  interp_alt v stack state = interp'_alt (v, stack, state)
End

Theorem interp_alt_def:
  interp_alt wh stack state =
    case next_action' wh stack state of
    | Ret => Ret Termination
    | Err => Ret Error
    | Div => Div
    | Act a new_stack new_state =>
        Vis a (λs. case s of
          | INL x => Ret $ FinalFFI a x
          | INR y =>
              if STRLEN y ≤ max_FFI_return_size then
                interp_alt (wh_Constructor "Ret" [Lit (Str y)])
                           new_stack new_state
              else Ret $ FinalFFI a FFI_failure)
Proof
  fs [Once interp_alt,interp'_alt_def]
  \\ once_rewrite_tac [io_treeTheory.io_unfold_err] \\ fs []
  \\ Cases_on ‘next_action' wh stack state’ \\ fs []
  \\ fs [combinTheory.o_DEF,FUN_EQ_THM] \\ rw []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ fs [interp_alt,interp'_alt_def]
QED

Theorem interp_alt_thm:
  tick_wh_rel v w ∧
  tcont_rel c d ∧
  tstate_rel s t ⇒
    interp_alt v c s = interp w d t
Proof
  strip_tac
  \\ rw [Once io_treeTheory.io_bisimulation]
  \\ qexists_tac ‘
    λt1 t2.
      (t1 = t2 ∨
       ∃v c s w d t.
         t1 = interp_alt v c s ∧
         t2 = interp w d t ∧
         tick_wh_rel v w ∧
         tcont_rel c d ∧
         tstate_rel s t)’
  \\ rw []
  >- (
    disj2_tac
    \\ irule_at Any EQ_REFL
    \\ irule_at Any EQ_REFL \\ gs [])
  >- (
    drule_all_then assume_tac next_action'_thm \\ gs []
    \\ qpat_x_assum ‘Ret _ = _’ mp_tac
    \\ once_rewrite_tac [pure_semanticsTheory.interp_def, interp_alt_def]
    \\ Cases_on ‘next_action' v' c' s'’
    \\ Cases_on ‘next_action w' d' t''’ \\ gvs [])
  >- (
    drule_all_then assume_tac next_action'_thm \\ gs []
    \\ qpat_x_assum ‘_ = Div’ mp_tac
    \\ once_rewrite_tac [pure_semanticsTheory.interp_def, interp_alt_def]
    \\ Cases_on ‘next_action' v' c' s'’
    \\ Cases_on ‘next_action w' d' t''’ \\ gvs [])
  \\ drule_all_then assume_tac next_action'_thm \\ gs []
  \\ qpat_x_assum ‘Vis _ _ = _’ mp_tac
  \\ rw [Once pure_semanticsTheory.interp_def, Once interp_alt_def]
  \\ Cases_on ‘next_action' v' c' s'’
  \\ Cases_on ‘next_action w' d' t''’ \\ gvs []
  \\ rw [] \\ CASE_TAC \\ gs [] \\ rw []
  \\ disj2_tac
  \\ irule_at Any EQ_REFL
  \\ irule_at Any EQ_REFL \\ gs []
  \\ simp [Once tick_rel_cases]
QED

Theorem pure_to_thunk_next[local]:
  ∀k v c s w d t.
    v_rel v w ∧
    cont_rel c d ∧
    state_rel s t ∧
    next' k v c s ≠ Err ⇒
      next_rel (next' k v c s) (next k w d t)
Proof
  ho_match_mp_tac pure_semanticsTheory.next_ind \\ rw []
  \\ simp [Once next'_def]
  \\ Cases_on ‘v = wh_Error ∨
               v = wh_Diverge ∨
               (∃x. v = wh_Atom x) ∨
               (∃s x. v = wh_Closure s x)’
  >- ((* Error *)
    rgs [Once next'_def]
    \\ Cases_on ‘w’ \\ rgs [Once thunk_semanticsTheory.next_def]
    \\ gs [Once next'_def])
  \\ ‘∃n xs. v = wh_Constructor n xs’
    by (Cases_on ‘v’ \\ gs [])
  \\ gvs []
  \\ rename1 ‘v_rel _ w’ \\ Cases_on ‘w’ \\ gvs []
  \\ rename1 ‘v_rel _ (INR w)’ \\ Cases_on ‘w’ \\ gvs []
  \\ gs [LIST_REL_EL_EQN]
  \\ IF_CASES_TAC \\ gs []
  >- ((* Ret *)
    gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
    \\ rename1 ‘thunk_rel x y’
    \\ simp [Once thunk_semanticsTheory.next_def]
    \\ rgs [Once next'_def, thunk_rel_def] \\ gvs []
    \\ Cases_on ‘k = 0’ \\ gs []
    >- (
      Cases_on ‘c’ \\ Cases_on ‘d’ \\ rgs []
      \\ rgs [force_apply_closure_def, force_def,
              thunk_rel_def, dest_anyThunk_def, subst_funs_def,
              apply_closure'_def]
      \\ ‘eval_wh e ≠ wh_Error’
        by (strip_tac \\ gs [])
      \\ drule_all_then assume_tac exp_rel_eval
      \\ Cases_on ‘eval_wh e’ \\ Cases_on ‘eval y’ \\ gvs []
      \\ rename1 ‘v_rel _ (INR w)’
      \\ Cases_on ‘w’ \\ gs [thunk_semanticsTheory.apply_closure_def,
                             dest_anyClosure_def])
    \\ reverse (Cases_on ‘c’) \\ Cases_on ‘d’ \\ gs []
    >- (
      first_x_assum irule \\ gs [thunk_rel_def])
    \\ gvs [force_apply_closure_def, force_def,
            thunk_rel_def, dest_anyThunk_def, subst_funs_def,
            apply_closure'_def]
    \\ ‘eval_wh e ≠ wh_Error’
      by (strip_tac \\ gs [])
    \\ drule_all_then assume_tac exp_rel_eval
    \\ Cases_on ‘eval_wh e’ \\ Cases_on ‘eval y’ \\ gs []
    \\ rename1 ‘v_rel _ (INR w)’
    \\ Cases_on ‘w’ \\ gs [thunk_semanticsTheory.apply_closure_def,
                           dest_anyClosure_def]
    \\ first_x_assum irule \\ gs []
    \\ irule exp_rel_eval
    \\ gs [pure_expTheory.bind_def, FLOOKUP_UPDATE, pure_expTheory.closed_def,
           freevars_subst1, EXTENSION, SUBSET_DEF, DISJ_EQ_IMP]
    \\ irule_at Any exp_rel_subst \\ gs []
    \\ fs [pure_expTheory.closed_def, EXTENSION]
    \\ strip_tac \\ gs [Once next'_def])
  \\ IF_CASES_TAC \\ gs []
  >- ((* Raise *)
    gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
    \\ rename1 ‘thunk_rel x y’
    \\ simp [Once thunk_semanticsTheory.next_def]
    \\ rgs [Once next'_def, thunk_rel_def] \\ gvs []
    \\ Cases_on ‘k = 0’ \\ gs []
    >- (
      Cases_on ‘c’ \\ Cases_on ‘d’ \\ rgs []
      \\ rgs [force_apply_closure_def, force_def,
              thunk_rel_def, dest_anyThunk_def, subst_funs_def,
              apply_closure'_def]
      \\ ‘eval_wh e ≠ wh_Error’
        by (strip_tac \\ gs [])
      \\ drule_all_then assume_tac exp_rel_eval
      \\ Cases_on ‘eval_wh e’ \\ Cases_on ‘eval y’ \\ gvs []
      \\ rename1 ‘v_rel _ (INR w)’
      \\ Cases_on ‘w’ \\ gs [thunk_semanticsTheory.apply_closure_def,
                             dest_anyClosure_def])
    \\ Cases_on ‘c’ \\ Cases_on ‘d’ \\ gs []
    >- (
      first_x_assum irule \\ gs [thunk_rel_def])
    \\ gvs [force_apply_closure_def, force_def,
            thunk_rel_def, dest_anyThunk_def, subst_funs_def,
            apply_closure'_def]
    \\ ‘eval_wh e ≠ wh_Error’
      by (strip_tac \\ gs [])
    \\ drule_all_then assume_tac exp_rel_eval
    \\ Cases_on ‘eval_wh e’ \\ Cases_on ‘eval y’ \\ gs []
    \\ rename1 ‘v_rel _ (INR w)’
    \\ Cases_on ‘w’ \\ gs [thunk_semanticsTheory.apply_closure_def,
                           dest_anyClosure_def]
    \\ first_x_assum irule \\ gs []
    \\ irule exp_rel_eval
    \\ gs [pure_expTheory.bind_def, FLOOKUP_UPDATE, pure_expTheory.closed_def,
           freevars_subst1, EXTENSION, SUBSET_DEF, DISJ_EQ_IMP]
    \\ irule_at Any exp_rel_subst \\ gs []
    \\ fs [pure_expTheory.closed_def, EXTENSION]
    \\ strip_tac \\ gs [Once next'_def])
  \\ IF_CASES_TAC \\ gs []
  >- ((* Bind *)
    simp [Once thunk_semanticsTheory.next_def]
    \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 2 ⇔ n = 1 ∨ n = 0”,
            SF DNF_ss]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule \\ gs []
    \\ gs [Once next'_def]
    \\ rename1 ‘thunk_rel x2 y2’
    \\ rename1 ‘v_rel (eval_wh x1) (force y1)’
    \\ ‘eval_wh x1 ≠ wh_Error’
      by (strip_tac \\ gs [Once next'_def])
    \\ gvs [thunk_rel_def, force_def, dest_anyThunk_def, subst_funs_def]
    \\ irule exp_rel_eval \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  >- ((* Handle *)
    simp [Once thunk_semanticsTheory.next_def]
    \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 2 ⇔ n = 1 ∨ n = 0”,
            SF DNF_ss]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule \\ gs []
    \\ gs [Once next'_def]
    \\ rename1 ‘thunk_rel x2 y2’
    \\ rename1 ‘v_rel (eval_wh x1) (force y1)’
    \\ ‘eval_wh x1 ≠ wh_Error’
      by (strip_tac \\ gs [Once next'_def])
    \\ gvs [thunk_rel_def, force_def, dest_anyThunk_def, subst_funs_def]
    \\ irule exp_rel_eval \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  >- ((* Act *)
    gs [Once thunk_semanticsTheory.next_def,
        Once next'_def]
    \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”, SF DNF_ss,
            pure_semanticsTheory.with_atom_def,
            pure_semanticsTheory.with_atoms_def,
            thunk_semanticsTheory.with_atoms_def]
    \\ IF_CASES_TAC \\ gs []
    \\ gvs [force_list_def, force_def, thunk_rel_def, dest_anyThunk_def,
            subst_funs_def]
    \\ drule_all_then assume_tac exp_rel_eval
    \\ rename1 ‘v_rel (eval_wh x) (eval y)’
    \\ IF_CASES_TAC \\ gs []
    >- (
      Cases_on ‘eval y’ \\ gs [v_rel_def])
    \\ Cases_on ‘eval_wh x’ \\ gs [pure_semanticsTheory.get_atoms_def]
    \\ CASE_TAC \\ gs []
    \\ namedCases_on ‘eval y’ ["a","a"] \\ gs []
    \\ Cases_on ‘a’ \\ gs [thunk_semanticsTheory.get_atoms_def]
    \\ CASE_TAC \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  >- ((* Alloc *)
    simp [Once thunk_semanticsTheory.next_def]
    \\ rgs [Once next'_def]
    \\ rgs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 2 ⇔ n = 0 ∨ n = 1”,
            SF DNF_ss, pure_semanticsTheory.with_atom_def,
            pure_semanticsTheory.with_atoms_def,
            thunk_semanticsTheory.with_atoms_def]
    \\ rename1 ‘thunk_rel x2 y2’
    \\ ‘eval_wh x2 ≠ wh_Error’
      by (strip_tac \\ gs [])
    \\ rgs [thunk_rel_def, force_list_def, force_def, dest_anyThunk_def,
            subst_funs_def] \\ gvs []
    \\ drule_all_then assume_tac exp_rel_eval
    \\ rename1 ‘v_rel (eval_wh x2) (eval y2)’
    \\ IF_CASES_TAC \\ gs []
    >- (
      Cases_on ‘eval y2’ \\ gs [])
    \\ Cases_on ‘eval_wh x2’ \\ gs [pure_semanticsTheory.get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    >- (
      namedCases_on ‘eval y2’ ["a", "a"] \\ gs []
      \\ Cases_on ‘a’ \\ gs [thunk_semanticsTheory.get_atoms_def]
      \\ CASE_TAC \\ gs [])
    \\ namedCases_on ‘eval y2’ ["a", "a"] \\ gs []
    \\ Cases_on ‘a’ \\ gvs [thunk_semanticsTheory.get_atoms_def]
    \\ first_x_assum irule
    \\ gs [state_rel_def, LIST_REL_REPLICATE_same, thunk_rel_def]
    \\ gs [LIST_REL_EL_EQN, exp_rel_rules])
  \\ IF_CASES_TAC \\ gs []
  >- ((* Length *)
    simp [Once thunk_semanticsTheory.next_def]
    \\ rgs [Once next'_def]
    \\ rgs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”, SF DNF_ss,
            pure_semanticsTheory.with_atom_def,
            pure_semanticsTheory.with_atoms_def,
            thunk_semanticsTheory.with_atoms_def]
    \\ rename1 ‘thunk_rel x y’
    \\ ‘eval_wh x ≠ wh_Error’
      by (strip_tac \\ gs [])
    \\ rgs [thunk_rel_def, force_list_def, force_def, dest_anyThunk_def,
            subst_funs_def] \\ gvs []
    \\ drule_all_then assume_tac exp_rel_eval
    \\ rename1 ‘v_rel (eval_wh x) (eval y)’
    \\ IF_CASES_TAC \\ gs []
    >- (
      Cases_on ‘eval y’ \\ gs [])
    \\ Cases_on ‘eval_wh x’ \\ gs [pure_semanticsTheory.get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    >- (
      namedCases_on ‘eval y’ ["a", "a"] \\ gs []
      \\ Cases_on ‘a’ \\ gs [thunk_semanticsTheory.get_atoms_def]
      \\ CASE_TAC \\ gs [state_rel_def, LIST_REL_EL_EQN])
    \\ namedCases_on ‘eval y’ ["a", "a"] \\ gs []
    \\ Cases_on ‘a’ \\ gvs [thunk_semanticsTheory.get_atoms_def]
    \\ ‘n < LENGTH t’
      by gs [state_rel_def, LIST_REL_EL_EQN, arithmeticTheory.NOT_LESS_EQUAL]
    \\ gs []
    \\ first_x_assum irule \\ gs []
    \\ gs [state_rel_def, thunk_rel_def, LIST_REL_EL_EQN, exp_rel_rules])
  \\ IF_CASES_TAC \\ gs []
  >- ((* Deref *)
    simp [Once thunk_semanticsTheory.next_def]
    \\ rgs [Once next'_def]
    \\ rgs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 2 ⇔ n = 0 ∨ n = 1”,
            SF DNF_ss]
    \\ rename1 ‘with_atom2 [x1; x2]’
    \\ rename1 ‘with_atoms [y1; y2]’
    \\ rgs [pure_semanticsTheory.with_atom_def,
            pure_semanticsTheory.with_atoms_def,
            thunk_semanticsTheory.with_atoms_def,
            pure_semanticsTheory.with_atom2_def]
    \\ rgs [thunk_rel_def, force_list_def, force_def, dest_anyThunk_def,
            subst_funs_def] \\ gvs []
    \\ ‘eval_wh x1 ≠ wh_Error’
      by (strip_tac \\ gs [])
    \\ drule_all_then assume_tac exp_rel_eval
    \\ ‘eval_wh x2 ≠ wh_Error’
      by (strip_tac \\ gs [])
    \\ drule_all_then assume_tac exp_rel_eval
    \\ rename1 ‘v_rel (eval_wh x1) (eval y1)’
    \\ rename1 ‘v_rel (eval_wh x2) (eval y2)’
    \\ gs []
    \\ IF_CASES_TAC \\ gs []
    >- (
      Cases_on ‘eval y1’ \\ gs [])
    >- (
      Cases_on ‘eval y2’ \\ gs []
      \\ Cases_on ‘eval y1’ \\ gs [])
    \\ Cases_on ‘eval_wh x1’ \\ Cases_on ‘eval_wh x2’
    \\ gs [pure_semanticsTheory.get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ ‘LENGTH s = LENGTH t’
      by gs [state_rel_def, LIST_REL_EL_EQN]
    \\ namedCases_on ‘eval y2’ ["a", "a"] \\ gs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ namedCases_on ‘eval y1’ ["a", "a"] \\ gs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ simp [thunk_semanticsTheory.get_atoms_def]
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    >- (
      IF_CASES_TAC \\ gs []
      \\ reverse IF_CASES_TAC \\ gs []
      \\ gs [state_rel_def, LIST_REL_EL_EQN]
      \\ first_x_assum irule
      \\ gs [arithmeticTheory.NOT_LESS_EQUAL]
      \\ first_x_assum drule
      \\ strip_tac
      \\ ‘Num i < LENGTH (EL n s)’
        by intLib.ARITH_TAC
      \\ first_x_assum (drule_then assume_tac) \\ gs [thunk_rel_def])
    >- (
      IF_CASES_TAC \\ gs []
      \\ first_x_assum irule \\ gs []
      \\ first_assum (irule_at Any)
      \\ first_assum (irule_at Any)
      \\ gs [thunk_rel_def]
      \\ ‘Cons "Subscript" [] = Cons "Subscript" (MAP Delay [])’
        by gs []
      \\ pop_assum SUBST1_TAC
      \\ simp [exp_rel_Cons])
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ gs [state_rel_def, LIST_REL_EL_EQN]
    \\ first_x_assum irule
    \\ first_assum (irule_at Any)
    \\ first_assum (irule_at Any) \\ gs []
    \\ gs [thunk_rel_def]
    \\ ‘Cons "Subscript" [] = Cons "Subscript" (MAP Delay [])’
      by gs []
    \\ pop_assum SUBST1_TAC
    \\ simp [exp_rel_Cons]
    \\ intLib.ARITH_TAC)
  \\ IF_CASES_TAC \\ gs []
  >- ((* Update *)
    simp [Once thunk_semanticsTheory.next_def]
    \\ rgs [Once next'_def]
    \\ rgs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 3 ⇔ n = 0 ∨ n = 1 ∨ n = 2”,
            SF DNF_ss]
    \\ rename1 ‘with_atom2 [x1; x2]’
    \\ rename1 ‘with_atoms [y1; y2]’
    \\ rgs [pure_semanticsTheory.with_atom_def,
            pure_semanticsTheory.with_atoms_def,
            thunk_semanticsTheory.with_atoms_def,
            pure_semanticsTheory.with_atom2_def]
    \\ rgs [thunk_rel_def, force_list_def, force_def, dest_anyThunk_def,
            subst_funs_def] \\ gvs []
    \\ ‘eval_wh x1 ≠ wh_Error’
      by (strip_tac \\ gs [])
    \\ drule_all_then assume_tac exp_rel_eval
    \\ ‘eval_wh x2 ≠ wh_Error’
      by (strip_tac \\ gs [])
    \\ drule_all_then assume_tac exp_rel_eval
    \\ rename1 ‘v_rel (eval_wh x1) (eval y1)’
    \\ rename1 ‘v_rel (eval_wh x2) (eval y2)’
    \\ rgs []
    \\ IF_CASES_TAC \\ gs []
    >- (
      Cases_on ‘eval y1’ \\ gs [])
    >- (
      Cases_on ‘eval y2’ \\ gs []
      \\ Cases_on ‘eval y1’ \\ gs [])
    \\ Cases_on ‘eval_wh x1’ \\ Cases_on ‘eval_wh x2’
    \\ gs [pure_semanticsTheory.get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ ‘LENGTH s = LENGTH t’
      by gs [state_rel_def, LIST_REL_EL_EQN]
    \\ namedCases_on ‘eval y2’ ["a", "a"] \\ gs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ namedCases_on ‘eval y1’ ["a", "a"] \\ gs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ simp [thunk_semanticsTheory.get_atoms_def]
    \\ IF_CASES_TAC \\ gs [arithmeticTheory.NOT_LESS_EQUAL]
    \\ IF_CASES_TAC \\ gs []
    >- (
      IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ gs [state_rel_def, LIST_REL_EL_EQN]
      \\ first_x_assum irule \\ gs []
      \\ reverse conj_tac
      >- (
        simp [thunk_rel_def]
        \\ ‘Cons "" [] = Cons "" (MAP Delay [])’
          by gs []
        \\ pop_assum SUBST1_TAC
        \\ simp [exp_rel_Cons])
      \\ qx_gen_tac ‘m’
      \\ rw [LENGTH_LUPDATE, EL_LUPDATE] \\ rw []
      \\ gs [thunk_rel_def])
    >- (
      IF_CASES_TAC \\ gs []
      \\ gs [state_rel_def, LIST_REL_EL_EQN]
      \\ first_x_assum irule \\ gs []
      \\ simp [thunk_rel_def]
      \\ ‘Cons "Subscript" [] = Cons "Subscript" (MAP Delay [])’
        by gs []
      \\ pop_assum SUBST1_TAC
      \\ simp [exp_rel_Cons]
      \\ intLib.ARITH_TAC)
    \\ IF_CASES_TAC \\ gs [arithmeticTheory.NOT_LESS_EQUAL, state_rel_def,
                           LIST_REL_EL_EQN]
    \\ first_x_assum irule \\ gs []
    \\ simp [thunk_rel_def]
    \\ ‘Cons "Subscript" [] = Cons "Subscript" (MAP Delay [])’
      by gs []
    \\ pop_assum SUBST1_TAC
    \\ simp [exp_rel_Cons]
    \\ intLib.ARITH_TAC)
  \\ rw [Once thunk_semanticsTheory.next_def]
QED

Theorem pure_to_thunk_next_action:
  v_rel v w ∧
  cont_rel c d ∧
  state_rel s t ⇒
  next_action' v c s ≠ Err ⇒
    next_rel (next_action' v c s) (next_action w d t)
Proof
  rw [thunk_semanticsTheory.next_action_def]
  \\ ‘∀k. next' k v c s ≠ Err’
    by (rpt strip_tac
        \\ qpat_x_assum ‘next_action' _ _ _ ≠ _’ mp_tac
        \\ rw [next_action'_def]
        \\ DEEP_INTRO_TAC some_intro \\ simp []
        \\ rw []
        >- (
          qpat_assum ‘_ = Err’ (SUBST1_TAC o SYM)
          \\ irule next'_next'
          \\ gs [])
        \\ qexists_tac ‘k’ \\ gs [])
  \\ rw [next_action'_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ simp [PULL_FORALL]
  \\ qx_gen_tac ‘i’
  \\ qx_gen_tac ‘j’
  \\ qx_gen_tac ‘k’
  \\ rw []
  >- (
    ‘next' j v c s ≠ Err’
      by gs []
    \\ ‘∀k. tnext_rel (next' k v c s) (next k v c s)’
      by (irule next'_thm
          \\ gs [tcont_rel_refl, tstate_rel_refl, tick_wh_rel_refl])
    \\ drule_all_then assume_tac pure_to_thunk_next
    \\ drule_then (qspec_then ‘j’ mp_tac) next_next
    \\ impl_tac \\ rw []
    \\ strip_tac \\ gs []
    \\ Cases_on ‘next' j v c s’ \\ gs [])
  \\ ‘next' i v c s ≠ Err’
    by gs []
  \\ ‘∀k. tnext_rel (next' k v c s) (next k v c s)’
    by (irule next'_thm
        \\ gs [tcont_rel_refl, tstate_rel_refl, tick_wh_rel_refl])
  \\ gs []
  \\ ‘next' i v c s ≠ Err’
    by gs []
  \\ drule_all_then assume_tac pure_to_thunk_next \\ gs []
  \\ ‘next' k v c s ≠ Err’
    by gs []
  \\ drule_all_then assume_tac pure_to_thunk_next \\ gs []
QED

Theorem pure_to_thunk_interp[local]:
  v_rel v w ∧
  cont_rel c d ∧
  state_rel s t ∧
  safe_itree (interp v c s) ⇒
    interp v c s = interp w d t
Proof
  strip_tac
  \\ ‘interp v c s = interp_alt v c s’
    by (rw [Once EQ_SYM_EQ]
        \\ irule_at Any interp_alt_thm
        \\ simp [tick_wh_rel_refl, tcont_rel_refl, tstate_rel_refl])
  \\ pop_assum SUBST_ALL_TAC
  \\ rw [Once io_treeTheory.io_bisimulation]
  \\ qexists_tac ‘
    λt1 t2.
      safe_itree t1 ∧
      (t1 = t2 ∨
       ∃v c s w d t.
         t1 = interp_alt v c s ∧
         t2 = interp w d t ∧
         interp_alt v c s ≠ Ret Error ∧
         v_rel v w ∧
         cont_rel c d ∧ state_rel s t)’
  \\ rw []
  >- (
    disj2_tac
    \\ irule_at Any EQ_REFL
    \\ irule_at Any EQ_REFL \\ gs []
    \\ strip_tac
    \\ gs [Once safe_itree_cases])
  >- (
    ‘next_action' v' c' s' ≠ Err’
      by (strip_tac
          \\ qpat_x_assum ‘interp_alt v' _ _ ≠ _’ mp_tac
          \\ rw [Once interp_alt_def])
    \\ drule_all_then assume_tac pure_to_thunk_next_action
    \\ qpat_x_assum ‘Ret _ = _’ mp_tac
    \\ once_rewrite_tac [thunk_semanticsTheory.interp_def, interp_alt_def]
    \\ Cases_on ‘next_action' v' c' s'’
    \\ Cases_on ‘next_action w' d' t''’ \\ gvs [])
  >- (
    ‘next_action' v' c' s' ≠ Err’
      by (strip_tac
          \\ qpat_x_assum ‘interp_alt v' _ _ = _’ mp_tac
          \\ rw [Once interp_alt_def])
    \\ drule_all_then assume_tac pure_to_thunk_next_action
    \\ qpat_x_assum ‘_ = Div’ mp_tac
    \\ once_rewrite_tac [thunk_semanticsTheory.interp_def, interp_alt_def]
    \\ Cases_on ‘next_action' v' c' s'’
    \\ Cases_on ‘next_action w' d' t''’ \\ gvs [])
  >- (
    rgs [Once safe_itree_cases])
  \\ ‘next_action' v' c' s' ≠ Err’
    by (strip_tac
        \\ qpat_x_assum ‘interp_alt v' _ _ ≠ _’ mp_tac
        \\ rw [Once interp_alt_def])
  \\ drule_all_then assume_tac pure_to_thunk_next_action
  \\ qpat_x_assum ‘Vis _ _ = _’ mp_tac
  \\ rw [Once interp_alt_def, Once thunk_semanticsTheory.interp_def]
  \\ Cases_on ‘next_action' v' c' s'’
  \\ Cases_on ‘next_action w' d' t''’ \\ gvs []
  \\ rgs [Once safe_itree_cases]
  \\ rw [] \\ CASE_TAC \\ gs [] \\ rw []
  \\ disj2_tac
  \\ irule_at Any EQ_REFL
  \\ irule_at Any EQ_REFL \\ gs []
  \\ simp [thunk_rel_def, exp_rel_Prim]
  \\ strip_tac
  \\ first_x_assum (qspec_then ‘INR y’ assume_tac)
  \\ rgs [Once safe_itree_cases]
QED

Theorem semantics_fail[local]:
  safe_itree (semantics x c s) ⇒
    eval_wh x ≠ wh_Error
Proof
  simp [pure_semanticsTheory.semantics_def,
        Once pure_semanticsTheory.interp_def,
        pure_semanticsTheory.next_action_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ rw [] \\ strip_tac \\ gs []
  \\ rgs [Once pure_semanticsTheory.next_def]
  \\ rgs [Once safe_itree_cases]
QED

Theorem pure_to_thunk_semantics:
  exp_rel x y ∧
  closed x ∧
  safe_itree (semantics x Done []) ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ drule_then assume_tac semantics_fail
  \\ gs [pure_semanticsTheory.semantics_def,
         thunk_semanticsTheory.semantics_def]
  \\ irule pure_to_thunk_interp \\ gs []
  \\ simp [state_rel_def]
  \\ irule exp_rel_eval \\ gs []
QED

val _ = export_theory ();

