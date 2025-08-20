(*
  Proof of correctness for the pure_to_thunk compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax dep_rewrite
     intLib;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     pure_semanticsTheory thunk_semanticsTheory thunk_semantics_delayedTheory
     pure_evalTheory pure_configTheory thunkLang_primitivesTheory
     pure_exp_lemmasTheory pure_miscTheory;

val _ = new_theory "pure_to_thunk_1Proof";

val _ = set_grammar_ancestry ["finite_map", "pred_set", "rich_list",
                              "pure_semantics", "thunk_semantics",
                              "thunk_semantics_delayed", "pure_exp_lemmas",
                              "pure_misc", "pure_config"];

val _ = numLib.prefer_num ();

(*
  NOTES ON COMPILING PURELANG TO THUNKLANG:

  thunkLang-pureLang simulation.

  As pureLang is lazy it allows non-functional value declarations that are
  mutually recursive, and lazy value declarations. All such computations are
  suspended thunkLang-side by Lam or Delay. This relation (exp_rel) acts as
  if the compiler inserted Delay everywhere.

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
  * [Monad]
    - `Ret`/`Raise` have their arguments delayed, so that future call-by-value applications to `Bind` produce the correct semantics.
        Ret e   --> Ret (Delay e)
        Raise e --> Raise (Delay e)
    - `Act`/`Length` must delay their return values to maintain this invariant:
        Act e    --> Bind (Act e) (λv. Ret (Delay v))
        Length e --> Bind (Length e) (λv. Ret (Delay v))
    - `Alloc` also delays its return value, but must further ensure that items stored in arrays are delayed to match PureLang's call-by-name arrays.
        Alloc n e --> Bind (Alloc n (Delay e)) (λv. Ret (Delay v))`
    - `Deref` delays its potential exception to align with the `Ret`/`Raise` invariant:
        Deref l e --> Handle (Deref l e) (λv. Raise (Delay v))
    - `Update` delays three things: the element it stores, its return value, and its potential exception
        Update l n e -->
          Bind
            (Handle (Update l n (Delay e)) (λv. Raise (Delay v)))
            (λv. Ret (Delay v))
    - `Bind`/`Handle` are straightforwardly compiled
  * [Letrec]
    - We expect all expressions in the list of bindings to be suspended by
      something (either Lam or Delay), so we insert Delay everywhere.
 *)

Overload Suspend[local] = “λx. Force (Value (Thunk x))”;

Overload Rec[local] = “λf n. Force (Value (Recclosure f n))”;


(* Simple monadic operation mapping *)
Inductive mop_rel:
  mop_rel "Bind" pure_config$Bind ∧
  mop_rel "Handle" Handle
End

(* Ret/Raise require a Delay operation *)
Inductive mop_ret_rel:
  mop_ret_rel "Ret" pure_config$Ret ∧
  mop_ret_rel "Raise" Raise
End

(* Length/Alloc/Act require wrapping in a `Ret $ Delay` *)
Inductive mop_delay_rel:
  mop_delay_rel "Length" pure_config$Length NONE ∧
  mop_delay_rel "Alloc" Alloc (SOME 1n) ∧
  mop_delay_rel "Act" Act NONE
End

(* Deref / Update handled separately *)

val mop_cases_ss = simpLib.named_rewrites "mop_cases_ss" [
                    mop_rel_cases, mop_ret_rel_cases, mop_delay_rel_cases];
val mop_cases = SF mop_cases_ss;

Definition opt_delay_arg_def[simp]:
  opt_delay_arg NONE ys = ys ∧
  opt_delay_arg (SOME idx) ys = LUPDATE (Delay $ EL idx ys) idx ys
End

Inductive exp_rel:
[exp_rel_Value_Rec:]
  (∀f g x y n.
     LIST_REL (\(fn, x) (gn, y). fn = gn ∧ exp_rel x y ∧
                                 freevars x SUBSET set (MAP FST f)) f g ∧
     ALOOKUP (REVERSE f) n = SOME x ∧
     ALOOKUP (REVERSE g) n = SOME y ⇒
       exp_rel (Letrec f x) (Rec (MAP (λ(gn, y). (gn, Delay y)) g) n))
[exp_rel_Value_Suspend:]
  (∀x y.
     exp_rel x y ∧
     closed x ⇒
       exp_rel (Tick x) (Suspend y))
[exp_rel_Var:]
  (∀n.
     exp_rel (pure_exp$Var n) (Force (Var n)))
[exp_rel_Lam:]
  (∀s x y.
     exp_rel x y ⇒
       exp_rel (Lam s x) (Lam s y))
[exp_rel_App:]
  (∀f g x y.
     exp_rel f g ∧
     exp_rel x y ⇒
       exp_rel (App f (Tick x)) (App g (Delay y)))
[exp_rel_Let:]
  (∀s x y x1 y1.
     exp_rel x y ∧ exp_rel x1 y1 ⇒
       exp_rel (Let s (Tick x) x1) (Let (SOME s) (Delay y) y1))
[exp_rel_If:]
  (∀x1 y1 z1 x2 y2 z2.
     LIST_REL exp_rel [x1; y1; z1] [x2; y2; z2] ⇒
       exp_rel (If x1 y1 z1) (If x2 y2 z2))
[exp_rel_Cons:]
  (∀n xs ys.
     n ∉ monad_cns ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Cons n xs) (Prim (Cons n) (MAP Delay ys)))
[exp_rel_LitVal:]
  (exp_rel (Lit l) (Value (Atom l)))
[exp_rel_ConsVal:]
  (cn ∉ monad_cns ⇒ exp_rel (Cons cn []) (Value (Constructor cn [])))
[exp_rel_Monad:]
  (∀n mop xs ys.
     mop_rel n mop ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Cons n xs) (Monad mop ys))
[exp_rel_Monad_Ret:]
  (∀n mop xs ys.
     mop_ret_rel n mop ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Cons n xs) (Monad mop (MAP Delay ys)))
[exp_rel_Monad_Delay:]
  (∀n mop idopt xs ys.
     mop_delay_rel n mop idopt ∧ (∀idx. idopt = SOME idx ⇒ idx < LENGTH xs) ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Cons n xs) (Monad mop (opt_delay_arg idopt ys)))
[exp_rel_Deref:]
  (∀xs ys.
     LIST_REL exp_rel xs ys ⇒
        exp_rel (Cons "Deref" xs) (Monad Deref ys))
[exp_rel_Update:]
  (∀xs ys.
     LIST_REL exp_rel xs ys ∧ 2 < LENGTH xs ⇒
        exp_rel (Cons "Update" xs) (Monad Update (opt_delay_arg (SOME 2n) ys)))
[exp_rel_Proj:]
  (∀s i xs ys.
     LIST_REL exp_rel xs ys ∧ s ∉ monad_cns ⇒
       exp_rel (Prim (Proj s i) xs) (Force (Prim (Proj s i) ys)))
[exp_rel_Seq:]
  (∀x1 x2 y1 y2.
     LIST_REL exp_rel [x1; y1] [x2; y2] ⇒
       exp_rel (Seq x1 y1) (Let NONE x2 y2))
[exp_rel_Seq_fresh:]
  (∀x1 x2 y1 y2 fresh.
     LIST_REL exp_rel [x1; y1] [x2; y2] ∧
     fresh ∉ freevars y1 ⇒
       exp_rel (Seq x1 y1) (Let (SOME fresh) x2 y2))
[exp_rel_Prim:]
  (∀op xs ys.
     op ≠ If ∧
     op ≠ Seq ∧
     (∀n. op ≠ Cons n) ∧
     (∀s i. op ≠ Proj s i) ∧
     (∀s i a. op = IsEq s i a ⇒ a) ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim op xs) (Prim op ys))
[exp_rel_Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn, x) (gn, y). fn = gn ∧ exp_rel x y) f g ∧
     exp_rel x y ⇒
       exp_rel (Letrec f x) (Letrec (MAP (λ(gn, x). (gn, Delay x)) g) y))
End

Definition thunk_rel_def:
  thunk_rel x v ⇔
    ∃y. v = Thunk y ∧
        exp_rel x y ∧
        closed x
End

Definition v_rel_def[simp]:
  v_rel wh_Error (INL Type_error) = T ∧
  v_rel wh_Diverge (INL Diverge) = T ∧
  v_rel (wh_Closure s x) (INR (Closure t y)) =
    (s = t ∧ exp_rel x y ∧ freevars x ⊆ {s}) ∧
  v_rel (wh_Constructor s xs) (INR (Constructor t ys)) =
    (s = t ∧ s ∉ monad_cns ∧ LIST_REL thunk_rel xs ys ∧ EVERY closed xs) ∧
  v_rel (wh_Constructor s xs) (INR (Monadic mop ys)) =
    (EVERY closed xs ∧ (
     mop_rel s mop ∧ LIST_REL exp_rel xs ys ∨
     (∃zs.
        mop_ret_rel s mop ∧
        LIST_REL exp_rel xs zs ∧ ys = MAP Delay zs) ∨
     (∃zs.
        mop_ret_rel s mop ∧
        LIST_REL thunk_rel xs zs ∧ ys = MAP (λz. Value z) zs) ∨
     (∃mop' idopt zs.
        mop = mop' ∧
        ys = opt_delay_arg idopt zs ∧
        mop_delay_rel s mop' idopt ∧
        (∀idx. idopt = SOME idx ⇒ idx < LENGTH xs) ∧
        LIST_REL exp_rel xs zs) ∨
     (∃zs.
        s = "Deref" ∧ mop = Deref ∧
        ys = zs ∧
        LIST_REL exp_rel xs zs) ∨
     (∃zs.
        s = "Update" ∧ mop = Update ∧
        ys = opt_delay_arg (SOME 2) zs ∧
        LIST_REL exp_rel xs zs ∧ 2 < LENGTH xs)
     )) ∧
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
       s ∉ monad_cns ∧
       EVERY closed xs ∧
       LIST_REL thunk_rel xs ys) ∧
  v_rel x (INR (Monadic mop zs)) =
    (∃xs s.
       x = wh_Constructor s xs ∧
       EVERY closed xs ∧
       (mop_rel s mop ∧ LIST_REL exp_rel xs zs ∨
       (∃ys.
          mop_ret_rel s mop ∧
          LIST_REL exp_rel xs ys ∧ zs = MAP Delay ys) ∨
       (∃ys.
          mop_ret_rel s mop ∧
          LIST_REL thunk_rel xs ys ∧ zs = MAP (λz. Value z) ys) ∨
       (∃mop' idopt ys.
          mop = mop' ∧
          zs = opt_delay_arg idopt ys ∧
          mop_delay_rel s mop' idopt ∧
          (∀idx. idopt = SOME idx ⇒ idx < LENGTH xs) ∧
          LIST_REL exp_rel xs ys) ∨
       (∃ys.
          s = "Deref" ∧ mop = Deref ∧
          zs = ys ∧
          LIST_REL exp_rel xs ys) ∨
       (∃ys.
          s = "Update" ∧ mop = Update ∧
          zs = opt_delay_arg (SOME 2) ys ∧
          LIST_REL exp_rel xs ys ∧ 2 < LENGTH xs)
         )) ∧
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
  \\ imp_res_tac pure_expTheory.exp_size_lemma \\ fs []
QED

Triviality LIST_REL_IMP_MAP_FST_EQ:
  ∀f g. LIST_REL P f g ∧ (∀x y. P x y ⇒ FST x = FST y) ⇒
        MAP FST f = MAP FST g
Proof
  Induct \\ fs [PULL_EXISTS]
QED

Triviality IMP_UNION_DIFF_EQ_EMPTY:
  x ⊆ z ∧ y ⊆ z ⇒ x ∪ y DIFF z = ∅
Proof
  fs [SUBSET_DEF,EXTENSION]
  \\ metis_tac []
QED

Triviality IMP_BIGUNION_SUBSET:
  (∀x. x IN s ⇒ x SUBSET z) ⇒ BIGUNION s SUBSET z
Proof
  fs [SUBSET_DEF,PULL_EXISTS] \\ metis_tac []
QED

Triviality LIST_REL_ALOOKUP_REVERSE_IMP:
  ∀f g.
    LIST_REL P f g ∧ MAP FST f = MAP FST g ∧
    ALOOKUP (REVERSE f) n = SOME x ∧
    ALOOKUP (REVERSE g) n = SOME y ⇒
    P (n,x) (n,y)
Proof
  Induct using SNOC_INDUCT \\ fs []
  \\ strip_tac \\ Cases using SNOC_CASES
  \\ fs [LIST_REL_SNOC,REVERSE_SNOC]
  \\ rename [‘FST a = FST b’]
  \\ PairCases_on ‘a’ \\ PairCases_on ‘b’
  \\ fs [] \\ rw [] \\ fs []
  \\ res_tac \\ fs []
QED

Theorem exp_rel_freevars:
  ∀x y. exp_rel x y ⇒ freevars x = freevars y
Proof
  ho_match_mp_tac exp_rel_ind \\ rw []
  \\ fs [freevars_def, pure_expTheory.closed_def, DELETE_DEF,
         AC UNION_COMM UNION_ASSOC, MAP_MAP_o, combinTheory.o_DEF]
  >- (
    drule LIST_REL_IMP_MAP_FST_EQ \\ fs [FORALL_PROD] \\ strip_tac
    \\ irule IMP_UNION_DIFF_EQ_EMPTY
    \\ irule_at Any IMP_BIGUNION_SUBSET
    \\ conj_asm1_tac >-
     (fs [MEM_MAP,PULL_EXISTS,FORALL_PROD] \\ rw []
      \\ drule_all LIST_REL_MEM
      \\ fs [EXISTS_PROD] \\ rw [] \\ fs [])
    \\ pop_assum irule
    \\ drule_all LIST_REL_ALOOKUP_REVERSE_IMP
    \\ fs [MEM_MAP,EXISTS_PROD]
    \\ rw []
    \\ imp_res_tac ALOOKUP_MEM \\ fs []
    \\ first_x_assum $ irule_at Any \\ fs [])
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
    \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE, COND_RAND, freevars_def]
    )
  >- (
    ntac 2 AP_TERM_TAC >> irule LIST_EQ >>
    Cases_on `idopt` >>
    gvs [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE, COND_RAND, freevars_def]
    )
  >- (
    AP_TERM_TAC \\ AP_TERM_TAC
    \\ irule LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP])
  >- (
    ntac 2 AP_TERM_TAC >> irule LIST_EQ >>
    gvs [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE, COND_RAND, freevars_def]
    )
  >- (
    AP_TERM_TAC \\ AP_TERM_TAC
    \\ irule LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP])
  >- (fs [EXTENSION] \\ metis_tac [])
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

Triviality subst1_opt_delay_arg:
  ∀ys idopt n e.
  (∀idx. idopt = SOME idx ⇒ idx < LENGTH ys) ⇒
  MAP (subst1 n e) (opt_delay_arg idopt ys) =
  opt_delay_arg idopt (MAP (subst1 n e) ys)
Proof
  Induct >> Cases_on `idopt` >> rw[opt_delay_arg_def, LUPDATE_DEF, subst_def] >>
  simp[LUPDATE_MAP, subst_def] >>
  Cases_on `x` >> gvs[EL_MAP]
QED

Theorem exp_rel_subst:
  ∀x y a b n s.
    exp_rel x y ∧
    exp_rel a b ∧
    closed a ⇒
      exp_rel (subst1 n (Tick a) x)
              (subst1 n (Thunk b) y)
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
    >- ( (* Value $ Atom *)
      simp[subst1_def] >> simp[Once exp_rel_cases]
      )
    >- ( (* Unit *)
      simp[subst1_def] >> simp[Once exp_rel_cases]
      )
    >- ( (* Monad - mop_rel *)
      simp[subst_single_def, subst1_def] >>
      rw[Once exp_rel_cases] >> disj1_tac >>
      gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS] >> rw[EL_MAP]
      )
    >- ( (* Monad - mop_ret_rel *)
      simp[subst_single_def, subst1_def] >>
      rw[Once exp_rel_cases] >> gvs[mop_cases] >>
      qrefine `MAP f ys` >> simp[MAP_MAP_o, combinTheory.o_DEF, subst1_def] >>
      irule_at Any EQ_REFL >> gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP]
      )
    >- ( (* Monad - mop_delay_rel *)
      simp[subst_single_def, subst1_def] >>
      DEP_REWRITE_TAC[subst1_opt_delay_arg] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      rw[Once exp_rel_cases] >> gvs[mop_cases]
      >- gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP]
      >- (
        irule_at Any EQ_REFL >>
        gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP]
        )
      >- gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP]
      )
    >- ( (* Deref *)
      simp[subst_single_def, subst1_def] >>
      DEP_REWRITE_TAC[subst1_opt_delay_arg] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      rw[Once exp_rel_cases] >> gvs[mop_cases]
      >- gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP] >>
      irule_at Any EQ_REFL >>
      gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP]
      )
    >- ( (* Update *)
      simp[subst_single_def, subst1_def] >>
      simp[LUPDATE_MAP, subst_def] >>
      rw[Once exp_rel_cases] >> gvs[mop_cases] >>
      qrefine `MAP foo ys` >> imp_res_tac LIST_REL_LENGTH >> gvs[EL_MAP] >>
      simp[SF ETA_ss] >> irule_at Any EQ_REFL >>
      gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP]
      )
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
    >- ((* Seq fresh *)
      simp [subst_single_def, subst1_def]
      \\ irule exp_rel_Seq_fresh \\ fs []
      \\ fs [SF DNF_ss]
      \\ DEP_REWRITE_TAC [pure_exp_lemmasTheory.freevars_subst]
      \\ fs [FRANGE_FUPDATE,pure_expTheory.closed_def]
      \\ rw [] \\ fs [pure_exp_lemmasTheory.subst1_ignore])
    >- ((* Others *)
      simp [subst_single_def, subst1_def]
      \\ rw [Once exp_rel_cases, EVERY2_MAP]
      \\ gvs [LIST_REL_EL_EQN] \\ rw []
      \\ last_x_assum irule \\ fs [MEM_EL]
      \\ irule_at Any EQ_REFL \\ fs []))
  >- ((* App *)
    qpat_x_assum ‘exp_rel (App _ _) _’ mp_tac
    \\ rw [Once exp_rel_cases]
    >- (qmatch_asmsub_rename_tac ‘exp_rel f g’
        \\ qmatch_asmsub_rename_tac ‘exp_rel x y’
        \\ simp [subst_single_def, subst1_def]
        \\ irule exp_rel_App \\ fs []
        \\ first_x_assum irule
        \\ fs [pure_expTheory.exp_size_def])
    \\ fs [subst_single_def, subst1_def]
    \\ irule exp_rel_Let
    \\ last_x_assum $ irule_at Any \\ fs []
    \\ rw [pure_expTheory.exp_size_def]
    \\ first_x_assum $ drule_at $ Pos last
    \\ disch_then $ drule_at $ Pos last
    \\ simp [Once exp_rel_cases,PULL_EXISTS]
    \\ disch_then $ qspec_then ‘n’ drule \\ fs []
    \\ disch_then $ qspec_then ‘n’ mp_tac \\ fs []
    \\ fs [subst_single_def, subst1_def]
    \\ simp [Once exp_rel_cases,PULL_EXISTS])
  >- ((* Lam *)
    qpat_x_assum ‘exp_rel (Lam n x) _’ mp_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [subst_single_def, subst1_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ irule exp_rel_Lam \\ fs [])
  >- ((* Letrec *)
    qpat_x_assum ‘exp_rel (Letrec _ _) _’ mp_tac
    \\ rw [Once exp_rel_cases]
    >~ [‘Rec _ _’] >-
     (fs [subst_single_def, subst1_def]
      \\ IF_CASES_TAC \\ fs []
      >- (irule exp_rel_Value_Rec \\ fs [])
      \\ qsuff_tac ‘subst1 n (Tick a) x = x ∧
                    MAP (λ(g,z). (g,subst1 n (Tick a) z)) lcs = lcs’
      >- (fs [] \\ rw [] \\ irule exp_rel_Value_Rec \\ fs [])
      \\ irule_at Any pure_miscTheory.MAP_ID_ON
      \\ simp [FORALL_PROD] \\ rw []
      \\ imp_res_tac ALOOKUP_MEM \\ gvs []
      \\ imp_res_tac LIST_REL_MEM
      \\ fs [UNCURRY] \\ gvs []
      \\ irule pure_exp_lemmasTheory.subst1_ignore
      \\ fs [SUBSET_DEF]
      \\ CCONTR_TAC \\ res_tac \\ fs [])
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

Triviality subst_opt_delay_arg:
  ∀ys idopt s.
  (∀idx. idopt = SOME idx ⇒ idx < LENGTH ys) ⇒
  MAP (λe. subst s e) (opt_delay_arg idopt ys) =
  opt_delay_arg idopt (MAP (λe. subst s e) ys)
Proof
  Induct >> Cases_on `idopt` >> rw[opt_delay_arg_def, LUPDATE_DEF, subst_def] >>
  simp[LUPDATE_MAP, subst_def] >>
  Cases_on `x` >> gvs[EL_MAP]
QED

Theorem exp_rel_subst_list[local]:
  ∀x f g y ks.
    LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel x y ∧
                              freevars x ⊆ set (MAP FST f)) f g ∧
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
  \\ ‘MAP FST f = MAP FST g’ by (drule LIST_REL_IMP_MAP_FST_EQ \\ fs [FORALL_PROD])
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
  >- simp[Once exp_rel_cases]
  >- simp[Once exp_rel_cases]
  >- ( (* Monad - mop_rel *)
    rw[Once exp_rel_cases] >> disj1_tac >>
    gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS] >> rw[EL_MAP] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
    )
  >- ( (* Monad - mop_ret_rel *)
    rw[Once exp_rel_cases] >> gvs[mop_cases] >>
    qrefine `MAP foo ys` >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, subst_def] >>
    irule_at Any EQ_REFL >> gvs[LIST_REL_EL_EQN, EL_MAP, MEM_EL, PULL_EXISTS]
    )
  >- ( (* Monad - mop_delay_rel *)
    rw[Once exp_rel_cases] >> gvs[mop_cases] >>
    gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP] >>
    simp[GSYM FILTER_REVERSE, ALOOKUP_FILTER] >>
    simp[LUPDATE_MAP, subst_def, SF ETA_ss] >>
    qmatch_goalsub_abbrev_tac `Delay (subst subs _)` >>
    qexists `MAP (subst subs) ys` >> simp[EL_MAP] >>
    unabbrev_all_tac >> gvs[]
    )
  >- ( (* Deref *)
    rw[Once exp_rel_cases] >> gvs[mop_cases] >>
    gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP] >>
    simp[GSYM FILTER_REVERSE, ALOOKUP_FILTER] >>
    simp[LUPDATE_MAP, subst_def] >>
    qmatch_goalsub_abbrev_tac `Delay (subst subs _)` >>
    qexists `MAP (subst subs) ys` >>
    unabbrev_all_tac >> gvs[EL_MAP, SF ETA_ss]
    )
  >- ( (* Update *)
    rw[Once exp_rel_cases] >> gvs[mop_cases] >>
    gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP] >>
    simp[GSYM FILTER_REVERSE, ALOOKUP_FILTER] >>
    simp[LUPDATE_MAP, subst_def] >>
    qmatch_goalsub_abbrev_tac `Delay (subst subs _)` >>
    qexists `MAP (subst subs) ys` >>
    unabbrev_all_tac >> gvs[EL_MAP, SF ETA_ss]
    )
  >- ((* Proj *)
    irule exp_rel_Proj
    \\ fs [EVERY2_MAP, LIST_REL_EL_EQN]
    \\ rw [] \\ gvs [EL_MEM])
  >- ((* Seq *)
    irule exp_rel_Seq \\ fs [SF DNF_ss]
    \\ first_x_assum irule \\ fs []
    \\ first_assum (irule_at Any))
  >- ((* Seq fresh *)
    irule exp_rel_Seq_fresh \\ fs [SF DNF_ss]
    \\ DEP_REWRITE_TAC [pure_exp_lemmasTheory.freevars_subst] \\ fs []
    \\ conj_tac
    >-
     (ho_match_mp_tac finite_mapTheory.IN_FRANGE_FUPDATE_LIST_suff
      \\ fs [MEM_MAP,PULL_EXISTS,MEM_FILTER,EXISTS_PROD,FORALL_PROD,EVERY_MEM]
      \\ rw [] \\ drule_all LIST_REL_MEM
      \\ fs [EXISTS_PROD] \\ rw [])
    \\ first_x_assum drule_all
    \\ disch_then $ qspec_then ‘fresh INSERT ks’ mp_tac
    \\ match_mp_tac $ METIS_PROVE []
          “x = x1 ∧ m = m1 ⇒ exp_rel x (subst m y) ⇒ exp_rel x1 (subst m1 y)”
    \\ reverse conj_tac
    >- fs [FILTER_MAP,FILTER_FILTER,LAMBDA_PROD,combinTheory.o_DEF]
    \\ once_rewrite_tac [pure_exp_lemmasTheory.subst_FDIFF]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ fs [finite_mapTheory.fmap_eq_flookup,FLOOKUP_DRESTRICT]
    \\ rw [] \\ fs [alistTheory.flookup_fupdate_list]
    \\ qabbrev_tac ‘ff = Letrec f’ \\ pop_assum kall_tac
    \\ fs [GSYM MAP_REVERSE,GSYM FILTER_REVERSE]
    \\ qspec_tac (‘REVERSE f’,‘xs’)
    \\ Induct \\ fs [FORALL_PROD,AllCaseEqs()]
    \\ rw [] \\ CCONTR_TAC \\ fs []
    \\ gvs [AllCaseEqs()]
    \\ metis_tac [])
  \\ irule exp_rel_Prim \\ fs [EVERY2_MAP]
  \\ conj_tac >- fs []
  \\ irule LIST_REL_mono
  \\ first_assum (irule_at Any) \\ rw []
  )
  >- ((* App *)
  pop_assum mp_tac
  \\ rw [Once exp_rel_cases]
  >- (rw [subst_def, pure_expTheory.subst_def]
      \\ irule exp_rel_App \\ fs []
      \\ first_x_assum irule
      \\ fs [pure_expTheory.exp_size_def])
  \\ fs [subst_def, pure_expTheory.subst_def]
  \\ irule exp_rel_Let \\ fs []
  \\ first_x_assum drule
  \\ simp [Once exp_rel_cases,PULL_EXISTS]
  \\ disch_then drule
  \\ simp [Once exp_rel_cases,PULL_EXISTS]
  \\ fs [subst_def, pure_expTheory.subst_def,pure_expTheory.exp_size_def])
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
  \\ rename [‘Letrec’]
  \\ pop_assum mp_tac
  \\ rw [Once exp_rel_cases]
  \\ rw [subst_def, pure_expTheory.subst_def, exp_rel_Value_Suspend]
  >~ [‘Rec _ _’] >-
   (irule exp_rel_Value_Rec \\ fs []
    \\ simp [GSYM MAP_REVERSE, ALOOKUP_MAP]
    \\ simp [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD]
    \\ fs [EVERY2_MAP, LAMBDA_PROD, LIST_REL_EL_EQN] \\ rw []
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename1 ‘EL m lcs’
    \\ ‘MEM (EL m lcs) lcs’ by fs [EL_MEM]
    \\ first_x_assum (drule_all_then assume_tac) \\ gs []
    \\ qpat_abbrev_tac ‘e1 = subst _ e’
    \\ qsuff_tac ‘e1 = e’
    >- (‘MAP (λ(p1,p2). p1) lcs = MAP FST lcs’ by fs [MAP_EQ_f,FORALL_PROD] \\ fs [])
    \\ unabbrev_all_tac
    \\ irule pure_exp_lemmasTheory.subst_ignore
    \\ fs [IN_DISJOINT,SUBSET_DEF]
    \\ metis_tac [])
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
  \\ simp [FILTER_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
QED

Theorem exp_rel_subst_funs:
  ∀x f g y ks.
    LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel x y ∧ freevars x ⊆ set (MAP FST f)) f g ∧
    exp_rel x y ⇒
    exp_rel (subst_funs f x)
            (subst_funs (MAP (λ(gn, x). (gn, Delay x)) g) y)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ simp [subst_funs_def, pure_expTheory.subst_funs_def,
           pure_expTheory.bind_def]
  \\ IF_CASES_TAC \\ fs []
  >- (drule_all_then (qspec_then ‘EMPTY’ mp_tac) exp_rel_subst_list
      \\ simp [FILTER_T, GSYM LAMBDA_PROD])
  \\ ‘F’ suffices_by rw []
  \\ pop_assum mp_tac \\ simp []
  \\ fs [flookup_fupdate_list, FILTER_MAP, GSYM MAP_REVERSE, ALOOKUP_MAP,
         CaseEq "option"]
  \\ simp [EVERY_MAP, LAMBDA_PROD, EVERY_FILTER]
  \\ ‘MAP FST f = MAP FST g’ by (drule LIST_REL_IMP_MAP_FST_EQ \\ fs [FORALL_PROD])
  \\ fs [EVERY_MEM,FORALL_PROD] \\ rw []
  \\ imp_res_tac ALOOKUP_MEM \\ fs []
  \\ imp_res_tac LIST_REL_MEM \\ fs [EXISTS_PROD]
  \\ rw [] \\ gvs [UNCURRY]
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
    >-
     (Cases_on ‘eval_wh_to k x = wh_Error’ \\ fs []
      \\ first_x_assum (drule_then assume_tac)
      \\ ‘∃res. eval_to k g = INR res’
        by (Cases_on ‘eval_to k g’ \\ gs []
            \\ Cases_on ‘eval_wh_to k x’ \\ fs [])
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
    \\ fs [eval_wh_to_def,eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum irule
    \\ imp_res_tac exp_rel_closed \\ gvs []
    \\ fs [pure_expTheory.bind_def, FLOOKUP_UPDATE]
    \\ irule_at Any exp_rel_subst \\ fs []
    \\ irule_at Any closed_freevars_subst1
    \\ fs [pure_expTheory.closed_def])
  >~ [‘Letrec’] >-
   (rw []
    \\ qpat_x_assum ‘exp_rel (Letrec f y) _’ mp_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_wh_to_def, Once eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- ((* Rec *)
      CONV_TAC (PATH_CONV "rl" (SIMP_CONV (srw_ss()) [eval_to_def])) \\ gs []
      \\ imp_res_tac ALOOKUP_SOME \\ fs [dest_anyThunk_def]
      \\ simp [GSYM MAP_REVERSE, ALOOKUP_MAP]
      \\ qmatch_goalsub_abbrev_tac ‘eval_to (k - 1) x’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ gvs []
      \\ TRY (IF_CASES_TAC \\ gvs [])
      \\ ‘v_rel (eval_wh_to (k - 1) (subst_funs f y))
                (eval_to (k - 1) x)’
        suffices_by (
          gvs [] \\ rpt strip_tac \\ gvs [eval_wh_to_def]
          \\ Cases_on ‘y'’ \\ gvs [is_anyThunk_def, dest_anyThunk_def]
          \\ Cases_on ‘eval_wh_to (k - 1) (subst_funs f y)’ \\ gvs [])
      \\ first_x_assum irule \\ unabbrev_all_tac
      \\ irule_at Any exp_rel_subst_funs \\ fs []
      \\ drule_then (qspec_then ‘REVERSE f’ mp_tac) ALOOKUP_SOME_EL_2
      \\ impl_tac
      >>~- ([‘MAP FST _ = MAP FST _’],
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
      \\ rw []
      \\ irule_at Any IMP_closed_subst
      \\ fs [pure_expTheory.subst_funs_def, pure_expTheory.bind_def,
             flookup_fupdate_list, FDOM_FUPDATE_LIST, subst_ignore,
             subst_funs_def, eval_wh_to_def,FRANGE_FLOOKUP,PULL_EXISTS]
      \\ simp [AllCaseEqs()] \\ rw []
      \\ imp_res_tac ALOOKUP_MEM
      \\ gvs [MEM_MAP,EXISTS_PROD,EVERY_MEM,FORALL_PROD,PULL_EXISTS]
      \\ res_tac \\ fs []
      \\ fs [SUBSET_DEF,MEM_MAP,EXISTS_PROD])
    >- ((* Tick *)
      CONV_TAC (PATH_CONV "rl" (SIMP_CONV (srw_ss()) [eval_to_def]))
      \\ gs [dest_anyThunk_def]
      \\ Cases_on ‘eval_to (k - 1) (subst_funs [] y'')’ \\ gvs []
      \\ TRY (IF_CASES_TAC \\ gvs [])
      \\ ‘v_rel (eval_wh_to (k - 1) (subst_funs [] y))
                (eval_to (k - 1) (subst_funs [] y''))’
        suffices_by (
          gvs [] \\ rpt strip_tac \\ gvs [eval_wh_to_def]
          \\ Cases_on ‘y'’ \\ gvs [is_anyThunk_def, dest_anyThunk_def]
          \\ Cases_on ‘eval_wh_to (k - 1) (subst_funs [] y)’ \\ gvs [])
      \\ first_x_assum irule
      \\ fs [pure_expTheory.subst_funs_def, pure_expTheory.bind_def,
             flookup_fupdate_list, FDOM_FUPDATE_LIST, subst_ignore,
             subst_funs_def, eval_wh_to_def])
    \\ first_x_assum irule
    \\ irule_at Any exp_rel_subst_funs \\ fs []
    \\ gs [pure_expTheory.subst_funs_def, pure_expTheory.bind_def,
           flookup_fupdate_list, GSYM MAP_REVERSE, ALOOKUP_MAP_2,
           eval_wh_to_def]
    \\ conj_tac >-
     (qpat_x_assum ‘EVERY _ _’ mp_tac
      \\ qspec_tac (‘MAP FST f’,‘s’)
      \\ drule LIST_REL_LENGTH
      \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
      \\ qid_spec_tac ‘g’
      \\ qid_spec_tac ‘f’
      \\ Induct \\ fs []
      \\ gen_tac \\ Cases \\ fs []
      \\ gvs [UNCURRY])
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
        \\ reverse $ IF_CASES_TAC
        >- (gvs [EXISTS_MAP, EXISTS_MEM, is_anyThunk_def, dest_anyThunk_def])
        \\ rw [] \\ gvs [EL_MAP]
        \\ gs [thunk_rel_def, EVERY_EL]
        \\ rw [LIST_REL_EL_EQN, EL_MAP, thunk_rel_def])
      >- simp[get_atoms_def]
      >- (gvs[mop_cases] >> metis_tac[])
      >- (gvs[mop_cases] >> metis_tac[])
      >- (gvs[mop_cases] >> metis_tac[])
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
        \\ IF_CASES_TAC \\ fs [monad_cns_def])
      \\ ‘ys ≠ []’ by (strip_tac \\ fs [])
      \\ simp [get_atoms_MAP_Diverge]
      \\ gs [NIL_iff_NOT_MEM]
      \\ rw [] \\ gs []
      )
    \\ rw [Once exp_rel_cases]
    >- ((* If *)
      simp [eval_to_def, eval_wh_to_def]
      \\ gvs [LENGTH_EQ_NUM_compute, SF DNF_ss]
      \\ ‘eval_wh_to (k - 1) x1 ≠ wh_Error’
        by (gs [eval_wh_to_def, AllCaseEqs ()])
      \\ first_assum drule_all
      \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
      \\ rename1 ‘INR res’
      \\ CASE_TAC \\ reverse $ Cases_on ‘res’ \\ gvs []
      >- (strip_tac >> gvs[mop_cases])
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
      \\ IF_CASES_TAC \\ gvs []
      )
    >- ((* Cons *)
      simp [eval_wh_to_def, eval_to_def, result_map_MAP, combinTheory.o_DEF,
            result_map_def, MEM_MAP, MAP_MAP_o, EVERY2_MAP, thunk_rel_def,
            SF ETA_ss]
      \\ gs [LIST_REL_EL_EQN, EVERY_EL]
      \\ reverse $ IF_CASES_TAC \\ gvs []
      >- (gvs [EL_MAP, is_anyThunk_def, dest_anyThunk_def])
      \\ simp [LIST_REL_EL_EQN, EL_MAP, thunk_rel_def, EVERY_EL])
    >- (simp[eval_wh_to_def, eval_to_def, get_atoms_def])
    >- (simp[eval_wh_to_def, eval_to_def, monad_cns_def])
    >- (gvs[mop_cases, eval_wh_to_def, eval_to_def] >> metis_tac[])
    >- (gvs[mop_cases, eval_wh_to_def, eval_to_def] >> metis_tac[])
    >- (gvs[mop_cases, eval_wh_to_def, eval_to_def] >> metis_tac[])
    >- (gvs[mop_cases, eval_wh_to_def, eval_to_def] >> metis_tac[])
    >- (gvs[mop_cases, eval_wh_to_def, eval_to_def] >> metis_tac[])
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
        Cases_on ‘eval_wh_to (k - 1) x’ \\ Cases_on ‘v’
        \\ gvs[mop_cases, monad_cns_def])
      \\ Cases_on ‘v’ \\ gvs []
      \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gvs []
      \\ first_x_assum (drule_all_then assume_tac)
      \\ fs [thunk_rel_def, dest_anyThunk_def, subst_funs_def,
             EVERY_EL]
      \\ Cases_on ‘eval_to (k - 1) y'’ \\ gvs []
      \\ TRY (IF_CASES_TAC \\ gvs [])
      \\ ‘v_rel (eval_wh_to (k - 1) (EL i xs)) (eval_to (k - 1) y')’
        suffices_by (
          gvs [] \\ rpt strip_tac \\ gvs [eval_wh_to_def]
          \\ Cases_on ‘y''’ \\ gvs [is_anyThunk_def, dest_anyThunk_def]
          \\ Cases_on ‘eval_wh_to (k - 1) (EL i xs)’ \\ gvs [])
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
    >- ((* Seq fresh *)
      simp [eval_wh_to_def, eval_to_def]
      \\ fs [SF DNF_ss]
      \\ ‘eval_wh_to (k - 1) x1 ≠ wh_Error’
        by (strip_tac \\ gs [eval_wh_to_def])
      \\ first_assum (drule_all_then assume_tac) \\ fs []
      \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs [eval_wh_to_def]
      \\ IF_CASES_TAC \\ gvs []
      \\ imp_res_tac exp_rel_freevars
      \\ fs [subst1_fresh])
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
          \\ Cases_on ‘v’ \\ gvs []
          \\ gvs[mop_cases, monad_cns_def])
        \\ pairarg_tac \\ gvs []
        \\ Cases_on ‘v’ \\ gvs []
        \\ IF_CASES_TAC \\ gvs [monad_cns_def]
        \\ drule_then assume_tac LIST_REL_LENGTH
        \\ IF_CASES_TAC \\ gvs [monad_cns_def])
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
          \\ IF_CASES_TAC \\ gs [monad_cns_def])
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
  cont_rel (BC x c) (BC v d) = (closed x ∧ exp_rel x v ∧ cont_rel c d) ∧
  cont_rel (HC x c) (HC v d) = (closed x ∧ exp_rel x v ∧ cont_rel c d) ∧
  cont_rel _ _ = F
End

Definition state_rel_def:
  state_rel = LIST_REL (LIST_REL thunk_rel)
End

Definition next_rel_def[simp]:
  next_rel Ret Ret = T ∧
  next_rel Div Div = T ∧
  next_rel Err Err = T ∧
  next_rel (Act a c s) (Act b d t) = (
    a = b ∧ cont_rel c d ∧ state_rel s t) ∧
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
  (∀n. tick_rel (pure_exp$Var n) (pure_exp$Var n))
[~Prim:]
  (∀op xs ys.
     LIST_REL tick_rel xs ys ⇒
       tick_rel (Prim op xs) (Prim op ys))
[~App:]
  (∀f g x y.
     tick_rel f g ∧
     tick_rel x y ⇒
       tick_rel (App f x) (App g y))
[~Lam:]
  (∀s x y.
     tick_rel x y ⇒
       tick_rel (Lam s x) (Lam s y))
[~Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ tick_rel x y) f g ∧
     tick_rel x y ⇒
       tick_rel (Letrec f x) (Letrec g y))
[~Tick:]
  (∀x y.
     tick_rel x y ⇒
       tick_rel x (Tick y))
End

Theorem tick_rel_def =
  [“tick_rel (Var v) x”,
   “tick_rel (Prim op xs) x”,
   “tick_rel (App f x) y”,
   “tick_rel (Lam s x) y”,
   “tick_rel (Letrec f x) y”]
  |> map (SIMP_CONV (srw_ss()) [Once tick_rel_cases])
  |> LIST_CONJ;

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

Theorem tick_rel_subst:
  ∀x y.
    tick_rel x y ⇒
      ∀vs ws.
        fmap_rel tick_rel vs ws ⇒
          tick_rel (subst vs x) (subst ws y)
Proof
  ho_match_mp_tac tick_rel_strongind \\ rw []
  >~ [‘Var n’] >- (
    gs [pure_expTheory.subst_def, fmap_rel_OPTREL_FLOOKUP, OPTREL_def]
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ gs [tick_rel_Var])
  >~ [‘Prim op xs’] >- (
    simp [pure_expTheory.subst_def]
    \\ irule tick_rel_Prim
    \\ gvs [EVERY2_MAP, LIST_REL_EL_EQN])
  >~ [‘App f x’] >- (
    simp [pure_expTheory.subst_def]
    \\ irule tick_rel_App \\ gs [])
  >~ [‘Lam s x’] >- (
    simp [pure_expTheory.subst_def]
    \\ irule tick_rel_Lam
    \\ first_x_assum (irule_at Any)
    \\ gs [fmap_rel_def, DOMSUB_FAPPLY_THM])
  >~ [‘Letrec f x’] >- (
    simp [pure_expTheory.subst_def]
    \\ irule tick_rel_Letrec
    \\ first_x_assum (irule_at Any)
    \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
    \\ ‘MAP FST f = MAP FST g’
      by (irule LIST_EQ \\ gs [EL_MAP])
    \\ qmatch_goalsub_abbrev_tac ‘A ∧ _’
    \\ ‘A’ suffices_by rw []
    \\ unabbrev_all_tac
    \\ gs [fmap_rel_OPTREL_FLOOKUP, FDOM_FDIFF_alt]
    \\ qx_gen_tac ‘xx’
    \\ first_x_assum (qspec_then ‘xx’ assume_tac)
    \\ rw [FLOOKUP_FDIFF] \\ gs [OPTREL_def])
  >~ [‘Tick y’] >- (
    rw [pure_expTheory.subst_def]
    \\ irule tick_rel_Tick
    \\ gs [])
QED

Theorem tick_rel_freevars:
  ∀x y. tick_rel x y ⇒ freevars x = freevars y
Proof
  ho_match_mp_tac tick_rel_strongind \\ rw []
  \\ gvs [BIGUNION, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
  \\ ‘MAP FST f = MAP FST g’
    by (irule LIST_EQ \\ gs [EL_MAP, ELIM_UNCURRY])
  \\ rw [EQ_IMP_THM, EXTENSION, DISJ_EQ_IMP]
  \\ gs [MEM_EL, EL_MAP, ELIM_UNCURRY, SF SFY_ss]
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem subst_empty[local,simp]:
  pure_exp$subst_funs [] x = x
Proof
  rw [pure_expTheory.subst_funs_def, FUPDATE_LIST_THM]
QED

Theorem tick_rel_Fail[simp]:
  tick_rel Fail Fail
Proof
  rw [Once tick_rel_def]
QED

Theorem tick_rel_FUNPOW:
  ∀x y.
  tick_rel x y ⇒
    (∀w. x ≠ Tick w) ⇒
      ∃n z.
          y = FUNPOW Tick n z ∧
          tick_rel x z ∧
          (∀w. z ≠ Tick w)
Proof
  ho_match_mp_tac tick_rel_strongind \\ rw []
  >~ [‘Var n’] >- (
    qexists_tac ‘0’
    \\ simp [tick_rel_Var])
  >~ [‘Prim op xs’] >- (
    qexists_tac ‘0’
    \\ irule_at Any tick_rel_Prim
    \\ gvs [LIST_REL_EL_EQN])
  >~ [‘App f x’] >- (
    qexists_tac ‘0’
    \\ irule_at Any tick_rel_App
    \\ gvs [])
  >~ [‘Lam s x’] >- (
    qexists_tac ‘0’
    \\ irule_at Any tick_rel_Lam
    \\ gvs [])
  >~ [‘Letrec f x’] >- (
    qexists_tac ‘0’
    \\ irule_at Any tick_rel_Letrec
    \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY]
    \\ strip_tac \\ gs [])
  >~ [‘Tick x’] >- (
    gs []
    \\ first_x_assum (irule_at Any) \\ gs []
    \\ qexists_tac ‘SUC n’
    \\ simp [arithmeticTheory.FUNPOW_SUC])
QED

Theorem eval_wh_to_Tick[local]:
  ∀n k x. eval_wh_to (k + n) (FUNPOW Tick n x) = eval_wh_to k x
Proof
  Induct \\ rw [eval_wh_to_def]
  \\ gs [arithmeticTheory.FUNPOW_SUC, eval_wh_to_def, arithmeticTheory.ADD1]
QED

Theorem tick_rel_eval_wh_to:
  ∀k x y.
    tick_rel x y ⇒
      ∃j. tick_wh_rel (eval_wh_to k x) (eval_wh_to (k + j) y)
Proof
  ho_match_mp_tac eval_wh_to_ind \\ rw []
  >~ [‘Var m’] >- (
    dxrule_then assume_tac tick_rel_FUNPOW \\ gvs []
    \\ gvs [Once tick_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_wh_to_Tick, eval_wh_to_def])
  >~ [‘Lam s x’] >- (
    dxrule_then assume_tac tick_rel_FUNPOW \\ gvs []
    \\ gvs [Once tick_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_wh_to_Tick, eval_wh_to_def])
  >~ [‘App f x’] >- (
    dxrule_then assume_tac tick_rel_FUNPOW \\ gvs []
    \\ gvs [Once tick_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_wh_to_Tick, eval_wh_to_def]
    \\ rename1 ‘tick_rel x y’
    \\ simp [eval_wh_to_def]
    \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac)) \\ gs []
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘j’
      \\ simp [])
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
    \\ ‘∀j1. eval_wh_to (j + j1 + k) g = eval_wh_to (j + k) g’
      by (strip_tac \\ irule eval_wh_inc \\ gs [])
    \\ Cases_on ‘eval_wh_to k f’ \\ Cases_on ‘eval_wh_to (j + k) g’ \\ gvs []
    \\ rename1 ‘tick_rel e1 e2’
    \\ ‘tick_rel (bind1 q x e1) (bind1 q y e2)’
      by (simp [bind1_def]
          \\ imp_res_tac tick_rel_freevars
          \\ rw [pure_expTheory.closed_def]
          \\ irule tick_rel_subst
          \\ gs [fmap_rel_def])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_wh_to (k - 1) (bind1 q x e1) = wh_Diverge’ \\ gs []
    >- (
      Cases_on ‘j1 ≤ j’
      >- (
        qexists_tac ‘j1’
        \\ IF_CASES_TAC \\ gs []
        \\ drule_then (qspec_then ‘j + k’ (assume_tac o GSYM)) eval_wh_inc
        \\ gs [])
      \\ gs [arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_OR_EQ]
      \\ qexists_tac ‘j’
      \\ IF_CASES_TAC \\ gs []
      \\ CCONTR_TAC
      \\ drule_then (qspec_then ‘j1 + k - 1’ (assume_tac o GSYM)) eval_wh_inc
      \\ gs [])
    \\ qexists_tac ‘j + j1’ \\ gs []
    \\ ‘eval_wh_to (j + (j1 + k) - 1) (bind1 q y e2) =
        eval_wh_to (j1 + k - 1) (bind1 q y e2)’
      suffices_by rw []
    \\ irule eval_wh_inc \\ gs []
    \\ strip_tac
    \\ Cases_on ‘eval_wh_to (k - 1) (bind1 q x e1)’ \\ gs [])
  >~ [‘Letrec f x’] >- (
    Cases_on ‘f = []’ \\ gvs []
    >~ [‘tick_rel (Tick x) y’] >- (
      Cases_on ‘k = 0’ \\ gs []
      >- (
        gvs [Once tick_rel_def]
        \\ qexists_tac ‘0’
        \\ simp [eval_wh_to_def])
      \\ ‘∃n z. 0 < n ∧ y = FUNPOW Tick n z ∧ tick_rel x z’
        by (‘∀z y.
               tick_rel z y ⇒
               ∀x. z = Tick x ⇒
                 ∃n u. 0 < n ∧ y = FUNPOW Tick n u ∧ tick_rel x u’
              suffices_by rw []
            \\ rpt (pop_assum kall_tac)
            \\ ho_match_mp_tac tick_rel_strongind \\ rw []
            >- (
             Cases_on ‘∃x. z = Tick x’ \\ gvs []
             >- (
               first_assum (irule_at (Pos last))
               \\ qexists_tac ‘SUC 0’ \\ gs [])
             \\ drule_all_then strip_assume_tac tick_rel_FUNPOW
             \\ gvs []
             \\ first_assum (irule_at Any)
             \\ qexists_tac ‘SUC n’
             \\ simp [arithmeticTheory.FUNPOW_SUC])
           \\ qexists_tac ‘SUC n’
           \\ qexists_tac ‘u’
           \\ simp [arithmeticTheory.FUNPOW_SUC])
      \\ ‘∃m. n = SUC m’ by (Cases_on ‘n’ \\ gs []) \\ gvs []
      \\ qpat_x_assum ‘tick_rel (Tick x) _’ kall_tac
      \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
      \\ simp [eval_wh_to_def, arithmeticTheory.FUNPOW_SUC]
      \\ Q.REFINE_EXISTS_TAC ‘j + m’
      \\ ‘j + m + k - 1 = j + k - 1 + m’
        by gs []
      \\ pop_assum SUBST1_TAC
      \\ simp [eval_wh_to_Tick])
    \\ dxrule_then assume_tac tick_rel_FUNPOW \\ gvs []
    \\ gvs [Once tick_rel_def, eval_wh_to_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = j + k + n”]
    \\ simp [eval_wh_to_Tick, eval_wh_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ first_x_assum (irule_at Any)
    \\ simp [pure_expTheory.subst_funs_def, pure_expTheory.bind_def]
    \\ ‘fmap_rel tick_rel
                 (FEMPTY |++ MAP (λ(n,x). (n, Letrec f x)) f)
                 (FEMPTY |++ MAP (λ(n,x). (n, Letrec g x)) g)’
      suffices_by (
        gs [fmap_rel_OPTREL_FLOOKUP, OPTREL_def]
        \\ rw [] \\ gs []
        >- (
          irule tick_rel_subst
          \\ rw [fmap_rel_OPTREL_FLOOKUP, OPTREL_def]
          \\ first_x_assum irule)
        \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ gs []
        \\ first_x_assum (drule_then assume_tac)
        \\ drule_then assume_tac tick_rel_freevars
        \\ gs [pure_expTheory.closed_def])
    \\ rw [fmap_rel_OPTREL_FLOOKUP, flookup_fupdate_list]
    \\ rw [OPTREL_def, CaseEq "option"] \\ rw [GSYM OPTREL_def]
    \\ irule LIST_REL_OPTREL
    \\ rw [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY, Once tick_rel_cases]
    \\ gs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP])
  >~ [‘_ 0 (Prim op xs)’] >- (
    dxrule_then assume_tac tick_rel_FUNPOW \\ gvs []
    \\ gvs [Once tick_rel_def]
    \\ qexists_tac ‘n’
    \\ simp [SIMP_RULE std_ss [] (Q.SPECL [‘n’,‘0’] eval_wh_to_Tick),
             eval_wh_to_def]
    \\ Cases_on ‘op’ \\ gs []
    >- ((* If *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute])
    >- ((* IsEq *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1n ⇔ n = 0”])
    >- ((* Proj *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1n ⇔ n = 0”])
    >- ((* AtomOp *)
      gvs [LIST_REL_EL_EQN]
      \\ Cases_on ‘xs = []’ \\ gs []
      >- (
        CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs []
        \\ rw [tick_rel_def])
      \\ ‘ys ≠ []’ by (strip_tac \\ gs [])
      \\ simp [get_atoms_MAP_Diverge])
    >- ((* Seq *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1n ⇔ n = 0”]))
  >~ [‘Prim op xs’] >- (
    dxrule_then assume_tac tick_rel_FUNPOW \\ gvs []
    \\ gvs [Once tick_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = j + k + n”]
    \\ simp [eval_wh_to_Tick, eval_wh_to_def]
    \\ Cases_on ‘op’ \\ gs []
    >- ((* If *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 3 ⇔ n = 0 ∨ n = 1 ∨ n = 2”,
              SF DNF_ss]
      \\ rename [‘eval_wh_to (k - 1) x1’, ‘tick_rel x1 x2’]
      \\ qpat_x_assum ‘tick_rel x1 _’ assume_tac
      \\ first_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
      \\ reverse (Cases_on ‘∃s xs. eval_wh_to (k - 1) x1 = wh_Constructor s xs’)
      >- (
        qexists_tac ‘j’
        \\ CASE_TAC \\ gs [])
      \\ gs []
      \\ Cases_on ‘xs ≠ []’ \\ gs []
      >- (
        qexists_tac ‘j’
        \\ gvs [LIST_REL_EL_EQN]
        \\ IF_CASES_TAC \\ gs []
        \\ IF_CASES_TAC \\ gs [])
      \\ reverse (Cases_on ‘s = "True" ∨ s = "False"’)
      >- (
        qexists_tac ‘j’
        \\ gvs [LIST_REL_EL_EQN]
        \\ IF_CASES_TAC \\ gs []
        \\ IF_CASES_TAC \\ gs [])
      \\ gs [Once DISJ_EQ_IMP]
      \\ rename [‘if s = "True" then _ (k - 1) y1 else _’, ‘tick_rel y1 y2’]
      \\ qpat_x_assum ‘tick_rel y1 _’ assume_tac
      \\ first_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
      \\ rename [‘if _ then _ else _ (k - 1) z1’, ‘tick_rel z1 z2’]
      \\ qpat_x_assum ‘tick_rel z1 _’ assume_tac
      \\ first_x_assum (drule_then (qx_choose_then ‘j2’ assume_tac))
      \\ IF_CASES_TAC \\ gs []
      >- (
        Cases_on ‘eval_wh_to (k - 1) y1 = wh_Diverge’ \\ gs []
        >- (
          qexists_tac ‘j1’
          \\ Cases_on ‘eval_wh_to (j1 + k - 1) x2 = wh_Diverge’ \\ gs []
          \\ drule_then (qspec_then ‘j + k - 1’ assume_tac) eval_wh_to_agree
          \\ gs [])
        \\ ‘eval_wh_to (j1 + k - 1) y2 ≠ wh_Diverge’
          by (strip_tac \\ Cases_on ‘eval_wh_to (k - 1) y1’ \\ gs [])
        \\ drule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_wh_inc
        \\ ‘eval_wh_to (j + k - 1) x2 ≠ wh_Diverge’
          by gs []
        \\ drule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_wh_inc
        \\ qexists_tac ‘j + j1’ \\ gs [])
      \\ Cases_on ‘eval_wh_to (k - 1) z1 = wh_Diverge’ \\ gs []
      >- (
        qexists_tac ‘j2’
        \\ Cases_on ‘eval_wh_to (j2 + k - 1) x2 = wh_Diverge’ \\ gs []
        \\ drule_then (qspec_then ‘j + k - 1’ assume_tac) eval_wh_to_agree
        \\ gs [])
      \\ ‘eval_wh_to (j2 + k - 1) z2 ≠ wh_Diverge’
        by (strip_tac \\ Cases_on ‘eval_wh_to (k - 1) z1’ \\ gs [])
      \\ drule_then (qspec_then ‘j + j2 + k - 1’ assume_tac) eval_wh_inc
      \\ ‘eval_wh_to (j + k - 1) x2 ≠ wh_Diverge’
        by gs []
      \\ drule_then (qspec_then ‘j + j2 + k - 1’ assume_tac) eval_wh_inc
      \\ qexists_tac ‘j + j2’ \\ gs [])
    >- ((* IsEq *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1n ⇔ n = 0”]
      \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
      \\ qexists_tac ‘j’
      \\ CASE_TAC \\ gs [LIST_REL_EL_EQN]
      \\ rw [] \\ gs [tick_rel_def])
    >- ((* Proj *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1n ⇔ n = 0”]
      \\ rename1 ‘tick_rel x y’
      \\ first_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
      \\ reverse (Cases_on ‘∃s xs. eval_wh_to (k - 1) x = wh_Constructor s xs’)
      >- (
        qexists_tac ‘j’
        \\ CASE_TAC \\ gs [])
      \\ gs [] \\ reverse IF_CASES_TAC \\ gvs []
      >- (
        qexists_tac ‘j’
        \\ rw [] \\ gs [LIST_REL_EL_EQN])
      \\ gvs [LIST_REL_EL_EQN]
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
      \\ rename1 ‘_ (EL n xs) (EL n ys)’
      \\ Cases_on ‘eval_wh_to (k - 1) (EL n xs) = wh_Diverge’ \\ gs []
      >- (
        Cases_on ‘eval_wh_to (k - 1) (EL n ys) = wh_Diverge’ \\ gs []
        >- (
          qexists_tac ‘j1’
          \\ Cases_on ‘eval_wh_to (j1 + k - 1) y = wh_Diverge’ \\ gs []
          \\ drule_then (qspec_then ‘j + k - 1’ (assume_tac o GSYM))
                        eval_wh_to_agree
          \\ gs [])
        \\ drule_then (qspec_then ‘j1 + k - 1’ assume_tac) eval_wh_inc \\ gs [])
      \\ ‘eval_wh_to (j1 + k - 1) (EL n ys) ≠ wh_Diverge’
        by (strip_tac \\ Cases_on ‘eval_wh_to (k - 1) (EL n xs)’ \\ gs [])
      \\ drule_then (qspec_then ‘j1 + j + k - 1’ assume_tac) eval_wh_inc
      \\ ‘eval_wh_to (j + k - 1) y ≠ wh_Diverge’
        by gs []
      \\ drule_then (qspec_then ‘j1 + j + k - 1’ assume_tac) eval_wh_inc
      \\ qexists_tac ‘j + j1’ \\ gs [])
    >- ((* AtomOp *)
      gvs [LIST_REL_EL_EQN]
      \\ ‘∃j. pure_eval$get_atoms (MAP (λx. eval_wh_to (k - 1) x) xs) =
              get_atoms (MAP (λx. eval_wh_to (j + k - 1) x) ys)’
        suffices_by (
          disch_then (qx_choose_then ‘j’ assume_tac)
          \\ qexists_tac ‘j’ \\ gs []
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs []
          \\ rw [tick_rel_def])
      \\ Cases_on ‘xs = []’ \\ gs []
      \\ ‘ys ≠ []’
        by (strip_tac \\ gs [])
      \\ gs [MEM_EL, PULL_EXISTS]
      \\ ‘∀x y. tick_rel x y ⇒
            ∃j. tick_wh_rel (eval_wh_to (k - 1) x)
                            (eval_wh_to (j + k - 1) y)’
        by (rw []
            \\ first_x_assum (irule_at Any) \\ gs []
            \\ qexists_tac ‘0’ \\ gs []
            \\ Cases_on ‘ys’ \\ gs [])
      \\ qpat_x_assum ‘∀x n. _ < _ ⇒ _’  kall_tac
      \\ ‘∀n. n < LENGTH ys ⇒
            ∃j. tick_wh_rel (eval_wh_to (k - 1) (EL n xs))
                            (eval_wh_to (j + k - 1) (EL n ys))’
        by rw []
      \\ qpat_x_assum ‘∀n. _ < _ ⇒ tick_rel _ _’ kall_tac
      \\ qpat_x_assum ‘∀x y. _’ kall_tac
      \\ gs [get_atoms_def]
      \\ IF_CASES_TAC \\ gs []
      >- (
        gs [EXISTS_MEM, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
        \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
        \\ qexists_tac ‘j’
        \\ ‘error_Atom (eval_wh_to (j + k - 1) (EL n ys))’
          suffices_by rw [SF SFY_ss]
        \\ Cases_on ‘eval_wh_to (k - 1) (EL n xs)’
        \\ Cases_on ‘eval_wh_to (j + k - 1) (EL n ys)’ \\ gs [])
      \\ gs [Once EVERY_MEM, Once MEM_EL, PULL_EXISTS, EL_MAP]
      \\ ‘∃j. ∀n. n < LENGTH ys ⇒
            ¬error_Atom (eval_wh_to (j + k - 1) (EL n ys))’
        by (qpat_x_assum ‘LENGTH _ = _’ mp_tac
            \\ rpt (qpat_x_assum ‘∀n. _’ mp_tac)
            \\ Cases_on ‘k’ \\ gs [arithmeticTheory.ADD1]
            \\ rename1 ‘eval_wh_to k’
            \\ rpt (pop_assum kall_tac)
            \\ qid_spec_tac ‘xs’
            \\ qid_spec_tac ‘ys’
            \\ Induct \\ simp [] \\ Cases_on ‘xs’ \\ simp []
            \\ qx_gen_tac ‘y’
            \\ rename1 ‘EL _ (x::xs)’
            \\ rw []
            \\ first_x_assum (qspec_then ‘xs’ mp_tac)
            \\ impl_tac
            >- (
              qx_gen_tac ‘n’ \\ rw []
              \\ first_x_assum (qspec_then ‘SUC n’ assume_tac)
              \\ first_x_assum (qspec_then ‘SUC n’ strip_assume_tac)
              \\ gs [SF SFY_ss])
            \\ impl_tac
            >- (
              qx_gen_tac ‘n’ \\ rw []
              \\ first_x_assum (qspec_then ‘SUC n’ assume_tac)
              \\ first_x_assum (qspec_then ‘SUC n’ strip_assume_tac)
              \\ gs [SF SFY_ss])
            \\ rw []
            \\ last_assum (qspec_then ‘0’ mp_tac) \\ simp_tac std_ss []
            \\ disch_then (qx_choose_then ‘j1’ assume_tac)
            \\ qpat_assum ‘∀n. _ ⇒ ¬error_Atom (_ _ (EL _ (_::_)))’
              (qspec_then ‘0’ mp_tac)
            \\ simp_tac list_ss []
            \\ strip_tac
            \\ ‘¬error_Atom (eval_wh_to (j1 + k) y)’
              by (strip_tac
                  \\ Cases_on ‘eval_wh_to k x’
                  \\ Cases_on ‘eval_wh_to (j1 + k) y’ \\ gs [])
            \\ qexists_tac ‘MIN j1 j’
            \\ Cases \\ gs []
            >- (
              rw [arithmeticTheory.MIN_DEF]
              \\ gs [arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_OR_EQ]
              \\ strip_tac
              \\ ‘eval_wh_to (j + k) y ≠ wh_Diverge’
                by (strip_tac \\ gs [])
              \\ drule_then (qspec_then ‘j1 + k’ assume_tac) eval_wh_inc
              \\ gs [])
            \\ rw [arithmeticTheory.MIN_DEF]
            \\ strip_tac
            \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ gs []
            \\ ‘eval_wh_to (j1 + k) (EL n ys) ≠ wh_Diverge’
              by (strip_tac \\ gs [])
            \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_wh_inc \\ gs [])
      \\ IF_CASES_TAC \\ gs []
      >- (
        gs [EXISTS_MEM, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
        \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
        \\ qexists_tac ‘MIN j j1’ >>
        gvs[EVERY_MAP] >> goal_assum $ drule_at Any >> rw[]
        >- (
          rw[EVERY_EL] >> first_x_assum $ drule_then assume_tac >>
          CCONTR_TAC >> gvs[] >>
          ‘eval_wh_to (k + MIN j j1 - 1) (EL n' ys) ≠ wh_Diverge’ by
            (CCONTR_TAC >> gvs[]) >>
          drule eval_wh_inc >> disch_then $ qspec_then ‘j + k - 1’ mp_tac >>
          impl_tac >- gvs[arithmeticTheory.MIN_DEF] >>
          strip_tac >> gvs[]
          )
        >- (
          CCONTR_TAC >> gvs[] >>
          drule eval_wh_inc >>
          disch_then $ qspec_then ‘j1 + k - 1’ assume_tac >> gvs[] >>
          gvs[arithmeticTheory.MIN_DEF]
          )
        )
      \\ gs [MEM_EL, EL_MAP, SF CONJ_ss]
      \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ ‘∃i. ∀n. n < LENGTH ys ⇒
                tick_wh_rel (eval_wh_to (k - 1) (EL n xs))
                            (eval_wh_to (i + k - 1) (EL n ys))’
        by (Cases_on ‘k’ \\ gs [arithmeticTheory.ADD1]
            \\ rename1 ‘eval_wh_to k’
            \\ rpt (qpat_x_assum ‘_ ≠ []’ kall_tac)
            \\ rpt (pop_assum mp_tac)
            \\ qid_spec_tac ‘ys’
            \\ qid_spec_tac ‘xs’
            \\ Induct \\ simp []
            \\ Cases_on ‘ys’ \\ simp []
            \\ rename1 ‘LENGTH xs = LENGTH ys’
            \\ qx_gen_tac ‘x’ \\ rename1 ‘y::ys’ \\ rw []
            \\ first_x_assum drule
            \\ impl_tac
            >- (
              rw [] \\ gs []
              \\ rename1 ‘n < LENGTH ys’
              \\ rpt (first_x_assum (qspec_then ‘SUC n’ assume_tac)) \\ gs []
              \\ gs [SF SFY_ss])
            \\ disch_then (qx_choose_then ‘j1’ assume_tac)
            \\ last_x_assum (qspec_then ‘0’ mp_tac) \\ simp []
            \\ disch_then (qx_choose_then ‘j2’ assume_tac)
            \\ qexists_tac ‘j + j1 + j2’
            \\ Cases \\ gs []
            >- (
              ‘0 < SUC (LENGTH ys)’
                by gs []
              \\ first_x_assum (drule_then assume_tac)
              \\ first_x_assum (drule_then assume_tac)
              \\ first_x_assum (drule_then assume_tac) \\ gs []
              \\ ‘eval_wh_to (j2 + k) y ≠ wh_Diverge’
                by (strip_tac \\ Cases_on ‘eval_wh_to k x’ \\ gs [])
              \\ drule_then (qspec_then ‘j1 + j2 + j + k’ assume_tac)
                            eval_wh_inc
              \\ gs [])
            \\ strip_tac
            \\ ‘SUC n < SUC (LENGTH ys)’
              by gs []
            \\ first_x_assum (drule_then assume_tac)
            \\ first_x_assum (drule_then assume_tac)
            \\ first_x_assum (drule_then assume_tac) \\ gs []
            \\ ‘eval_wh_to (j1 + k) (EL n ys) ≠ wh_Diverge’
              by (strip_tac \\ Cases_on ‘eval_wh_to k (EL n xs)’ \\ gs [])
            \\ drule_then (qspec_then ‘j1 + j2 + j + k’ assume_tac)
                          eval_wh_inc
            \\ gs [])
      \\ qexists_tac ‘i’
      \\ gs [EXISTS_MEM, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
      \\ IF_CASES_TAC \\ gs []
      >- (
        ‘eval_wh_to (k - 1) (EL n xs) ≠ wh_Diverge’
          by (strip_tac \\ gs [])
        \\ last_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
        \\ ‘eval_wh_to (j1 + k - 1) (EL n ys) ≠ wh_Diverge’
          by (strip_tac \\ Cases_on ‘eval_wh_to (k - 1) (EL n xs)’ \\ gs [])
        \\ drule_then (qspec_then ‘i + k - 1’ assume_tac) eval_wh_to_agree
        \\ ‘eval_wh_to (i + k - 1) (EL n ys) ≠ wh_Diverge’
          by (strip_tac \\ gs [])
        \\ gs []
        \\ ‘error_Atom (eval_wh_to (i + k - 1) (EL n ys))’
          by (Cases_on ‘eval_wh_to (j1 + k - 1) (EL n ys)’ \\ gs [])
        \\ ‘error_Atom (eval_wh_to (k - 1) (EL n xs))’
          by (Cases_on ‘eval_wh_to (k - 1) (EL n xs)’
              \\ Cases_on ‘eval_wh_to (i + k - 1) (EL n ys)’ \\ gs [])
        \\ gs [])
      \\ simp [DISJ_EQ_IMP, Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ gs [DISJ_EQ_IMP, Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ conj_tac
      >- (
        rw []
        \\ first_x_assum drule
        \\ first_x_assum drule
        \\ rw [] \\ strip_tac
        \\ Cases_on ‘eval_wh_to (k - 1) (EL n xs)’ \\ gs [])
      \\ ‘∀x y. tick_wh_rel x y ∧ ¬error_Atom x ⇒ dest_Atom x = dest_Atom y’
        by (Cases \\ rw [dest_Atom_def])
      \\ simp [MAP_MAP_o, combinTheory.o_DEF]
      \\ once_rewrite_tac [EQ_SYM_EQ]
      \\ irule LIST_EQ \\ gvs [EL_MAP] \\ rw []
      \\ first_x_assum irule
      \\ gs [SF SFY_ss]
      \\ strip_tac \\ gs [SF SFY_ss])
    \\ gvs [LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ gs []
    \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 2 ⇔ n = 0 ∨ n = 1”,
            SF DNF_ss]
    \\ rename [‘eval_wh_to (k - 1) x1 = _’, ‘tick_rel x1 y1’]
    \\ Cases_on ‘eval_wh_to (k - 1) x1 = wh_Diverge ∨
                 eval_wh_to (k - 1) x1 = wh_Error’
    >- (
      qpat_x_assum ‘tick_rel x1 _’ assume_tac
      \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
      \\ qexists_tac ‘j’ \\ gs [])
    \\ rename1 ‘tick_rel x2 y2’ \\ gs []
    \\ Cases_on ‘eval_wh_to (k - 1) x2 = wh_Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_wh_to (k - 1) y1 = wh_Diverge’ \\ gs []
      >- (qexists_tac ‘0’ \\ simp [])
      \\ ‘∀j. eval_wh_to (j + k - 1) y1 = eval_wh_to (k - 1) y1’
        by (strip_tac \\ irule eval_wh_inc \\ gs [])
      \\ gs []
      \\ qpat_x_assum ‘tick_rel x1 _’ assume_tac
      \\ first_assum (drule_then (qx_choose_then ‘j’ assume_tac))
      \\ ‘eval_wh_to (j + k - 1) y1 ≠ wh_Error’
        by (strip_tac \\ Cases_on ‘eval_wh_to (k - 1) x1’ \\ gs [])
      \\ gs []
      \\ qpat_x_assum ‘tick_rel x2 _’ assume_tac
      \\ first_assum (drule_then (qx_choose_then ‘j2’ assume_tac))
      \\ qexists_tac ‘j2’
      \\ Cases_on ‘eval_wh_to (k - 1) x2’ \\ gs [])
    \\ first_assum (drule_then (qx_choose_then ‘j2’ assume_tac))
    \\ qpat_x_assum ‘tick_rel x1 _’ assume_tac
    \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
    \\ ‘eval_wh_to (j2 + k - 1) y2 ≠ wh_Diverge’
      by (strip_tac \\ Cases_on ‘eval_wh_to (k - 1) x2’ \\ gs [])
    \\ ‘eval_wh_to (j1 + k - 1) y1 ≠ wh_Diverge’
      by (strip_tac \\ Cases_on ‘eval_wh_to (k - 1) x1’ \\ gs [])
    \\ ‘eval_wh_to (j2 + j1 + k - 1) y1 = eval_wh_to (j1 + k - 1) y1’
      by (irule eval_wh_inc \\ gs [])
    \\ ‘eval_wh_to (j1 + j2 + k - 1) y2 = eval_wh_to (j2 + k - 1) y2’
      by (irule eval_wh_inc \\ gs [])
    \\ qexists_tac ‘j1 + j2’ \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ Cases_on ‘eval_wh_to (k - 1) x1’ \\ gs [])
QED

Theorem tick_rel_eval_wh:
  tick_rel x y ⇒ tick_wh_rel (eval_wh x) (eval_wh y)
Proof
  rw [eval_wh_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro
  \\ simp [PULL_FORALL]
  \\ qx_gen_tac ‘i’
  \\ qx_gen_tac ‘j’
  \\ qx_gen_tac ‘k’
  \\ rw []
  >- (
    drule_then (qspec_then ‘j’ (qx_choose_then ‘k’ assume_tac))
               tick_rel_eval_wh_to
    \\ ‘eval_wh_to (j + k) y = eval_wh_to (i + j + k) y’
      by (once_rewrite_tac [EQ_SYM_EQ] \\ irule eval_wh_inc \\ gs []
          \\ strip_tac \\ Cases_on ‘eval_wh_to j x’ \\ gs [])
    \\ gs []
    \\ ‘eval_wh_to i y = eval_wh_to (i + j + k) y’
      by (once_rewrite_tac [EQ_SYM_EQ] \\ irule eval_wh_inc \\ gs [])
    \\ gs [])
  >- (
    CCONTR_TAC \\ gs []
    \\ drule_then (qspec_then ‘i’ (qx_choose_then ‘k’ assume_tac))
                  tick_rel_eval_wh_to
    \\ gs []
    \\ drule_then (qspec_then ‘i + k’ assume_tac) eval_wh_inc \\ gs [])
  \\ drule_then (qspec_then ‘k’ (qx_choose_then ‘j’ assume_tac))
                tick_rel_eval_wh_to
  \\ gs []
QED

Theorem next'_thm:
  ∀k v c s w d t.
    tick_wh_rel v w ∧
    tstate_rel s t ∧
    tcont_rel c d ⇒
      tnext_rel (next k v c s) (next' k w d t)
Proof
  ho_match_mp_tac pure_semanticsTheory.next_ind \\ rw []
  \\ simp [Once pure_semanticsTheory.next_def]
  \\ Cases_on ‘v = wh_Error ∨
               v = wh_Diverge ∨
               (∃x. v = wh_Atom x) ∨
               (∃s x. v = wh_Closure s x)’
  >- ((* Error *)
    rgs [Once next'_def]
    \\ simp [next'_def])
  \\ ‘∃n xs. v = wh_Constructor n xs’
    by (Cases_on ‘v’ \\ gs [])
  \\ gvs []
  \\ drule_then assume_tac LIST_REL_LENGTH
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once next'_def]
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
      \\ simp [pure_expTheory.bind_def, FLOOKUP_UPDATE]
      \\ rename1 ‘freevars z’
      \\ qpat_x_assum ‘tick_rel _ z’ assume_tac
      \\ drule_then assume_tac tick_rel_freevars
      \\ gs [pure_expTheory.closed_def]
      \\ IF_CASES_TAC \\ gs []
      \\ irule tick_rel_subst \\ gs [fmap_rel_def]
      \\ irule tick_rel_Tick \\ gs [])
    \\ IF_CASES_TAC \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once next'_def]
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
    \\ simp [pure_expTheory.bind_def, FLOOKUP_UPDATE]
    \\ rename1 ‘freevars z’
    \\ qpat_x_assum ‘tick_rel _ z’ assume_tac
    \\ drule_then assume_tac tick_rel_freevars
    \\ gs [pure_expTheory.closed_def]
    \\ IF_CASES_TAC \\ gs []
    \\ irule tick_rel_subst \\ gs [fmap_rel_def]
    \\ irule tick_rel_Tick \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once next'_def]
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule \\ gs []
    \\ irule tick_rel_eval_wh \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once next'_def]
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule \\ gs []
    \\ irule tick_rel_eval_wh \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once next'_def]
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ simp [with_atom_def, pure_semanticsTheory.with_atoms_def]
    \\ rename1 ‘tick_rel x y’
    \\ drule_then assume_tac tick_rel_eval_wh
    \\ Cases_on ‘eval_wh x’ \\ Cases_on ‘eval_wh y’
    \\ gs [pure_semanticsTheory.get_atoms_def]
    \\ CASE_TAC \\ gvs [])
  \\ IF_CASES_TAC \\ gs []
  >- (
    simp [Once next'_def]
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
    simp [Once next'_def]
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
    simp [Once next'_def]
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
    simp [Once next'_def]
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
  \\ rw [Once next'_def]
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
  metis_tac [arithmeticTheory.LESS_EQ_CASES, next'_less_eq]
QED

Theorem next_action'_thm:
  tick_wh_rel v w ∧
  tstate_rel s t ∧
  tcont_rel c d ⇒
    tnext_rel (next_action v c s) (next_action' w d t)
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
    itree_unfold_err
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
  \\ once_rewrite_tac [itreeTheory.itree_unfold_err] \\ fs []
  \\ Cases_on ‘next_action' wh stack state’ \\ fs []
  \\ fs [combinTheory.o_DEF,FUN_EQ_THM] \\ rw []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ fs [interp_alt,interp'_alt_def]
QED

Theorem interp_alt_thm:
  tick_wh_rel v w ∧
  tcont_rel c d ∧
  tstate_rel s t ⇒
    interp v c s = interp_alt w d t
Proof
  strip_tac
  \\ rw [Once itreeTheory.itree_bisimulation]
  \\ qexists_tac ‘
    λt1 t2.
      (t1 = t2 ∨
       ∃v c s w d t.
         t1 = interp v c s ∧
         t2 = interp_alt w d t ∧
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
    \\ Cases_on ‘next_action v' c' s'’
    \\ Cases_on ‘next_action' w' d' t''’ \\ gvs [])
  >- (
    drule_all_then assume_tac next_action'_thm \\ gs []
    \\ qpat_x_assum ‘_ = Div’ mp_tac
    \\ once_rewrite_tac [pure_semanticsTheory.interp_def, interp_alt_def]
    \\ Cases_on ‘next_action v' c' s'’
    \\ Cases_on ‘next_action' w' d' t''’ \\ gvs [])
  \\ drule_all_then assume_tac next_action'_thm \\ gs []
  \\ qpat_x_assum ‘Vis _ _ = _’ mp_tac
  \\ rw [Once pure_semanticsTheory.interp_def, Once interp_alt_def]
  \\ Cases_on ‘next_action v' c' s'’
  \\ Cases_on ‘next_action' w' d' t''’ \\ gvs []
  \\ rw [] \\ CASE_TAC \\ gs [] \\ rw []
  \\ disj2_tac
  \\ irule_at Any EQ_REFL
  \\ irule_at Any EQ_REFL \\ gs []
  \\ simp [Once tick_rel_cases]
QED

Triviality eval_simps[simp]:
  eval (Delay e) = INR (Thunk e) ∧
  eval (Lit l) = INR (Atom l) ∧
  eval (Monad mop es) = INR (Monadic mop es) ∧
  eval (Lam x body) = INR (Closure x body) ∧
  eval (Value v) = INR v ∧
  eval (Cons cn []) = INR (Constructor cn [])
Proof
  rw[thunkLangTheory.eval_def] >>
  DEEP_INTRO_TAC some_intro >> simp[thunkLangTheory.eval_to_def, result_map_def]
QED

Theorem pure_to_thunk_next[local]:
  ∀k v c s w d t.
    v_rel v w ∧
    cont_rel c d ∧
    state_rel s t ∧
    next' k v c s ≠ Err ⇒
      ∃ck. next_rel (next' k v c s) (next_delayed (k + ck) w d t)
Proof
  ho_match_mp_tac pure_semanticsTheory.next_ind \\ rw []
  \\ simp [Once next'_def]
  \\ Cases_on ‘v = wh_Error ∨
               v = wh_Diverge ∨
               (∃x. v = wh_Atom x) ∨
               (∃s x. v = wh_Closure s x)’
  >- ((* Error *)
    rgs [Once next'_def]
    \\ Cases_on ‘w’ \\ rgs [Once next_delayed_def]
    \\ gs [Once next'_def])
  \\ ‘∃n xs. v = wh_Constructor n xs’
    by (Cases_on ‘v’ \\ gs [])
  \\ gvs []
  \\ rename1 ‘v_rel _ w’ \\ Cases_on ‘w’ \\ gvs []
  \\ rename1 ‘v_rel _ (INR w)’ \\ Cases_on ‘w’ \\ gvs []
  \\ gs [LIST_REL_EL_EQN]
  >- (gvs[monad_cns_def] >> simp[next_delayed_def])
  \\ gvs[mop_cases]
  >~ [`Monadic Ret (MAP Delay _)`]
  >- ((* Ret - Delay *)
    `LENGTH zs = 1` by (CCONTR_TAC >> gvs[Once next'_def]) >>
    gvs[LENGTH_EQ_NUM_compute, numeral_less_thm]
    \\ simp [Once next_delayed_def, with_value_def,
             is_anyThunk_def, dest_anyThunk_def]
    \\ rgs [Once next'_def] \\ gvs []
    \\ Cases_on ‘k = 0’ \\ gs []
    >- (
      reverse $ Cases_on ‘c’ \\ Cases_on ‘d’ \\ rgs [] >- (qexists `0` >> simp[])
      \\ rgs[apply_closure'_def, AllCaseEqs()]
      \\ ‘eval_wh e ≠ wh_Error’ by (strip_tac \\ gs [])
      \\ drule_all_then assume_tac exp_rel_eval
      \\ Cases_on ‘eval_wh e’ \\ Cases_on ‘eval y’ \\ gvs []
      \\ qexists `0` >> simp[]
      ) >>
    reverse $ Cases_on `c` >> Cases_on `d` >> gvs[]
    >- (first_x_assum irule >> simp[mop_cases]) >>
    gvs[apply_closure_def, apply_closure'_def, with_value_def] >>
    `eval_wh e ≠ wh_Error` by (CCONTR_TAC >> gvs[]) >>
    drule_all_then assume_tac exp_rel_eval >>
    Cases_on `eval_wh e` >> Cases_on `eval e'` >> gvs[] >>
    rename1 `v_rel _ (INR w)` >> Cases_on `w` >> gvs[dest_anyClosure_def] >>
    first_x_assum irule >> simp[]
    \\ irule exp_rel_eval
    \\ gs [pure_expTheory.bind_def, FLOOKUP_UPDATE, pure_expTheory.closed_def,
           freevars_subst1, EXTENSION, SUBSET_DEF, DISJ_EQ_IMP]
    \\ irule_at Any exp_rel_subst \\ gs []
    \\ fs [pure_expTheory.closed_def, EXTENSION]
    \\ strip_tac \\ gs [Once next'_def]
    )
  >~ [`wh_Constructor "Ret"`]
  >- ((* Ret - thunk_rel *)
    `LENGTH zs = 1` by (CCONTR_TAC >> gvs[Once next'_def]) >>
    gvs[LENGTH_EQ_NUM_compute, numeral_less_thm]
    \\ simp [Once next_delayed_def, with_value_def]
    \\ `is_anyThunk h'`
      by (Cases_on `h'`
          \\ gvs [thunk_rel_def, is_anyThunk_def, dest_anyThunk_def])
    \\ rw []
    \\ rgs [Once next'_def] \\ gvs []
    \\ Cases_on ‘k = 0’ \\ gs []
    >- (
      reverse $ Cases_on ‘c’ \\ Cases_on ‘d’ \\ rgs [] >- (qexists `0` >> simp[])
      \\ rgs[apply_closure'_def, AllCaseEqs()]
      \\ ‘eval_wh e ≠ wh_Error’ by (strip_tac \\ gs [])
      \\ drule_all_then assume_tac exp_rel_eval
      \\ Cases_on ‘eval_wh e’ \\ Cases_on ‘eval y’ \\ gvs []
      \\ qexists `0` >> simp[]
      ) >>
    reverse $ Cases_on `c` >> Cases_on `d` >> gvs[]
    >- (first_x_assum irule >> simp[mop_cases]) >>
    gvs[apply_closure_def, apply_closure'_def, with_value_def] >>
    `eval_wh e ≠ wh_Error` by (CCONTR_TAC >> gvs[]) >>
    drule_all_then assume_tac exp_rel_eval >>
    Cases_on `eval_wh e` >> Cases_on `eval e'` >> gvs[] >>
    rename1 `v_rel _ (INR w)` >> Cases_on `w` >> gvs[dest_anyClosure_def] >>
    first_x_assum irule >> simp[]
    \\ irule exp_rel_eval
    \\ gs [pure_expTheory.bind_def, FLOOKUP_UPDATE, pure_expTheory.closed_def,
           freevars_subst1, EXTENSION, SUBSET_DEF, DISJ_EQ_IMP]
    \\ gvs[thunk_rel_def]
    \\ irule_at Any exp_rel_subst \\ gs []
    \\ strip_tac \\ gs [Once next'_def]
    )
  >~ [`Monadic Raise (MAP Delay _)`]
  >- ((* Raise - Delay *)
    `LENGTH zs = 1` by (CCONTR_TAC >> gvs[Once next'_def]) >>
    gvs[LENGTH_EQ_NUM_compute, numeral_less_thm]
    \\ simp [Once next_delayed_def, with_value_def,
             is_anyThunk_def, dest_anyThunk_def]
    \\ rgs [Once next'_def] \\ gvs []
    \\ Cases_on ‘k = 0’ \\ gs []
    >- (
      Cases_on ‘c’ \\ Cases_on ‘d’ \\ rgs [] >- (qexists `0` >> simp[])
      \\ rgs[apply_closure'_def, AllCaseEqs()]
      \\ ‘eval_wh e ≠ wh_Error’ by (strip_tac \\ gs [])
      \\ drule_all_then assume_tac exp_rel_eval
      \\ Cases_on ‘eval_wh e’ \\ Cases_on ‘eval y’ \\ gvs []
      \\ qexists `0` >> simp[]
      ) >>
    Cases_on `c` >> Cases_on `d` >> gvs[]
    >- (first_x_assum irule >> simp[mop_cases]) >>
    gvs[apply_closure_def, apply_closure'_def, with_value_def] >>
    `eval_wh e ≠ wh_Error` by (CCONTR_TAC >> gvs[]) >>
    drule_all_then assume_tac exp_rel_eval >>
    Cases_on `eval_wh e` >> Cases_on `eval e'` >> gvs[] >>
    rename1 `v_rel _ (INR w)` >> Cases_on `w` >> gvs[dest_anyClosure_def] >>
    first_x_assum irule >> simp[]
    \\ irule exp_rel_eval
    \\ gs [pure_expTheory.bind_def, FLOOKUP_UPDATE, pure_expTheory.closed_def,
           freevars_subst1, EXTENSION, SUBSET_DEF, DISJ_EQ_IMP]
    \\ irule_at Any exp_rel_subst \\ gs []
    \\ fs [pure_expTheory.closed_def, EXTENSION]
    \\ strip_tac \\ gs [Once next'_def]
    )
  >~ [`wh_Constructor "Raise"`]
  >- ((* Raise - thunk_rel *)
    `LENGTH zs = 1` by (CCONTR_TAC >> gvs[Once next'_def]) >>
    gvs[LENGTH_EQ_NUM_compute, numeral_less_thm]
    \\ simp [Once next_delayed_def, with_value_def]
    \\ `is_anyThunk h'`
      by (Cases_on `h'`
          \\ gvs [thunk_rel_def, is_anyThunk_def, dest_anyThunk_def])
    \\ rgs [Once next'_def] \\ gvs []
    \\ Cases_on ‘k = 0’ \\ gs []
    >- (
      Cases_on ‘c’ \\ Cases_on ‘d’ \\ rgs [] >- (qexists `0` >> simp[])
      \\ rgs[apply_closure'_def, AllCaseEqs()]
      \\ ‘eval_wh e ≠ wh_Error’ by (strip_tac \\ gs [])
      \\ drule_all_then assume_tac exp_rel_eval
      \\ Cases_on ‘eval_wh e’ \\ Cases_on ‘eval y’ \\ gvs []
      \\ qexists `0` >> simp[]
      ) >>
    Cases_on `c` >> Cases_on `d` >> gvs[]
    >- (first_x_assum irule >> simp[mop_cases]) >>
    gvs[apply_closure_def, apply_closure'_def, with_value_def] >>
    `eval_wh e ≠ wh_Error` by (CCONTR_TAC >> gvs[]) >>
    drule_all_then assume_tac exp_rel_eval >>
    Cases_on `eval_wh e` >> Cases_on `eval e'` >> gvs[] >>
    rename1 `v_rel _ (INR w)` >> Cases_on `w` >> gvs[dest_anyClosure_def] >>
    first_x_assum irule >> simp[]
    \\ irule exp_rel_eval
    \\ gs [pure_expTheory.bind_def, FLOOKUP_UPDATE, pure_expTheory.closed_def,
           freevars_subst1, EXTENSION, SUBSET_DEF, DISJ_EQ_IMP]
    \\ gvs[thunk_rel_def]
    \\ irule_at Any exp_rel_subst \\ gs []
    \\ fs [pure_expTheory.closed_def, EXTENSION]
    \\ strip_tac \\ gs [Once next'_def]
    )
  >~ [`wh_Constructor "Bind"`]
  >- ((* Bind *)
    `LENGTH xs = 2` by (CCONTR_TAC >> gvs[Once next'_def]) >>
    gvs[LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss] >>
    simp [Once next_delayed_def]
    \\ IF_CASES_TAC \\ gs [] >- (qexists `0` >> simp[])
    \\ first_x_assum irule \\ gs []
    \\ gs [Once next'_def]
    \\ irule exp_rel_eval \\ gs []
    \\ gvs[Once next'_def] \\ CCONTR_TAC \\ gvs[]
    )
  >~ [`wh_Constructor "Handle"`]
  >- ((* Handle *)
    `LENGTH l = 2` by (CCONTR_TAC >> gvs[Once next'_def]) >>
    gvs[LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss] >>
    simp [Once next_delayed_def]
    \\ IF_CASES_TAC \\ gs [] >- (qexists `0` >> simp[])
    \\ first_x_assum irule \\ gs []
    \\ gs [Once next'_def]
    \\ irule exp_rel_eval \\ gs []
    \\ gvs[Once next'_def] \\ CCONTR_TAC \\ gvs[]
    )
  >~ [`Act`]
  >- ((* Act *)
    `LENGTH zs = 1` by (CCONTR_TAC >> gvs[Once next'_def]) >>
    gvs[LENGTH_EQ_NUM_compute, numeral_less_thm] >>
    ntac 2 $ simp[Once next_delayed_def] >>
    gs [Once next'_def] >>
    gvs[pure_semanticsTheory.with_atom_def,
        pure_semanticsTheory.with_atoms_def,
        thunk_semanticsTheory.with_atoms_def,
        result_map_def] >>
    (*qrefine `ck + 1` >> simp[] >>*)
    `eval_wh h ≠ wh_Error` by (CCONTR_TAC >> gvs[]) >>
    drule_all_then assume_tac exp_rel_eval >>
    rename1 `v_rel (eval_wh x) (eval y)` >>
    Cases_on `eval_wh x` >> Cases_on `eval y` >>
    gvs[pure_semanticsTheory.get_atoms_def] >>
    rename1 `v_rel (wh_Atom a) (INR b)` >> Cases_on `b` >> gvs[] >>
    simp[thunk_semanticsTheory.get_atoms_def] >> CASE_TAC >> gvs[]
    )
  >~ [`Alloc`]
  >- ((* Alloc *)
    `LENGTH zs = 2` by (CCONTR_TAC >> gvs[Once next'_def]) >>
    gvs[LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss] >>
    simp[LUPDATE_DEF] >>
    rename1 `wh_Constructor _ [x1;x2]` >> rename1 `Monadic Alloc [z1; _ z2]`
    \\ rgs [Once next'_def]
    \\ rgs [pure_semanticsTheory.with_atom_def,
            pure_semanticsTheory.with_atoms_def] >>
    `eval_wh x1 ≠ wh_Error` by (CCONTR_TAC >> gvs[]) >>
    drule_all_then assume_tac exp_rel_eval >>
    simp[Once next_delayed_def] >>
    simp[thunk_semanticsTheory.with_atoms_def, result_map_def] >>
    reverse $ Cases_on `eval_wh x1` >> gvs[pure_semanticsTheory.get_atoms_def]
    >- (
      Cases_on `k = 0` >> gvs[] >>
      Cases_on `eval z1` >> gvs[]
      ) >>
    Cases_on `eval z1` >> gvs[] >> rename1 `eval z1 = INR y` >>
    simp [is_anyThunk_def, dest_anyThunk_def] >>
    Cases_on `y` >> gvs[] >> simp[thunk_semanticsTheory.get_atoms_def] >>
    BasicProvers.TOP_CASE_TAC >> gvs[] >>
    IF_CASES_TAC >> gvs[] >- (qexists `0` >> simp[]) >>
    first_x_assum irule >> rw[] >> gvs[state_rel_def]
    >- gvs[LIST_REL_EL_EQN, EL_REPLICATE, thunk_rel_def] >>
    gvs[mop_cases] >> simp[Once exp_rel_cases] >> gvs[LIST_REL_EL_EQN]
    )
  >~ [`Length`]
  >- ((* Length *)
    `LENGTH zs = 1` by (CCONTR_TAC >> gvs[Once next'_def]) >>
    gvs[LENGTH_EQ_NUM_compute, numeral_less_thm] >>
    rename1 `wh_Constructor _ [x]` >> rename1 `Monadic Length [y]`
    \\ rgs [Once next'_def]
    \\ rgs [pure_semanticsTheory.with_atom_def,
            pure_semanticsTheory.with_atoms_def,
            thunk_semanticsTheory.with_atoms_def]
    \\ ‘eval_wh x ≠ wh_Error’ by (strip_tac \\ gs []) >>
    simp[Once next_delayed_def] >>
    simp[thunk_semanticsTheory.with_atoms_def, result_map_def] >>
    drule_all_then assume_tac exp_rel_eval >> simp[] >>
    reverse $ Cases_on `eval_wh x` >> gvs[pure_semanticsTheory.get_atoms_def]
    >- (
      Cases_on `k = 0` >> gvs[] >>
      Cases_on `eval y` >> gvs[]
      ) >>
    Cases_on `eval y` >> gvs[] >> rename1 `eval y = INR a` >>
    Cases_on `a` >> gvs[] >> rename1 `Atom a` >>
    simp[thunk_semanticsTheory.get_atoms_def] >>
    BasicProvers.TOP_CASE_TAC >> gvs[] >>
    `LENGTH s = LENGTH t` by gvs[state_rel_def, LIST_REL_EL_EQN] >>
    IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[] >- (qexists `0` >> simp[]) >>
    first_x_assum irule >> rw[] >> gvs[mop_cases] >>
    `LENGTH (EL n s) = LENGTH (EL n t)` by gvs[state_rel_def, LIST_REL_EL_EQN] >>
    simp[Once exp_rel_cases]
    )
  >~ [`Deref`]
  >- ((* Deref *)
    rename1 `wh_Constructor "Deref" zs` >>
    `LENGTH zs = 2` by (CCONTR_TAC >> gvs[Once next'_def]) >>
    gvs[LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss] >>
    rename1 `wh_Constructor _ [x1;x2]` >> rename1 `Monadic Deref [z1;z2]` >>
    simp [Once next_delayed_def]
    \\ rgs [Once next'_def]
    \\ rgs [pure_semanticsTheory.with_atom_def,
            pure_semanticsTheory.with_atoms_def,
            thunk_semanticsTheory.with_atoms_def, result_map_def,
            pure_semanticsTheory.with_atom2_def]
    \\ ‘eval_wh x1 ≠ wh_Error’ by (strip_tac \\ gs [])
    \\ drule_all_then assume_tac exp_rel_eval
    \\ ‘eval_wh x2 ≠ wh_Error’ by (strip_tac \\ gs [])
    \\ drule_all_then assume_tac exp_rel_eval
    \\ Cases_on `eval z1 = INL Type_error` \\ gs []
    \\ Cases_on `eval z2 = INL Type_error` \\ gs []
    \\ IF_CASES_TAC \\ gs []
    >- (Cases_on ‘eval z1’ \\ gs [])
    >- (Cases_on ‘eval z2’ \\ gs [])
    \\ Cases_on ‘eval_wh x1’ \\ Cases_on ‘eval_wh x2’
    \\ gs [pure_semanticsTheory.get_atoms_def] >>
    namedCases_on `eval z1` ["a1", "a1"] >> gvs[] >> Cases_on `a1` >> gvs[] >>
    namedCases_on `eval z2` ["a2", "a2"] >> gvs[] >> Cases_on `a2` >> gvs[] >>
    simp[thunk_semanticsTheory.get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ ‘LENGTH s = LENGTH t’ by gs [state_rel_def, LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ gs [] \\
    Cases_on `k = 0` >> gvs[] >- (qexists `0` >> simp[]) >>
    `LENGTH (EL n s) = LENGTH (EL n t)` by gvs[state_rel_def, LIST_REL_EL_EQN] >>
    IF_CASES_TAC >> gvs[DISJ_EQ_IMP]
    >- (
      first_x_assum irule >> simp[mop_cases] >>
      `Num i < LENGTH (EL n s)` by intLib.ARITH_TAC >> gvs[] >>
      gvs[state_rel_def, LIST_REL_EL_EQN] >>
      gvs[arithmeticTheory.NOT_LESS_EQUAL] >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      pop_assum drule >> rw[thunk_rel_def]
      )
    >- (
      BasicProvers.TOP_CASE_TAC >- gvs[] >>
      first_x_assum irule >> simp[mop_cases, PULL_EXISTS] >>
      goal_assum $ drule_at Any >> irule_at Any integerTheory.INT_LT_REFL >>
      simp[Once exp_rel_cases, monad_cns_def]
      )
    )
  >~ [`Update`]
  >- ((* Update *)
    `LENGTH zs = 3` by (CCONTR_TAC >> gvs[Once next'_def]) >>
    gvs[LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss] >>
    rename1 `wh_Constructor _ [x1;x2;x3]` >>
    rename1 `Monadic _ (LUPDATE _ _ [z1;z2;z3])` >>
    simp [Once next_delayed_def] >> simp[LUPDATE_DEF]
    \\ rgs [Once next'_def]
    \\ rgs [pure_semanticsTheory.with_atom_def,
            pure_semanticsTheory.with_atoms_def,
            thunk_semanticsTheory.with_atoms_def, result_map_def,
            pure_semanticsTheory.with_atom2_def]
    \\ ‘eval_wh x1 ≠ wh_Error’ by (strip_tac \\ gs [])
    \\ drule_all_then assume_tac exp_rel_eval
    \\ ‘eval_wh x2 ≠ wh_Error’ by (strip_tac \\ gs [])
    \\ drule_all_then assume_tac exp_rel_eval
    \\ Cases_on `eval z1 = INL Type_error` \\ gs []
    \\ Cases_on `eval z2 = INL Type_error` \\ gs []
    \\ IF_CASES_TAC \\ gs []
    >- (Cases_on ‘eval z1’ \\ gs [])
    >- (Cases_on ‘eval z2’ \\ gs [])
    \\ Cases_on ‘eval_wh x1’ \\ Cases_on ‘eval_wh x2’
    \\ gs [pure_semanticsTheory.get_atoms_def] \\
    namedCases_on `eval z1` ["a1", "a1"] >> gvs[] >> Cases_on `a1` >> gvs[] >>
    namedCases_on `eval z2` ["a2", "a2"] >> gvs[] >> Cases_on `a2` >> gvs[] >>
    simp [is_anyThunk_def, dest_anyThunk_def] >>
    simp[thunk_semanticsTheory.get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ ‘LENGTH s = LENGTH t’ by gs [state_rel_def, LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ gs [arithmeticTheory.NOT_LESS_EQUAL] >>
    `LENGTH (EL n s) = LENGTH (EL n t)` by gvs[state_rel_def, LIST_REL_EL_EQN] >>
    Cases_on `k = 0` >> gvs[] >- (qexists `0` >> simp[]) >>
    IF_CASES_TAC >> gvs[DISJ_EQ_IMP]
    >- (
      first_x_assum irule >> simp[mop_cases] >>
      simp[Once exp_rel_cases, monad_cns_def] >>
      gvs[state_rel_def, LIST_REL_EL_EQN, EL_LUPDATE, COND_RAND] >>
      simp[thunk_rel_def]
      )
    >- (
      first_x_assum irule >> simp[mop_cases, PULL_EXISTS] >>
      goal_assum $ drule_at Any >> irule_at Any integerTheory.INT_LT_REFL >>
      simp[Once exp_rel_cases, monad_cns_def]
      )
    )
QED

Theorem pure_to_thunk_next_action':
  v_rel v w ∧
  cont_rel c d ∧
  state_rel s t ⇒
  next_action' v c s ≠ Err ⇒
    next_rel (next_action' v c s) (next_action_delayed w d t)
Proof
  rw[] >>
  `∀k. next' k v c s ≠ Err` by (
    CCONTR_TAC >> qpat_x_assum `next_action' _ _ _ ≠ _` mp_tac >>
    gvs[next_action'_def] >> DEEP_INTRO_TAC some_intro >> rw[]
    >- (drule next'_next' >> disch_then $ qspec_then `k` mp_tac >> simp[])
    >- (qexists `k` >> simp[])) >>
  qpat_x_assum `next_action' _ _ _ ≠ Err` mp_tac >>
  simp[next_action'_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
  >- (
    rw[next_action_delayed_def] >>
    DEEP_INTRO_TAC some_intro >> rw[] >>
    `next' x v c s ≠ Err` by simp[] >>
    drule_all_then assume_tac pure_to_thunk_next >> gvs[] >>
    drule next_delayed_less_eq >> disch_then $ qspec_then `ck + x` mp_tac >>
    gvs[]
    ) >>
  `next' x v c s ≠ Err` by simp[] >>
  drule_all_then assume_tac pure_to_thunk_next >> gvs[] >>
  simp[next_action_delayed_def] >> DEEP_INTRO_TAC some_intro >> rw[] >> gvs[] >>
  drule next_delayed_next_delayed >>
  disch_then $ qspec_then `ck + x` assume_tac >>
  Cases_on `next' x v c s` >> Cases_on `next_delayed (ck + x) w d t` >> gvs[]
QED

Theorem pure_to_thunk_interp_alt[local]:
  v_rel v w ∧
  cont_rel c d ∧
  state_rel s t ∧
  safe_itree (interp_alt v c s) ⇒
    interp_alt v c s = interp_delayed w d t
Proof
  rw [Once itreeTheory.itree_bisimulation]
  \\ qexists_tac ‘
    λt1 t2.
      safe_itree t1 ∧
      (t1 = t2 ∨
       ∃v c s w d t.
         t1 = interp_alt v c s ∧
         t2 = interp_delayed w d t ∧
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
    \\ drule_all_then assume_tac pure_to_thunk_next_action'
    \\ qpat_x_assum ‘Ret _ = _’ mp_tac
    \\ once_rewrite_tac [interp_delayed_def, interp_alt_def]
    \\ Cases_on ‘next_action' v' c' s'’
    \\ Cases_on ‘next_action_delayed w' d' t''’ \\ gvs [])
  >- (
    ‘next_action' v' c' s' ≠ Err’
      by (strip_tac
          \\ qpat_x_assum ‘interp_alt v' _ _ = _’ mp_tac
          \\ rw [Once interp_alt_def])
    \\ drule_all_then assume_tac pure_to_thunk_next_action'
    \\ qpat_x_assum ‘_ = Div’ mp_tac
    \\ once_rewrite_tac [interp_delayed_def, interp_alt_def]
    \\ Cases_on ‘next_action' v' c' s'’
    \\ Cases_on ‘next_action_delayed w' d' t''’ \\ gvs [])
  >- (
    rgs [Once safe_itree_cases])
  \\ ‘next_action' v' c' s' ≠ Err’
    by (strip_tac
        \\ qpat_x_assum ‘interp_alt v' _ _ ≠ _’ mp_tac
        \\ rw [Once interp_alt_def])
  \\ drule_all_then assume_tac pure_to_thunk_next_action'
  \\ qpat_x_assum ‘Vis _ _ = _’ mp_tac
  \\ rw [Once interp_alt_def, Once interp_delayed_def]
  \\ Cases_on ‘next_action' v' c' s'’
  \\ Cases_on ‘next_action_delayed w' d' t''’ \\ gvs []
  \\ rgs [Once safe_itree_cases]
  \\ rw [] \\ CASE_TAC \\ gs [] \\ rw []
  \\ disj2_tac
  \\ irule_at Any EQ_REFL
  \\ irule_at Any EQ_REFL \\ gvs[mop_cases] \\ simp[Once exp_rel_cases]
  \\ first_x_assum (qspec_then ‘INR y’ assume_tac)
  \\ rgs [Once safe_itree_cases]
QED

Theorem pure_to_thunk_interp[local]:
  tick_wh_rel v0 v ∧ v_rel v w ∧
  tcont_rel c0 c ∧ cont_rel c d ∧
  tstate_rel s0 s ∧ state_rel s t ∧
  safe_itree (interp v0 c0 s0) ⇒
    interp v0 c0 s0 = interp_delayed w d t
Proof
  rw []
  \\ drule_all_then assume_tac interp_alt_thm \\ gs []
  \\ irule pure_to_thunk_interp_alt \\ gs []
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
  tick_rel x0 x ∧ exp_rel x y ∧
  closed x0 ∧
  safe_itree (semantics x0 Done []) ⇒
    semantics x0 Done [] = semantics_delayed y Done []
Proof
  strip_tac
  \\ drule_then assume_tac semantics_fail
  \\ gs [pure_semanticsTheory.semantics_def, semantics_delayed_def]
  \\ irule pure_to_thunk_interp \\ gs []
  \\ simp [state_rel_def, tstate_rel_def]
  \\ irule_at Any tick_rel_eval_wh
  \\ last_assum (irule_at Any) \\ qexists_tac ‘Done’
  \\ irule_at Any exp_rel_eval \\ gs []
  \\ drule_then assume_tac tick_rel_freevars
  \\ gs [pure_expTheory.closed_def]
  \\ drule_then assume_tac tick_rel_eval_wh
  \\ strip_tac
  \\ Cases_on ‘eval_wh x0’ \\ gs []
QED

(* This relation is the composition of tick_rel with exp_rel, and thus takes
 * the full pure_to_thunk step.
 *)

Inductive compile_rel:
[~Var:]
  (∀n.
     compile_rel (pure_exp$Var n) (Force (Var n)))
[~Lam:]
  (∀s x y.
     compile_rel x y ⇒
       compile_rel (Lam s x) (Lam s y))
[~App:]
  (∀f g x y.
     compile_rel f g ∧
     compile_rel x y ⇒
       compile_rel (App f x) (App g (Delay y)))
[~Let:]
  (∀f g x y.
     compile_rel f g ∧
     compile_rel x y ⇒
       compile_rel (Let s x f) (Let (SOME s) (Delay y) g))
[~Fail:]
  (compile_rel Fail Fail)
[~If:]
  (∀x1 y1 z1 x2 y2 z2.
     LIST_REL compile_rel [x1; y1; z1] [x2; y2; z2] ⇒
       compile_rel (If x1 y1 z1) (If x2 y2 z2))
[~Cons:]
  (∀n xs ys.
     LIST_REL compile_rel xs ys ∧ n ∉ monad_cns ⇒
       compile_rel (Cons n xs) (Prim (Cons n) (MAP Delay ys)))
[~Monadic:]
  (∀n mop xs ys.
     mop_rel n mop ∧
     LIST_REL compile_rel xs ys ⇒
       compile_rel (Cons n xs) (Monad mop ys))
[~Monadic_Ret:]
  (∀n mop xs ys.
     mop_ret_rel n mop ∧
     LIST_REL compile_rel xs ys ⇒
       compile_rel (Cons n xs) (Monad mop (MAP Delay ys)))
[~Monadic_Delay:]
  (∀n mop idopt xs ys.
     mop_delay_rel n mop idopt ∧ (∀idx. idopt = SOME idx ⇒ idx < LENGTH xs) ∧
     LIST_REL compile_rel xs ys ⇒
        compile_rel (Cons n xs) (Monad mop (opt_delay_arg idopt ys)))
[~Deref:]
  (∀xs ys.
     LIST_REL compile_rel xs ys ⇒
       compile_rel (Cons "Deref" xs) (Monad Deref ys))
[~Update:]
  (∀xs ys.
     LIST_REL compile_rel xs ys ∧ 2 < LENGTH xs ⇒
       compile_rel (Cons "Update" xs)
                   (Monad Update (opt_delay_arg (SOME 2n) ys)))
[~Proj:]
  (∀s i xs ys.
     LIST_REL compile_rel xs ys ∧ s ∉ monad_cns ⇒
       compile_rel (Prim (Proj s i) xs) (Force (Prim (Proj s i) ys)))
[~Seq:]
  (∀x1 x2 y1 y2.
     LIST_REL compile_rel [x1; y1] [x2; y2] ⇒
       compile_rel (Seq x1 y1) (Let NONE x2 y2))
[~Seq_fresh:]
  (∀x1 x2 y1 y2.
     LIST_REL compile_rel [x1; y1] [x2; y2] ∧
     fresh ∉ freevars y1 ⇒
       compile_rel (Seq x1 y1) (Let (SOME fresh) x2 y2))
[~Prim:]
  (∀op xs ys.
     op ≠ If ∧
     op ≠ Seq ∧
     (∀n. op ≠ Cons n) ∧
     (∀s i. op ≠ Proj s i) ∧
     (∀s i a. op = IsEq s i a ⇒ a) ∧
     LIST_REL compile_rel xs ys ⇒
       compile_rel (Prim op xs) (Prim op ys))
[~Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn, x) (gn, y). fn = gn ∧ compile_rel x y) f g ∧
     compile_rel x y ⇒
       compile_rel (Letrec f x) (Letrec (MAP (λ(gn, x). (gn, Delay x)) g) y))
End

Theorem LIST_REL_lemma[local]:
  ∀xs ys.
    LIST_REL (λx y. ∃x'. R1 x x' ∧ R2 x' y) xs ys ⇒
      ∃xs'. LIST_REL R1 xs xs' ∧ LIST_REL R2 xs' ys
Proof
  Induct \\ simp []
  \\ Cases_on ‘ys’ \\ simp []
  \\ rw [PULL_EXISTS]
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem compile_rel_thm:
  ∀x y. compile_rel x y ⇒ ∃x'. tick_rel x x' ∧ exp_rel x' y
Proof
  ho_match_mp_tac compile_rel_ind \\ rw []
  >- ((* Var *)
    irule_at Any exp_rel_Var
    \\ simp [tick_rel_Var])
  >- ((* Lam *)
    irule_at Any exp_rel_Lam
    \\ irule_at Any tick_rel_Lam
    \\ first_assum (irule_at Any)
    \\ gs [])
  >- ((* App *)
    irule_at Any exp_rel_App
    \\ irule_at Any tick_rel_App
    \\ irule_at (Pos (el 2)) tick_rel_Tick
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* Let *)
    irule_at Any exp_rel_Let
    \\ irule_at Any tick_rel_App
    \\ irule_at Any tick_rel_Lam
    \\ irule_at (Pos (el 2)) tick_rel_Tick
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* Fail *)
    irule_at Any exp_rel_Prim
    \\ irule_at Any tick_rel_Prim
    \\ gs [SF SFY_ss])
  >- ((* If *)
    irule_at Any exp_rel_If
    \\ irule_at Any tick_rel_Prim
    \\ gs [SF SFY_ss])
  >- ((* Cons *)
    irule_at Any exp_rel_Cons
    \\ irule_at Any tick_rel_Prim \\ simp[]
    \\ irule_at Any LIST_REL_lemma \\ gs [])
  >- ((* Monad - mop_rel *)
    irule_at Any exp_rel_Monad >> goal_assum drule
    \\ irule_at Any tick_rel_Prim \\ simp[]
    \\ irule_at Any LIST_REL_lemma \\ gs [])
  >- ((* Monad - mop_ret_rel *)
    irule_at Any exp_rel_Monad_Ret >> goal_assum drule
    \\ irule_at Any tick_rel_Prim \\ simp[]
    \\ irule_at Any LIST_REL_lemma \\ gs [])
  >- ((* Monad - mop_delay_rel *)
    irule_at Any exp_rel_Monad_Delay >> goal_assum drule >>
    drule LIST_REL_lemma >> rw[] >>
    irule_at Any tick_rel_Prim >> goal_assum drule >> gvs[] >>
    imp_res_tac LIST_REL_LENGTH >> gvs[]
    )
  >- ( (* Deref *)
    irule_at Any exp_rel_Deref
    \\ irule_at Any tick_rel_Prim
    \\ irule_at Any LIST_REL_lemma \\ gs [])
  >- ( (* Update *)
    irule_at Any $ SRULE [] exp_rel_Update
    \\ irule_at Any tick_rel_Prim
    \\ drule LIST_REL_lemma \\ rw[]
    \\ rpt $ goal_assum drule
    \\ imp_res_tac LIST_REL_LENGTH \\ gs[])
  >- ((* Proj *)
    irule_at Any exp_rel_Proj \\ simp[]
    \\ irule_at Any tick_rel_Prim
    \\ irule_at Any LIST_REL_lemma \\ gs [])
  >- ((* Seq *)
    irule_at Any exp_rel_Seq
    \\ irule_at Any tick_rel_Prim \\ gs []
    \\ first_assum (irule_at (Pos hd))
    \\ first_assum (irule_at (Pos hd)) \\ gs []
    \\ imp_res_tac tick_rel_freevars
    \\ gvs [pure_expTheory.closed_def])
  >- ((* Seq fresh *)
    irule_at Any exp_rel_Seq_fresh
    \\ irule_at Any tick_rel_Prim \\ gs []
    \\ first_assum (irule_at (Pos hd))
    \\ first_assum (irule_at (Pos hd)) \\ gs []
    \\ imp_res_tac tick_rel_freevars
    \\ gvs [pure_expTheory.closed_def])
  >- ((* Prim *)
    irule_at Any exp_rel_Prim
    \\ irule_at Any tick_rel_Prim \\ gs []
    \\ simp [AC CONJ_COMM CONJ_ASSOC]
    \\ once_rewrite_tac [CONJ_ASSOC]
    \\ once_rewrite_tac [CONJ_COMM]
    \\ rw [RIGHT_EXISTS_AND_THM]
    \\ irule_at Any LIST_REL_lemma \\ gs [])
  >- ((* Letrec *)
    irule_at Any exp_rel_Letrec
    \\ irule_at Any tick_rel_Letrec
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule LIST_REL_lemma
    \\ irule EVERY2_mono
    \\ first_assum (irule_at Any)
    \\ gs [LAMBDA_PROD, EXISTS_PROD, FORALL_PROD] \\ rw []
    \\ first_assum (irule_at Any) \\ gs []
    \\ imp_res_tac tick_rel_freevars
    \\ gvs [pure_expTheory.closed_def])
QED

Theorem compile_rel_freevars:
  compile_rel x y ⇒ freevars x = freevars y
Proof
  rw []
  \\ imp_res_tac compile_rel_thm
  \\ imp_res_tac exp_rel_freevars
  \\ imp_res_tac tick_rel_freevars
  \\ gvs []
QED

Theorem compile_semantics:
  compile_rel x y ∧
  closed x ∧
  safe_itree (semantics x Done []) ⇒
    semantics x Done [] = semantics_delayed y Done []
Proof
  strip_tac
  \\ drule_then strip_assume_tac compile_rel_thm
  \\ drule_all pure_to_thunk_semantics \\ rw []
QED

val _ = export_theory ();
