(*
  This stage removes some unnecessary thunk allocations that are introduced by
  the pure_to_thunk stage of the compiler.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax intLib;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite;
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory
     thunk_untickProofTheory;

val _ = new_theory "thunk_unthunkProof";

val _ = set_grammar_ancestry ["finite_map", "pred_set", "rich_list",
                              "thunkLang", "thunk_semantics", "thunkLangProps"];

val _ = numLib.prefer_num ();

Theorem SUM_REL_THM[local,simp] = sumTheory.SUM_REL_THM;

(* --------------------------
   exp_inv:
   --------------------------

   The thunk_unthunk step sits just after the pure_to_thunk step, and the syntax
   is expected look like the syntax produced by the latter:
   - variables are bound to thunks using Delays under Letrecs,
   - arguments to function- and constructor application are thunked using Delay

 *)

Inductive exp_inv:
[exp_inv_Var:]
  (∀v.
     exp_inv (Var v)) ∧
[exp_inv_Value:]
  (∀v.
     v_inv v ⇒
       exp_inv (Value v)) ∧
[exp_inv_App:]
  (∀f x.
     exp_inv f ∧
     exp_inv x ⇒
       exp_inv (App f (Delay x))) ∧
[exp_inv_Lam:]
  (∀s x.
     exp_inv x ⇒
       exp_inv (Lam s x)) ∧
[exp_inv_Letrec:]
  (∀f x.
     EVERY exp_inv (MAP SND f) ∧
     exp_inv x ⇒
       exp_inv (Letrec (MAP (λ(f,x). (f, Delay x)) f) x)) ∧
[exp_inv_Let:]
  (∀bv x y.
     exp_inv x ∧
     exp_inv y ⇒
       exp_inv (Let bv x y)) ∧
[exp_inv_If:]
  (∀x y z.
     exp_inv x ∧
     exp_inv y ∧
     exp_inv z ⇒
       exp_inv (If x y z)) ∧
[exp_inv_Prim_Cons:]
  (∀nm xs.
     EVERY exp_inv xs ⇒
       exp_inv (Prim (Cons nm) (MAP Delay xs))) ∧
[exp_inv_Prim:]
  (∀op xs.
     (∀nm. op ≠ Cons nm) ∧
     EVERY exp_inv xs ⇒
       exp_inv (Prim op xs)) ∧
[exp_inv_Monad:]
  (∀mop xs.
     EVERY exp_inv xs ⇒
       exp_inv (Monad mop xs)) ∧
[exp_inv_Delay:]
  (∀x.
     exp_inv x ⇒
       exp_inv (Delay x)) ∧
[exp_inv_Force:]
  (∀x.
    exp_inv x ⇒
      exp_inv (Force x)) ∧
[v_inv_Atom:]
  (∀x.
     v_inv (Atom x)) ∧
[v_inv_Constructor:]
  (∀s vs.
     EVERY v_inv vs ⇒
       v_inv (Constructor s vs)) ∧
[v_inv_Monadic:]
  (∀mop xs.
     EVERY exp_inv xs ⇒
       v_inv (Monadic mop xs)) ∧
[v_inv_Closure:]
  (∀s x.
     exp_inv x ⇒
       v_inv (Closure s x)) ∧
[v_inv_Recclosure:]
  (∀f n.
     EVERY (λv. ∃x. v = Delay x ∧ exp_inv x) (MAP SND f) ⇒
       v_inv (Recclosure f n)) ∧
[v_inv_Thunk:]
  (∀x.
     exp_inv x ⇒
       v_inv (Thunk x)) ∧
[v_inv_DoTick:]
  (∀v.
     v_inv v ⇒
       v_inv (DoTick v))
End

Theorem exp_inv_def:
  (∀v.
     exp_inv (Var v) = T) ∧
  (∀v.
     exp_inv (Value v) = v_inv v) ∧
  (∀f x.
     exp_inv (App f x) =
       (∃y. x = Delay y ∧
            exp_inv f ∧
            exp_inv y)) ∧
  (∀s x.
     exp_inv (Lam s x) =
       exp_inv x) ∧
  (∀bv x y.
     exp_inv (Let bv x y) =
       (exp_inv x ∧
        exp_inv y)) ∧
  (∀f x.
     exp_inv (Letrec f x) =
       (∃g. f = MAP (λ(fn,x). (fn,Delay x)) g ∧
            EVERY exp_inv (MAP SND g) ∧
            exp_inv x)) ∧
  (∀x y z.
     exp_inv (If x y z) =
       (exp_inv x ∧
        exp_inv y ∧
        exp_inv z)) ∧
  (∀nm xs.
     exp_inv (Prim (Cons nm) xs) =
       (∃ys. xs = MAP Delay ys ∧
             EVERY exp_inv ys)) ∧
  (∀op xs.
     (∀nm. op ≠ Cons nm) ⇒
     exp_inv (Prim op xs) =
       EVERY exp_inv xs) ∧
  (∀mop xs.
     exp_inv (Monad mop xs) =
       EVERY exp_inv xs) ∧
  (∀x.
     exp_inv (Force x) = exp_inv x) ∧
  (∀x.
     exp_inv (Delay x) =
       exp_inv x)
Proof
  rw [] \\ rw [Once exp_inv_cases]
  \\ rw [Once exp_inv_cases]
QED

Theorem v_inv_def[simp]:
  (∀s vs. v_inv (Constructor s vs) = EVERY v_inv vs) ∧
  (∀mop xs. v_inv (Monadic mop xs) = EVERY exp_inv xs) ∧
  (∀s x. v_inv (Closure s x) = exp_inv x) ∧
  (∀f n. v_inv (Recclosure f n) =
           EVERY (λv. ∃x. v = Delay x ∧ exp_inv x) (MAP SND f)) ∧
  (∀x. v_inv (Thunk x) = exp_inv x) ∧
  (∀v. v_inv (DoTick v) = v_inv v) ∧
  (∀x. v_inv (Atom x) = T)
Proof
  rw [] \\ rw [Once exp_inv_cases, AC CONJ_COMM CONJ_ASSOC]
QED

(* --------------------------
   exp_rel:
   --------------------------

   Since all variables will be substituted away by thunk values, an expression
   “Delay (Force (Var v))” will in practice evaluate to the same thing as
   “Var v” would, but consume more clock. The exception are those expressions
   used in Letrecs.

 *)

Definition is_delay_def[simp]:
  is_delay (Delay x) = T ∧
  is_delay _ = F
End

Inductive exp_rel:
[exp_rel_Delay_Force_Var:]
  (∀v.
     exp_rel (Delay (Force (Var v))) (MkTick (Var v))) ∧
[exp_rel_Value:]
  (∀v w.
     v_rel v w ⇒
       exp_rel (Delay (Force (Value v))) (MkTick (Value w))) ∧
[exp_rel_Var:]
  (∀v.
     exp_rel (Var v) (Var v)) ∧
[exp_rel_Value_Unchanged:]
  (∀v w.
     v_rel v w ⇒
       exp_rel (Value v) (Value w)) ∧
[exp_rel_Lam:]
  (∀s x y.
     exp_rel x y ⇒
       exp_rel (Lam s x) (Lam s y)) ∧
[exp_rel_App:]
  (∀f x g y.
     exp_rel f g ∧
     exp_rel x y ⇒
       exp_rel (App f x) (App g y)) ∧
[exp_rel_If:]
  (∀x1 y1 z1 x2 y2 z2.
     LIST_REL exp_rel [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel (If x1 y1 z1) (If x2 y2 z2)) ∧
[exp_rel_Prim:]
  (∀op xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim op xs) (Prim op ys)) ∧
[exp_rel_Monad:]
  (∀mop xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Monad mop xs) (Monad mop ys)) ∧
[exp_rel_Let:]
  (∀bv x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
       exp_rel (Let bv x1 y1) (Let bv x2 y2)) ∧
[exp_rel_Letrec:]
  (∀f x g y.
     LIST_REL (λ(f,x) (g,y).
                 f = g ∧
                 is_delay x ∧
                 is_delay y ∧
                 exp_rel x y) f g ∧
     exp_rel x y ⇒
       exp_rel (Letrec f x) (Letrec g y)) ∧
[exp_rel_Delay:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Delay x) (Delay y)) ∧
[exp_rel_Force:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Force x) (Force y)) ∧
[v_rel_Closure:]
  (∀s x y.
     exp_rel x y ∧
     freevars x ⊆ {s} ⇒
       v_rel (Closure s x) (Closure s y)) ∧
[v_rel_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y).
                 fn = gn ∧
                 is_delay x ∧
                 is_delay y ∧
                 exp_rel x y ∧
                 freevars x ⊆ set (MAP FST f)) f g ⇒
       v_rel (Recclosure f n) (Recclosure g n)) ∧
[v_rel_Constructor:]
  (∀s vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws)) ∧
[v_rel_Monadic:]
  (∀mop xs ys.
     LIST_REL exp_rel xs ys ∧ EVERY closed xs ⇒
       v_rel (Monadic mop xs) (Monadic mop ys)) ∧
[v_rel_Thunk_Same:]
  (∀x y.
     exp_rel x y ∧
     closed x ⇒
       v_rel (Thunk x) (Thunk y)) ∧
[v_rel_Thunk_Changed:]
  (∀v w.
     v_rel v w ⇒
       v_rel (Thunk (Force (Value v))) (DoTick w)) ∧
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x))
End

Theorem v_rel_def[simp]:
  (∀s x z.
     v_rel (Closure s x) z =
       (∃y. z = Closure s y ∧
                exp_rel x y ∧
                freevars x ⊆ {s})) ∧
  (∀f n z.
     v_rel (Recclosure f n) z =
       (∃g. z = Recclosure g n ∧
            LIST_REL (λ(fn,x) (gn,y).
                        fn = gn ∧
                        is_delay x ∧
                        is_delay y ∧
                        exp_rel x y ∧
                        freevars x ⊆ set (MAP FST f)) f g)) ∧
  (∀s vs z.
     v_rel (Constructor s vs) z =
       (∃ws. z = Constructor s ws ∧
             LIST_REL v_rel vs ws)) ∧
  (∀op xs z.
     v_rel (Monadic mop xs) z =
       (∃ys. z = Monadic mop ys ∧
             LIST_REL exp_rel xs ys ∧
             EVERY closed xs)) ∧
  (∀x z.
     v_rel (Atom x) z = (z = Atom x))
Proof
  rw [] \\ rw [Once exp_rel_cases]
  \\ rw [EQ_SYM_EQ, AC CONJ_COMM CONJ_ASSOC, EQ_IMP_THM]
QED

Theorem v_rel_Thunk_def:
  v_rel (Thunk x) z =
    ((∃y w. z = Thunk y ∧
            x = w ∧
            exp_rel w y ∧
            closed w) ∨
     (∃v y. x = Force (Value v) ∧
            z = DoTick y ∧
            v_rel v y))
Proof
  rw [Once exp_rel_cases]
  \\ rw [EQ_SYM_EQ, AC CONJ_COMM CONJ_ASSOC, EQ_IMP_THM, SF SFY_ss]
QED

Theorem v_rel_Thunk_simps[simp]:
  (∀x s vs. ¬v_rel (Thunk x) (Constructor s vs)) ∧
  (∀x mop xs. ¬v_rel (Thunk x) (Monadic mop xs)) ∧
  (∀x s y. ¬v_rel (Thunk x) (Closure s y)) ∧
  (∀x y. ¬v_rel (Thunk x) (Atom y)) ∧
  (∀x w. ¬v_rel (DoTick x) w)
Proof
  rpt conj_tac
  \\ Cases_on ‘x’ \\ rw [v_rel_Thunk_def]
  \\ rw [Once exp_rel_cases]
QED

Theorem v_rel_rev[simp]:
  (∀w.
     v_rel v (DoTick w) =
       (∃x. v = Thunk (Force (Value x)) ∧
            v_rel x w)) ∧
  (∀s y.
     v_rel v (Closure s y) =
       (∃x. v = Closure s x ∧
            exp_rel x y ∧
            freevars x ⊆ {s})) ∧
  (∀g n.
     v_rel v (Recclosure g n) =
       ((∃f. v = Recclosure f n ∧
             LIST_REL (λ(fn,x) (gn,y).
                         fn = gn ∧
                         is_delay x ∧
                         is_delay y ∧
                         exp_rel x y ∧
                         freevars x ⊆ set (MAP FST f)) f g))) ∧
  (∀v s vs.
     v_rel v (Constructor s vs) =
       (∃ws. v = Constructor s ws ∧
             LIST_REL v_rel ws vs)) ∧
  (∀v mop ys.
     v_rel v (Monadic mop ys) =
       (∃xs. v = Monadic mop xs ∧
             LIST_REL exp_rel xs ys ∧
             EVERY closed xs)) ∧
  (∀v s.
     v_rel v (Thunk s) =
      (∃x y.
         v = Thunk x ∧
         s = y ∧
         exp_rel x y ∧
         closed x)) ∧
  (∀v a.
     v_rel v (Atom a) = (v = Atom a))
Proof
  rw [] \\ Cases_on ‘v’ \\ simp []
  \\ rw [EQ_IMP_THM]
  \\ fs [v_rel_Thunk_def, SF SFY_ss]
QED

Theorem is_delay_subst[local,simp]:
  is_delay (subst ws x) = is_delay x
Proof
  Cases_on ‘x’ \\ rw [subst_def]
  >- (
    CASE_TAC \\ fs [])
  \\ rename1 ‘Let s’
  \\ Cases_on ‘s’ \\ rw [subst_def]
QED

Theorem exp_rel_freevars:
  ∀x y. exp_rel x y ⇒ freevars x = freevars y
Proof
  qsuff_tac ‘(∀x y. exp_rel x y ⇒ freevars x = freevars y) ∧ (∀v w. v_rel v w ⇒ T)’
  >- rw []
  \\ ho_match_mp_tac exp_rel_ind
  \\ rw [] \\ fs [freevars_def]
  >-
   (AP_TERM_TAC \\ AP_TERM_TAC
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS])
  >-
   (AP_TERM_TAC \\ AP_TERM_TAC
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS])
  >~ [‘Let opt’] >-
   (Cases_on ‘opt’ \\ rw [] \\ fs [freevars_def])
  \\ match_mp_tac $ METIS_PROVE []
     “s1 = s2 ∧ x1 = x2 ⇒ s UNION (f s1) DIFF x1 = s UNION (f s2) DIFF x2”
  \\ last_assum mp_tac
  \\ qid_spec_tac ‘g’
  \\ qid_spec_tac ‘f’
  \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD]
  \\ metis_tac []
QED

Triviality ALOOKUP_REVERSE_lemma:
  ∀vs ws.
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    MAP FST vs = MAP FST ws ⇒
    ALOOKUP (REVERSE vs) s = NONE ∧
    ALOOKUP (REVERSE ws) s = NONE ∨
    ∃v w.
      ALOOKUP (REVERSE vs) s = SOME v ∧
      ALOOKUP (REVERSE ws) s = SOME w ∧
      v_rel v w
Proof
  Induct \\ fs [PULL_EXISTS,MAP_EQ_CONS,FORALL_PROD]
  \\ rw [] \\ fs [ALOOKUP_APPEND]
  \\ first_x_assum drule \\ fs []
  \\ rw [] \\ fs []
QED

Theorem exp_rel_subst:
  ∀vs x ws y.
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    MAP FST vs = MAP FST ws ∧
    exp_rel x y ⇒
      exp_rel (subst vs x) (subst ws y)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac
  >- ((* Var *)
    rw [Once exp_rel_cases]
    \\ fs [subst_def]
    \\ Cases_on ‘ALOOKUP (REVERSE vs) s’
    \\ Cases_on ‘ALOOKUP (REVERSE ws) s’ \\ gvs []
    >- rw [Once exp_rel_cases]
    >- (gvs [ALOOKUP_NONE,MAP_REVERSE]
        \\ imp_res_tac ALOOKUP_MEM \\ gvs []
        \\ gvs [MEM_MAP,EXISTS_PROD])
    \\ drule_all ALOOKUP_REVERSE_lemma
    \\ disch_then $ qspec_then ‘s’ mp_tac
    \\ strip_tac \\ fs []
    \\ rw [Once exp_rel_cases])
  >- ((* Prim *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Prim
    \\ gs [EVERY2_MAP]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw [])
  >- ((* Monad *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Monad
    \\ gs [EVERY2_MAP]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw [])
  >- ((* If *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_If \\ fs [])
  >- ((* App *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_App \\ fs [])
  >- ((* Lam *)
    rw [Once exp_rel_cases]
    \\ gvs [subst_def]
    \\ irule exp_rel_Lam
    \\ first_x_assum irule
    \\ fs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. x ≠ s’ \\ fs []
    \\ irule LIST_REL_FILTER \\ fs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ simp [])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Let \\ fs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Let \\ gs []
    \\ first_x_assum irule
    \\ fs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. x ≠ s’ \\ fs []
    \\ irule LIST_REL_FILTER \\ fs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ simp [])
  >- ((* Letrec *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ ‘MAP FST f = MAP FST g’
      by (fs [ELIM_UNCURRY, LIST_REL_CONJ]
          \\ irule LIST_EQ
          \\ gvs [LIST_REL_EL_EQN] \\ rw [EL_MAP])
    \\ irule exp_rel_Letrec
    \\ gvs [EVERY2_MAP, LAMBDA_PROD]
    \\ first_assum (irule_at Any)
    \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. ¬MEM x (MAP FST g)’ \\ fs []
    \\ irule_at Any LIST_REL_FILTER \\ fs []
    \\ irule_at Any EVERY2_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ simp [FORALL_PROD] \\ rw []
    \\ first_assum irule
    \\ simp [MAP_FST_FILTER, SF SFY_ss]
    \\ irule_at Any LIST_REL_FILTER \\ fs []
    \\ irule_at Any EVERY2_mono
    \\ first_assum (irule_at Any) \\ rw [])
  >- ((* Delay *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def, exp_rel_Value, exp_rel_Delay, SF SFY_ss]
    \\ qmatch_asmsub_abbrev_tac ‘LIST_REL R _ _’
    \\ ‘OPTREL R (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
      by (irule LIST_REL_OPTREL
          \\ gvs [EVERY2_MAP, ELIM_UNCURRY, LIST_REL_CONJ, Abbr ‘R’]
          \\ pop_assum mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘ws’ \\ Induct_on ‘vs’ \\ Cases_on ‘ws’ \\ simp [])
    \\ gvs [Abbr ‘R’, OPTREL_def, exp_rel_Delay_Force_Var, exp_rel_Value])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Force \\ fs [])
  >- ((* Value *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ rw [Once exp_rel_cases])
  >- ((* MkTick *)
    rw [Once exp_rel_cases])
QED

Theorem exp_inv_subst:
  ∀xs x.
    EVERY v_inv (MAP SND xs) ∧
    exp_inv x ⇒
      exp_inv (subst xs x)
Proof
  qsuff_tac ‘
    (∀x. exp_inv x ⇒
       ∀xs. EVERY v_inv (MAP SND xs) ⇒
         exp_inv (subst xs x)) ∧
    (∀v. v_inv v ⇒ T)’
  >- rw []
  \\ ho_match_mp_tac exp_inv_strongind \\ rw []
  >- ((* Var *)
    simp [subst_def]
    \\ CASE_TAC \\ fs [exp_inv_def]
    \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
    \\ gs [EVERY_EL, EL_MAP]
    \\ first_x_assum (drule_then assume_tac) \\ gs [])
  >- ((* Value *)
    gvs [subst_def, exp_inv_def])
  >- ((* App *)
    gvs [subst_def, exp_inv_def])
  >- ((* Lam *)
    gvs [subst_def, exp_inv_def]
    \\ first_x_assum irule
    \\ gs [EVERY_MAP, EVERY_FILTER, EVERY_MEM, ELIM_UNCURRY, SF SFY_ss])
  >- ((* Letrec *)
    gs [subst_def, exp_inv_def]
    \\ gvs [EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
            EVERY_FILTER, GSYM FST_THM]
    \\ qpat_x_assum ‘∀xs. EVERY _ xs ⇒ _’ (irule_at Any)
    \\ gvs [EVERY_MEM, FORALL_PROD, subst_def, SF SFY_ss]
    \\ qmatch_goalsub_abbrev_tac ‘subst m’
    \\ qexists_tac ‘MAP (λ(n,x). (n,subst m x)) f’
    \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MEM_MAP, EXISTS_PROD,
           PULL_EXISTS, subst_def, exp_inv_def, SF SFY_ss]
    \\ qunabbrev_tac ‘m’
    \\ conj_tac
    >- (
      rw [MEM_FILTER]
      \\ first_x_assum (irule_at Any)
      \\ first_assum (irule_at Any))
    \\ rw []
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ first_x_assum irule
    \\ rw [MEM_FILTER]
    \\ first_x_assum (irule_at Any)
    \\ first_assum (irule_at Any))
  >- ((* Let *)
    Cases_on ‘bv’ \\ gvs [subst_def, exp_inv_def]
    \\ first_x_assum irule
    \\ gs [EVERY_MAP, EVERY_MEM, MEM_FILTER])
  >- ((* If *)
    gvs [subst_def, exp_inv_def])
  >- ((* Prim Cons *)
      gs [subst_def, exp_inv_def, EVERY_MAP, EVERY_MEM, SF SFY_ss]
      \\ rename1 ‘subst ys’
      \\ qexists_tac ‘MAP (subst ys) xs’
      \\ rw [MAP_MAP_o, combinTheory.o_DEF, subst_def]
      \\ gvs [MEM_MAP, PULL_EXISTS, exp_inv_def, subst_def])
  >- ((* Prim *)
    gvs [subst_def, exp_inv_def, EVERY_MAP, EVERY_MEM, SF SFY_ss])
  >- ((* Monad *)
    gvs [subst_def, exp_inv_def, EVERY_MAP, EVERY_MEM, SF SFY_ss])
  >- ((* Delay *)
    gvs [subst_def, exp_inv_def])
  >- ((* Force *)
    simp [subst_def]
    \\ irule exp_inv_Force \\ gs [])
QED

Theorem exp_rel_eval_to:
  ∀k x y.
    exp_rel x y ∧
    exp_inv x ∧
    closed x ⇒
      ($= +++ (λv w. v_rel v w ∧ v_inv v))
        (eval_to k x)
        (eval_to k y)
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac
  >- ((* Value *)
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def, exp_inv_def])
  >- ((* App *)
    rename1 ‘App x1 y1’
    \\ rw [Once exp_rel_cases]
    \\ rw [eval_to_def] \\ gvs [exp_inv_def]
    \\ first_x_assum (drule_all_then strip_assume_tac)
    \\ first_x_assum (drule_all_then strip_assume_tac)
    \\ Cases_on ‘eval_to k x1’ \\ Cases_on ‘eval_to k g’ \\ gs []
    \\ qpat_x_assum ‘exp_rel (Delay _) _’ mp_tac
    \\ rw [Once exp_rel_cases] \\ gs [eval_to_def]
    \\ rename1 ‘dest_anyClosure v1’
    \\ rename1 ‘v_rel v1 v2’
    THEN (
      Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gvs [dest_anyClosure_def]
      >- ((* Thunk-Thunk *)
        IF_CASES_TAC \\ gs []
        \\ qmatch_goalsub_abbrev_tac ‘_ (eval_to _ (subst [s,w1] _))
                                        (eval_to _ (subst [s,w2] _))’
        \\ ‘[s,w1] = [] ++ [s,w1]’ by gs [] \\ pop_assum SUBST1_TAC
        \\ ‘[s,w2] = [] ++ [s,w2]’ by gs [] \\ pop_assum SUBST1_TAC
        \\ first_x_assum irule \\ simp []
        \\ simp [closed_subst]
        \\ irule_at Any exp_inv_subst
        \\ irule_at Any exp_rel_subst \\ simp []
        \\ unabbrev_all_tac \\ gs [exp_inv_def]
        \\ (irule_at Any v_rel_Thunk_Changed ORELSE
            irule_at Any v_rel_Thunk_Same))
      >- ((* Recclosure-Recclosure *)
        rename1 ‘LIST_REL _ xs ys’
        \\ ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧
                            exp_rel _x _y)
                   (ALOOKUP (REVERSE xs) s)
                   (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL
              \\ gs [LIST_REL_CONJ, ELIM_UNCURRY])
        \\ gs [OPTREL_def]
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [])))
  >- ((* Lam *)
    rw [Once exp_rel_cases, Once exp_inv_cases]
    \\ fs [exp_inv_def, eval_to_def])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases]
    \\ gvs [exp_inv_def]
    \\ rename1 ‘exp_rel x1 x2’
    \\ rename1 ‘exp_rel y1 y2’
    \\ rw [eval_to_def]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_cases]
    \\ gvs [exp_inv_def]
    \\ rename1 ‘exp_rel x1 x2’
    \\ rename1 ‘exp_rel y1 y2’
    \\ rw [eval_to_def]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ first_x_assum irule
    \\ gs [closed_subst, exp_inv_subst]
    \\ irule_at Any exp_rel_subst \\ gs [])
  >- ((* If *)
    rw [Once exp_rel_cases] \\ fs [exp_inv_def]
    \\ rename1 ‘If x y z’
    \\ rw [eval_to_def] \\ gvs [exp_inv_def]
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs [])
  >- ((* Letrec *)
    rw [Once exp_rel_cases]
    \\ rw [eval_to_def] \\ gvs [exp_inv_def]
    \\ first_x_assum irule
    \\ simp [subst_funs_def, closed_subst]
    \\ irule_at Any exp_rel_subst
    \\ irule_at Any exp_inv_subst
    \\ irule_at Any LIST_EQ
    \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, SUBSET_DIFF_EMPTY,
           GSYM FST_THM, EL_MAP, EVERY_MAP, SF CONJ_ss]
    \\ gs [ELIM_UNCURRY]
    \\ gvs [LIST_REL_EL_EQN, EL_MAP, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS,
            freevars_def, MEM_EL]
    \\ rw [ELIM_UNCURRY, freevars_def, MAP_MAP_o, combinTheory.o_DEF,
           SF ETA_ss])
  >- ((* Delay *)
    rw [Once exp_rel_cases]
    \\ rgs [eval_to_def, exp_inv_def, v_rel_Thunk_Same])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ CONV_TAC (PATH_CONV "lr" (SIMP_CONV (srw_ss()) [Once eval_to_def]))
    \\ CONV_TAC (PATH_CONV "r" (SIMP_CONV (srw_ss()) [Once eval_to_def]))
    \\ rename1 ‘exp_rel x y’
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum (drule_then assume_tac)
    \\ fs [exp_inv_def] \\ gvs []
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ rename1 ‘v_rel v1 v2’
    \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gvs [dest_anyThunk_def]
    >- ((* Recclosure-Recclosure *)
      rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧
                          exp_rel _x _y)
                 (ALOOKUP (REVERSE xs) s)
                 (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gs [LIST_REL_CONJ, ELIM_UNCURRY])
      \\ rgs [OPTREL_def]
      \\ Cases_on ‘_x’ \\ gs [] \\ Cases_on ‘_y’ \\ gs []
      \\ first_x_assum irule
      \\ simp [closed_subst, subst_funs_def]
      \\ irule_at Any exp_rel_subst
      \\ irule_at Any exp_inv_subst
      \\ irule_at Any LIST_EQ
      \\ simp [EVERY2_MAP, EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF,
               LAMBDA_PROD, GSYM FST_THM]
      \\ rgs [ELIM_UNCURRY, LIST_REL_CONJ]
      \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
      \\ rgs [LIST_REL_EL_EQN, EVERY_EL, MEM_EL, PULL_EXISTS, EL_MAP, EVERY_EL,
              Once exp_rel_cases, exp_inv_def, SF CONJ_ss]
      \\ rpt (first_x_assum (drule_then strip_assume_tac))
      \\ gs [exp_inv_def, freevars_def])
    >- ((* Thunk-Thunk *)
      first_x_assum irule
      \\ gs [subst_funs_def, EVERY_EL])
    \\ gs [subst_funs_def, exp_inv_def]
    \\ first_x_assum irule
    \\ gs [EVERY_EL, EL_MAP, exp_rel_Force, exp_rel_Value_Unchanged])
  >- ((* MkTick *)
    rw [Once exp_rel_cases])
  >- ((* Prim *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ Cases_on ‘op’ \\ gs [exp_inv_def, EVERY_EL, EL_MAP, LIST_REL_EL_EQN]
    >- ((* Cons *)
      rgs [result_map_def, MAP_MAP_o, combinTheory.o_DEF, MEM_MAP, eval_to_def,
           PULL_EXISTS, MEM_EL]
      \\ IF_CASES_TAC \\ gs []
      >- (
        rpt (first_x_assum (drule_then assume_tac))
        \\ gs [exp_inv_def])
      \\ IF_CASES_TAC \\ gs []
      >- (
        rpt (first_x_assum (drule_then assume_tac))
        \\ gs [exp_inv_def])
      \\ rgs [EVERY2_MAP, EVERY_MAP, LIST_REL_EL_EQN, EVERY_EL]
      \\ rw []
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [exp_inv_def])
    >- ((* IsEq *)
      IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1 ⇔ n = 0”, exp_inv_def]
      \\ rename1 ‘exp_rel x y’
      \\ first_x_assum (drule_all_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel v1 v2’
      \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gvs []
      \\ drule_then assume_tac LIST_REL_LENGTH
      \\ IF_CASES_TAC \\ gs [])
    >- ((* Proj *)
      IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LENGTH_EQ_NUM_compute,DECIDE “n < 1 ⇔ n = 0:num”]
      \\ res_tac
      \\ Cases_on ‘eval_to (k − 1) h’
      \\ Cases_on ‘eval_to (k − 1) h'’ \\ fs []
      \\ Cases_on ‘y’ \\ Cases_on ‘y'’ \\ gvs []
      \\ drule_then assume_tac LIST_REL_LENGTH
      \\ gvs []
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LIST_REL_EL_EQN,EVERY_EL])
    >- ((* AtomOp *)
      Cases_on ‘k = 0’ \\ gs []
      >- (
        simp [result_map_def, MEM_MAP]
        \\ gs [GSYM NOT_NULL_MEM, NULL_EQ]
        \\ Cases_on ‘xs = []’ \\ gs []
        >- (
          CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [])
        \\ ‘ys ≠ []’ by (strip_tac \\ gs [])
        \\ gs [])
      \\ qmatch_goalsub_abbrev_tac ‘result_map f ys’
      \\ qsuff_tac ‘result_map f xs = result_map f ys’
      >- (
        rw []
        \\ Cases_on ‘result_map f ys’ \\ gs []
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [])
      \\ Cases_on ‘result_map f xs’
      >- (
        Cases_on ‘result_map f ys’
        >- (
          rgs [result_map_def, CaseEq "bool", Abbr ‘f’, MEM_MAP, MEM_EL,
               PULL_EXISTS]
          \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
          >- (
            rpt (first_x_assum (drule_then assume_tac))
            \\ Cases_on ‘eval_to (k - 1) (EL n xs)’
            \\ gs [CaseEqs ["sum", "v"]])
          \\ qpat_x_assum ‘n < LENGTH ys’ kall_tac
          \\ rename1 ‘m < LENGTH ys’
          \\ rpt (first_x_assum (drule_then assume_tac))
          \\ Cases_on ‘eval_to (k - 1) (EL m ys)’
          \\ rgs [CaseEqs ["sum", "v"]]
          \\ rename1 ‘v_rel _ w’
          \\ Cases_on ‘w’ \\ gs [])
        \\ gvs [result_map_def, CaseEq "bool", Abbr ‘f’, MEM_MAP, MEM_EL,
                PULL_EXISTS]
        \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        >- (
          rpt (first_x_assum (drule_then assume_tac))
          \\ Cases_on ‘eval_to (k - 1) (EL n ys)’
          \\ gs [CaseEqs ["sum", "v"]]
          \\ rename1 ‘v_rel _ w’
          \\ Cases_on ‘w’ \\ gs [])
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ Cases_on ‘eval_to (k - 1) (EL n ys)’
        \\ gvs [CaseEqs ["sum", "v"], v_rel_Thunk_def])
      \\ Cases_on ‘result_map f ys’ \\ gs []
      >- (
        gvs [result_map_def, CaseEq "bool", Abbr ‘f’, MEM_MAP, MEM_EL,
             PULL_EXISTS]
        \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        >- (
          rpt (first_x_assum (drule_then assume_tac))
          \\ Cases_on ‘eval_to (k - 1) (EL n xs)’
          \\ gs [CaseEqs ["sum", "v"]])
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ Cases_on ‘eval_to (k - 1) (EL n xs)’
        \\ gvs [CaseEqs ["sum", "v"], v_rel_Thunk_def])
      \\ irule_at Any LIST_EQ
      \\ gvs [result_map_def, MEM_EL, CaseEq "bool", EL_MAP]
      \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)] \\ rw []
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ gs [EL_MAP]
      \\ Cases_on ‘∃err. f (EL x ys) = INL err’ \\ gs []
      >- (
        Cases_on ‘err’ \\ gs [])
      \\ Cases_on ‘∃err. f (EL x xs) = INL err’ \\ gs []
      >- (
        Cases_on ‘err’ \\ gs [])
      \\ Cases_on ‘f (EL x ys)’ \\ Cases_on ‘f (EL x xs)’ \\ gs []
      \\ gs [Abbr ‘f’, PULL_EXISTS, CaseEqs ["sum", "v"]]
      \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs []))
  >- ((* Monad *)
    rw[Once exp_rel_cases] >> gvs[eval_to_def, exp_inv_def]
    )
QED

Theorem exp_rel_eval:
  exp_rel x y ∧
  exp_inv x ∧
  closed x ⇒
    ($= +++ (λv w. v_rel v w ∧ v_inv v)) (eval x) (eval y)
Proof
  simp [eval_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro
  \\ rw []
  >- (
    rename1 ‘_ (eval_to k x) (eval_to j y)’
    \\ drule_all_then (qspec_then ‘MAX j k’ assume_tac) exp_rel_eval_to
    \\ drule_then (qspec_then ‘j’ assume_tac) eval_to_mono
    \\ qpat_x_assum ‘eval_to j y ≠ INL _’ assume_tac
    \\ drule_then (qspec_then ‘k’ assume_tac) eval_to_mono
    \\ Cases_on ‘k ≤ j’ \\ gvs [arithmeticTheory.MAX_DEF])
  >- (
    rename1 ‘_ _ (eval_to k y)’
    \\ first_x_assum (qspec_then ‘k’ (assume_tac o SYM)) \\ simp []
    \\ irule exp_rel_eval_to
    \\ simp [])
  \\ rename1 ‘_ (eval_to k x) _’
  \\ first_x_assum (qspec_then ‘k’ (assume_tac o SYM)) \\ simp []
  \\ irule exp_rel_eval_to \\ simp []
QED

(* -------------------------------------------------------------------------
 * Top-level semantics
 * ------------------------------------------------------------------------- *)

Overload v_inv_rel = ``λv w. v_inv v ∧ v_rel v w``
Overload exp_inv_rel = ``λx y. exp_inv x ∧ closed x ∧ exp_rel x y``

Triviality exp_inv_rel_eval:
  exp_inv_rel x y ==>
    ($= +++ v_inv_rel) (eval x) (eval y)
Proof
  rw[] >> drule_all exp_rel_eval >>
  Cases_on `eval x` >> Cases_on `eval y` >> gvs[]
QED

Triviality exp_inv_rel_subst:
  ∀vs x ws y.
    LIST_REL v_inv_rel (MAP SND vs) (MAP SND ws) ∧
    MAP FST vs = MAP FST ws ∧
    exp_inv_rel x y ⇒
      exp_inv_rel (subst vs x) (subst ws y)
Proof
  rw[]
  >- (irule exp_inv_subst >> gvs[LIST_REL_EL_EQN, EVERY_EL])
  >- (simp[closed_subst] >> gvs[closed_def])
  >- (irule exp_rel_subst >> gvs[LIST_REL_EL_EQN, EVERY_EL])
QED

Theorem unthunk_apply_closure[local]:
  exp_inv_rel x y ∧
  v_inv_rel v2 w2 ∧
  (∀x y.
     ($= +++ v_inv_rel) x y ⇒
       next_rel v_inv_rel exp_inv_rel (f x) (g y)) ⇒
    next_rel v_inv_rel exp_inv_rel
             (apply_closure x v2 f)
             (apply_closure y w2 g)
Proof
  rw [apply_closure_def, with_value_def] >>
  drule_all_then assume_tac exp_rel_eval >>
  Cases_on `eval x` >> Cases_on `eval y` >> gvs[] >- (CASE_TAC >> gvs[]) >>
  rename1 `eval x = INR v1` >> rename1 `eval y = INR w1`
  \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [dest_anyClosure_def]
  >- (
    first_x_assum irule
    \\ irule exp_inv_rel_eval
    \\ gs [closed_subst]
    \\ irule_at Any exp_inv_subst
    \\ irule_at Any exp_rel_subst
    \\ gs [])
  \\ rename1 ‘LIST_REL _ xs ys’
  \\ ‘OPTREL (λx y. is_delay x ∧ is_delay y)
             (ALOOKUP (REVERSE xs) s)
             (ALOOKUP (REVERSE ys) s)’
    by (irule LIST_REL_OPTREL
        \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY])
  \\ gs [OPTREL_def]
  \\ CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs []
QED

Theorem unthunk_rel_ok[local]:
  rel_ok T v_inv_rel exp_inv_rel
Proof
  rw [rel_ok_def]
  >- ((* apply_closure preserves rel *)
    simp [unthunk_apply_closure])
  >- ((* Thunks go to Thunks or DoTicks *)
    Cases_on ‘s’ \\ gs []
    \\ Cases_on ‘w’ \\ gs [])
  >- ((* Constructors are related *)
    gs [LIST_REL_EL_EQN, EVERY_EL])
  >- ((* exp_inv holds for Lits *)
    simp [exp_inv_def])
  >- ((* Equal literals are related *)
    simp [exp_rel_Prim])
  >- ((* exp_inv holds for 0-arity conses *)
    simp [exp_inv_def])
  >- ((* Equal 0-arity conses are related *)
    simp [exp_rel_Prim])
  >- simp[exp_inv_def] (* v_inv v ⇒ exp_inv (Value v) *)
  >- simp[exp_rel_Value_Unchanged] (* v_rel v1 v2 ⇒ exp_rel (Value v1) (Value v2) *)
  >- gvs[LIST_REL_EL_EQN, EVERY_EL]
QED

Theorem unthunk_sim_ok[local]:
  sim_ok T v_inv_rel exp_inv_rel
Proof
  rw [sim_ok_def]
  \\ simp [exp_inv_rel_eval]
  >- (irule exp_inv_subst >> gvs[LIST_REL_EL_EQN, EVERY_EL])
  >- gvs[closed_subst, closed_def]
  >- (irule exp_rel_subst >> gvs[LIST_REL_EL_EQN, EVERY_EL])
QED

Theorem unthunk_semantics:
  exp_rel x y ∧
  exp_inv x ∧
  closed x ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ irule sim_ok_semantics
  \\ irule_at Any unthunk_sim_ok
  \\ irule_at Any unthunk_rel_ok \\ gs []
QED

(* -------------------------------------------------------------------------
 * Removing MkTick
 * ------------------------------------------------------------------------- *)

Inductive delay_force:
[delay_force_Delat_Force_Var:]
  (∀v.
     delay_force (Delay (Force (Var v))) (Var v)) ∧
[delay_force_Var:]
  (∀v.
     delay_force (Var v) (Var v)) ∧
[delay_force_Lam:]
  (∀s x y.
     delay_force x y ⇒
       delay_force (Lam s x) (Lam s y)) ∧
[delay_force_App:]
  (∀f x g y.
     delay_force f g ∧
     delay_force (Delay x) y ⇒
       delay_force (App f (Delay x)) (App g y)) ∧
[delay_force_If:]
  (∀x1 y1 z1 x2 y2 z2.
     LIST_REL delay_force [x1;y1;z1] [x2;y2;z2] ⇒
       delay_force (If x1 y1 z1) (If x2 y2 z2)) ∧
[delay_force_Prim:]
  (∀op xs ys.
     LIST_REL delay_force xs ys ∧
     (∀m. op = Cons m ⇒ EVERY is_delay xs) ⇒
       delay_force (Prim op xs) (Prim op ys)) ∧
[delay_force_Monad:]
  (∀mop xs ys.
     LIST_REL delay_force xs ys ⇒
       delay_force (Monad mop xs) (Monad mop ys)) ∧
[delay_force_Let:]
  (∀bv x1 y1 x2 y2.
     delay_force x1 x2 ∧
     delay_force y1 y2 ⇒
       delay_force (Let bv x1 y1) (Let bv x2 y2)) ∧
[delay_force_Letrec:]
  (∀f x g y.
     LIST_REL (λ(f,x) (g,y).
                 f = g ∧
                 is_delay x ∧
                 is_delay y ∧
                 delay_force x y) f g ∧
     delay_force x y ⇒
       delay_force (Letrec f x) (Letrec g y)) ∧
[delay_force_Delay:]
  (∀x y.
     delay_force x y ⇒
       delay_force (Delay x) (Delay y)) ∧
[delay_force_Force:]
  (∀x y.
     delay_force x y ⇒
       delay_force (Force x) (Force y))
End

Overload remove_mktick = “thunk_untickProof$exp_rel”

Theorem delay_force_thm:
  ∀x y. delay_force x y ⇒ ∃x'. exp_rel x x' ∧ remove_mktick x' y ∧ exp_inv x
Proof
  ho_match_mp_tac delay_force_ind \\ rw []
  >- (* Delay_Force_Var *)
   (irule_at Any exp_rel_Delay_Force_Var \\ fs [exp_inv_def]
    \\ irule_at Any thunk_untickProofTheory.exp_rel_MkTick
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Var)
  >- (* Var *)
   (irule_at Any exp_rel_Var \\ fs [exp_inv_def]
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Var)
  >- (* Lam *)
   (irule_at Any exp_rel_Lam \\ fs [exp_inv_def]
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Lam
    \\ first_assum (irule_at Any) \\ gs [])
  >- (* App *)
   (irule_at Any exp_rel_App \\ fs [exp_inv_def]
    \\ irule_at Any thunk_untickProofTheory.exp_rel_App
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* If *)
    irule_at Any exp_rel_If \\ fs [exp_inv_def]
    \\ irule_at Any thunk_untickProofTheory.exp_rel_If
    \\ gs [SF SFY_ss])
  >- ((* Prim *)
    irule_at Any exp_rel_Prim \\ fs [exp_inv_def]
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Prim
    \\ ‘EVERY exp_inv xs’ by
        (rw [EVERY_MEM] \\ imp_res_tac LIST_REL_MEM \\ fs [])
    \\ ‘exp_inv (Prim op xs)’ by
     (Cases_on ‘op’ \\ gvs [exp_inv_def]
      \\ last_x_assum kall_tac
      \\ Induct_on ‘xs’ \\ fs [] \\ rw [] \\ gvs []
      \\ once_rewrite_tac [EQ_SYM_EQ]
      \\ fs [MAP_EQ_CONS,PULL_EXISTS]
      \\ Cases_on ‘h’ \\ fs [exp_inv_def]
      \\ metis_tac [])
    \\ fs []
    \\ last_x_assum mp_tac
    \\ qid_spec_tac ‘xs’
    \\ qid_spec_tac ‘ys’
    \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD,PULL_FORALL,EXISTS_PROD,MAP_EQ_CONS]
    \\ rw [] \\ res_tac \\ fs []
    \\ metis_tac [])
  >- ( (* Monad *)
    simp[exp_inv_def] >>
    irule_at Any exp_rel_Monad >>
    irule_at Any thunk_untickProofTheory.exp_rel_Monad >>
    pop_assum mp_tac >> Induct_on `LIST_REL` >> rw[PULL_EXISTS] >>
    rpt $ goal_assum drule
    )
  >- (* Let *)
   (irule_at Any exp_rel_Let \\ fs [exp_inv_def]
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Let
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* Letrec *)
    irule_at Any exp_rel_Letrec \\ fs [exp_inv_def]
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Letrec
    \\ first_assum $ irule_at Any
    \\ first_assum $ irule_at Any
    \\ last_x_assum $ mp_tac
    \\ qid_spec_tac ‘g’
    \\ qid_spec_tac ‘f’
    \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD,EXISTS_PROD]
    \\ rw []
    \\ first_x_assum drule \\ strip_tac \\ gvs []
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ simp [MAP_EQ_CONS,PULL_EXISTS,EXISTS_PROD]
    \\ Cases_on ‘p_2’ \\ gvs [is_delay_def]
    \\ Cases_on ‘p_2'’ \\ gvs [is_delay_def]
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Delay
    \\ fs [exp_inv_def]
    \\ fs [ok_bind_def]
    \\ qpat_x_assum ‘remove_mktick _ (Delay _)’ mp_tac
    \\ simp [Once thunk_untickProofTheory.exp_rel_cases]
    \\ reverse strip_tac
    >-
     (gvs []
      \\ qpat_x_assum ‘exp_rel _ (MkTick _)’ mp_tac
      \\ simp [Once exp_rel_cases]
      \\ pop_assum mp_tac
      \\ simp [Once thunk_untickProofTheory.exp_rel_cases]
      \\ rpt strip_tac \\ gvs [])
    \\ gvs []
    \\ first_x_assum $ irule_at $ Pos last \\ fs []
    \\ first_x_assum $ irule_at $ Any \\ fs []
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ rename [‘LIST_REL _ (MAP _ xs) ys ⇒ LIST_REL _ ts ys ⇒ _’]
    \\ qid_spec_tac ‘ts’
    \\ qid_spec_tac ‘xs’
    \\ qid_spec_tac ‘ys’
    \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD,PULL_FORALL,EXISTS_PROD,MAP_EQ_CONS]
    \\ rw []
    \\ first_x_assum $ irule_at $ Pos $ el 2 \\ fs []
    \\ first_x_assum $ irule_at Any \\ fs []
    \\ first_x_assum $ irule_at Any \\ fs [])
  >-
   (irule_at Any thunk_untickProofTheory.exp_rel_Delay \\ fs [exp_inv_def]
    \\ irule_at Any exp_rel_Delay \\ fs [SF SFY_ss])
  >-
   (irule_at Any thunk_untickProofTheory.exp_rel_Force \\ fs [exp_inv_def]
    \\ irule_at Any exp_rel_Force \\ fs [SF SFY_ss])
QED

Theorem delay_force_closed:
  delay_force x y ∧ closed x ⇒ closed y
Proof
  rw [] \\ imp_res_tac delay_force_thm
  \\ imp_res_tac exp_rel_freevars
  \\ imp_res_tac thunk_untickProofTheory.exp_rel_freevars
  \\ fs [closed_def]
QED

Theorem delay_force_semantics:
  delay_force x y ∧
  closed x ∧
  pure_semantics$safe_itree (semantics x Done []) ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ imp_res_tac delay_force_thm
  \\ drule_all unthunk_semantics
  \\ strip_tac \\ fs []
  \\ drule untick_semantics
  \\ fs [] \\ disch_then irule
  \\ imp_res_tac exp_rel_freevars
  \\ fs [closed_def]
QED

val _ = export_theory ();
