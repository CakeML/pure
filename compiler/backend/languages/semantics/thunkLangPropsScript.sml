(*
  Some useful theorems about the thunkLang_subst syntax and semantics.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax intLib;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory thunk_semanticsTheory;
open pure_miscTheory;

local open pure_semanticsTheory in end;

val _ = new_theory "thunkLangProps";

val _ = set_grammar_ancestry ["thunkLang", "pure_misc", "thunk_semantics"];

val _ = numLib.prefer_num ();

Theorem exp_size_lemma:
  (∀x xs. MEM x xs ⇒ exp_size x ≤ exp4_size xs) ∧
  (∀x y xs. MEM (x,y) xs ⇒ exp_size y ≤ exp1_size xs) ∧
  (∀x xs. MEM x xs ⇒ v_size x < exp5_size xs)
Proof
  rpt conj_tac
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [exp_size_def]
  \\ first_x_assum drule
  \\ simp []
QED

(* -------------------------------------------------------------------------
 * Alternative induction theorem for :exp
 * ------------------------------------------------------------------------- *)

Theorem exp_ind:
  ∀P.
    (∀n. P (Var n)) ∧
    (∀op xs. (∀a. MEM a xs ⇒ P a) ⇒ P (Prim op xs)) ∧
    (∀x y z. P x ∧ P y ∧ P z ⇒ P (If x y z)) ∧
    (∀x y. P x ∧ (∀z. exp_size z ≤ exp_size y ⇒ P z) ⇒ P x ⇒ P (App x y)) ∧
    (∀s b. P b ⇒ P (Lam s b)) ∧
    (∀v x y. P x ∧ P y ⇒ P (Let v x y)) ∧
    (∀f x. (∀n x'. MEM (n,x') f ⇒ P x') ∧ P x ⇒ P (Letrec f x)) ∧
    (∀x. P x ⇒ P (Delay x)) ∧
    (∀x. P x ⇒ P (Box x)) ∧
    (∀x. P x ⇒ P (Force x)) ∧
    (∀v. P (Value v)) ∧
    (∀x. P x ⇒ P (MkTick x)) ⇒
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
  \\ fs [exp_size_def]
  \\ imp_res_tac exp_size_lemma \\ fs []
QED

(* -------------------------------------------------------------------------
 * Various lemmas
 * ------------------------------------------------------------------------- *)

(* TODO move to pure_misc? *)
Theorem LIST_REL_FILTER:
  ∀xs ys.
    LIST_REL (λx y. P (FST x) ∧ P (FST y) ⇒ R x y) xs ys ⇒
    MAP FST xs = MAP FST ys ⇒
      LIST_REL R (FILTER (λ(x,y). P x) xs)  (FILTER (λ(x,y). P x) ys)
Proof
  ho_match_mp_tac LIST_REL_ind \\ rw [] \\ fs [ELIM_UNCURRY]
QED

(* TODO pure_misc? *)
Theorem MAP_FST_FILTER:
  MAP FST (FILTER (λ(a,b). P a) xs) = FILTER P (MAP FST xs)
Proof
  irule LIST_EQ
  \\ rw [EL_MAP, FILTER_MAP, combinTheory.o_DEF, LAMBDA_PROD]
QED

Theorem LIST_TO_SET_FILTER_DIFF[local]:
  set (FILTER P l) = set l DIFF {x | ¬P x}
Proof
  rw [LIST_TO_SET_FILTER, DIFF_DEF, INTER_DEF, EXTENSION, CONJ_COMM]
QED

(* -------------------------------------------------------------------------
 * Lemmas about substitution
 * ------------------------------------------------------------------------- *)

Theorem freevars_subst:
  ∀m x. freevars (subst m x) = freevars x DIFF set (MAP FST m)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  \\ rw [subst_def]
  \\ simp [freevars_def]
  \\ fs [AC UNION_COMM UNION_ASSOC, UNION_DIFF_DISTRIBUTE]
  >- (
    CASE_TAC \\ fs [freevars_def, ALOOKUP_NONE, MAP_REVERSE]
    \\ drule ALOOKUP_SOME
    \\ simp [MAP_REVERSE])
  >- (
    rw [MAP_MAP_o, combinTheory.o_DEF, EXTENSION, EQ_IMP_THM]
    \\ gvs [MEM_MAP]
    \\ irule_at Any EQ_REFL
    \\ first_assum (irule_at Any) \\ fs []
    \\ rw [MEM_MAP])
  >- (
    simp [DIFF_COMM]
    \\ rw [EXTENSION, MEM_MAP, MEM_FILTER, EQ_IMP_THM]
    \\ gs [ELIM_UNCURRY, DISJ_EQ_IMP])
  >- (
    simp [UNION_DIFF_DISTRIBUTE, AC UNION_COMM UNION_ASSOC, DIFF_COMM]
    \\ AP_TERM_TAC
    \\ rw [EXTENSION, MEM_MAP, MEM_FILTER, EQ_IMP_THM]
    \\ gs [ELIM_UNCURRY, DISJ_EQ_IMP])
  >- (
    fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    \\ fs [MAP_FST_FILTER]
    \\ fs [LIST_TO_SET_FILTER_DIFF]
    \\ fs [DIFF_COMM, UNION_DIFF_DISTRIBUTE, AC UNION_COMM UNION_ASSOC]
    \\ fs [GSYM DIFF_UNION]
    \\ AP_TERM_TAC
    \\ rw [EXTENSION, DISJ_EQ_IMP, EQ_IMP_THM]
    \\ gvs [MEM_MAP, LAMBDA_PROD, EXISTS_PROD, PULL_EXISTS, SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gvs [SF SFY_ss]
    \\ gvs [MEM_MAP, LAMBDA_PROD, EXISTS_PROD])
QED

Theorem closed_subst:
  closed (subst m x) ⇔ freevars x ⊆ set (MAP FST m)
Proof
  rw [closed_def, freevars_subst, SUBSET_DIFF_EMPTY]
QED

Theorem closed_simps[simp]:
  (∀f x. closed (App f x) ⇔ closed f ∧ closed x) ∧
  (∀s x y. closed (Let (SOME s) x y) ⇔ closed x ∧ freevars y ⊆ {s}) ∧
  (∀s x y. closed (Lam s x) ⇔ freevars x ⊆ {s}) ∧
  (∀x y. closed (Let NONE x y) ⇔ closed x ∧ closed y) ∧
  (∀x y z. closed (If x y z) ⇔ closed x ∧ closed y ∧ closed z) ∧
  (∀f x. closed (Letrec f x) ⇔
     BIGUNION (set (MAP (λ(f,x). freevars x) f)) ⊆ set (MAP FST f) ∧
     freevars x ⊆ set (MAP FST f)) ∧
  (∀op xs. closed (Prim op xs) ⇔ EVERY closed xs) ∧
  (∀x. closed (Force x) ⇔ closed x)  ∧
  (∀x. closed (Delay x) ⇔ closed x)  ∧
  (∀x. closed (Box x) ⇔ closed x)  ∧
  (∀v. closed (Value v) ⇔ T)  ∧
  (∀x. closed (MkTick x) ⇔ closed x) ∧
  (∀v. closed (Var v) ⇔ F)
Proof
  rw [closed_def, freevars_def]
  \\ simp [SUBSET_DIFF_EMPTY, AC CONJ_COMM CONJ_ASSOC]
  \\ rw [DISJ_EQ_IMP, EQ_IMP_THM]
  \\ fs [LIST_TO_SET_EQ_SING, EVERY_MAP, GSYM closed_def, SF ETA_ss]
  \\ Cases_on ‘xs’ \\ fs []
QED

Theorem subst_remove:
  ∀vs x bvs.
    DISJOINT bvs (freevars x) ⇒
      subst (FILTER (λ(n,x). n ∉ bvs) vs) x =
      subst vs x
Proof
  ho_match_mp_tac subst_ind \\ rw []
  >- ((* Var *)
    gs [freevars_def]
    \\ simp [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER])
  >- ((* Prim *)
    gs [freevars_def]
    \\ rw [subst_def, MAP_EQ_f]
    \\ gs [MEM_MAP, DISJ_EQ_IMP, SF DNF_ss,
           DECIDE “A ⇒ ¬MEM a b ⇔ MEM a b ⇒ ¬A”])
  >- ((* If *)
    gs [freevars_def, subst_def, DISJOINT_SYM])
  >- ((* App *)
    gs [freevars_def, subst_def, DISJOINT_SYM])
  >- ((* Lam *)
    gs [freevars_def, subst_def, DISJOINT_SYM, FILTER_FILTER,
        LAMBDA_PROD, AC CONJ_COMM CONJ_ASSOC]
    \\ first_x_assum (qspec_then ‘bvs DIFF {s}’ mp_tac)
    \\ simp [AC CONJ_COMM CONJ_ASSOC, SF DNF_ss]
    \\ disch_then irule
    \\ gs [DISJOINT_ALT, DISJ_EQ_IMP]
    \\ rpt strip_tac \\ gs [])
  >- ((* Let NONE *)
    gs [freevars_def, subst_def, FILTER_FILTER, DISJOINT_SYM])
  >- ((* Let SOME *)
    gs [freevars_def, subst_def, DISJOINT_SYM, FILTER_FILTER,
        LAMBDA_PROD, AC CONJ_COMM CONJ_ASSOC]
    \\ first_x_assum (qspec_then ‘bvs DIFF {s}’ mp_tac)
    \\ simp [AC CONJ_COMM CONJ_ASSOC, SF DNF_ss]
    \\ disch_then irule
    \\ gs [DISJOINT_ALT, DISJ_EQ_IMP]
    \\ rpt strip_tac \\ gs [])
  >- ((* Letrec *)
    gs [freevars_def, subst_def, MAP_EQ_f, FILTER_FILTER, LAMBDA_PROD,
        FORALL_PROD]
    \\ ‘DISJOINT (bvs DIFF set (MAP FST f)) (freevars x)’
      by (gs [DISJOINT_ALT, DISJ_EQ_IMP]
          \\ rpt strip_tac \\ gs [])
    \\ first_x_assum drule
    \\ disch_then (SUBST1_TAC o SYM)
    \\ simp [SF DNF_ss, AC CONJ_COMM CONJ_ASSOC]
    \\ rw []
    \\ first_x_assum drule
    \\ disch_then (qspec_then ‘bvs DIFF set (MAP FST f)’ mp_tac)
    \\ impl_tac
    >- (
      gs [DISJOINT_ALT, DISJ_EQ_IMP]
      \\ rpt strip_tac \\ gs []
      \\ first_x_assum (drule_then assume_tac) \\ gs []
      \\ first_x_assum (drule_then assume_tac)
      \\ rgs [DISJ_EQ_IMP, MEM_MAP])
    \\ simp [AC CONJ_COMM CONJ_ASSOC, SF DNF_ss])
  >- ((* Delay *)
    gs [freevars_def, subst_def])
  >- ((* Box *)
    gs [freevars_def, subst_def])
  >- ((* Force *)
    gs [freevars_def, subst_def])
  >- ((* Value *)
    gs [freevars_def, subst_def])
  >- ((* MkTick *)
    gs [freevars_def, subst_def])
QED

Theorem subst1_notin_frees =
  subst_remove
  |> Q.SPECL [‘[n,v]’,‘x’,‘{n}’]
  |> SIMP_RULE (srw_ss()) [IN_DISJOINT]
  |> GSYM;

Theorem MEM_FST:
  ∀l p. MEM p l ⇒ MEM (FST p) (MAP FST l)
Proof
  Induct >> gvs [FORALL_PROD] >>
  rw [] >>
  last_x_assum $ drule_then assume_tac >> gvs []
QED

Theorem subst_commutes:
  ∀x vs ws.
    DISJOINT (set (MAP FST vs)) (set (MAP FST ws)) ⇒ subst vs (subst ws x) = subst ws (subst vs x)
Proof
  ho_match_mp_tac exp_ind
  \\ rpt conj_tac
  \\ simp [subst_def] \\ rw []
  \\ simp [subst_def]
  >- (CASE_TAC
      >- (CASE_TAC \\ gvs [subst_def])
      \\ CASE_TAC \\ gvs [subst_def]
      \\ rpt $ dxrule_then assume_tac ALOOKUP_MEM
      \\ rpt $ dxrule_then assume_tac MEM_FST
      \\ gvs [MAP_REVERSE, DISJOINT_ALT])
  >- (
    simp [MAP_MAP_o, combinTheory.o_DEF]
    \\ irule LIST_EQ
    \\ gvs [EL_MAP, MEM_EL, PULL_EXISTS]
    \\ rw [] \\ last_x_assum irule \\ gvs [])
  >- first_x_assum $ drule_then irule
  >- first_x_assum $ drule_then irule
  >- first_x_assum $ drule_then irule
  >- first_x_assum $ drule_then irule
  >- (first_x_assum irule \\ gvs [])
  >- (first_x_assum irule
      \\ gvs [DISJOINT_ALT] \\ rpt $ strip_tac
      \\ gvs [MEM_MAP, MEM_FILTER, PULL_EXISTS]
      \\ last_x_assum $ dxrule_then $ dxrule_then assume_tac
      \\ gvs [])
  >- (
    rename1 ‘Let x’
    \\ Cases_on ‘x’ \\ simp [subst_def]
    >- (conj_tac \\ last_x_assum $ dxrule_then irule)
    \\ last_x_assum $ drule_then $ irule_at Any
    \\ last_x_assum irule
    \\ gvs [DISJOINT_ALT] \\ rpt $ strip_tac
    \\ gvs [MEM_MAP, MEM_FILTER, PULL_EXISTS]
    \\ last_x_assum $ dxrule_then $ dxrule_then assume_tac
    \\ gvs [])
  >- (
    gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    \\ irule LIST_EQ
    \\ gvs [EL_MAP, MEM_EL, PULL_EXISTS, ELIM_UNCURRY,
            DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
    \\ rw []
    \\ first_x_assum irule \\ gs []
    \\ conj_tac
    >- (irule_at Any PAIR \\ gs [])
    \\ gvs [DISJOINT_ALT] \\ rpt $ strip_tac
    \\ gvs [MEM_MAP, MEM_FILTER, PULL_EXISTS]
    \\ last_x_assum $ dxrule_then $ dxrule_then assume_tac
    \\ gvs [])
  >- (
    gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    \\ first_x_assum $ irule
    \\ gvs [DISJOINT_ALT] \\ rpt $ strip_tac
    \\ gvs [MEM_MAP, MEM_FILTER, PULL_EXISTS]
    \\ last_x_assum $ dxrule_then $ dxrule_then assume_tac
    \\ gvs [])
QED

Theorem subst1_commutes:
  ∀x v n m w.
    n ≠ m ⇒ subst1 n v (subst1 m w x) = subst1 m w (subst1 n v x)
Proof
  gvs [subst_commutes]
QED

(* TODO pure_misc? *)
Theorem ALOOKUP_SOME_REVERSE_EL:
  ALOOKUP (REVERSE l) k = SOME v ⇒ ∃n. n < LENGTH l ∧ EL n l = (k, v)
Proof
  strip_tac
  \\ dxrule_then strip_assume_tac ALOOKUP_SOME_EL
  \\ gvs [EL_REVERSE]
  \\ qmatch_asmsub_abbrev_tac ‘EL m l’
  \\ first_assum (irule_at (Pos (el 2)))
  \\ gs [Abbr ‘m’]
QED

(* -------------------------------------------------------------------------
 * Wellfounded relation that can be used with WF_IND to avoid annoying
 * induction theorems.
 * ------------------------------------------------------------------------- *)

Definition eval_to_wo_def:
  eval_to_wo = inv_image ($< LEX $<) (I ## exp_size)
End

Theorem eval_to_wo_WF:
  WF eval_to_wo
Proof
  rw [eval_to_wo_def]
  \\ irule relationTheory.WF_inv_image
  \\ irule WF_LEX \\ gs []
QED

Theorem eval_to_wo_def = REWRITE_RULE [LEX_DEF] eval_to_wo_def;

(* -------------------------------------------------------------------------
 * Generalized semantics theorem
 * ------------------------------------------------------------------------- *)

Definition sim_ok_def:
  sim_ok allow_error Rv Re ⇔
    (∀x y.
       Re x y ∧
       closed x ∧
       (¬allow_error ⇒ eval x ≠ INL Type_error) ⇒
         ($= +++ Rv) (eval x) (eval y)) ∧
    (∀vs ws x y.
       LIST_REL Rv (MAP SND vs) (MAP SND ws) ∧
       MAP FST vs = MAP FST ws ∧
       Re x y ⇒
         Re (subst vs x) (subst ws y))
End

Definition cont_rel_def[simp]:
  cont_rel Rv Done Done = T ∧
  cont_rel Rv (BC v c) (BC w d) = (Rv v w ∧ cont_rel Rv c d) ∧
  cont_rel Rv (HC v c) (HC w d) = (Rv v w ∧ cont_rel Rv c d) ∧
  cont_rel Rv _ _ = F
End

Definition state_rel_def:
  state_rel Rv = LIST_REL (LIST_REL Rv)
End

Definition next_rel_def[simp]:
  next_rel Rv (Act a c s) (Act b d t) =
    (a = b ∧ cont_rel Rv c d ∧ state_rel Rv s t) ∧
  next_rel Rv Ret Ret = T ∧
  next_rel Rv Div Div = T ∧
  next_rel Rv Err Err = T ∧
  next_rel Rv (_: (string # string) next_res) _ = F
End

Definition rel_ok_def:
  rel_ok allow_error Rv ⇔
    (∀v w.
       Rv v w ∧
       (¬allow_error ⇒ force v ≠ INL Type_error) ⇒
         ($= +++ Rv) (force v) (force w)) ∧
    (∀v1 w1 v2 w2 f g.
       Rv v1 w1 ∧
       Rv v2 w2 ∧
       (¬allow_error ⇒
          apply_closure v1 v2 f ≠ Err ∧
          f (INL Type_error) = Err) ∧
       (∀x y.
              ($= +++ Rv) x y ∧
              (¬allow_error ⇒ f x ≠ Err) ⇒
                next_rel Rv (f x) (g y)
                ) ⇒
         next_rel Rv (apply_closure v1 v2 f)
                     (apply_closure w1 w2 g)) ∧
    (∀s x w.
       Rv (Closure s x) w ⇒ (∃t y. w = Closure t y) ∨ (∃g m. w = Recclosure g m)) ∧
    (∀f n w.
       Rv (Recclosure f n) w ⇒ ∃g m. w = Recclosure g m) ∧
    (∀s w.
       Rv (Thunk s) w ⇒ (∃t. w = Thunk t) ∨ (∃v. w = DoTick v)) ∧
    (∀x w.
       Rv (Atom x) w ⇒ w = Atom x) ∧
    (∀v w.
       Rv (DoTick v) w ⇒
         ¬allow_error ∨
         (∃u. w = DoTick u)) ∧
    (∀s vs w.
       Rv (Constructor s vs) w ⇒ ∃ws. w = Constructor s ws ∧
                                      LIST_REL Rv vs ws) ∧
    (∀s x y.
       x = y ⇒
         Rv (Constructor s [Thunk (INR (Lit x))])
            (Constructor s [Thunk (INR (Lit y))])) ∧
    (∀s t.
       Rv (Constructor s [Thunk (INR (Cons t []))])
          (Constructor s [Thunk (INR (Cons t []))])) ∧
    (∀s v w.
       Rv v w ⇒
         Rv (Constructor s [v])
            (Constructor s [w]))
End

fun print_tac str g = (print (str ^ "\n"); ALL_TAC g);

val _ = print "Proving sim_ok_next ...\n";

(* next preserves relation *)
Theorem sim_ok_next:
  ∀k v c s w d t.
    rel_ok allow_error Rv ∧
    sim_ok allow_error Rv Re ∧
    ($= +++ Rv) v w ∧
    cont_rel Rv c d ∧
    state_rel Rv s t ∧
    (¬allow_error ⇒ next k v c s ≠ Err) ⇒
      next_rel Rv (next k v c s) (next k w d t)
Proof
  ho_match_mp_tac next_ind \\ rw []
  \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs []
  >- (
    simp [next_def]
    \\ CASE_TAC \\ gs [])
  \\ rename1 ‘Rv v w’
  \\ Cases_on ‘(∃s x. v = Closure s x) ∨
               (∃f n. v = Recclosure f n) ∨
               (∃x. v = Thunk x) ∨
               (∃x. v = Atom x)’
  >- (
    gvs [rel_ok_def]
    \\ res_tac \\ rgs []
    >~ [‘Atom x’] >- (
      Cases_on ‘w’ \\ res_tac \\ gs []
      \\ simp [next_def])
    \\ simp [next_def])
  \\ Cases_on ‘∃x. v = DoTick x’
  >- (
    gvs [rel_ok_def]
    \\ gs [Once next_def]
    \\ res_tac \\ gvs []
    \\ simp [Once next_def]
    \\ simp [Once next_def])
  \\  fs []
  \\ ‘∃nm vs. v = Constructor nm vs’
    by (Cases_on ‘v’ \\ gs [])
  \\ gvs []
  \\ simp [Once next_def]
  \\ print_tac "[1/9] Ret"
  \\ IF_CASES_TAC \\ gs []
  >- ((* Ret *)
    qpat_assum ‘rel_ok _ _’ mp_tac
    \\ simp_tac std_ss [rel_ok_def] \\ rw []
    \\ res_tac
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute, DECIDE “∀x. x < 1n ⇔ x = 0”]
    \\ Cases_on ‘k = 0’ \\ gs []
    >- (
      simp [Once next_def]
      \\ Cases_on ‘c’ \\ Cases_on ‘d’ \\ gs [])
    \\ qmatch_goalsub_abbrev_tac ‘next_rel _ X’
    \\ simp [Once next_def] \\ simp [Abbr ‘X’]
    \\ Cases_on ‘c’ \\ Cases_on ‘d’ \\ gs []
    >- (
      simp [force_apply_closure_def]
      \\ rename1 ‘Rv v w’
      \\ ‘($= +++ Rv) (force v) (force w)’
        by (first_x_assum irule \\ gs [] \\ rw []
            \\ strip_tac \\ gs []
            \\ qpat_x_assum ‘next k (INR _) _ _ ≠ _’ mp_tac
            \\ simp [Once next_def, force_apply_closure_def])
      \\ Cases_on ‘force v’ \\ Cases_on ‘force w’ \\ gs []
      >- (
        CASE_TAC \\ gs [])
      \\ first_x_assum irule \\ gs [] \\ strip_tac
      \\ rgs [Once next_def, force_apply_closure_def]
      \\ simp [Once next_def])
    \\ first_x_assum irule \\ gs []
    \\ rpt strip_tac
    \\ gs [Once next_def])
  \\ print_tac "[2/9] Raise"
  \\ IF_CASES_TAC \\ gs []
  >- ((* Raise *)
    qpat_assum ‘rel_ok _ _’ mp_tac
    \\ simp_tac std_ss [rel_ok_def] \\ rw []
    \\ res_tac
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute, DECIDE “∀x. x < 1n ⇔ x = 0”]
    \\ Cases_on ‘k = 0’ \\ gs []
    >- (
     simp [Once next_def]
     \\ Cases_on ‘c’ \\ Cases_on ‘d’ \\ gs [])
    \\ qmatch_goalsub_abbrev_tac ‘next_rel _ X’
    \\ simp [Once next_def] \\ simp [Abbr ‘X’]
    \\ Cases_on ‘c’ \\ Cases_on ‘d’ \\ gs []
    >- (
      first_x_assum irule \\ gs []
      \\ rpt strip_tac
      \\ gs [Once next_def])
    \\ simp [force_apply_closure_def]
    \\ rename1 ‘Rv v w’
    \\ ‘($= +++ Rv) (force v) (force w)’
      by (first_x_assum irule \\ gs [] \\ rw []
          \\ strip_tac \\ gs []
          \\ rgs [Once next_def, force_apply_closure_def])
      \\ Cases_on ‘force v’ \\ Cases_on ‘force w’ \\ gs []
      >- (
        CASE_TAC \\ gs [])
      \\ first_x_assum irule \\ gs [] \\ strip_tac
      \\ rgs [Once next_def, force_apply_closure_def]
      \\ simp [Once next_def])
  \\ print_tac "[3/9] Bind"
  \\ IF_CASES_TAC \\ gs []
  >- ((* Bind *)
    qpat_assum ‘rel_ok _ _’ mp_tac
    \\ simp_tac std_ss [rel_ok_def] \\ strip_tac \\ gs [] \\ res_tac \\ gvs []
    \\ rgs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2n ⇔ x = 0 ∨ x = 1”]
    \\ rw [] \\ rgs [SF DNF_ss]
    >- (
      simp [Once next_def])
    \\ qmatch_goalsub_abbrev_tac ‘next_rel _ X’
    \\ simp [Once next_def]
    \\ qunabbrev_tac ‘X’
    \\ rename1 ‘Rv v w’
    \\ ‘¬allow_error ⇒ force v ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ qpat_x_assum ‘_next _ _ _ _ ≠ _’ mp_tac
          \\ simp [Once next_def, force_apply_closure_def]
          \\ simp [Once next_def])
    \\ ‘($= +++ Rv) (force v) (force w)’
      by gs []
    \\ first_x_assum irule \\ gs []
    \\ rw [] \\ gs []
    \\ gs [Once next_def])
  \\ print_tac "[4/9] Handle"
  \\ IF_CASES_TAC \\ gs []
  >- ((* Handle *)
    qpat_assum ‘rel_ok _ _’ mp_tac
    \\ simp_tac std_ss [rel_ok_def] \\ strip_tac \\ gs [] \\ res_tac \\ gvs []
    \\ rgs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2n ⇔ x = 0 ∨ x = 1”]
    \\ rw [] \\ rgs [SF DNF_ss]
    >- (
      simp [Once next_def])
    \\ qmatch_goalsub_abbrev_tac ‘next_rel _ X’
    \\ simp [Once next_def]
    \\ qunabbrev_tac ‘X’
    \\ rename1 ‘Rv v w’
    \\ ‘¬allow_error ⇒ force v ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ qpat_x_assum ‘_next _ _ _ _ ≠ _’ mp_tac
          \\ simp [Once next_def, force_apply_closure_def]
          \\ simp [Once next_def])
    \\ ‘($= +++ Rv) (force v) (force w)’
      by gs []
    \\ first_x_assum irule \\ gs []
    \\ rw [] \\ gs []
    \\ gs [Once next_def])
  \\ print_tac "[5/9] Act"
  \\ IF_CASES_TAC \\ gs []
  >- ((* Act *)
    qpat_assum ‘rel_ok _ _’ mp_tac
    \\ simp_tac std_ss [rel_ok_def] \\ strip_tac \\ gs [] \\ res_tac \\ gvs []
    \\ simp [Once next_def]
    \\ gs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute, DECIDE “∀x. x < 1n ⇔ x = 0”]
    \\ simp [with_atoms_def, result_map_def] \\ gvs[]
    \\ rename1 ‘Rv v w’
    \\ ‘¬allow_error ⇒ force v ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ gs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (force v) (force w)’
      by gs []
    \\ Cases_on ‘force v’ \\ Cases_on ‘force w’ \\ gs []
    >- (
      Cases_on `x'` \\ gs []
      )
    \\ gvs []
    \\ rename1 ‘Rv a b’
    \\ Cases_on ‘a’ \\ Cases_on ‘b’ \\ res_tac \\ gvs [get_atoms_def]
    \\ CASE_TAC \\ gs []
    \\ gs [Once next_def, with_atoms_def, get_atoms_def, result_map_def])
  \\ print_tac "[6/9] Alloc"
  \\ IF_CASES_TAC \\ gs []
  >- ((* Alloc *)
    qpat_assum ‘rel_ok _ _’ mp_tac
    \\ simp_tac std_ss [rel_ok_def] \\ strip_tac \\ gs [] \\ res_tac \\ gvs []
    \\ qmatch_goalsub_abbrev_tac ‘next_rel _ X’
    \\ simp [Once next_def]
    \\ simp [Abbr ‘X’]
    \\ rgs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2n ⇔ x = 0 ∨ x = 1”, SF DNF_ss]
    \\ rgs [with_atoms_def, result_map_def] \\ gvs[]
    \\ rename1 ‘Rv v w’
    \\ ‘¬allow_error ⇒ force v ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ rgs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (force v) (force w)’
      by gs []
    \\ Cases_on ‘force v’ \\ Cases_on ‘force w’ \\ gs []
    >- (
      Cases_on `x'` \\ gs [])
    \\ gvs []
    \\ rename1 ‘Rv a b’
    \\ rgs [Once next_def, with_atoms_def, result_map_def]
    \\ Cases_on ‘a’ \\ Cases_on ‘b’ \\ res_tac \\ gvs [get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule \\ gs []
    \\ simp [PULL_EXISTS]
    \\ qexists_tac ‘[Int i]’ \\ simp []
    \\ gs [state_rel_def, LIST_REL_REPLICATE_same, LIST_REL_EL_EQN])
  \\ print_tac "[7/9] Length"
  \\ IF_CASES_TAC \\ gs []
  >- ((* Length *)
    qpat_assum ‘rel_ok _ _’ mp_tac
    \\ simp_tac std_ss [rel_ok_def] \\ strip_tac \\ gs [] \\ res_tac \\ gvs []
    \\ qmatch_goalsub_abbrev_tac ‘next_rel _ X’
    \\ simp [Once next_def]
    \\ simp [Abbr ‘X’]
    \\ rgs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
           DECIDE “∀x. x < 1n ⇔ x = 0”, SF DNF_ss]
    \\ rgs [with_atoms_def, result_map_def]
    \\ rename1 ‘Rv v w’
    \\ ‘¬allow_error ⇒ force v ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ rgs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (force v) (force w)’
      by gs []
    \\ Cases_on ‘force v’ \\ Cases_on ‘force w’ \\ gs []
    >- (
      Cases_on `x'` \\ gs [])
    \\ gvs []
    \\ rename1 ‘Rv a b’
    \\ rgs [Once next_def, with_atoms_def, result_map_def]
    \\ Cases_on ‘a’ \\ Cases_on ‘b’ \\ res_tac \\ gvs [get_atoms_def]
    \\ gvs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ ‘LENGTH s = LENGTH t’
      by gvs [LIST_REL_EL_EQN, state_rel_def]
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule \\ gs []
    \\ simp [PULL_EXISTS]
    \\ qexists_tac ‘[Loc n]’ \\ simp []
    \\ ‘LENGTH (EL n s) = LENGTH (EL n t)’
      by gvs [state_rel_def, LIST_REL_EL_EQN]
    \\ gs []
    \\ strip_tac \\ gvs []
    \\ simp[Once next_def]
    )
  \\ print_tac "[8/9] Deref"
  \\ IF_CASES_TAC \\ gs []
  >- ((* Deref *)
    qpat_assum ‘rel_ok _ _’ mp_tac
    \\ simp_tac std_ss [rel_ok_def] \\ strip_tac \\ gs [] \\ res_tac \\ gvs []
    \\ qmatch_goalsub_abbrev_tac ‘next_rel _ X’
    \\ simp [Once next_def]
    \\ simp [Abbr ‘X’]
    \\ rgs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
           DECIDE “∀x. x < 2n ⇔ x = 0 ∨ x = 1”, SF DNF_ss]
    \\ rgs [with_atoms_def, result_map_def] \\ gvs[]
    \\ rename1 ‘Rv v w’
    \\ ‘¬allow_error ⇒ force v ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ rgs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (force v) (force w)’
      by gs []
    \\ qmatch_goalsub_rename_tac `_ ∨ force a = _`
    \\ rename1 ‘Rv a b’
    \\ ‘¬allow_error ⇒ force a ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ rgs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (force a) (force b)’
      by gs []
    \\ Cases_on ‘force v’ \\ Cases_on ‘force w’ \\ fs[]
    >- (
      Cases_on `x'` \\ fs[]
      \\ Cases_on ‘force a’ \\ Cases_on ‘force b’ \\ fs[]
      \\ Cases_on `x''` \\ gvs[]
      )
    \\ Cases_on ‘force a’ \\ Cases_on ‘force b’ \\ fs[]
    >- (
      Cases_on `x'` \\ fs[]
      )
    \\ gvs []
    \\ rename1 ‘force v = INR v1’
    \\ rename1 ‘force a = INR v2’
    \\ rename1 ‘force w = INR w1’
    \\ rename1 ‘force b = INR w2’
    \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ res_tac \\ gvs [get_atoms_def]
    \\ Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ res_tac \\ gvs [get_atoms_def]
    >- (
      BasicProvers.TOP_CASE_TAC \\ gs []
      \\ BasicProvers.TOP_CASE_TAC \\ gs []
      \\ ‘LENGTH s = LENGTH t’
        by gs [state_rel_def, LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ ‘LENGTH (EL n s) = LENGTH (EL n t)’
        by gs [state_rel_def, LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum irule \\ gs []
        \\ simp [PULL_EXISTS]
        \\ qexists_tac ‘[Loc n; Int i]’ \\ simp []
        \\ gs [state_rel_def, LIST_REL_EL_EQN, arithmeticTheory.NOT_LESS_EQUAL]
        \\ first_x_assum (irule_at Any)
        \\ last_x_assum (drule_then strip_assume_tac)
        \\ first_x_assum (irule_at Any)
        \\ rw [] >- intLib.ARITH_TAC
        \\ rgs [Once next_def, with_atoms_def, get_atoms_def, result_map_def])
      >- (
        first_x_assum irule \\ gs []
        \\ simp [PULL_EXISTS]
        \\ qexists_tac ‘[Loc n; Int i]’ \\ simp []
        \\ strip_tac \\ gvs []
        \\ rgs [Once next_def, with_atoms_def, get_atoms_def, result_map_def])
      \\ last_x_assum irule \\ gs []
      \\ simp [PULL_EXISTS]
      \\ qexists_tac ‘[Loc n; Int i]’ \\ simp []
      \\ rw[] \\ gvs[]
      \\ qpat_x_assum `_ ≠ Err` mp_tac
      \\ simp[Once next_def, with_atoms_def, result_map_def, get_atoms_def]
      )
    \\ irule FALSITY
    \\ qpat_x_assum `_ ≠ Err` mp_tac
    \\ simp[Once next_def, with_atoms_def, result_map_def, get_atoms_def]
    )
  \\ print_tac "[9/9] Update"
  \\ IF_CASES_TAC \\ gs []
  >- ((* Update *)
    qpat_assum ‘rel_ok _ _’ mp_tac
    \\ simp_tac std_ss [rel_ok_def] \\ strip_tac \\ gs [] \\ res_tac \\ gvs []
    \\ qmatch_goalsub_abbrev_tac ‘next_rel _ X’
    \\ simp [Once next_def]
    \\ simp [Abbr ‘X’]
    \\ rgs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
           DECIDE “∀x. x < 3n ⇔ x = 0 ∨ x = 1 ∨ x = 2”, SF DNF_ss]
    \\ rgs [with_atoms_def, result_map_def] \\ gvs[]
    \\ rename1 ‘Rv v w’
    \\ ‘¬allow_error ⇒ force v ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ rgs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (force v) (force w)’
      by gs []
    \\ qmatch_goalsub_rename_tac `_ ∨ force a = _`
    \\ rename1 ‘Rv a b’
    \\ ‘¬allow_error ⇒ force a ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ rgs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (force a) (force b)’
      by gs []
    \\ Cases_on ‘force v’ \\ Cases_on ‘force w’ \\ fs[]
    >- (
      Cases_on `x'` \\ fs[]
      \\ Cases_on ‘force a’ \\ Cases_on ‘force b’ \\ fs[]
      \\ Cases_on `x''` \\ gvs[]
      )
    \\ Cases_on ‘force a’ \\ Cases_on ‘force b’ \\ fs[]
    >- (
      Cases_on `x'` \\ fs[]
      )
    \\ rename1 ‘force v = INR v1’
    \\ rename1 ‘force a = INR v2’
    \\ rename1 ‘force w = INR w1’
    \\ rename1 ‘force b = INR w2’
    \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ res_tac \\ gvs [get_atoms_def]
    \\ Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ res_tac \\ gvs [get_atoms_def]
    >- (
      BasicProvers.TOP_CASE_TAC \\ gs []
      \\ BasicProvers.TOP_CASE_TAC \\ gs []
      \\ ‘LENGTH s = LENGTH t’
        by gs [state_rel_def, LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ ‘LENGTH (EL n s) = LENGTH (EL n t)’
        by gs [state_rel_def, LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      >- (
        last_x_assum irule \\ gs []
        \\ simp [PULL_EXISTS]
        \\ qexists_tac ‘[Loc n; Int i]’ \\ simp []
        \\ gvs [state_rel_def, LIST_REL_EL_EQN, EL_LUPDATE]
        \\ rw [] \\ rw [LENGTH_LUPDATE]
        \\ rw [EL_LUPDATE]
        \\ rgs [Once next_def, with_atoms_def, get_atoms_def, result_map_def])
      >- (
        first_x_assum irule \\ gs []
        \\ simp [PULL_EXISTS]
        \\ qexists_tac ‘[Loc n; Int i]’ \\ simp []
        \\ strip_tac \\ gvs []
        \\ rgs [Once next_def, with_atoms_def, get_atoms_def, result_map_def])
      \\ last_x_assum irule \\ gs []
      \\ simp [PULL_EXISTS]
      \\ qexists_tac ‘[Loc n; Int i]’ \\ simp []
      \\ rw[] \\ gvs[]
      \\ qpat_x_assum `_ ≠ Err` mp_tac
      \\ simp[Once next_def, with_atoms_def, result_map_def, get_atoms_def]
      )
    \\ irule FALSITY
    \\ qpat_x_assum `_ ≠ Err` mp_tac
    \\ simp[Once next_def, with_atoms_def, result_map_def, get_atoms_def]
    )
  \\ gs [rel_ok_def]
  \\ res_tac \\ gvs [] \\ imp_res_tac LIST_REL_LENGTH
  \\ rw [Once next_def] \\ gs []
QED

val _ = print "Done with sim_ok_next.\n";

Theorem sim_ok_next_action:
  rel_ok allow_error Rv ∧
  sim_ok allow_error Rv Re ∧
  ($= +++ Rv) v w ∧
  cont_rel Rv c d ∧
  state_rel Rv s t ∧
  (¬allow_error ⇒ next_action v c s ≠ Err) ⇒
    next_rel Rv (next_action v c s) (next_action w d t)
Proof
  strip_tac
  \\ rw [next_action_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ simp [PULL_FORALL]
  \\ qx_gen_tac ‘i’
  \\ qx_gen_tac ‘j’
  \\ qx_gen_tac ‘k’
  \\ ‘∀m. ¬allow_error ⇒ next m v c s ≠ Err’
    by (rpt strip_tac \\ gs []
        \\ gs [next_action_def]
        \\ qpat_x_assum ‘_ ≠ Err’ mp_tac
        \\ DEEP_INTRO_TAC some_intro \\ simp []
        \\ simp [PULL_EXISTS]
        \\ qexists_tac ‘m’ \\ gs []
        \\ rw []
        \\ drule_then (qspec_then ‘m’ assume_tac) next_next
        \\ gs [])
  \\ rw []
  >- (
    first_x_assum (qspec_then ‘i’ assume_tac)
    \\ drule_all_then assume_tac sim_ok_next \\ gs []
    \\ drule_then (qspec_then ‘i’ mp_tac) next_next
    \\ impl_tac \\ rw []
    \\ strip_tac
    \\ Cases_on ‘next i w d t’ \\ gs [])
  >- (
    last_x_assum (qspec_then ‘i’ assume_tac)
    \\ drule_all_then assume_tac sim_ok_next \\ gs [SF SFY_ss])
  \\ last_x_assum (qspec_then ‘k’ assume_tac)
  \\ drule_all_then assume_tac sim_ok_next \\ gs [SF SFY_ss]
QED

Theorem sim_ok_interp:
  rel_ok allow_error Rv ∧
  sim_ok allow_error Rv Re ∧
  ($= +++ Rv) v w ∧
  cont_rel Rv c d ∧
  state_rel Rv s t ∧
  (¬allow_error ⇒ pure_semantics$safe_itree (interp v c s)) ⇒
    interp v c s = interp w d t
Proof
  strip_tac \\
  rw [Once itreeTheory.itree_bisimulation] >>
  qexists_tac `λt1 t2.
    (¬allow_error ⇒ pure_semantics$safe_itree t1) ∧
    (t1 = t2 ∨
     ∃v c s w d t.
       interp v c s = t1 ∧
       interp w d t = t2 ∧
       ($= +++ Rv) v w ∧
       cont_rel Rv c d ∧
       state_rel Rv s t)` >>
  rw []
  >~ [‘Vis a f’] >- (
    rgs [Once pure_semanticsTheory.safe_itree_cases])
  >~ [‘interp v c s = interp w d t’] >- (
    disj2_tac >> rpt $ irule_at Any EQ_REFL >> simp[]
  )
  \\ ‘¬allow_error ⇒ next_action v' c' s' ≠ Err’
    by (rpt strip_tac \\ gs []
        \\ rgs [Once interp_def, Once pure_semanticsTheory.safe_itree_cases])
  \\ drule_all sim_ok_next_action \\ strip_tac
  >- (
    qpat_x_assum `_ = Ret _` mp_tac
    \\ once_rewrite_tac [interp_def]
    \\ Cases_on `next_action v' c' s'`
    \\ Cases_on `next_action w' d' t''` \\ gvs[])
  >- (
    qpat_x_assum `_ = Div` mp_tac >>
    once_rewrite_tac[interp_def] >>
    Cases_on `next_action v' c' s'` >> Cases_on `next_action w' d' t''` >>
    gvs[])
  >- (
    qpat_x_assum `_ = Vis _ _ ` mp_tac
    \\ rw [Once interp_def]
    \\ rw [Once interp_def]
    \\ Cases_on `next_action v' c' s'`
    \\ Cases_on `next_action w' d' t''` \\ gvs []
    \\ rw [] \\ rgs [Once pure_semanticsTheory.safe_itree_cases]
    \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ disj2_tac
    \\ rpt (irule_at Any EQ_REFL) \\ simp []
    \\ gs [rel_ok_def])
QED

Theorem semantics_fail:
  pure_semantics$safe_itree (semantics x c s) ⇒
    eval x ≠ INL Type_error
Proof
  simp [semantics_def, Once interp_def, next_action_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ rw [] \\ strip_tac \\ gs []
  \\ rgs [Once next_def]
  \\ rgs [Once pure_semanticsTheory.safe_itree_cases]
QED

Theorem sim_ok_semantics:
  rel_ok allow_error Rv ∧
  sim_ok allow_error Rv Re ∧
  Re x y ∧
  closed x ∧
  (¬allow_error ⇒ pure_semantics$safe_itree (semantics x Done [])) ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ rw [semantics_def]
  \\ irule sim_ok_interp
  \\ qpat_assum ‘sim_ok _ _ _’ (irule_at Any)
  \\ gs [cont_rel_def, state_rel_def, sim_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
  \\ rw [] \\ gs [semantics_fail, SF SFY_ss]
  \\ gs [semantics_def]
QED

(* -------------------------------------------------------------------------
 * eval/eval_to props
 * ------------------------------------------------------------------------- *)

Theorem eval_to_equals_eval:
  eval_to k x ≠ INL Diverge ⇒ eval_to k x = eval x
Proof
  rw [eval_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ rename1 ‘_ = eval_to j x’
  \\ imp_res_tac eval_to_mono
  \\ Cases_on ‘k ≤ j’ \\ gs []
QED

Theorem eval_Force:
  eval (Force (Value v)) =
    case dest_Tick v of
      NONE =>
        do
          (wx,binds) <- dest_anyThunk v;
          case wx of
            INL v => return v
          | INR y => eval (subst_funs binds y)
        od
    | SOME w => eval (Force (Value w))
Proof
  simp [Once eval_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ rw []
  >- (
    fs [Once eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ fs [Once eval_to_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    >- (
      Cases_on ‘dest_anyThunk v’ \\ gs []
      \\ pairarg_tac \\ gvs []
      \\ CASE_TAC \\ gs []
      \\ irule eval_to_equals_eval \\ gs [])
    \\ irule eval_to_equals_eval \\ gs [])
  \\ Cases_on ‘dest_Tick v’ \\ gs []
  >- (
    gs [Once eval_to_def]
    \\ gs [Once eval_to_def]
    \\ Cases_on ‘dest_anyThunk v’ \\ gs []
    >- (
      first_x_assum (qspec_then ‘1’ assume_tac)
      \\ Cases_on ‘v’ \\ gs [])
    \\ pairarg_tac \\ gvs []
    \\ CASE_TAC \\ gs []
    \\ simp [eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ first_x_assum (qspec_then ‘x + 1’ assume_tac) \\ gs [])
  \\ simp [eval_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ gs [Once eval_to_def]
  \\ gs [Once eval_to_def]
  \\ rename1 ‘eval_to k’
  \\ first_x_assum (qspec_then ‘k + 1’ assume_tac) \\ gs []
QED

Theorem force_eval:
  force v = eval (Force (Value v))
Proof
  rw [Once eval_Force] \\ rw [force_def]
QED

Theorem apply_force_rel:
  Rv v w ∧
  (∀x y.
     Re x y ∧
     (allow_error ∨ eval x ≠ INL Type_error) ⇒
       ($= +++ Rv) (eval x) (eval y)) ∧
  (∀v w. Rv v w ⇒ Re (Force (Value v)) (Force (Value w))) ∧
  (allow_error ∨ force v ≠ INL Type_error) ⇒
    ($= +++ Rv) (force v) (force w)
Proof
  rw [force_eval]
QED

Theorem eval_not_error:
  eval x ≠ INL Type_error ⇒
    ∀k. eval_to k x ≠ INL Type_error
Proof
  simp [eval_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ qx_gen_tac ‘j’ \\ rw []
  \\ drule_then (qspec_then ‘k’ assume_tac) eval_to_mono
  \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
  \\ drule_then (qspec_then ‘j’ assume_tac) eval_to_mono
  \\ Cases_on ‘j < k’ \\ gs []
QED

Theorem eval_to_eval_lift:
  (∀k x y.
     Re x y ∧
     (allow_error ∨ (∀k. eval_to k x ≠ INL Type_error)) ⇒
       ($= +++ Rv) (eval_to k x) (eval_to k y)) ⇒
    ∀x y.
      Re x y ∧
      (allow_error ∨ eval x ≠ INL Type_error) ⇒
        ($= +++ Rv) (eval x) (eval y)
Proof
  rw [DISJ_EQ_IMP]
  \\ ‘¬allow_error ⇒ ∀k. eval_to k x ≠ INL Type_error’
    by (rw [DISJ_EQ_IMP] \\ gs []
        \\ drule eval_not_error \\ gs [])
  \\ qpat_x_assum ‘eval x = _ ⇒ _’ kall_tac
  \\ simp [eval_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro
  \\ simp [PULL_FORALL]
  \\ qx_gen_tac ‘i’
  \\ qx_gen_tac ‘j’
  \\ qx_gen_tac ‘k’
  \\ rw [] \\ gs []
  >- (
    first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (qspec_then ‘i + j’ assume_tac)
    \\ dxrule_then (qspec_then ‘i + j’ assume_tac) eval_to_mono
    \\ dxrule_then (qspec_then ‘i + j’ assume_tac) eval_to_mono \\ gs [])
  >- (
    first_x_assum (drule_then assume_tac) \\ gs [])
  \\ first_x_assum (drule_then assume_tac) \\ gs []
QED

val _ = export_theory ();
