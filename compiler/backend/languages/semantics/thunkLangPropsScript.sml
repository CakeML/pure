(*
  Some useful theorems about the thunkLang_subst syntax and semantics.
 *)
Theory thunkLangProps
Ancestors
  string option sum pair list alist finite_map
  pred_set rich_list thunkLang_primitives
  pure_semantics[qualified]
  thunkLang pure_misc thunk_semantics
Libs
  term_tactic monadsyntax intLib


val _ = numLib.prefer_num ();

Theorem exp_size_lemma:
  (∀x xs. MEM x xs ⇒ exp_size x ≤ list_size exp_size xs) ∧
  (∀x y xs. MEM (x,y) xs ⇒
    exp_size y ≤ list_size (pair_size (list_size char_size) exp_size) xs) ∧
  (∀x xs. MEM x xs ⇒ v_size x < list_size v_size xs)
Proof
  rpt conj_tac
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [exp_size_def]
  \\ first_x_assum drule
  \\ simp []
QED

(* -------------------------------------------------------------------------
 * Property about terms stating they do not contain a value
 * ------------------------------------------------------------------------- *)

Definition no_value_def:
  (no_value (Var n) = T) ∧
  (no_value (Force x) = no_value x) ∧
  (no_value (Prim op xs) = EVERY no_value xs) ∧
  (no_value (Monad mop xs) = EVERY no_value xs) ∧
  (no_value (If x y z) = (no_value x ∧ no_value y ∧ no_value z)) ∧
  (no_value (App x y) = (no_value x ∧ no_value y)) ∧
  (no_value (Lam s x) = no_value x) ∧
  (no_value (Let opt x y) = (no_value x ∧ no_value y)) ∧
  (no_value (MkTick x) = no_value x) ∧
  (no_value (Letrec f x) = (no_value x ∧ EVERY no_value (MAP SND f) ∧ EVERY ok_bind (MAP SND f))) ∧
  (no_value (Value v) = F) ∧
  (no_value (Delay x) = no_value x)
Termination
  WF_REL_TAC ‘measure exp_size’ >>
  simp[MEM_MAP, PULL_EXISTS] >> simp[SND_THM] >>
  Induct_on ‘f’ >> rw[] >> pairarg_tac >> gvs[] >>
  last_x_assum drule >> disch_then $ qspec_then ‘x’ assume_tac >> gvs[]
End

Theorem no_value_Lams:
  ∀l x. no_value (Lams l x) = no_value x
Proof
  Induct >> gs [no_value_def]
QED

Theorem no_value_Apps:
  ∀l x. no_value (Apps x l) = (no_value x ∧ EVERY no_value l)
Proof
  Induct >> gs [no_value_def] >>
  metis_tac []
QED

(* -------------------------------------------------------------------------
 * Lemmas about Lams and Apps
 * ------------------------------------------------------------------------- *)

Theorem freevars_Lams:
  ∀l e. freevars (Lams l e) = freevars e DIFF (set l)
Proof
  Induct >> gvs [freevars_def, DIFF_INTER_COMPL] >>
  gvs [SET_EQ_SUBSET, SUBSET_DEF]
QED

Theorem freevars_Apps:
  ∀l e. freevars (Apps e l) = freevars e ∪ BIGUNION (set (MAP freevars l))
Proof
  Induct >> gvs [freevars_def, UNION_ASSOC]
QED

Theorem boundvars_Lams:
  ∀l e. boundvars (Lams l e) = boundvars e ∪ (set l)
Proof
  Induct >> gvs [boundvars_def] >>
  once_rewrite_tac [INSERT_SING_UNION] >>
  rw [SET_EQ_SUBSET, SUBSET_DEF]
QED

Theorem boundvars_Apps:
  ∀l e. boundvars (Apps e l) = boundvars e ∪ BIGUNION (set (MAP boundvars l))
Proof
  Induct >> gvs [boundvars_def, UNION_ASSOC]
QED

Theorem eval_to_Lams:
  ∀(l : string list) k e. l ≠ [] ⇒ eval_to k (Lams l e) = INR (Closure (HD l) (Lams (TL l) e))
Proof
  Cases >> gvs [eval_to_def]
QED

Theorem Lams_split:
  ∀l e. l ≠ [] ⇒ Lams l e = Lam (HD l) (Lams (TL l) e)
Proof
  Cases >> gvs []
QED


(* -------------------------------------------------------------------------
 * Alternative induction theorem for :exp
 * ------------------------------------------------------------------------- *)

Theorem exp_ind:
  ∀P.
    (∀n. P (Var n)) ∧
    (∀op xs. (∀a. MEM a xs ⇒ P a) ⇒ P (Prim op xs)) ∧
    (∀mop xs. (∀a. MEM a xs ⇒ P a) ⇒ P (Monad mop xs)) ∧
    (∀x y z. P x ∧ P y ∧ P z ⇒ P (If x y z)) ∧
    (∀x y. P x ∧ (∀z. exp_size z ≤ exp_size y ⇒ P z) ⇒ P x ⇒ P (App x y)) ∧
    (∀s b. P b ⇒ P (Lam s b)) ∧
    (∀v x y. P x ∧ P y ⇒ P (Let v x y)) ∧
    (∀f x. (∀n x'. MEM (n,x') f ⇒ P x') ∧ P x ⇒ P (Letrec f x)) ∧
    (∀x. P x ⇒ P (Delay x)) ∧
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

Theorem boundvars_subst:
  ∀e l. boundvars (subst l e) = boundvars e
Proof
  Induct using freevars_ind >> rw [boundvars_def, subst_def]
  >- (CASE_TAC >> gvs [boundvars_def])
  >- (AP_TERM_TAC >> AP_TERM_TAC >>
      irule LIST_EQ >> rw [EL_MAP] >>
      last_x_assum irule >>
      gvs [EL_MEM])
  >- (AP_TERM_TAC >> AP_TERM_TAC >>
      irule LIST_EQ >> rw [EL_MAP] >>
      last_x_assum irule >>
      gvs [EL_MEM])
  >- (gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM] >>
      AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
      AP_TERM_TAC >> AP_TERM_TAC >>
      irule LIST_EQ >> rw [EL_MAP] >>
      pairarg_tac >> gvs [] >>
      last_x_assum irule >>
      gvs [MEM_EL] >>
      first_x_assum $ irule_at Any >> gvs [])
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
  (∀mop xs. closed (Monad mop xs) ⇔ EVERY closed xs) ∧
  (∀x. closed (Force x) ⇔ closed x)  ∧
  (∀x. closed (Delay x) ⇔ closed x)  ∧
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

Theorem subst_APPEND:
  ∀e l1 l2. subst (l1 ++ l2) e = subst l1 (subst l2 e)
Proof
  Induct using freevars_ind >> gvs [subst_def, FILTER_APPEND]
  >- (gvs [REVERSE_APPEND, ALOOKUP_APPEND] >>
      rw [] >> CASE_TAC >> gvs [subst_def])
  >- (rw [] >> irule LIST_EQ >>
      rw [EL_MAP] >>
      last_x_assum irule >> gvs [EL_MEM])
  >- (rw [] >> irule LIST_EQ >>
      rw [EL_MAP] >>
      last_x_assum irule >> gvs [EL_MEM]) >>
  rw []
  >- (irule LIST_EQ >>
      rw [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, EL_MAP] >>
      pairarg_tac >> gvs [MEM_EL, PULL_EXISTS] >>
      last_x_assum irule >>
      first_x_assum $ irule_at Any >> gvs [])
  >- rw [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
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
  >- ((* Monad *)
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

Theorem subst_notin_frees:
  ∀vs e. DISJOINT (set (MAP FST vs)) (freevars e) ⇒ subst vs e = e
Proof
  Induct >> gvs [subst_empty] >> Cases >>
  once_rewrite_tac [CONS_APPEND] >> rw [subst_APPEND] >>
  gvs [subst1_notin_frees]
QED

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

Theorem subst_App:
  ∀vs f e. subst vs (App f e) = App (subst vs f) (subst vs e)
Proof
  gvs [subst_def]
QED

Theorem subst_Force:
  ∀vs e. subst vs (Force e) = Force (subst vs e)
Proof
  gvs [subst_def]
QED

Theorem subst_Tick:
  ∀vs e. subst vs (Tick e) = Tick (subst vs e)
Proof
  gvs [subst_def, GSYM LAMBDA_PROD, FILTER_T]
QED

Theorem subst_Var:
  ∀vs s. subst vs (Var s) = case ALOOKUP (REVERSE vs) s of NONE => Var s | SOME x2 => Value x2
Proof
  gvs [subst_def]
QED

Theorem subst_Lams:
  ∀l e b. subst b (Lams l e) = Lams l (subst (FILTER (λ(v,e). ¬MEM v l) b) e)
Proof
  Induct >> gvs [subst_def, GSYM LAMBDA_PROD, FILTER_T, FILTER_FILTER] >>
  gvs [LAMBDA_PROD, CONJ_COMM]
QED

Theorem subst_Apps:
  ∀l e b. subst b (Apps e l) = Apps (subst b e) (MAP (subst b) l)
Proof
  Induct >> gvs [subst_def]
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

Theorem eval_to_wo_def[allow_rebind] = REWRITE_RULE [LEX_DEF] eval_to_wo_def;

(* -------------------------------------------------------------------------
 * Generalized semantics theorem
 * ------------------------------------------------------------------------- *)

Definition sim_ok_def:
  sim_ok allow_error Rv Re ⇔
    (∀x y.
       Re x y ∧
       (¬allow_error ⇒ eval x ≠ INL Type_error) ⇒
         ($= +++ Rv) (eval x) (eval y)) ∧
    (∀vs ws x y.
       LIST_REL Rv (MAP SND vs) (MAP SND ws) ∧
       MAP FST vs = MAP FST ws ∧
       Re x y ⇒
         Re (subst vs x) (subst ws y))
End

Definition cont_rel_def[simp]:
  cont_rel Re Done Done = T ∧
  cont_rel Re (BC v c) (BC w d) = (Re v w ∧ cont_rel Re c d) ∧
  cont_rel Re (HC v c) (HC w d) = (Re v w ∧ cont_rel Re c d) ∧
  cont_rel Re _ _ = F
End

Definition state_rel_def:
  state_rel Rv = LIST_REL (LIST_REL Rv)
End

Definition next_rel_def[simp]:
  next_rel Rv Re (thunk_semantics$Act a c s) (thunk_semantics$Act b d t) =
    (a = b ∧ cont_rel Re c d ∧ state_rel Rv s t) ∧
  next_rel Rv Re Ret Ret = T ∧
  next_rel Rv Re Div Div = T ∧
  next_rel Rv Re Err Err = T ∧
  next_rel Rv Re (_: (string # string) next_res) _ = F
End

Definition rel_ok_def:
  rel_ok allow_error Rv Re ⇔
    (∀v1 w1 v2 w2 f g.
       Re v1 w1 ∧
       Rv v2 w2 ∧
       (¬allow_error ⇒
          apply_closure v1 v2 f ≠ Err ∧
          f (INL Type_error) = Err) ∧
       (∀(x : err + v) y.
              ($= +++ Rv) x y ∧
              (¬allow_error ⇒ f x ≠ Err) ⇒
                next_rel Rv Re (f x) (g y)
                ) ⇒
         next_rel Rv Re (apply_closure v1 v2 f)
                        (apply_closure w1 w2 g)) ∧
    (∀s x w.
       Rv (Closure s x) w ⇒ (∃t y. w = Closure t y) ∨ (∃g m. w = Recclosure g m)) ∧
    (∀f n w.
       Rv (Recclosure f n) w ⇒ (∃g m. w = Recclosure g m) ∨ (∃t y. w = Closure t y)) ∧
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
       x = y ⇒ Rv (Monadic s [Lit x])
                  (Monadic s [Lit y])) ∧
    (∀s t.
       Rv (Monadic s [Cons t []])
          (Monadic s [Cons t []])) ∧
    (∀s x y.
       Rv x y ⇒ Rv (Monadic s [Value x])
                   (Monadic s [Value y])) ∧
    (∀mop vs w.
       Rv (Monadic mop vs) w ⇒ ∃ws. w = Monadic mop ws ∧
                                      LIST_REL Re vs ws)
End

Theorem rel_ok_get_atoms:
  ∀x y.
    rel_ok ae Rv Re ∧
    LIST_REL Rv x y ∧
    (∀z. MEM z x ⇒ ∀w. z ≠ DoTick w) ⇒
      get_atoms x = get_atoms y
Proof
  ho_match_mp_tac get_atoms_ind \\ rw [] \\ fs [rel_ok_def] \\ gs []
  >~[ ‘get_atoms (DoTick _::_)’] >- (
    gvs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, SF DNF_ss])
  \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs [get_atoms_def]
  \\ metis_tac[]
QED


fun print_tac str g = (print (str ^ "\n"); ALL_TAC g);

val _ = print "Proving sim_ok_next ...\n";

(* next preserves relation *)
Theorem sim_ok_next:
  ∀k v c s w d t.
    rel_ok allow_error Rv Re ∧
    sim_ok allow_error Rv Re ∧
    ($= +++ Rv) v w ∧
    cont_rel Re c d ∧
    state_rel Rv s t ∧
    (¬allow_error ⇒ next k v c s ≠ Err) ⇒
      next_rel Rv Re (next k v c s) (next k w d t)
Proof
  ho_match_mp_tac next_ind \\ rw []
  \\ qpat_x_assum ‘(_ +++ _) _ _’ mp_tac
  \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ simp []
  >- (
    rw [next_def]
    \\ CASE_TAC \\ simp [])
  \\ rename1 ‘Rv v w’
  \\ Cases_on ‘(∃s x. v = Closure s x) ∨ (∃f n. v = Recclosure f n) ∨
               (∃x. v = Thunk x) ∨ (∃x. v = Atom x)  ∨ (∃nm vs. v = Constructor nm vs)’
  >- (
    qpat_x_assum ‘rel_ok _ _ _’ mp_tac \\ rw [rel_ok_def]
    \\ rpt (first_x_assum (drule_all_then assume_tac)) \\ rw [] \\ fs []
    \\ simp [next_def])
  \\ Cases_on ‘∃x. v = DoTick x’
  >- (
    qpat_x_assum ‘rel_ok _ _ _’ mp_tac \\ rw [rel_ok_def]
    \\ gs [Once next_def]
    \\ rpt (first_x_assum (drule_all_then assume_tac)) \\ rw [] \\ fs []
    \\ simp [Once next_def] \\ simp [Once next_def])
  \\ rfs []
  \\ ‘∃mop vs. v = Monadic mop vs’
    by (ntac 5 (pop_assum mp_tac) \\ Cases_on ‘v’ \\ simp [] \\ fs[])
  \\ rw []
  \\ ‘∃ws. w = Monadic mop ws ∧ LIST_REL Re vs ws’
    by (qpat_x_assum ‘Rv _ _’ mp_tac
        \\ qpat_x_assum ‘rel_ok _ _ _’ mp_tac
        \\ rw [rel_ok_def]
        \\ rpt (first_x_assum drule) \\ rw [])
  \\ rw []
  \\ drule_then assume_tac LIST_REL_LENGTH
  \\ once_rewrite_tac [next_def] \\ simp []
  \\ print_tac "[1/9] Ret"
  \\ IF_CASES_TAC \\ simp[]
  >- ((* Ret *)
    gvs[LENGTH_EQ_NUM_compute] >> simp[with_value_def] >> rename1 `Re v w` >>
    `($= +++ Rv) (eval v) (eval w)` by (
      fs[rel_ok_def] >> first_x_assum drule >> rw[] >>
      gvs[sim_ok_def] >> first_x_assum irule >> simp[] >>
      rw[] >> CCONTR_TAC >> fs[Once next_def, with_value_def]) >>
    Cases_on `eval v` >> Cases_on `eval w` >> gvs[] >- (CASE_TAC >> gvs[]) >>
    rw[] >> reverse $ Cases_on `c` >> Cases_on `d` >> gvs[] >> rw[]
    >- (first_x_assum irule >> rw[] >> gvs[] >> fs[Once next_def, with_value_def]) >>
    fs[rel_ok_def] >> first_x_assum irule >> rw[] >> gvs[] >>
    fs[Once next_def, with_value_def]
    )
  \\ print_tac "[2/9] Raise"
  \\ IF_CASES_TAC
  >- ((* Raise *)
    gvs[LENGTH_EQ_NUM_compute] >> simp[with_value_def] >> rename1 `Re v w` >>
    `($= +++ Rv) (eval v) (eval w)` by (
      fs[rel_ok_def] >> first_x_assum drule >> rw[] >>
      gvs[sim_ok_def] >> first_x_assum irule >> simp[] >>
      rw[] >> CCONTR_TAC >> fs[Once next_def, with_value_def]) >>
    Cases_on `eval v` >> Cases_on `eval w` >> gvs[] >- (CASE_TAC >> gvs[]) >>
    rw[] >> Cases_on `c` >> Cases_on `d` >> gvs[] >> rw[]
    >- (first_x_assum irule >> rw[] >> gvs[] >> fs[Once next_def, with_value_def]) >>
    fs[rel_ok_def] >> first_x_assum irule >> rw[] >> gvs[] >>
    fs[Once next_def, with_value_def]
    )
  \\ print_tac "[3/9] Bind"
  \\ IF_CASES_TAC
  >- ((* Bind *)
    rw[]
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2 ⇔ x = 0 ∨ x = 1”]
    \\ fs [SF DNF_ss]
    \\ first_x_assum irule \\ rw []
    \\ fs[Once next_def]
    \\ fs [sim_ok_def]
    \\ first_x_assum irule \\ simp[]
    \\ fs[rel_ok_def] \\ first_x_assum drule \\ rw[]
    \\ fs[Once next_def]
    \\ Cases_on `eval h` \\ gvs[] \\ Cases_on `x` \\ gvs[]
    )
  \\ print_tac "[4/9] Handle"
  \\ IF_CASES_TAC
  >- ((* Handle *)
    rw[]
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2 ⇔ x = 0 ∨ x = 1”]
    \\ fs [SF DNF_ss]
    \\ first_x_assum irule \\ rw []
    \\ fs[Once next_def]
    \\ fs [sim_ok_def]
    \\ first_x_assum irule \\ simp[]
    \\ fs[rel_ok_def] \\ first_x_assum drule \\ rw[]
    \\ fs[Once next_def]
    \\ Cases_on `eval h` \\ gvs[] \\ Cases_on `x` \\ gvs[]
    )
  \\ print_tac "[5/9] Act"
  \\ IF_CASES_TAC
  >- ((* Act *)
    rw [] \\ gs []
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute, DECIDE “∀x. x < 1 ⇔ x = 0”]
    \\ rename1 ‘Re v w’
    \\ simp [with_atoms_def, result_map_def]
    \\ ‘¬allow_error ⇒ eval v ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ gs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (eval v) (eval w)’ by (
      gvs[sim_ok_def] >> first_x_assum irule >>
      fs[rel_ok_def] >> first_x_assum drule >> simp[])
    \\ Cases_on ‘eval v’ \\ Cases_on ‘eval w’ \\ gvs []
    >~ [‘eval _ = INL err’] >- (Cases_on ‘err’ \\ fs [])
    \\ rename1 ‘eval v = INR a’  \\ rename1 ‘eval w = INR b’
    \\ ‘¬allow_error ⇒ get_atoms [a] ≠ NONE’
      by (rpt strip_tac \\ gs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘∀x. a = Atom x ⇒ a = b’
      by (rpt strip_tac \\ gs [rel_ok_def])
    \\ reverse (Cases_on ‘∃x. a = Atom x’) \\ gvs [get_atoms_def]
    >- (
      ‘get_atoms [a] = NONE’
        by (Cases_on ‘a’ \\ fs [get_atoms_def])
      \\ simp []
      \\ Cases_on ‘b’ \\ gvs [get_atoms_def]
      \\ Cases_on ‘a’ \\ fs [get_atoms_def, rel_ok_def]
      \\ rpt (first_x_assum (drule_then assume_tac)) \\ rw [])
    \\ CASE_TAC \\ fs [])
  \\ print_tac "[6/9] Alloc"
  \\ IF_CASES_TAC
  >- ((* Alloc *)
    rw [] \\ gs []
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2 ⇔ x = 0 ∨ x = 1”]
    \\ gvs [SF DNF_ss]
    \\ rename1 ‘Rv (_ _ [v1; v2]) (_ _ [w1; w2])’
    \\ gvs [with_atoms_def, result_map_def]
    \\ ‘¬allow_error ⇒ eval v1 ≠ INL Type_error ∧ eval v2 ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ gs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (eval v1) (eval w1)’ by (
      gvs[sim_ok_def] >> first_x_assum irule >>
      fs[rel_ok_def] >> first_x_assum drule >> simp[])
    \\ ‘($= +++ Rv) (eval v2) (eval w2)’ by (
      gvs[sim_ok_def] >> first_x_assum irule >>
      fs[rel_ok_def] >> first_x_assum rev_drule >> simp[]) >>
    `∀err. eval v1 = INL err ⇔ eval w1 = INL err` by (
      Cases_on `eval v1` >> Cases_on `eval w1` >> gvs[]) >>
    `∀err. eval v2 = INL err ⇔ eval w2 = INL err` by (
      Cases_on `eval v2` >> Cases_on `eval w2` >> gvs[]) >>
    IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[] >>
    Cases_on `eval v1` >> gvs[]
    >~ [`eval _ = INL err`] >- (Cases_on `err` >> gvs[SF DNF_ss, EQ_IMP_THM]) >>
    Cases_on `eval v2` >> gvs[]
    >~ [`eval _ = INL err`] >- (Cases_on `err` >> gvs[SF DNF_ss, EQ_IMP_THM]) >>
    Cases_on `eval w1` >> gvs[] >> Cases_on `eval w2` >> gvs[]
    \\ rename1 ‘eval v1 = INR a’  \\ rename1 ‘eval w1 = INR b’
    \\ ‘¬allow_error ⇒ get_atoms [a] ≠ NONE’
      by (rpt strip_tac \\ gs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘∀x. a = Atom x ⇒ a = b’
      by (rpt strip_tac \\ gs [rel_ok_def])
    \\ reverse (Cases_on ‘∃x. a = Atom x’) \\ gvs [get_atoms_def]
    >- (
      ‘get_atoms [a] = NONE’
        by (Cases_on ‘a’ \\ fs [get_atoms_def])
      \\ simp []
      \\ Cases_on ‘b’ \\ gvs [get_atoms_def]
      \\ Cases_on ‘a’ \\ fs [get_atoms_def, rel_ok_def]
      \\ rpt (first_x_assum (drule_then assume_tac)) \\ rw []) >>
    BasicProvers.TOP_CASE_TAC >> gvs[] >>
    BasicProvers.TOP_CASE_TAC >> gvs[] >>
    first_x_assum irule >>
    gvs[state_rel_def, LIST_REL_REPLICATE_same, LIST_REL_EL_EQN, rel_ok_def] >>
    rw[] >> gvs[] >>
    qpat_x_assum `next _ _ _ _ ≠ _` mp_tac >>
    simp[Once next_def, with_atoms_def,
        result_map_def, get_atoms_def, with_value_def]
    )
  \\ print_tac "[7/9] Length"
  \\ IF_CASES_TAC
  >- ((* Length *)
    rw [] \\ gs []
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute, DECIDE “∀x. x < 1 ⇔ x = 0”]
    \\ rename1 ‘Re v w’
    \\ simp [with_atoms_def, result_map_def]
    \\ ‘¬allow_error ⇒ eval v ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ gs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (eval v) (eval w)’ by (
      gvs[sim_ok_def] >> first_x_assum irule >>
      fs[rel_ok_def] >> first_x_assum drule >> simp[])
    \\ Cases_on ‘eval v’ \\ Cases_on ‘eval w’ \\ gvs []
    >~ [‘eval _ = INL err’] >- (Cases_on ‘err’ \\ fs [])
    \\ rename1 ‘eval v = INR a’  \\ rename1 ‘eval w = INR b’
    \\ ‘¬allow_error ⇒ get_atoms [a] ≠ NONE’
      by (rpt strip_tac \\ gs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘∀x. a = Atom x ⇒ a = b’
      by (rpt strip_tac \\ gs [rel_ok_def])
    \\ reverse (Cases_on ‘∃x. a = Atom x’) \\ gvs [get_atoms_def]
    >- (
      ‘get_atoms [a] = NONE’
        by (Cases_on ‘a’ \\ fs [get_atoms_def])
      \\ simp []
      \\ Cases_on ‘b’ \\ gvs [get_atoms_def]
      \\ Cases_on ‘a’ \\ fs [get_atoms_def, rel_ok_def]
      \\ rpt (first_x_assum (drule_then assume_tac)) \\ rw [])
    \\ ‘LENGTH s = LENGTH t’
      by gs [state_rel_def, LIST_REL_EL_EQN]
    \\ Cases_on ‘k = 0’ \\ fs [] \\ CASE_TAC \\ fs []
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum (resolve_then Any irule HD) \\ simp []
    \\ gs [state_rel_def, LIST_REL_REPLICATE_same, LIST_REL_EL_EQN, rel_ok_def]
    \\ strip_tac
    \\ gs [Once next_def, with_atoms_def, result_map_def, get_atoms_def])
  \\ print_tac "[8/9] Deref"
  \\ IF_CASES_TAC
  >- ((* Deref *)
    rw [] \\ gs []
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2 ⇔ x = 0 ∨ x = 1”]
    \\ gvs [SF DNF_ss]
    \\ rename1 ‘Rv (_ _ [v1; v2]) (_ _ [w1; w2])’
    \\ simp [with_atoms_def, result_map_def]
    \\ ‘¬allow_error ⇒ eval v1 ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ gs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘¬allow_error ⇒ eval v2 ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ gs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (eval v1) (eval w1)’ by (
      gvs[sim_ok_def] >> first_x_assum irule >>
      fs[rel_ok_def] >> first_x_assum drule >> simp[])
    \\ ‘($= +++ Rv) (eval v2) (eval w2)’ by (
      gvs[sim_ok_def] >> first_x_assum irule >>
      fs[rel_ok_def] >> first_x_assum drule >> simp[])
    \\ Cases_on ‘eval v1’ \\ Cases_on ‘eval w1’ \\ gvs []
    >~ [‘eval _ = INL err’] >- (
      Cases_on ‘err = Type_error’ \\ fs []
      \\ Cases_on ‘eval v2’ \\ Cases_on ‘eval w2’ \\ gvs []
      >~ [‘eval _ = INL err’] >- (
        Cases_on ‘err’ \\ fs [])
      \\ Cases_on ‘err’ \\ fs [])
    \\ Cases_on ‘eval v2’ \\ Cases_on ‘eval w2’ \\ gvs []
    >~ [‘eval _ = INL err’] >- (
        Cases_on ‘err’ \\ fs [])
    \\ rename1 ‘eval v1 = INR a1’  \\ rename1 ‘eval w1 = INR b1’
    \\ rename1 ‘eval v2 = INR a2’  \\ rename1 ‘eval w2 = INR b2’
    \\ ‘¬allow_error ⇒ get_atoms [a1; a2] ≠ NONE’
      by (rpt strip_tac \\ gs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘∀x. a1 = Atom x ⇒ a1 = b1’
      by (rpt strip_tac \\ gs [rel_ok_def])
    \\ ‘∀x. a2 = Atom x ⇒ a2 = b2’
      by (rpt strip_tac \\ gs [rel_ok_def])
    \\ reverse (Cases_on ‘∃x. a1 = Atom x’) \\ fs []
    >- (
      Cases_on ‘∃y. b1 = Atom y’ \\ fs []
      >- (
        rw [] \\ fs [rel_ok_def]
        \\ qpat_x_assum ‘Rv a1 b1’ assume_tac
        \\ Cases_on ‘a1’ \\ fs []
        \\ rpt (first_x_assum (drule_then assume_tac)) \\ rw []
        \\ fs [get_atoms_def])
      \\ ‘get_atoms [a1; a2] = NONE’
        by (Cases_on ‘a1’ \\ fs [get_atoms_def])
      \\ ‘get_atoms [b1; b2] = NONE’
        by (Cases_on ‘b1’ \\ fs [get_atoms_def])
      \\ simp [])
    \\ reverse (Cases_on ‘∃x. a2 = Atom x’) \\ fs []
    >- (
      Cases_on ‘∃y. b2 = Atom y’ \\ fs []
      >- (
        rw [] \\ fs [rel_ok_def]
        \\ qpat_x_assum ‘Rv a2 b2’ assume_tac
        \\ Cases_on ‘a2’ \\ fs []
        \\ rpt (first_x_assum (drule_then assume_tac)) \\ rw []
        \\ fs [get_atoms_def])
      \\ rw []
      \\ ‘get_atoms [a2] = NONE’
        by (Cases_on ‘a2’ \\ fs [get_atoms_def])
      \\ ‘get_atoms [b2] = NONE’
        by (Cases_on ‘b2’ \\ fs [get_atoms_def])
      \\ gvs [] \\ simp [get_atoms_def])
    \\ rw [] \\ simp [get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ ‘LENGTH s = LENGTH t’
      by fs [state_rel_def, LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ qpat_x_assum ‘¬_ ⇒ next _ _ _ _ ≠ _’ mp_tac
    \\ simp [Once next_def, with_atoms_def, result_map_def, get_atoms_def]
    \\ strip_tac
    \\ ‘LENGTH (EL n t) = LENGTH (EL n s)’
      by gvs [state_rel_def, LIST_REL_EL_EQN]
    \\ rpt (first_x_assum (resolve_then Any assume_tac HD) \\ fs [])
    \\ IF_CASES_TAC \\ fs []
    >- (
      first_x_assum irule \\ gs [SF SFY_ss]
      \\ fs [rel_ok_def]
      \\ first_x_assum irule
      \\ qpat_x_assum ‘state_rel _ _ _’ mp_tac
      \\ rw [state_rel_def]
      \\ fs [Once LIST_REL_EL_EQN]
      \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ gs [LIST_REL_EL_EQN]
      \\ first_x_assum $ qspec_then ‘Num i’ assume_tac \\ gvs []
      \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ gvs [])
    \\ first_x_assum irule \\ gs [SF SFY_ss]
    \\ fs [rel_ok_def] \\ intLib.COOPER_TAC)
  \\ print_tac "[9/9] Update"
  \\ IF_CASES_TAC
  >- ((* Update *)
    rw [] \\ gs []
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 3 ⇔ x = 0 ∨ x = 1 ∨ x = 2”]
    \\ gvs [SF DNF_ss]
    \\ rename1 ‘Rv (_ _ [v1; v2; v3]) (_ _ [w1; w2; w3])’
    \\ simp [with_atoms_def, result_map_def]
    \\ ‘¬allow_error ⇒ eval v1 ≠ INL Type_error ∧
          eval v2 ≠ INL Type_error ∧eval v3 ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ gs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (eval v1) (eval w1)’ by (
      gvs[sim_ok_def] >> first_x_assum irule >>
      fs[rel_ok_def] >> first_x_assum drule >> simp[])
    \\ ‘($= +++ Rv) (eval v2) (eval w2)’ by (
      gvs[sim_ok_def] >> first_x_assum irule >>
      fs[rel_ok_def] >> first_x_assum rev_drule >> simp[])
    \\ ‘($= +++ Rv) (eval v3) (eval w3)’ by (
      gvs[sim_ok_def] >> first_x_assum irule >>
      fs[rel_ok_def] >> first_x_assum rev_drule >> simp[]) >>
    `∀err. eval v1 = INL err ⇔ eval w1 = INL err` by (
      Cases_on `eval v1` >> Cases_on `eval w1` >> gvs[]) >>
    `∀err. eval v2 = INL err ⇔ eval w2 = INL err` by (
      Cases_on `eval v2` >> Cases_on `eval w2` >> gvs[]) >>
    `∀err. eval v3 = INL err ⇔ eval w3 = INL err` by (
      Cases_on `eval v3` >> Cases_on `eval w3` >> gvs[]) >>
    IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[] >>
    Cases_on `eval v1` >> gvs[]
    >~ [`eval _ = INL err`] >- (Cases_on `err` >> gvs[EQ_IMP_THM, SF DNF_ss]) >>
    Cases_on `eval v2` >> gvs[]
    >~ [`eval _ = INL err`] >- (Cases_on `err` >> gvs[EQ_IMP_THM, SF DNF_ss]) >>
    Cases_on `eval v3` >> gvs[]
    >~ [`eval _ = INL err`] >- (Cases_on `err` >> gvs[EQ_IMP_THM, SF DNF_ss]) >>
    Cases_on `eval w1` >> gvs[] >> Cases_on `eval w2` >> gvs[] >>
    Cases_on `eval w3` >> gvs[]
    \\ rename1 ‘eval v1 = INR a1’  \\ rename1 ‘eval w1 = INR b1’
    \\ rename1 ‘eval v2 = INR a2’  \\ rename1 ‘eval w2 = INR b2’
    \\ ‘¬allow_error ⇒ get_atoms [a1; a2] ≠ NONE’
      by (rpt strip_tac \\ gs [Once next_def, with_atoms_def, result_map_def])
    \\ ‘∀x. a1 = Atom x ⇒ a1 = b1’
      by (rpt strip_tac \\ gs [rel_ok_def])
    \\ ‘∀x. a2 = Atom x ⇒ a2 = b2’
      by (rpt strip_tac \\ gs [rel_ok_def])
    \\ reverse (Cases_on ‘∃x. a1 = Atom x’) \\ fs []
    >- (
      Cases_on ‘∃y. b1 = Atom y’ \\ fs []
      >- (
        rw [] \\ fs [rel_ok_def]
        \\ qpat_x_assum ‘Rv a1 b1’ assume_tac
        \\ Cases_on ‘a1’ \\ fs []
        \\ rpt (first_x_assum (drule_then assume_tac)) \\ rw []
        \\ fs [get_atoms_def])
      \\ ‘get_atoms [a1; a2] = NONE’
        by (Cases_on ‘a1’ \\ fs [get_atoms_def])
      \\ ‘get_atoms [b1; b2] = NONE’
        by (Cases_on ‘b1’ \\ fs [get_atoms_def])
      \\ simp [])
    \\ reverse (Cases_on ‘∃x. a2 = Atom x’) \\ fs []
    >- (
      Cases_on ‘∃y. b2 = Atom y’ \\ fs []
      >- (
        rw [] \\ fs [rel_ok_def]
        \\ qpat_x_assum ‘Rv a2 b2’ assume_tac
        \\ Cases_on ‘a2’ \\ fs []
        \\ rpt (first_x_assum (drule_then assume_tac)) \\ rw []
        \\ fs [get_atoms_def])
      \\ rw []
      \\ ‘get_atoms [a2] = NONE’
        by (Cases_on ‘a2’ \\ fs [get_atoms_def])
      \\ ‘get_atoms [b2] = NONE’
        by (Cases_on ‘b2’ \\ fs [get_atoms_def])
      \\ gvs [] \\ simp [get_atoms_def])
    \\ rw [] \\ simp [get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ ‘LENGTH s = LENGTH t’
      by fs [state_rel_def, LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ qpat_x_assum ‘¬_ ⇒ next _ _ _ _ ≠ _’ mp_tac
    \\ simp [Once next_def, with_value_def,
             with_atoms_def, result_map_def, get_atoms_def]
    \\ fs[result_map_def, get_atoms_def]
    \\ strip_tac
    \\ ‘LENGTH (EL n t) = LENGTH (EL n s)’
      by gvs [state_rel_def, LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ fs[]
    >- (
      first_x_assum irule >> simp[result_map_def, get_atoms_def]
      \\ gvs [state_rel_def, LIST_REL_EL_EQN, EL_LUPDATE]
      \\ rw [] \\ gs []
      \\ rw [EL_LUPDATE] \\ fs[rel_ok_def]
      )
    >- (last_x_assum irule >> fs[rel_ok_def])
    >- (first_x_assum irule >> fs[rel_ok_def])
    )
  \\ fs []
QED

val _ = print "Done with sim_ok_next.\n";

Theorem sim_ok_next_action:
  rel_ok allow_error Rv Re ∧
  sim_ok allow_error Rv Re ∧
  ($= +++ Rv) v w ∧
  cont_rel Re c d ∧
  state_rel Rv s t ∧
  (¬allow_error ⇒ next_action v c s ≠ Err) ⇒
    next_rel Rv Re (next_action v c s) (next_action w d t)
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
  rel_ok allow_error Rv Re ∧
  sim_ok allow_error Rv Re ∧
  ($= +++ Rv) v w ∧
  cont_rel Re c d ∧
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
       cont_rel Re c d ∧
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
  rel_ok allow_error Rv Re ∧
  sim_ok allow_error Rv Re ∧
  Re x y ∧
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

Theorem eval_to_Force_anyThunk:
  ∀k x v. eval_to k (Force x) = INR v ⇒ ¬is_anyThunk v
Proof
  Induct \\ rw [Once eval_to_def]
  \\ Cases_on `eval_to (SUC k) x` \\ gvs []
  \\ reverse $ Cases_on `dest_Tick y` \\ gvs []
  >- (first_x_assum drule \\ rw [])
  \\ Cases_on `dest_anyThunk y` \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ Cases_on `eval_to k (subst_funs binds y'')` \\ gvs []
QED

Theorem eval_Force:
  eval (Force (Value v)) =
    case dest_Tick v of
      NONE =>
        do (y,binds) <- dest_anyThunk v;
           res <- eval (subst_funs binds y);
           if is_anyThunk res then fail Type_error else return res
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
      \\ Cases_on ‘eval_to (x - 1) (subst_funs binds y')’ \\ gvs []
      \\ TRY (IF_CASES_TAC \\ gvs [])
      \\ Cases_on ‘eval (subst_funs binds y')’ \\ gvs []
      \\ ‘eval_to (x - 1) (subst_funs binds y') ≠ INL Diverge’ by gvs []
      \\ drule_then assume_tac eval_to_equals_eval \\ gvs [])
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
