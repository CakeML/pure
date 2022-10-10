(*
  This transformation allows rewriting

     Force (Var n)    into    Var m

  inside ‘body’ in expressions such as

     Let (SOME m) (Force (Var n)) body

*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory;
open pure_miscTheory thunkLangPropsTheory;

val _ = new_theory "thunk_let_forceProof";

val _ = set_grammar_ancestry ["finite_map", "pred_set", "rich_list",
                              "thunkLang", "wellorder", "quotient_sum",
                              "quotient_pair", "thunkLangProps"];

val _ = numLib.prefer_num ();

Theorem SUM_REL_def[local,simp] = quotient_sumTheory.SUM_REL_def;

Theorem PAIR_REL_def[local,simp] = quotient_pairTheory.PAIR_REL;

Datatype:
  lhs = Var string | Val thunkLang$v
End

Definition name_clash_def:
  name_clash NONE _ = F ∧
  name_clash _ NONE = F ∧
  name_clash (SOME n) (SOME (Var m, w)) = (n = m ∨ n = w) ∧
  name_clash (SOME n) (SOME (Val v, w)) = (n = w)
End

Inductive exp_rel:
[exp_rel_Let_Force_Var:]
  (∀m v w y1 y2.
     exp_rel (SOME (Var v,w)) y1 y2 ∧
     v ≠ w ⇒
       exp_rel m (Let (SOME w) (Force (Var v)) y1)
                 (Let (SOME w) (Force (Var v)) y2)) ∧
[exp_rel_Let_Force_Value:]
  (∀m v1 v2 w y1 y2.
     exp_rel (SOME (Val v1,w)) y1 y2 ∧ v_rel v1 v2 ⇒
       exp_rel m (Let (SOME w) (Force (Value v1)) y1)
                 (Let (SOME w) (Force (Value v2)) y2)) ∧
[exp_rel_Force_Var:]
  (∀v w.
     exp_rel (SOME(Var v,w)) (Force (Var v)) (Var w)) ∧
[exp_rel_Force_Value:]
  (∀v w.
     exp_rel (SOME(Val v,w)) (Force (Value v)) (Var w)) ∧
[exp_rel_Force_Value_Value:]
  (∀m i t v w.
     (∀j. eval_to (i + j) (Force (Value t)) = INR v) ∧ v_rel v w ⇒
     exp_rel m (Force (Value t)) (Value w)) ∧
(* Boilerplate: *)
[exp_rel_App:]
  (∀m f g x y.
     exp_rel m f g ∧
     exp_rel m x y ⇒
       exp_rel m (App f x) (App g y)) ∧
[exp_rel_Lam:]
  (∀m s x y.
     exp_rel NONE x y ⇒
       exp_rel m (Lam s x) (Lam s y)) ∧
[exp_rel_Letrec:]
  (∀m f g x y.
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel NONE x y) f g ∧
     exp_rel NONE x y ⇒
       exp_rel m (Letrec f x) (Letrec g y)) ∧
[exp_rel_Let:]
  (∀m bv x1 y1 x2 y2.
     exp_rel m x1 x2 ∧
     exp_rel (if name_clash bv m then NONE else m) y1 y2 ⇒
       exp_rel m (Let bv x1 y1) (Let bv x2 y2)) ∧
[exp_rel_If:]
  (∀m x1 x2 y1 y2 z1 z2.
     LIST_REL (exp_rel m) [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel m (If x1 y1 z1) (If x2 y2 z2)) ∧
[exp_rel_Prim:]
  (∀m op xs ys.
     LIST_REL (exp_rel m) xs ys ⇒
       exp_rel m (Prim op xs) (Prim op ys)) ∧
[exp_rel_Delay:]
  (∀m x y.
     exp_rel m x y ⇒
       exp_rel m (Delay x) (Delay y)) ∧
[exp_rel_Box:]
  (∀m x y.
     exp_rel m x y ⇒
       exp_rel m (Box x) (Box y)) ∧
[exp_rel_Force:]
  (∀m x y.
     exp_rel m x y ⇒
       exp_rel m (Force x) (Force y)) ∧
[exp_rel_MkTick:]
  (∀m x y.
     exp_rel m x y ⇒
       exp_rel m (MkTick x) (MkTick y)) ∧
[exp_rel_Var:]
  (∀m v.
     exp_rel m (Var v) (Var v)) ∧
[exp_rel_Value:]
  (∀m v w.
     v_rel v w ⇒
     exp_rel m (Value v) (Value w)) ∧
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x)) ∧
[v_rel_Constructor:]
  (∀vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws)) ∧
[v_rel_Closure:]
  (∀s x y.
     exp_rel NONE x y ∧ freevars x ⊆ {s} ⇒
       v_rel (Closure s x) (Closure s y)) ∧
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ⇒
       v_rel (DoTick v) (DoTick w)) ∧
[v_rel_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel NONE x y ∧
                               freevars x ⊆ set (MAP FST f)) f g ⇒
       v_rel (Recclosure f n) (Recclosure g n)) ∧
[v_rel_Thunk_INR:]
  (∀x y.
     exp_rel NONE x y ∧ closed x ⇒
       v_rel (Thunk (INR x)) (Thunk (INR y))) ∧
[v_rel_Thunk_INL:]
  (∀v w.
     v_rel v w ⇒
       v_rel (Thunk (INL v)) (Thunk (INL w)))
End

Theorem v_rel_cases[local] = CONJUNCT2 exp_rel_cases;

(* Boilerplate *)
Theorem v_rel_def[simp] =
  [ “v_rel (Closure s x) z”,
    “v_rel z (Closure s x)”,
    “v_rel (Recclosure s x) z”,
    “v_rel z (Recclosure s x)”,
    “v_rel (Constructor s x) z”,
    “v_rel z (Constructor s x)”,
    “v_rel (Atom x) z”,
    “v_rel z (Atom x)”,
    “v_rel (Thunk (INL x)) z”,
    “v_rel z (Thunk (INR x))” ]
  |> map (SIMP_CONV (srw_ss()) [Once v_rel_cases])
  |> LIST_CONJ;

Theorem exp_rel_NONE_freevars: (* statement needs to generalisation before proof *)
  exp_rel NONE x y ⇒ freevars x = freevars y
Proof
  cheat (*
  qsuff_tac ‘
    (∀x y. exp_rel x y ⇒ freevars x = freevars y) ∧
    (∀v w. v_rel v w ⇒ T)’
  >- rw []
  \\ ho_match_mp_tac exp_rel_strongind
  \\ simp [freevars_def]
  \\ rw []
  >- (
    rw [EXTENSION, EQ_IMP_THM] \\ gs [])
  >- (
    rw [EXTENSION, EQ_IMP_THM] \\ gs []
    \\ fs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN,
           Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
    \\ rw [] \\ gs [EL_MAP, ELIM_UNCURRY, SF CONJ_ss, SF SFY_ss])
  >- (
    Cases_on ‘bv’ \\ gs [freevars_def])
  >- (
    ‘MAP freevars xs = MAP freevars ys’
      suffices_by rw [SF ETA_ss]
    \\ irule LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP]) *)
QED

Definition subst_acc_def:
  subst_acc vs ws NONE = NONE ∧
  subst_acc vs ws (SOME (x,y)) =
    case x of
    | Val v => (SOME (x,y))
    | Var s => case ALOOKUP (REVERSE vs) s of
               | NONE => (SOME (x,y))
               | SOME w => (SOME (Val w,y))
End

Triviality MAP_FST_FILTER_NEQ:
  ∀vs. MAP FST (FILTER (λ(n,x). n ≠ w) vs) = FILTER (λx. x ≠ w) (MAP FST vs)
Proof
  Induct \\ fs [FORALL_PROD] \\ rw []
QED

Triviality LIST_REL_MAP_SND_FILTER:
  ∀vs ws.
    LIST_REL P (MAP SND vs) (MAP SND ws) ∧ MAP FST vs = MAP FST ws ⇒
    LIST_REL P (MAP SND (FILTER (λ(n,x). n ≠ w) vs))
               (MAP SND (FILTER (λ(n,x). n ≠ w) ws))
Proof
  Induct \\ fs [PULL_EXISTS]
  \\ rw [] \\ Cases_on ‘ws’ \\ fs []
  \\ gvs [] \\ res_tac
  \\ rpt $ first_x_assum $ irule_at $ Pos last
  \\ rw [] \\ gvs [UNCURRY]
QED

Triviality ALOOKUP_MEM_MAP_FST:
  ∀xs v x. ALOOKUP xs v = SOME x ⇒ MEM v (MAP FST xs)
Proof
  Induct \\ fs [FORALL_PROD] \\ rw []
QED

Theorem ALOOKUP_REVERSE_REVERSE:
  ∀vs ws v x1 x2.
    LIST_REL P (MAP SND vs) (MAP SND ws) ∧
    MAP FST vs = MAP FST ws ∧
    ALOOKUP (REVERSE vs) v = SOME x1 ∧
    ALOOKUP (REVERSE ws) v = SOME x2 ⇒
    P x1 x2
Proof
  Induct using SNOC_INDUCT \\ rw []
  \\ Cases_on ‘ws’ using SNOC_CASES
  \\ fs [REVERSE_SNOC]
  \\ rename [‘FST z = FST t’]
  \\ PairCases_on ‘z’
  \\ PairCases_on ‘t’
  \\ gvs [AllCaseEqs(),MAP_SNOC,LIST_REL_SNOC]
  \\ res_tac \\ fs []
QED

Theorem exp_rel_subst:
  ∀vs x ws y.
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    MAP FST vs = MAP FST ws ∧
    exp_rel NONE x y ⇒
      exp_rel NONE (subst vs x) (subst ws y)
Proof
  qsuff_tac ‘
    (∀m x y. exp_rel m x y ⇒
       ∀vs ws.
         LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
         MAP FST vs = MAP FST ws ∧
         (∀a w z. m = SOME (a,w) ⇒ ALOOKUP (REVERSE ws) w = NONE) ⇒
         exp_rel (subst_acc vs ws m) (subst vs x) (subst ws y)) ∧
    (∀v1 v2. v_rel v1 v2 ⇒ v_rel v1 v2)’
  >- (fs [] \\ disch_then $ qspec_then ‘NONE’ mp_tac \\ fs [subst_acc_def])
  \\ ho_match_mp_tac exp_rel_strongind
  \\ rpt strip_tac
  >- (* exp_rel_Let_Force_Var *)
   (fs [subst_def]
    \\ CASE_TAC \\ fs [] \\ fs [ALOOKUP_NONE]
    \\ CASE_TAC \\ fs [] \\ fs [ALOOKUP_NONE]
    \\ fs [MAP_REVERSE] \\ gvs []
    >-
     (irule exp_rel_Let_Force_Var \\ fs []
      \\ first_x_assum $ qspecl_then [‘FILTER (λ(n,x). n ≠ w) vs’,
                                      ‘FILTER (λ(n,x). n ≠ w) ws’] mp_tac
      \\ fs [subst_acc_def]
      \\ fs [MAP_FST_FILTER_NEQ,ALOOKUP_NONE,MEM_FILTER,MAP_REVERSE]
      \\ CASE_TAC
      >- (disch_then irule
          \\ irule LIST_REL_MAP_SND_FILTER \\ fs [])
      \\ imp_res_tac ALOOKUP_MEM \\ fs [MEM_FILTER]
      \\ qpat_x_assum ‘MAP FST _ = _’ (assume_tac o GSYM)
      \\ fs [] \\ fs [MEM_MAP,EXISTS_PROD] \\ gvs [])
    \\ imp_res_tac ALOOKUP_MEM_MAP_FST
    \\ fs [MAP_REVERSE] \\ gvs []
    \\ irule exp_rel_Let_Force_Value \\ fs []
    \\ first_x_assum $ qspecl_then [‘FILTER (λ(n,x). n ≠ w) vs’,
                                    ‘FILTER (λ(n,x). n ≠ w) ws’] mp_tac
    \\ fs [subst_acc_def]
    \\ fs [MAP_FST_FILTER_NEQ,ALOOKUP_NONE,MEM_FILTER,MAP_REVERSE]
    \\ impl_tac
    >- (irule LIST_REL_MAP_SND_FILTER \\ fs [])
    \\ fs [GSYM FILTER_REVERSE,ALOOKUP_FILTER]
    \\ drule_all ALOOKUP_REVERSE_REVERSE \\ fs [])
  >- (* exp_rel_Let_Force_Value *)
   (fs [subst_def]
    \\ irule exp_rel_Let_Force_Value \\ fs []
    \\ first_x_assum $ qspecl_then [‘FILTER (λ(n,x). n ≠ w) vs’,
                                    ‘FILTER (λ(n,x). n ≠ w) ws’] mp_tac
    \\ fs [subst_acc_def]
    \\ disch_then irule
    \\ fs [MAP_FST_FILTER_NEQ,ALOOKUP_NONE,MEM_FILTER,MAP_REVERSE]
    \\ irule LIST_REL_MAP_SND_FILTER \\ fs [])
  >- (* exp_rel_Force_Var *)
   (fs [subst_def,subst_acc_def]
    \\ CASE_TAC \\ fs []
    >- irule exp_rel_Force_Var
    >- irule exp_rel_Force_Value)
  >- (* exp_rel_Force_Value *)
   (fs [subst_def,subst_acc_def]
    \\ irule exp_rel_Force_Value)
  >- (* exp_rel_Force_Value_Value *)
   (fs [subst_def,subst_acc_def]
    \\ imp_res_tac exp_rel_Force_Value_Value
    \\ fs [])
  (* easy cases follow *)
  \\ cheat
QED

Definition force_goal_def: (* needs special attention to m *)
  force_goal k x =
    ∀y.
      exp_rel NONE x y ∧ closed x ∧
      (∀k. eval_to k x ≠ INL Type_error) ⇒
      ∃j.
        ($= +++ v_rel)
          (eval_to (j + k) x)
          (eval_to k y)
End

Theorem eval_to_WF_IND[local] =
  WF_IND
  |> GEN_ALL
  |> Q.ISPEC ‘eval_to_wo’
  |> REWRITE_RULE [eval_to_wo_WF]
  |> Q.SPEC ‘UNCURRY force_goal’
  |> SIMP_RULE std_ss [FORALL_PROD]

Theorem exp_rel_SOME_Val_IMP:
  exp_rel (SOME (Val v1,s)) y1 y2 ∧ v_rel u v ∧
  (∀j. eval_to (i + j) (Force (Value v1)) = INR u) ⇒
  exp_rel NONE (subst1 s u y1) (subst1 s v y2)
Proof
  qsuff_tac ‘
    (∀m y1 y2. exp_rel m y1 y2 ⇒
      ∀s i u v v1.
        (m ≠ NONE ⇒ m = SOME (Val v1,s)) ∧ v_rel u v ∧
        (∀j. eval_to (i + j) (Force (Value v1)) = INR u) ⇒
        exp_rel NONE (subst1 s u y1) (subst1 s v y2)) ∧
    (∀v1 v2. v_rel v1 v2 ⇒ v_rel v1 v2)’
  >- metis_tac []
  \\ ho_match_mp_tac exp_rel_strongind
  \\ rpt strip_tac
  \\ gvs [subst_def]

  \\ cheat
QED

Triviality IMP_closed_subst_Rec:
  LIST_REL
     (λ(fn,x) (gn,y).
       fn = gn ∧ exp_rel NONE x y ∧ freevars x ⊆ set (MAP FST xs)) xs ys ∧
  ALOOKUP (REVERSE xs) s = SOME (Delay x1) ⇒
  closed (subst (MAP (λ(g,x). (g,Recclosure xs g)) xs) x1)
Proof
  rw []
  \\ imp_res_tac ALOOKUP_MEM \\ fs []
  \\ drule_all LIST_REL_MEM \\ fs [EXISTS_PROD]
  \\ fs [freevars_def,closed_subst]
  \\ rw []
  \\ irule SUBSET_TRANS
  \\ pop_assum $ irule_at Any
  \\ fs [SUBSET_DEF,MEM_MAP,EXISTS_PROD]
QED

Theorem exp_rel_eval_to:
  ∀k x. force_goal k x
Proof
  ho_match_mp_tac eval_to_WF_IND
  \\ once_rewrite_tac [force_goal_def]
  \\ gen_tac
  \\ Cases \\ gs []
  >~ [‘Value v’] >-
   (ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘Let bv x1 y1’] >-
   (Cases_on ‘bv’
    >~ [‘Let NONE’] >-
     (strip_tac
      \\ rw [Once exp_rel_cases]
      \\ simp [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      >- (
       qexists_tac ‘0’
       \\ simp [])
      \\ ‘∀k. eval_to k x1 ≠ INL Type_error’
        by (qx_gen_tac ‘j’
            \\ strip_tac
            \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + 1’
            \\ simp [])
      \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) x1) (eval_to (k - 1) x2)’
        by (first_x_assum irule \\ simp [eval_to_wo_def])
      \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
      >-
       (qexists_tac ‘j’
        \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs [])
      \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
      \\ ‘∀k. eval_to k y1 ≠ INL Type_error’
        by (qx_gen_tac ‘j1’
            \\ strip_tac
            \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j1 + j + k’ \\ simp []
            \\ ‘eval_to (j + (j1 + k) - 1) x1 = eval_to (j + k - 1) x1’
              by (irule eval_to_mono \\ gs [])
            \\ simp []
            \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
            \\ irule eval_to_mono \\ simp [])
      \\ Cases_on ‘eval_to (k - 1) y2 = INL Diverge’ \\ gs []
      >-
       (Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
        >- (qexists_tac ‘0’ \\ simp [])
        \\ ‘∀j. eval_to (j + k - 1) x1 = eval_to (k - 1) x1’
          by (gen_tac \\ irule eval_to_mono \\ gs [])
        \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
        \\ ‘∀j. j + k - 1 = j + (k - 1)’ by gs []
        \\ asm_simp_tac std_ss []
        \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
        \\ first_x_assum irule
        \\ simp [eval_to_wo_def])
      \\ ‘∀j1. eval_to (j1 + j + k - 1) x1 = eval_to (j + k - 1) x1’
        by (gen_tac \\ irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Q.REFINE_EXISTS_TAC ‘j + j1’ \\ gs []
      \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
      \\ qmatch_goalsub_abbrev_tac ‘(_ +++ _) (eval_to _ lhs) (eval_to _ rhs)’
      \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) lhs)
                             (eval_to (k - 1) rhs)’
        suffices_by (
        disch_then (qx_choose_then ‘j1’ assume_tac)
        \\ qexists_tac ‘j1’
        \\ ‘eval_to (j + j1 + k - 1) lhs = eval_to (j1 + k - 1) lhs’
          by (irule eval_to_mono \\ gs []
              \\ strip_tac \\ gs []
              \\ Cases_on ‘eval_to (k - 1) rhs’ \\ gs [])
        \\ gs [])
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def])
    \\ rename [‘Let (SOME s) x1 y1’]
    \\ strip_tac
    \\ reverse (rw [Once exp_rel_cases])
    \\ gvs []
    >-
     (‘∀k. eval_to k x1 ≠ INL Type_error’
        by (qx_gen_tac ‘j’
            \\ strip_tac
            \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + 1’
            \\ simp [])
      \\ simp [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      >- (qexists_tac ‘0’ \\ simp [])
      \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) x1)
                             (eval_to (k - 1) x2)’
        by (first_x_assum irule \\ simp [eval_to_wo_def])
      \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
      >-
       (qexists_tac ‘j’
        \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs [])
      \\ ‘∀j1. eval_to (j1 + j + k - 1) x1 = eval_to (j + k - 1) x1’
        by (gen_tac \\ irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
      \\ rename1 ‘v_rel u v’
      \\ ‘∀k. eval_to k (subst1 s u y1) ≠ INL Type_error’
        by (qx_gen_tac ‘j1’
            \\ strip_tac
            \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + j1 + k’ \\ simp []
            \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
            \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to (k - 1) (subst1 s v y2) = INL Diverge’
      >-
       (Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
        >- (qexists_tac ‘0’ \\ simp [])
        \\ ‘∀j. eval_to (j + k - 1) x1 = eval_to (k - 1) x1’
          by (gen_tac \\ irule eval_to_mono \\ gs [])
        \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
        \\ ‘∀j. j + k - 1 = j + (k - 1)’ by gs []
        \\ asm_simp_tac std_ss []
        \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
        \\ first_x_assum irule
        \\ rgs [eval_to_wo_def]
        \\ irule_at Any exp_rel_subst \\ gs [closed_subst])
      \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
      \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
      \\ qmatch_goalsub_abbrev_tac ‘(_ +++ _) (eval_to _ lhs) (eval_to _ rhs)’
      \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) lhs)
                             (eval_to (k - 1) rhs)’
        suffices_by (
        disch_then (qx_choose_then ‘j1’ assume_tac)
        \\ qexists_tac ‘j1’
        \\ ‘eval_to (j + j1 + k - 1) lhs = eval_to (j1 + k - 1) lhs’
          by (irule eval_to_mono \\ gs []
              \\ strip_tac \\ gs []
              \\ Cases_on ‘eval_to (k - 1) rhs’ \\ gs [])
        \\ gs [])
      \\ first_x_assum irule
      \\ unabbrev_all_tac
      \\ gs [eval_to_wo_def, subst1_commutes]
      \\ irule_at Any exp_rel_subst \\ gs [closed_subst])
    \\ qabbrev_tac ‘x1 = Force (Value v1)’
    \\ qabbrev_tac ‘x2 = Force (Value v2)’
    \\ ‘∀k. eval_to k x1 ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j + 1’
          \\ simp [])
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ simp [])
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) x1)
                           (eval_to (k - 1) x2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def]
          \\ unabbrev_all_tac \\ fs []
          \\ irule exp_rel_Force \\ fs []
          \\ irule exp_rel_Value \\ fs [])
    \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    >-
     (qexists_tac ‘j’
      \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs [])
    \\ ‘∀j1. eval_to (j1 + j + k - 1) x1 = eval_to (j + k - 1) x1’
      by (gen_tac \\ irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
    \\ rename1 ‘v_rel u v’
    \\ ‘∀k. eval_to k (subst1 s u y1) ≠ INL Type_error’
      by (qx_gen_tac ‘j1’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j + j1 + k’ \\ simp []
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ irule eval_to_mono \\ gs [])
    \\ Cases_on ‘eval_to (k - 1) (subst1 s v y2) = INL Diverge’
    >-
     (Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
      >- (qexists_tac ‘0’ \\ simp [])
      \\ ‘∀j. eval_to (j + k - 1) x1 = eval_to (k - 1) x1’
        by (gen_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
      \\ ‘∀j. j + k - 1 = j + (k - 1)’ by gs []
      \\ asm_simp_tac std_ss []
      \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
      \\ first_x_assum irule
      \\ rgs [eval_to_wo_def]
      \\ gs [closed_subst]
      \\ drule_then irule exp_rel_SOME_Val_IMP \\ fs []
      \\ qexists_tac ‘j + k’  \\ rw []
      \\ rpt $ first_x_assum $ qspec_then ‘j'+1’ mp_tac \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
    \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
    \\ qmatch_goalsub_abbrev_tac ‘(_ +++ _) (eval_to _ lhs) (eval_to _ rhs)’
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) lhs)
                           (eval_to (k - 1) rhs)’
      suffices_by (
      disch_then (qx_choose_then ‘j1’ assume_tac)
      \\ qexists_tac ‘j1’
      \\ ‘eval_to (j + j1 + k - 1) lhs = eval_to (j1 + k - 1) lhs’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs []
            \\ Cases_on ‘eval_to (k - 1) rhs’ \\ gs [])
      \\ gs [])
    \\ first_x_assum irule
    \\ simp [eval_to_wo_def]
    \\ unabbrev_all_tac
    \\ fs [closed_subst]
    \\ drule_then irule exp_rel_SOME_Val_IMP \\ fs []
    \\ qexists_tac ‘j + k’  \\ rw []
    \\ rpt $ first_x_assum $ qspec_then ‘j'+1’ mp_tac \\ fs [])
  >~ [‘Force x’] >-
   (strip_tac
    \\ rw [Once exp_rel_cases]
    >-
      (qexists_tac ‘i’ \\ fs []
       \\ simp [EVAL “eval_to k (Value _)”])
    \\ rename1 ‘exp_rel NONE x y’
    \\ CONV_TAC (QUANT_CONV (LAND_CONV (SIMP_CONV std_ss [Once eval_to_def])))
    \\ CONV_TAC (QUANT_CONV (RAND_CONV (SIMP_CONV std_ss [Once eval_to_def])))
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ simp [])
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + k) x) (eval_to k y)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def]
          \\ qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
          \\ simp [Once eval_to_def]
          \\ qexists_tac ‘j + 1’ \\ simp []
          \\ ‘eval_to (j + 1) x = eval_to j x’
            suffices_by rw []
          \\ irule eval_to_mono \\ gs [])
    \\ Cases_on ‘eval_to k y = INL Diverge’
    >- (
      Cases_on ‘eval_to k x = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k) x = eval_to k x’
        by (gen_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k x’ \\ gs [])
    \\ Cases_on ‘eval_to (j + k) x’ \\ Cases_on ‘eval_to k y’ \\ gvs []
    >- (
      qexists_tac ‘j’
      \\ simp [])
    \\ rename1 ‘v_rel v w’
    \\ ‘OPTREL v_rel (dest_Tick v) (dest_Tick w)’
      by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
          \\ gs [Once (CONJUNCT2 exp_rel_cases)])
    \\ gs [OPTREL_def]
    >~ [‘dest_Tick _ = SOME _’] >-
     (Cases_on ‘eval_to (k - 1) (Force (Value y0)) = INL Diverge’
      >-
       (Cases_on ‘eval_to k x = INL Diverge’
        >-
         (qexists_tac ‘0’
          \\ simp [])
        \\ ‘∀j. eval_to (j + k) x = eval_to k x’
          by (gen_tac \\ irule eval_to_mono \\ gs [])
        \\ gs []
        \\ ‘∀j. j + k - 1 = j + (k - 1)’
          by gs []
        \\ asm_simp_tac std_ss []
        \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
        \\ first_x_assum irule
        \\ simp [eval_to_wo_def]
        \\ irule_at Any exp_rel_Force
        \\ irule_at Any exp_rel_Value
        \\ gs []
        \\ qx_gen_tac ‘j’
        \\ strip_tac
        \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _ ’ mp_tac
        \\ simp [Once eval_to_def]
        \\ qexists_tac ‘j + k’
        \\ asm_simp_tac std_ss []
        \\ simp []
        \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
        \\ irule eval_to_mono \\ gs [])
      \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
        by (gen_tac \\ irule eval_to_mono \\ gs [])
      \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
      \\ qsuff_tac ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1))
                                           (Force (Value x0)))
                                  (eval_to ( k - 1)
                                           (Force (Value y0)))’
      >- (
        disch_then (qx_choose_then ‘j1’ assume_tac)
        \\ ‘eval_to (j1 + j + k - 1) (Force (Value x0)) =
            eval_to (j1 + k - 1) (Force (Value x0))’
          by (irule eval_to_mono \\ gs []
              \\ strip_tac \\ gs []
              \\ Cases_on ‘eval_to (k - 1) (Force (Value y0))’ \\ gs [])
        \\ qexists_tac ‘j1’ \\ gs [])
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def, exp_size_def]
      \\ irule_at Any exp_rel_Force
      \\ irule_at Any exp_rel_Value \\ gs []
      \\ qx_gen_tac ‘j1’
      \\ strip_tac
      \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _ ’ mp_tac
      \\ simp [Once eval_to_def]
      \\ qexists_tac ‘j + (j1 + k)’
      \\ asm_simp_tac std_ss []
      \\ simp []
      \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
      \\ irule eval_to_mono \\ gs [])
    \\ Cases_on ‘dest_anyThunk w’ \\ gs []
    >- (
      qexists_tac ‘j’ \\ gs []
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
      \\ rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL (exp_rel NONE) (ALOOKUP (REVERSE xs) s)
                                (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL \\ gs []
            \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
            \\ fs [FORALL_PROD])
      \\ gs [OPTREL_def]
      \\ rgs [Once exp_rel_cases])
    \\ pairarg_tac \\ gvs []
    \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
    >- (
      rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL (exp_rel NONE) (ALOOKUP (REVERSE xs) s)
                                (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL \\ gs []
            \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
            \\ fs [FORALL_PROD])
      \\ gvs [OPTREL_def,AllCaseEqs()]
      \\ rgs [Once exp_rel_cases] \\ rw []
      \\ rename1 ‘exp_rel _ x1 y1’
      THEN (
        Cases_on ‘eval_to (k - 1) (subst_funs binds y1) = INL Diverge’
        >- (
          Cases_on ‘eval_to k x = INL Diverge’
          >- (
            qexists_tac ‘0’
            \\ simp [])
          \\ ‘∀j1. eval_to (j1 + k) x = eval_to (j + k) x’
            by (gen_tac
                \\ drule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
                \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
                \\ gs [])
          \\ gs []
          \\ ‘∀j. j + k - 1 = j + (k - 1)’ by gs []
          \\ asm_simp_tac std_ss []
          \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
          \\ first_x_assum irule
          \\ gs [eval_to_wo_def, subst_funs_def]
          \\ irule_at Any exp_rel_subst
          \\ drule_all IMP_closed_subst_Rec \\ strip_tac
          \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
                   EVERY2_MAP]
          \\ gvs [LIST_REL_EL_EQN, LIST_REL_CONJ, ELIM_UNCURRY]
          \\ irule_at Any LIST_EQ \\ gvs [EL_MAP]
          \\ qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
          \\ simp [Once eval_to_def]
          \\ qexists_tac ‘j + k’
          \\ simp [dest_anyThunk_def, subst_funs_def, ELIM_UNCURRY]
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ irule eval_to_mono \\ gs [])
        \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
          by (gen_tac \\ irule eval_to_mono \\ gs [])
        \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
        \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) (subst_funs xs x1))
                                   (eval_to (k - 1) (subst_funs binds y1))’
          suffices_by (
            disch_then (qx_choose_then ‘j1’ assume_tac)
            \\ ‘eval_to (j1 + j + k - 1) (subst_funs xs x1) =
                eval_to (j1 + k - 1) (subst_funs xs x1)’
              by (irule eval_to_mono \\ gs []
                  \\ strip_tac \\ gs []
                  \\ Cases_on ‘eval_to (k - 1) (subst_funs binds y1)’ \\ gs [])
            \\ qexists_tac ‘j1’ \\ gs [])
        \\ first_x_assum irule
        \\ gs [eval_to_wo_def, subst_funs_def]
        \\ irule_at Any exp_rel_subst
        \\ drule_all IMP_closed_subst_Rec \\ strip_tac
        \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
                 EVERY2_MAP]
        \\ gvs [LIST_REL_EL_EQN, LIST_REL_CONJ, ELIM_UNCURRY]
        \\ irule_at Any LIST_EQ \\ gvs [EL_MAP]
        \\ qx_gen_tac ‘j1’
        \\ strip_tac
        \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
        \\ simp [Once eval_to_def]
        \\ qexists_tac ‘j + (j1 + k)’
        \\ asm_simp_tac std_ss []
        \\ simp [dest_anyThunk_def, subst_funs_def, ELIM_UNCURRY]
        \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
        \\ irule eval_to_mono \\ gs []))
    \\ simp [subst_funs_def]
    \\ reverse CASE_TAC \\ gs []
    >- (
      rename1 ‘exp_rel _ x1 y1’
      \\ Cases_on ‘eval_to (k - 1) y1 = INL Diverge’
      >- (
        Cases_on ‘eval_to k x = INL Diverge’
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘∀j. eval_to (j + k) x = eval_to k x’
          by (gen_tac \\ irule eval_to_mono \\ gs [])
        \\ gvs []
        \\ ‘∀j. j + k - 1 = j + (k - 1)’ by gs []
        \\ asm_simp_tac std_ss []
        \\ qpat_assum `_ = INL Diverge` (SUBST1_TAC o SYM)
        \\ first_x_assum irule
        \\ gs [eval_to_wo_def]
        \\ qx_gen_tac ‘j’
        \\ strip_tac
        \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
        \\ simp [Once eval_to_def]
        \\ qexists_tac ‘j + k’
        \\ asm_simp_tac std_ss []
        \\ simp [dest_anyThunk_def, subst_funs_def]
        \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
        \\ irule eval_to_mono \\ gs [])
      \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
        by (gen_tac \\ irule eval_to_mono \\ gs [])
      \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
      \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) x1)
                                 (eval_to (k - 1) y1)’
        suffices_by (
          disch_then (qx_choose_then ‘j1’ assume_tac)
          \\ ‘eval_to (j1 + j + k - 1) x1 =
              eval_to (j1 + k - 1) x1’
            by (irule eval_to_mono \\ gs []
                \\ strip_tac \\ gs []
                \\ Cases_on ‘eval_to (k - 1) y1’ \\ gs [])
          \\ qexists_tac ‘j1’ \\ gs [])
      \\ first_x_assum irule
      \\ gs [eval_to_wo_def]
      \\ qx_gen_tac ‘j1’
      \\ strip_tac
      \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
      \\ simp [Once eval_to_def]
      \\ qexists_tac ‘j + (j1 + k)’
      \\ asm_simp_tac std_ss []
      \\ simp [dest_anyThunk_def, subst_funs_def]
      \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
      \\ irule eval_to_mono \\ gs [])
    \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
      by (gen_tac \\ irule eval_to_mono \\ gs [])
    \\ Q.REFINE_EXISTS_TAC ‘j + j1’ \\ gs []
    \\ rgs [Once (CONJUNCT2 exp_rel_cases)] \\ rw []
    \\ rename1 ‘eval_to k1 x1 = INR v1’
    \\ qexists_tac ‘j1 + k1’
    \\ ‘eval_to (k + k1 + j + j1 - 1) x1 = eval_to k1 x1’
      by (irule eval_to_mono \\ gs [])
    \\ gs [])
  >~ [‘Lam s x’] >-
   (ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘Delay x’] >-
   (ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘Box x’] >-
   (ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ rename1 ‘exp_rel _ x y’
    \\ simp [eval_to_def]
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + k) x) (eval_to k y)’
      suffices_by (
        disch_then (qx_choose_then ‘j’ assume_tac)
        \\ qexists_tac ‘j’
        \\ Cases_on ‘eval_to (j + k) x’ \\ Cases_on ‘eval_to k y’ \\ gs [])
    \\ first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def]
    \\ rpt strip_tac
    \\ first_x_assum (qspec_then ‘k’ mp_tac)
    \\ simp [eval_to_def])
  >~ [‘App f x’] >-
   (ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ rename1 ‘exp_rel _ x y’
    \\ simp [eval_to_def]
    \\ ‘∀k. eval_to k x ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ first_x_assum (qspec_then ‘j’ mp_tac)
          \\ simp [eval_to_def])
    \\ ‘∃j1. ($= +++ v_rel) (eval_to (j1 + k) x) (eval_to k y)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k) x’
      \\ gs [])
    \\ ‘∃u1. eval_to k y = INR u1’
      by (Cases_on ‘eval_to k y’ \\ gs []
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs []
          \\ Cases_on ‘eval_to (j1 + k) x’ \\ gs [])
    \\ simp []
    \\ ‘∀k. eval_to k f ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (App _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ ‘eval_to (j1 + k + j) f = eval_to j f’
            by (irule eval_to_mono \\ gs [])
          \\ ‘eval_to (j1 + k + j) x = eval_to (j1 + k) x’
            by (irule eval_to_mono \\ gs []
                \\ strip_tac \\ gs [])
          \\ qexists_tac ‘j1 + k + j’ \\ simp []
          \\ Cases_on ‘eval_to (j1 + k) x’ \\ gs [])
    \\ ‘∃j2. ($= +++ v_rel) (eval_to (j2 + k) f) (eval_to k g)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ ‘∃u2. eval_to (j1 + k) x = INR u2’
      by (Cases_on ‘eval_to (j1 + k) x’ \\ gs [])
    \\ gs []
    \\ Cases_on ‘eval_to k g’ \\ gs []
    >- (
      rename1 ‘_ = INL err’
      \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (j2 + k) f’ \\ gvs []
      \\ Cases_on ‘eval_to k x = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀i. eval_to (i + k) x = eval_to k x’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k x’ \\ gs []
      \\ Cases_on ‘eval_to k f’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ gs []
        \\ qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀i. eval_to (i + k) f = eval_to k f’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k f’ \\ gs [])
    \\ rename1 ‘eval_to k g = INR v1’
    \\ ‘∃v2. eval_to (j2 + k) f = INR v2’
      by (Cases_on ‘eval_to (j2 + k) f’ \\ gs [])
    \\ gs []
    \\ ‘∀j. eval_to (j + j1 + k) x = eval_to (j1 + k) x’
      by (strip_tac
          \\ irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ ‘∀j. eval_to (j + j2 + k) f = eval_to (j2 + k) f’
      by (strip_tac
          \\ irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ Cases_on ‘dest_anyClosure v1’ \\ gs []
    >- (
      qexists_tac ‘j1 + j2’ \\ gs []
      \\ once_rewrite_tac [DECIDE “j1 + (j2 + k) = j2 + (j1 + k)”]
      \\ gs []
      \\ Cases_on ‘v2’ \\ Cases_on ‘v1’ \\ gvs [dest_anyClosure_def]
      \\ rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL (exp_rel NONE) (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL \\ gs []
            \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
            \\ fs [FORALL_PROD])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel NONE x0 _’ mp_tac
      \\ rw [Once exp_rel_cases] \\ gs [])
    \\ pairarg_tac \\ gvs []
    \\ rename1 ‘subst (ws2 ++ [s2,w2]) b2’
    \\ ‘∃b1 ws1. dest_anyClosure v2 = INR (s2,b1,ws1) ∧
                 exp_rel NONE b1 b2 ∧
                 freevars b1 ⊆ set (MAP FST ws1) ∪ {s2} ∧
                 LIST_REL (λ(f,v) (g,w). f = g ∧ v_rel v w) ws1 ws2’
      by (Cases_on ‘v2’ \\ Cases_on ‘v1’ \\ gvs [dest_anyClosure_def]
          \\ rename1 ‘LIST_REL _ xs ys’
          \\ ‘OPTREL (exp_rel NONE) (ALOOKUP (REVERSE xs) s)
                                    (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL \\ gs []
                \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
                \\ fs [FORALL_PROD])
          \\ gs [OPTREL_def]
          \\ qpat_x_assum ‘exp_rel NONE x0 _’ mp_tac
          \\ rw [Once exp_rel_cases] \\ gs []
          \\ conj_tac
          >-
           (imp_res_tac ALOOKUP_MEM \\ fs []
            \\ drule_all LIST_REL_MEM \\ gvs [EXISTS_PROD] \\ strip_tac \\ fs []
            \\ fs [freevars_def,SUBSET_DEF,MEM_MAP,EXISTS_PROD] \\ metis_tac [])
          \\ gvs [EVERY2_MAP, LAMBDA_PROD]
          \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY])
    \\ IF_CASES_TAC \\ gs []
    >- (
      Cases_on ‘eval_to 0 x = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to j x = eval_to 0 x’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ Cases_on ‘eval_to 0 f = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to j f = eval_to 0 f’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ qexists_tac ‘0’ \\ simp [])
    \\ ‘∀k. eval_to k (subst (ws1 ++ [s2,u2]) b1) ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (App _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j1 + j2 + j + k’ \\ gs []
          \\ once_rewrite_tac
            [DECIDE “j + (j1 + (j2 + k)) = (j + j1) + (j2 + k)”] \\ gs []
          \\ once_rewrite_tac
            [DECIDE “j + (j1 + (j2 + k)) = (j + j2) + (j1 + k)”] \\ gs []
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ irule eval_to_mono \\ simp [])
    \\ Cases_on ‘eval_to (k - 1) (subst (ws2 ++ [s2,w2]) b2) = INL Diverge’
    >- (
      Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k) x = eval_to k x’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ Cases_on ‘eval_to k f = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k) f = eval_to k f’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ ‘∀j. j + k - 1 = j + (k - 1)’
        by gs []
      \\ asm_simp_tac bool_ss []
      \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def,closed_subst]
      \\ irule exp_rel_subst
      \\ gs [EVERY2_MAP, LIST_REL_CONJ, ELIM_UNCURRY]
      \\ irule LIST_EQ
      \\ gvs [EL_MAP, LIST_REL_EL_EQN])
    \\ Q.REFINE_EXISTS_TAC ‘j1 + j2 + j’ \\ gs []
    \\ once_rewrite_tac
      [DECIDE “j + (j1 + (j2 + k)) = (j + j2) + (j1 + k)”] \\ gs []
    \\ once_rewrite_tac
      [DECIDE “j + (j1 + (j2 + k)) = (j + j1) + (j2 + k)”] \\ gs []
    \\ qmatch_goalsub_abbrev_tac ‘_ (eval_to _ X1) (eval_to _ X2)’
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) X1) (eval_to (k - 1) X2)’
      by (first_x_assum irule
          \\ gs [Abbr ‘X1’, Abbr ‘X2’, eval_to_wo_def,closed_subst]
          \\ irule exp_rel_subst
          \\ gvs [EVERY2_MAP, LIST_REL_EL_EQN, ELIM_UNCURRY]
          \\ irule LIST_EQ
          \\ gs [EL_MAP])
    \\ qexists_tac ‘j’
    \\ ‘eval_to (j + k - 1) X1 ≠ INL Diverge’
      by (strip_tac \\ Cases_on ‘eval_to (k - 1) X2’ \\ gs [])
    \\ drule_then (qspec_then ‘j + j1 + j2 + k - 1’ assume_tac) eval_to_mono
    \\ gs [])
  >~ [‘Letrec f x’] >-
   (ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ rename1 ‘exp_rel _ x y’
    \\ ‘∀j. j + k - 1 = j + (k - 1)’
      by gs []
    \\ asm_simp_tac std_ss []
    \\ first_x_assum irule
    \\ simp [eval_to_wo_def, exp_size_def, subst_funs_def, closed_subst]
    \\ irule_at Any exp_rel_subst
    \\ rewrite_tac [CONJ_ASSOC]
    \\ reverse conj_tac
    >- fs [SUBSET_DEF,MEM_MAP,PULL_EXISTS,EXISTS_PROD]
    \\ rewrite_tac [GSYM CONJ_ASSOC]
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP, LAMBDA_PROD,
             GSYM FST_THM,SUBSET_DEF]
    \\ gs [ELIM_UNCURRY, LIST_REL_EL_EQN, SUBSET_DEF]
    \\ irule_at Any LIST_EQ
    \\ gs [EL_MAP,PULL_EXISTS,MEM_MAP]
    \\ conj_tac >- gvs [MEM_EL,SF SFY_ss]
    \\ qx_gen_tac ‘j’
    \\ strip_tac
    \\ qpat_x_assum ‘∀k. eval_to _ (Letrec _ _) ≠ _’ mp_tac
    \\ simp [eval_to_def, subst_funs_def]
    \\ qexists_tac ‘j + 1’ \\ simp [ELIM_UNCURRY])
  >~ [‘If x1 y1 z1’] >-
   (ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∀k. eval_to k x1 ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (If _ _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j + 1’ \\ gs [])
    \\ ‘∃j1. ($= +++ v_rel) (eval_to (j1 + (k - 1)) x1)
                                (eval_to (k - 1) x2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def])
    \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    >- (
      rename1 ‘_ = INL err’
      \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gvs []
      \\ qexists_tac ‘j1’ \\ simp [])
    \\ IF_CASES_TAC \\ gs []
    >- (
      ‘∀k. eval_to k y1 ≠ INL Type_error’
        by (qx_gen_tac ‘j’
            \\ strip_tac
            \\ qpat_x_assum ‘∀k. eval_to _ (If _ _ _) ≠ _’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + j1 + k’ \\ gs []
            \\ ‘eval_to (j + (j1 + k) - 1) x1 = eval_to (j1 + k - 1) x1’
              suffices_by (
                rw []
                \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
                \\ qpat_assum ‘eval_to j y1 = _’ (SUBST1_TAC o SYM)
                \\ irule eval_to_mono \\ gs [])
            \\ irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ ‘∃j2. ($= +++ v_rel) (eval_to (j2 + (k - 1)) y1)
                                  (eval_to (k - 1) y2)’
        by (first_x_assum irule \\ simp [eval_to_wo_def])
      \\ Cases_on ‘eval_to (k - 1) y2’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (j2 + k - 1) y1’ \\ gs []
        \\ Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘eval_to (j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
          by (drule_then (qspec_then ‘j1 + k - 1’ assume_tac ) eval_to_mono
              \\ drule_then (qspec_then ‘j2 + k - 1’ assume_tac ) eval_to_mono
              \\ gs [])
        \\ qexists_tac ‘j2’ \\ gs []
        \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs [])
      \\ qexists_tac ‘j1 + j2’
      \\ ‘eval_to (j1 + j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
      \\ ‘eval_to (j1 + j2 + k - 1) y1 = eval_to (j2 + k - 1) y1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j2 + k - 1) y1’ \\ gs [])
    \\ IF_CASES_TAC \\ gs []
    >- (
      ‘∀k. eval_to k z1 ≠ INL Type_error’
        by (qx_gen_tac ‘j’
            \\ strip_tac
            \\ qpat_x_assum ‘∀k. eval_to _ (If _ _ _) ≠ _’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + j1 + k’ \\ gs []
            \\ ‘eval_to (j + (j1 + k) - 1) x1 = eval_to (j1 + k - 1) x1’
              suffices_by (
                rw []
                \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
                \\ qpat_assum ‘eval_to j z1 = _’ (SUBST1_TAC o SYM)
                \\ irule eval_to_mono \\ gs [])
            \\ irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ ‘∃j2. ($= +++ v_rel) (eval_to (j2 + (k - 1)) z1)
                                  (eval_to (k - 1) z2)’
        by (first_x_assum irule \\ simp [eval_to_wo_def])
      \\ Cases_on ‘eval_to (k - 1) z2’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (j2 + k - 1) z1’ \\ gs []
        \\ Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘eval_to (j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
          by (drule_then (qspec_then ‘j1 + k - 1’ assume_tac ) eval_to_mono
              \\ drule_then (qspec_then ‘j2 + k - 1’ assume_tac ) eval_to_mono
              \\ gs [])
        \\ qexists_tac ‘j2’ \\ gs []
        \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs [])
      \\ qexists_tac ‘j1 + j2’
      \\ ‘eval_to (j1 + j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
      \\ ‘eval_to (j1 + j2 + k - 1) z1 = eval_to (j2 + k - 1) z1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j2 + k - 1) z1’ \\ gs [])
    \\ qexists_tac ‘j1’
    \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
    \\ rename1 ‘v_rel v w’
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs [])
  >~ [‘MkTick x’] >-
   (ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ rename1 ‘exp_rel _ x y’
    \\ simp [eval_to_def]
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + k) x) (eval_to k y)’
      suffices_by (
        disch_then (qx_choose_then ‘j’ assume_tac)
        \\ qexists_tac ‘j’
        \\ Cases_on ‘eval_to (j + k) x’ \\ Cases_on ‘eval_to k y’ \\ gs []
        \\ irule v_rel_DoTick \\ gs [])
    \\ first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def]
    \\ rpt strip_tac
    \\ first_x_assum (qspec_then ‘k’ mp_tac)
    \\ simp [eval_to_def])
  >~ [‘Prim op xs’]
  \\ ntac 2 strip_tac
  \\ rw [Once exp_rel_cases]
  \\ simp [eval_to_def]
  \\ gvs [LIST_REL_EL_EQN]
  \\ ‘∀n. n < LENGTH xs ⇒ ∀k. eval_to k (EL n xs) ≠ INL Type_error’
    by (ntac 2 strip_tac
        \\ qx_gen_tac ‘j’
        \\ strip_tac
        \\ qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ _’ mp_tac
        \\ simp [eval_to_def]
        \\ Cases_on ‘op’ \\ gs []
        >- (
         simp [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
         \\ qexists_tac ‘j’
         \\ gs [SF SFY_ss])
        >- (
         IF_CASES_TAC \\ gs []
         \\ gs [DECIDE “n < 1n ⇔ n = 0”]
         \\ gvs [LENGTH_EQ_NUM_compute]
         \\ qexists_tac ‘j + 1’
         \\ simp [])
        >- (
         IF_CASES_TAC \\ gs []
         \\ gs [DECIDE “n < 1n ⇔ n = 0”]
         \\ gvs [LENGTH_EQ_NUM_compute]
         \\ qexists_tac ‘j + 1’
         \\ simp [])
        \\ qexists_tac ‘j + 1’ \\ simp []
        \\ qmatch_goalsub_abbrev_tac ‘result_map f xs’
        \\ ‘result_map f xs = INL Type_error’
          suffices_by rw []
        \\ simp [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
        \\ gs [Abbr ‘f’]
        \\ IF_CASES_TAC \\ gs [])
  \\ ‘∀j. j ≤ k ⇒
          ∀n. n < LENGTH xs ⇒
              ∃m. ($= +++ v_rel) (eval_to (m + j) (EL n xs))
                                 (eval_to j (EL n ys))’
    by (qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ _’ kall_tac
        \\ rpt (pop_assum mp_tac)
        \\ qid_spec_tac ‘ys’
        \\ Induct_on ‘xs’ \\ simp []
        \\ Cases_on ‘ys’ \\ simp []
        \\ qx_gen_tac ‘x’
        \\ rpt strip_tac
        \\ rename1 ‘_ _ (_ _ (EL _ (y::ys)))’
        \\ last_x_assum (qspec_then ‘ys’ mp_tac)
        \\ simp [AND_IMP_INTRO]
        \\ impl_tac
        >- (
         reverse conj_tac
         >- (
           qx_gen_tac ‘m’ \\ strip_tac
           \\ first_x_assum (qspec_then ‘SUC m’ assume_tac)
           \\ gs [])
         \\ reverse conj_tac
         >- (
           qx_gen_tac ‘m’ \\ strip_tac
           \\ first_x_assum (qspec_then ‘SUC m’ assume_tac)
           \\ first_x_assum (qspec_then ‘SUC m’ assume_tac)
           \\ gs [])
         \\ qx_gen_tac ‘k1’ \\ qx_gen_tac ‘x1’ \\ rw []
         \\ gvs [eval_to_wo_def]
         \\ first_x_assum (irule_at Any)
         \\ gs [exp_size_def])
        \\ strip_tac
        \\ Cases_on ‘n’ \\ gs []
        \\ once_rewrite_tac [arithmeticTheory.ADD_COMM]
        \\ first_x_assum (irule_at Any)
        \\ simp [eval_to_wo_def, exp_size_def]
        \\ qpat_x_assum ‘∀n. n < SUC _ ⇒ _’ (qspec_then ‘0’ assume_tac)
        \\ gs []
        \\ qpat_x_assum ‘∀n. n < SUC _ ⇒ _’ (qspec_then ‘0’ assume_tac)
        \\ gs [])
  \\ last_x_assum kall_tac
  \\ Cases_on ‘op’ \\ gs []
  >- (* Cons *)
   (first_x_assum (qspec_then ‘k’ assume_tac) \\ gs []
    \\ qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ _’ kall_tac
    \\ ‘∃j. ($= +++ (LIST_REL v_rel))
            (result_map (λx. eval_to (j + k) x) xs)
            (result_map (λx. eval_to k x) ys)’
      suffices_by (
      disch_then (qx_choose_then ‘j’ assume_tac)
      \\ qexists_tac ‘j’
      \\ Cases_on ‘result_map (λx. eval_to (j + k) x ) xs’
      \\ Cases_on ‘result_map (λx. eval_to k x) ys’ \\ gs [])
    \\ ‘result_map (λx. eval_to k x) ys ≠ INL Type_error’
      by (gvs [result_map_def, CaseEq "bool"]
          \\ strip_tac
          \\ gs [Once MEM_EL, PULL_EXISTS, EL_MAP]
          \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
          \\ Cases_on ‘eval_to (j + k) (EL n xs)’ \\ gs [])
    \\ Cases_on ‘result_map (λx. eval_to k x) ys’ \\ gs []
    >- (
     rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs []
     \\ gs [result_map_def, MEM_EL, PULL_EXISTS, CaseEq "bool", EL_MAP,
            SF CONJ_ss]
     \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
     \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac)) \\ gs []
     \\ Cases_on ‘eval_to (j + k) (EL n xs)’ \\ gs []
     \\ qexists_tac ‘j’
     \\ simp [SF SFY_ss])
    \\ gs [result_map_def, MEM_EL, PULL_EXISTS, CaseEq "bool", EL_MAP,
           SF CONJ_ss]
    \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
    \\ ‘∃m. ∀n. n < LENGTH ys ⇒
                ($= +++ v_rel) (eval_to (k + m) (EL n xs))
                               (eval_to k (EL n ys))’
      suffices_by (
      disch_then (qx_choose_then ‘m’ assume_tac)
      \\ qexists_tac ‘m’
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_then assume_tac) \\ gs []
        \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
      \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ rw [EVERY2_MAP, LIST_REL_EL_EQN]
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
      >- (
        rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs [])
      \\ Cases_on ‘eval_to (k + m) (EL n xs)’ \\ gs [])
    \\ gvs []
    \\ rpt (pop_assum mp_tac)
    \\ qid_spec_tac ‘ys’
    \\ Induct_on ‘xs’ \\ simp []
    \\ Cases_on ‘ys’ \\ simp []
    \\ qx_gen_tac ‘x’
    \\ rename1 ‘_ (EL _ _) (EL _ (y::ys))’ \\ rw []
    \\ first_x_assum (qspec_then ‘ys’ mp_tac)
    \\ simp [AND_IMP_INTRO]
    \\ impl_tac
    >- (
     rw []
     \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
     \\ res_tac \\ fs []
     \\ gs [SF SFY_ss])
    \\ disch_then (qx_choose_then ‘m’ assume_tac)
    \\ qpat_x_assum ‘∀n. _ ⇒ ∃m. _’ (qspec_then ‘0’ mp_tac)
    \\ simp []
    \\ disch_then (qx_choose_then ‘m1’ assume_tac)
    \\ qexists_tac ‘m + m1’
    \\ Cases \\ gs []
    >- (
     ‘eval_to (k + (m + m1)) x = eval_to (k + m1) x’
        by (irule eval_to_mono \\ simp []
            \\ strip_tac \\ gs []
            \\ Cases_on ‘eval_to k y’ \\ gs []
            \\ ‘0 < SUC (LENGTH ys)’ by gs []
            \\ res_tac \\ fs [])
     \\ gs [])
    \\ strip_tac
    \\ rename1 ‘n < LENGTH ys’
    \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
    \\ res_tac \\ fs []
    \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
    >- (
     rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs [])
    \\ ‘eval_to (k + (m + m1)) (EL n xs) = eval_to (k + m) (EL n xs)’
      by (irule eval_to_mono \\ simp []
          \\ strip_tac \\ gs [])
    \\ gs [])
  >- (* IsEq *)
   (first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    >-
     (qexists_tac ‘0’
      \\ simp [])
    \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1 ⇔ n = 0”]
    \\ rename1 ‘exp_rel _ x y’
    \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
    >- (
     rename1 ‘_ = INL err’
     \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
     \\ qexists_tac ‘m’ \\ simp [])
    \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
    \\ rename1 ‘v_rel v w’
    \\ qexists_tac ‘m’ \\ simp []
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ gs [])
  >- (* Proj *)
   (first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    >- (
     qexists_tac ‘0’
     \\ simp [])
    \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1 ⇔ n = 0”]
    \\ rename1 ‘exp_rel _ x y’
    \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
    >- (
     rename1 ‘_ = INL err’
     \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
     \\ qexists_tac ‘m’ \\ simp [])
    \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
    \\ rename1 ‘v_rel v w’
    \\ qexists_tac ‘m’ \\ simp []
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ gs [])
  (* AtomOp *)
  \\ first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
  \\ Cases_on ‘k = 0’ \\ gs []
  >- (
    qexists_tac ‘0’
    \\ simp [result_map_def, MEM_MAP, GSYM NOT_NULL_MEM, NULL_EQ]
    \\ Cases_on ‘xs’ \\ Cases_on ‘ys’ \\ gs []
    \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs [])
  \\ qabbrev_tac ‘f = λj x. case eval_to (j + k - 1) x of
                              INR (Atom l) => INR l
                            | INL err => INL err
                            | _ => INL Type_error’
  \\ qabbrev_tac ‘g = λx. case eval_to (k - 1) x of
                            INR (Atom l) => INR l
                          | INL err => INL err
                          | _ => INL Type_error’
  \\ gs []
  \\ ‘∃j. result_map (f j) xs = result_map g ys’
    suffices_by (
    disch_then (qx_choose_then ‘j’ assume_tac)
    \\ qexists_tac ‘j’
    \\ simp [SF ETA_ss]
    \\ Cases_on ‘result_map g ys’ \\ gs []
    \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs [])
  \\ ‘∀j. result_map (f j) xs ≠ INL Type_error’
    by (rpt strip_tac
        \\ gs [result_map_def, MEM_EL, EL_MAP, SF CONJ_ss,
               CaseEq "bool", Abbr ‘f’]
        \\ qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ INL _’ mp_tac \\ simp []
        \\ simp [eval_to_def]
        \\ qexists_tac ‘j + k’
        \\ simp [result_map_def, MEM_MAP, MEM_EL, PULL_EXISTS]
        \\ IF_CASES_TAC \\ gs [])
  \\ qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ _’ kall_tac
  \\ Cases_on ‘result_map g ys = INL Diverge’ \\ gs []
  >- (
    unabbrev_all_tac \\ gs []
    \\ rgs [result_map_def, CaseEq "bool", MEM_MAP]
    \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
    \\ gvs [MEM_EL, PULL_EXISTS]
    \\ first_x_assum drule
    \\ pop_assum mp_tac
    \\ rpt CASE_TAC \\ gvs []
    \\ rw []
    \\ last_x_assum (drule_then assume_tac)
    \\ last_x_assum (drule_then assume_tac)
    \\ last_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
    \\ qexists_tac ‘j’
    \\ qexists_tac ‘n’
    \\ CASE_TAC \\ gs [])
  \\ rgs [result_map_def, MEM_EL, EL_MAP, SF CONJ_ss, Once (CaseEq "bool"),
          DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
  >- (
    ‘F’ suffices_by rw []
    \\ unabbrev_all_tac
    \\ gs [CaseEq "bool", DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
    \\ first_x_assum (drule_then (qx_choose_then ‘m’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) (EL n ys)’
    \\ Cases_on ‘eval_to (m + k - 1) (EL n xs)’ \\ gs []
    \\ first_x_assum (drule_then (qspec_then ‘m’ assume_tac))
    \\ rename1 ‘v_rel v w’
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [])
  \\ rgs [Once (CaseEq "bool"), DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
  \\ ‘∃j. ∀n. n < LENGTH ys ⇒
              ($= +++ v_rel) (eval_to (j + k - 1) (EL n xs))
                             (eval_to (k - 1) (EL n ys))’
    by (unabbrev_all_tac
        \\ rpt (pop_assum mp_tac)
        \\ qid_spec_tac ‘ys’
        \\ Induct_on ‘xs’ \\ simp []
        \\ qx_gen_tac ‘x’
        \\ Cases \\ simp []
        \\ rename1 ‘eval_to (k - 1) (EL _ (y::ys))’
        \\ rw []
        \\ last_x_assum (qspec_then ‘ys’ mp_tac)
        \\ simp [AND_IMP_INTRO, GSYM CONJ_ASSOC]
        \\ impl_tac
        >- (
         rw []
         \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
         \\ res_tac \\ fs []
         \\ gs [SF SFY_ss])
        \\ disch_then (qx_choose_then ‘j’ assume_tac)
        \\ ‘∃j1. ($= +++ v_rel) (eval_to (j1 + k - 1) x)
                                (eval_to (k - 1) y)’
          by (‘0 < SUC (LENGTH ys)’ by gs []
              \\ res_tac \\ fs []
              \\ qexists_tac ‘m’ \\ simp [])
        \\ qexists_tac ‘j + j1’
        \\ Cases \\ gs []
        >- (
         ‘eval_to (j + (j1 + k) - 1) x = eval_to (j1 + k - 1) x’
            by (irule eval_to_mono \\ gs []
                \\ strip_tac \\ gs []
                \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
                \\ ‘0 < SUC (LENGTH ys)’ by gs []
                \\ res_tac \\ fs []
                \\ gs [])
         \\ gs [])
        \\ qmatch_goalsub_rename_tac ‘n < LENGTH ys’
        \\ strip_tac
        \\ ‘eval_to (j + (j1 + k) - 1) (EL n xs) =
            eval_to (j + k - 1) (EL n xs)’
          by (irule eval_to_mono \\ gs []
              \\ strip_tac \\ gs []
              \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
              \\ res_tac \\ fs []
              \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs [])
        \\ gs [])
  \\ qexists_tac ‘j’
  \\ unabbrev_all_tac
  \\ gs [result_map_def, MEM_MAP, MAP_MAP_o, combinTheory.o_DEF]
  \\ IF_CASES_TAC \\ rgs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
  \\ IF_CASES_TAC \\ rgs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
  >- (
    first_x_assum (drule_then assume_tac)
    \\ gvs [CaseEqs ["sum", "v", "err"]]
    \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs [])
  \\ rw []
  >- (
    rpt (first_x_assum (drule_then assume_tac))
    \\ first_x_assum (qspec_then ‘j + k - 1’ assume_tac)
    \\ gvs [CaseEqs ["sum", "v", "err"]]
    \\ Cases_on ‘eval_to (j + k - 1) (EL n xs)’
    \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs []
    >- (
      strip_tac \\ gs [])
    \\ rename1 ‘v_rel u v’
    \\ first_x_assum (qspec_then ‘j’ assume_tac) \\ gs []
    \\ Cases_on ‘u’ \\ Cases_on ‘v’ \\ gs [])
  \\ irule_at Any LIST_EQ
  \\ rw [EL_MAP]
  \\ rpt (first_x_assum (drule_then assume_tac))
  \\ first_x_assum (qspec_then ‘j’ assume_tac)
  \\ rpt CASE_TAC \\ gs []
QED

Theorem exp_rel_eval_to = REWRITE_RULE [force_goal_def] exp_rel_eval_to;

Theorem exp_rel_eval:
  exp_rel NONE x y ∧ closed x ∧
  eval x ≠ INL Type_error ⇒
    ($= +++ v_rel) (eval x) (eval y)
Proof
  strip_tac
  \\ dxrule_then assume_tac eval_not_error
  \\ simp [eval_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  >- (
    rename1 ‘_ (eval_to k x) (eval_to j y)’
    \\ drule_all_then
      (qspec_then ‘MAX k j’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to
    \\ ‘eval_to (m + MAX k j) x = eval_to k x’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ ‘eval_to (MAX k j) y = eval_to j y’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ gs [])
  >- (
    rename1 ‘_ _ (eval_to j y)’
    \\ drule_all_then
      (qspec_then ‘j’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to \\ gs [])
  \\ rename1 ‘_ _ (eval_to k x)’
  \\ drule_all_then
    (qspec_then ‘k’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to
  \\ Cases_on ‘eval_to (k + m) x’ \\ gvs []
  \\ drule_then (qspec_then ‘k + m’ assume_tac) eval_to_mono \\ gs []
QED

Theorem force_apply_force[local]:
  v_rel v w ∧
  force v ≠ INL Type_error ⇒
    ($= +++ v_rel) (force v) (force w)
Proof
  rw [] \\ irule apply_force_rel \\ simp []
  \\ qexists_tac ‘λx y. exp_rel NONE x y ∧ closed x’
  \\ qexists_tac ‘F’
  \\ simp [exp_rel_Force, exp_rel_Value, exp_rel_eval]
QED

Theorem force_apply_closure[local]:
  v_rel v1 w1 ∧
  v_rel v2 w2 ∧
  apply_closure v1 v2 f ≠ Err ∧
  f (INL Type_error) = Err ∧
  (∀x y.
     ($= +++ v_rel) x y ∧ f x ≠ Err ⇒
       next_rel v_rel (f x) (g y)) ⇒
    next_rel v_rel
             (apply_closure v1 v2 f)
             (apply_closure w1 w2 g)
Proof
  rw [thunk_semanticsTheory.apply_closure_def]
  \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [dest_anyClosure_def]
  >- (
    first_x_assum irule \\ gs []
    \\ irule exp_rel_eval
    \\ gs [closed_subst]
    \\ irule_at Any exp_rel_subst \\ gs []
    \\ strip_tac \\ gs [])
  \\ rename1 ‘LIST_REL _ xs ys’
  \\ ‘OPTREL (λx y. exp_rel NONE x y ∧ freevars x ⊆ set (MAP FST xs))
        (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
    by (irule LIST_REL_OPTREL
        \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY])
  \\ gs [OPTREL_def]
  \\ qpat_x_assum ‘exp_rel NONE x y’ mp_tac
  \\ rw [Once exp_rel_cases] \\ gs []
  \\ first_x_assum irule \\ gs []
  \\ irule exp_rel_eval
  \\ irule_at Any exp_rel_subst
  \\ fs [closed_subst,freevars_def]
  \\ gs [EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
  \\ irule_at Any LIST_EQ
  \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
  \\ conj_tac
  >- (fs [SUBSET_DEF] \\ metis_tac [])
  \\ strip_tac \\ gs []
QED

Theorem force_rel_ok[local]:
  rel_ok F v_rel
Proof
  rw [rel_ok_def]
  >- ((* force preserves rel *)
    simp [force_apply_force])
  >- ((* ∀x. f x ≠ Err from rel_ok prevents this case *)
    simp [force_apply_closure])
  >- ((* Thunks go to Thunks or DoTicks *)
    Cases_on ‘s’ \\ gs []
    \\ gs [Once v_rel_cases])
  >- ((* Equal literals are related *)
    simp [exp_rel_Prim])
  >- ((* Equal 0-arity conses are related *)
    simp [exp_rel_Prim])
QED

Theorem force_sim_ok[local]:
  sim_ok F v_rel (exp_rel NONE)
Proof
  rw [sim_ok_def]
  \\ simp [exp_rel_eval]
  \\ irule exp_rel_subst \\ gs []
QED

Theorem case_force_semantics:
  exp_rel NONE x y ∧
  closed x ∧
  pure_semantics$safe_itree (semantics x Done []) ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ irule sim_ok_semantics
  \\ irule_at Any force_sim_ok
  \\ irule_at Any force_rel_ok \\ gs []
QED

val _ = export_theory ();
