(*
  This stage removes some unnecessary thunk allocations that are introduced by
  the pure_to_thunk stage of the compiler.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLang_substTheory
     thunkLang_primitivesTheory dep_rewrite;
open pure_miscTheory;

val _ = new_theory "thunk_subst_unthunk";

val _ = numLib.prefer_num ();

Inductive exp_rel:
[exp_rel_Var:]
  (∀v.
     exp_rel (Delay (Force (Var v))) (Var v)) ∧
[exp_rel_Delay_Value:]
  (∀v w.
     v_rel v w ⇒
       exp_rel (Delay (Force (Value v))) (Value w)) ∧
[exp_rel_Value:]
  (∀v w.
     v_rel v w ⇒
       exp_rel (Value v) (Value w)) ∧
[exp_rel_Lam:]
  (∀x y.
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
[exp_rel_Let:]
  (∀s x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
       exp_rel (Let s x1 y1) (Let s x2 y2)) ∧
[exp_rel_Letrec:]
  (∀f x g y.
     LIST_REL (λ(f,x) (g,y). f = g ∧ exp_rel x y) f g ∧
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
                   exp_rel x y ∧
                   freevars x ⊆ set (MAP FST f)) f g ⇒
      v_rel (Recclosure f n) (Recclosure g n)) ∧
[v_rel_Constructor:]
  (∀s vs ws.
     LIST_REL (λv w. ∃x y.
                 v = Thunk (INR x) ∧
                 w = Thunk (INR y) ∧
                 exp_rel x y ∧
                 closed x) vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws)) ∧
[v_rel_Thunk:]
  (∀x y.
    exp_rel x y ∧
    closed x ⇒
      v_rel (Thunk (INR x)) (Thunk (INR y))) ∧
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
                   exp_rel x y ∧
                   freevars x ⊆ set (MAP FST f)) f g)) ∧
  (∀s vs z.
     v_rel (Constructor s vs) z =
       (∃ws. z = Constructor s ws ∧
             LIST_REL (λv w. ∃x y.
                    v = Thunk (INR x) ∧
                    w = Thunk (INR y) ∧
                    exp_rel x y ∧
                    closed x) vs ws)) ∧
  (∀x z.
     v_rel (Atom x) z = (z = Atom x)) ∧
  (∀x z.
     v_rel (Thunk x) z =
       (∃y w. z = Thunk (INR y) ∧
              x = INR w ∧
              exp_rel w y ∧
              closed w))
Proof
  rw [] \\ rw [Once exp_rel_cases]
  \\ rw [EQ_SYM_EQ, AC CONJ_COMM CONJ_ASSOC, EQ_IMP_THM]
QED

Theorem v_rel_rev[simp]:
  (∀s y.
     v_rel v (Closure s y) =
       (∃x. v = Closure s x ∧
            exp_rel x y ∧
            freevars x ⊆ {s})) ∧
  (∀g n.
     v_rel v (Recclosure g n) =
       (∃f. v = Recclosure f n ∧
          LIST_REL (λ(fn,x) (gn,y).
                 fn = gn ∧
                 exp_rel x y ∧
                 freevars x ⊆ set (MAP FST f)) f g)) ∧
  (∀v s vs.
     v_rel v (Constructor s vs) =
       (∃ws. v = Constructor s ws ∧
             LIST_REL (λv w. ∃x y.
                    v = Thunk (INR x) ∧
                    w = Thunk (INR y) ∧
                    exp_rel x y ∧
                    closed x) ws vs)) ∧
  (∀v a.
     v_rel v (Atom a) = (v = Atom a)) ∧
  (∀v y.
     v_rel v (Thunk y) =
       (∃x z. v = Thunk (INR x) ∧
              y = INR z ∧
              exp_rel x z ∧
              closed x))
Proof
  rw [] \\ rw [Once exp_rel_cases]
QED

Theorem exp_size_lemma[local]:
  (∀x xs. MEM x xs ⇒ exp_size x ≤ exp4_size xs) ∧
  (∀x y xs. MEM (x,y) xs ⇒ exp_size y ≤ exp1_size xs)
Proof
  conj_tac
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [exp_size_def]
  \\ first_x_assum drule
  \\ simp []
QED

Theorem exp_ind_alt[local]:
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
    (∀v. P (Value v)) ⇒
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

Theorem MAP_FST_FILTER[local]:
  MAP FST (FILTER (λ(a,b). P a) xs) = FILTER P (MAP FST xs)
Proof
  irule LIST_EQ
  \\ rw [EL_MAP, FILTER_MAP, combinTheory.o_DEF, LAMBDA_PROD]
QED

(* TODO pure_misc? *)
Theorem LIST_TO_SET_FILTER_DIFF:
  set (FILTER P l) = set l DIFF {x | ¬P x}
Proof
  rw [LIST_TO_SET_FILTER, DIFF_DEF, INTER_DEF, EXTENSION, CONJ_COMM]
QED

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

(* TODO pure_misc? *)
Theorem LIST_REL_FILTER[local]:
  ∀xs ys.
    LIST_REL R xs ys ⇒
    MAP FST xs = MAP FST ys ⇒
      LIST_REL R (FILTER (λ(x,y). P x) xs)  (FILTER (λ(x,y). P x) ys)
Proof
  ho_match_mp_tac LIST_REL_ind \\ rw [] \\ fs [ELIM_UNCURRY]
QED

Theorem LIST_REL_ALOOKUP[local]:
  ∀xs ys.
    LIST_REL (λ(f,x) (g,y). f = g ∧ R x y) xs ys ⇒
      OPTREL R (ALOOKUP xs k) (ALOOKUP ys k)
Proof
  ho_match_mp_tac LIST_REL_ind
  \\ simp [OPTREL_def]
  \\ Cases \\ Cases \\ rw []
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
    rw [Once exp_rel_cases])
  >- ((* Prim *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Prim
    \\ simp [EVERY2_MAP]
    \\ gvs [LIST_REL_EL_EQN] \\ rw []
    \\ first_x_assum irule \\ fs [EL_MEM])
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
    \\ irule LIST_REL_FILTER \\ fs [])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Let \\ fs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Let \\ fs []
    \\ first_x_assum irule
    \\ fs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. x ≠ s’ \\ fs []
    \\ irule LIST_REL_FILTER \\ fs [])
  >- ((* Letrec *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ ‘MAP FST f = MAP FST g’
      by (fs [ELIM_UNCURRY, LIST_REL_CONJ]
          \\ irule LIST_EQ
          \\ gvs [LIST_REL_EL_EQN] \\ rw [EL_MAP])
    \\ irule exp_rel_Letrec
    \\ gvs [EVERY2_MAP, LAMBDA_PROD]
    \\ first_x_assum (irule_at Any)
    \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. ¬MEM x (MAP FST g)’ \\ fs []
    \\ irule_at Any LIST_REL_FILTER \\ fs []
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ rpt (pairarg_tac \\ gvs [])
    \\ first_x_assum irule
    \\ simp [MAP_FST_FILTER, LIST_REL_FILTER]
    \\ gs [SF SFY_ss])
  >- ((* Delay *)
    rw [Once exp_rel_cases]
    >- ((* Var *)
      ‘OPTREL v_rel (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
        by (irule LIST_REL_ALOOKUP
            \\ simp [EVERY2_REVERSE]
            \\ gvs [EVERY2_MAP, ELIM_UNCURRY, LIST_REL_CONJ]
            \\ pop_assum mp_tac
            \\ rpt (pop_assum kall_tac)
            \\ qid_spec_tac ‘ws’ \\ Induct_on ‘vs’ \\ Cases_on ‘ws’ \\ simp [])
      \\ fs [subst_def, OPTREL_def, exp_rel_Var, exp_rel_Delay_Value])
    >- ((* Value *)
      simp [subst_def, exp_rel_Delay_Value])
    \\ simp [subst_def, exp_rel_Delay])
  >- ((* Box *)
    rw [Once exp_rel_cases])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Force \\ fs [])
  >- ((* Value *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Value \\ fs [])
QED

Theorem dest_Closure_v_rel:
  v_rel v w ⇒
    (∀err. dest_Closure v = INL err ⇒ dest_Closure w = INL err) ∧
    (∀s x.
       dest_Closure v = INR (s, x) ⇒
         ∃env y.
           dest_Closure w = INR (s, y) ∧
           exp_rel x y ∧
           freevars x ⊆ {s})
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’
  \\ rw [Once exp_rel_cases]
  \\ rw [Once exp_rel_cases]
QED

Theorem dest_Thunk_v_rel:
  v_rel v w ⇒
    (∀err. dest_Thunk v = INL err ⇒ dest_Thunk w = INL err) ∧
    (∀nf x. dest_Thunk v = INR x ⇒
       ∃y.
         dest_Thunk w = INR y ∧
           ((∃v1 v2.
               x = INL v1 ∧
               y = INL v2 ∧
               v_rel v1 v2) ∨
            (∃env x1 x2.
               x = INR x1 ∧
               y = INR x2 ∧
               exp_rel x1 x2)))
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’ \\ rw []
QED

Theorem dest_Recclosure_v_rel:
  v_rel v w ⇒
    (∀err. dest_Recclosure v = INL err ⇒ dest_Recclosure w = INL err) ∧
    (∀f n.
       dest_Recclosure v = INR (f, n) ⇒
         ∃g env.
           dest_Recclosure w = INR (g, n) ∧
           LIST_REL (λ(fn,b) (gn,c).
                       fn = gn ∧
                       exp_rel b c ∧
                       freevars b ⊆ set (MAP FST f)) f g ∧
           (∀x. OPTREL exp_rel (ALOOKUP (REVERSE f) x) (ALOOKUP (REVERSE g) x)))
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’ \\ rw []
  \\ irule LIST_REL_ALOOKUP
  \\ rw [EVERY2_REVERSE]
  \\ irule LIST_REL_mono
  \\ first_assum (irule_at Any)
  \\ simp [ELIM_UNCURRY]
QED

Theorem SUM_REL_def[simp] = quotient_sumTheory.SUM_REL_def;

Theorem exp_rel_eval_to:
  ∀k x y.
    exp_rel x y ∧
    closed x ⇒
      ($= +++ v_rel) (eval_to k x) (eval_to k y)
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac
  >- ((* Value *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >- ((* Var *)
    fs [closed_def, freevars_def])
  >- ((* App *)
    rename1 ‘App x1 y1’
    \\ rw [Once exp_rel_cases]
    \\ rw [eval_to_def]
    \\ ‘closed x1 ∧ closed y1’ by fs [closed_def, freevars_def]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ rename1 ‘exp_rel x1 x2’
    \\ rename1 ‘exp_rel y1 y2’
    \\ Cases_on ‘eval_to k x1’ \\ Cases_on ‘eval_to k x2’ \\ fs []
    \\ Cases_on ‘eval_to k y1’ \\ Cases_on ‘eval_to k y2’ \\ fs []
    \\ drule_then strip_assume_tac dest_Closure_v_rel
    \\ drule_then strip_assume_tac dest_Recclosure_v_rel
    \\ rename1 ‘dest_anyClosure y’
    \\ Cases_on ‘dest_anyClosure y’ \\ fs []
    >- (
      rename1 ‘dest_anyClosure z’
      \\ Cases_on ‘y’ \\ Cases_on ‘z’ \\ gvs [dest_anyClosure_def]
      \\ rename1 ‘ALOOKUP (REVERSE _) ss’
      \\ first_x_assum (qspec_then ‘ss’ assume_tac)
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 y0’ mp_tac
      \\ Cases_on ‘x0’ \\ rw [Once exp_rel_cases] \\ fs [])
    \\ pairarg_tac \\ gvs []
    \\ rename1 ‘dest_anyClosure z’
    \\ reverse (Cases_on ‘y’) \\ Cases_on ‘z’ \\ gvs [dest_anyClosure_def]
    >- (
      rename1 ‘Recclosure l ss’
      \\ first_x_assum (qspec_then ‘ss’ assume_tac)
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 y0’ mp_tac
      \\ Cases_on ‘x0’ \\ rw [Once exp_rel_cases] \\ gvs []
      \\ first_x_assum irule
      \\ irule_at Any exp_rel_subst
      \\ fs [EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
             GSYM FST_THM]
      \\ irule_at Any LIST_REL_mono
      \\ first_assum (irule_at Any)
      \\ simp [FORALL_PROD]
      \\ irule_at Any LIST_EQ
      \\ gvs [EL_MAP, LIST_REL_EL_EQN, ELIM_UNCURRY]
      \\ simp [closed_subst, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
      \\ drule_then assume_tac ALOOKUP_SOME_EL
      \\ gvs [EL_REVERSE]
      \\ qmatch_asmsub_abbrev_tac ‘EL m xs’
      \\ rename1 ‘n < LENGTH ys’
      \\ ‘m < LENGTH ys’ by fs [Abbr ‘m’]
      \\ first_x_assum (drule_then assume_tac)
      \\ gvs [freevars_def, DIFF_SUBSET, UNION_COMM])
    \\ IF_CASES_TAC \\ gvs []
    \\ rename1 ‘eval_to k y1 = INR v1’
    \\ rename1 ‘eval_to k y2 = INR v2’
    \\ rename1 ‘eval_to k x1 = INR (Closure s b1)’
    \\ rename1 ‘eval_to k x2 = INR (Closure s b2)’
    \\ ‘[(s,v1)] = [] ++ [(s,v1)]’ by fs [] \\ pop_assum SUBST1_TAC
    \\ ‘[(s,v2)] = [] ++ [(s,v2)]’ by fs [] \\ pop_assum SUBST1_TAC
    \\ first_x_assum irule \\ fs []
    \\ irule_at Any exp_rel_subst \\ fs []
    \\ simp [closed_subst])
  >- ((* Lam *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ fs [closed_def, freevars_def, SUBSET_DIFF_EMPTY])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases]
    \\ rename1 ‘Let NONE x y’
    \\ ‘closed x ∧ closed y’ by fs [closed_def, freevars_def]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum (drule_then assume_tac)
    \\ first_x_assum (drule_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ Cases_on ‘eval_to (k - 1) x2’ \\ fs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_cases]
    \\ rename1 ‘Let (SOME n) x y’
    \\ ‘closed x ∧ freevars y ⊆ {n}’
      by fs [closed_def, freevars_def, SUBSET_DIFF_EMPTY]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum (drule_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ Cases_on ‘eval_to (k - 1) x2’ \\ fs []
    \\ first_x_assum irule
    \\ fs [closed_subst]
    \\ irule exp_rel_subst \\ fs [])
  >- ((* If *)
    rw [Once exp_rel_cases]
    \\ rename1 ‘If x y z’
    \\ ‘closed x ∧ closed y ∧ closed z’ by fs [closed_def, freevars_def]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs [])
  >- ((* Letrec *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum irule \\ fs []
    \\ fs [subst_funs_def, closed_def, freevars_subst, freevars_def]
    \\ fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, SUBSET_DIFF_EMPTY,
           GSYM FST_THM]
    \\ irule exp_rel_subst
    \\ fs [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP, LAMBDA_PROD,
           GSYM FST_THM]
    \\ irule_at Any LIST_EQ
    \\ gvs [EL_MAP]
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ gvs [ELIM_UNCURRY, EL_MAP, LIST_REL_EL_EQN] \\ rw []
    \\ gvs [BIGUNION_SUBSET, MEM_EL, PULL_EXISTS, EL_MAP])
  >- ((* Delay *)
    rw [Once exp_rel_cases]
    >- ((* Var *)
      fs [closed_def, freevars_def])
    >- ((* Value_Delay *)
      rw [eval_to_def, closed_def, freevars_def]
        (* Thunk (INR (Force (Value v))) related to w *)
      \\ cheat (* The right side value needs to be a thunk
                  related to the value on the left arrrgg what *)
    )
    \\ fs [closed_def, freevars_def, eval_to_def])
  >- ((* Box *)
    rw [Once exp_rel_cases])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ ‘closed x’ by fs [closed_def, freevars_def]
    \\ first_x_assum (drule_then assume_tac) \\ gs []
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ fs []
    \\ drule_then strip_assume_tac dest_Recclosure_v_rel
    \\ drule_then strip_assume_tac dest_Thunk_v_rel
    \\ rename1 ‘dest_anyThunk z’
    \\ Cases_on ‘dest_anyThunk z’ \\ fs []
    >- (
      rename1 ‘dest_anyThunk zz’
      \\ Cases_on ‘z’ \\ Cases_on ‘zz’ \\ fs [dest_anyThunk_def]
      \\ rename1 ‘ALOOKUP (REVERSE _) ss’
      \\ first_x_assum (qspec_then ‘ss’ assume_tac)
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ Cases_on ‘x0’ \\ rw [Once exp_rel_cases] \\ gvs [])
    \\ pairarg_tac \\ gvs []
    \\ rename1 ‘dest_anyThunk zz’
    \\ Cases_on ‘z’ \\ Cases_on ‘zz’ \\ gvs [dest_anyThunk_def]
    >- (
      rename1 ‘ALOOKUP (REVERSE _) ss’
      \\ first_x_assum (qspec_then ‘ss’ assume_tac)
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ Cases_on ‘x0’ \\ rw [Once exp_rel_cases] \\ gvs []
      >- ((* Var *)
        cheat (* Lost cause because some crucial invariant is missing *))
      >- ((* Value *)
        cheat (* Same as above *))
      \\ IF_CASES_TAC \\ fs []
      \\ first_x_assum irule
      \\ simp [subst_funs_def, closed_subst]
      \\ irule_at Any exp_rel_subst
      \\ simp [EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
               GSYM FST_THM]
      \\ irule_at Any LIST_REL_mono
      \\ first_assum (irule_at Any)
      \\ simp [ELIM_UNCURRY]
      \\ rename1 ‘LIST_REL _ xs ys’
      \\ irule_at Any LIST_EQ
      \\ gvs [LIST_REL_EL_EQN, EL_MAP]
      \\ imp_res_tac ALOOKUP_SOME_EL \\ gs [EL_REVERSE]
      \\ qmatch_asmsub_abbrev_tac ‘EL m xs’
      \\ ‘m < LENGTH ys’ by fs [Abbr ‘m’]
      \\ first_assum (drule_then assume_tac)
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs []
      \\ gvs [freevars_def]
      \\ rw []
      \\ first_x_assum (drule_then assume_tac)
      \\ pairarg_tac \\ gvs []
      \\ pairarg_tac \\ gvs [])
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum irule
    \\ simp [subst_funs_def])
  >- ((* Prim *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ gvs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
    \\ ‘∀n. n < LENGTH xs ⇒ closed (EL n xs)’
      by gvs [closed_def, freevars_def, LIST_TO_SET_EQ_SING, EVERY_MAP,
              EVERY_EL]
    \\ Cases_on ‘op’ \\ fs []
    >- ((* Cons *)
      Cases_on ‘map (λx. eval_to k x) xs’ \\ fs []
      >- (
        gvs [map_INL]
        \\ Cases_on ‘map (λy. eval_to k y) ys’ \\ fs []
        >- (
          gvs [map_INL]
          \\ rename1 ‘m < LENGTH ys’
          \\ Cases_on ‘m < n’
          >- (
            first_x_assum (drule_then assume_tac)
            \\ last_x_assum (drule_all_then assume_tac)
            \\ last_x_assum (drule_all_then assume_tac)
            \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs [])
          \\ Cases_on ‘n < m’
          >- (
            qpat_x_assum ‘n < LENGTH ys’ assume_tac
            \\ first_x_assum (drule_then assume_tac)
            \\ last_x_assum (drule_all_then assume_tac)
            \\ last_x_assum (drule_all_then assume_tac)
            \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
          \\ ‘n = m’ by fs []
          \\ pop_assum SUBST_ALL_TAC \\ gvs []
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_all_then assume_tac)
          \\ gs [])
        \\ drule_then assume_tac map_LENGTH
        \\ dxrule_then assume_tac map_INR \\ fs []
        \\ last_x_assum (drule_all_then assume_tac)
        \\ last_x_assum (drule_all_then assume_tac)
        \\ gs [])
      \\ drule_then assume_tac map_LENGTH
      \\ dxrule_then assume_tac map_INR \\ fs []
      \\ Cases_on ‘map (λy. eval_to k y) ys’ \\ fs []
      >- (
        gvs [map_INL]
        \\ last_x_assum (drule_all_then assume_tac)
        \\ last_x_assum (drule_all_then assume_tac)
        \\ gs [])
      \\ drule_then assume_tac map_LENGTH
      \\ dxrule_then assume_tac map_INR \\ fs []
      \\ rw [LIST_REL_EL_EQN]
      \\ first_x_assum (irule_at Any)
      \\ cheat (* Everything needs to be a thunk here *))
    >- ((* IsEq *)
      IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
      \\ Cases_on ‘eval_to (k - 1) y’ \\ fs []
      \\ rename1 ‘dest_Constructor z’
      \\ Cases_on ‘dest_Constructor z’ \\ fs []
      >- (
        Cases_on ‘z’ \\ fs []
        \\ rename1 ‘Thunk zz’ \\ Cases_on ‘zz’ \\ fs [])
      \\ pairarg_tac \\ gvs []
      \\ Cases_on ‘z’ \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ fs [])
    >- ((* Proj *)
      IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
      \\ Cases_on ‘eval_to (k - 1) y’ \\ fs []
      \\ rename1 ‘dest_Constructor z’
      \\ Cases_on ‘dest_Constructor z’ \\ fs []
      >- (
        Cases_on ‘z’ \\ fs []
        \\ rename1 ‘Thunk zz’ \\ Cases_on ‘zz’ \\ fs [])
      \\ pairarg_tac \\ gvs []
      \\ Cases_on ‘z’ \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ fs []
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ gvs [])
    >- ((* AtomOp *)
      Cases_on ‘k = 0’ \\ fs []
      >- (
        Cases_on ‘xs = []’ \\ fs [map_def]
        >- (
          CASE_TAC \\ fs []
          \\ CASE_TAC \\ fs [])
        \\ ‘ys ≠ []’ by (strip_tac \\ fs [])
        \\ qmatch_goalsub_abbrev_tac ‘map f’
        \\ ‘f = K (INL Diverge)’ by fs [Abbr ‘f’, FUN_EQ_THM]
        \\ simp [map_K_INL])
      \\ qmatch_goalsub_abbrev_tac ‘map f xs’
      \\ Cases_on ‘map f xs’ \\ fs []
      >- (
        gvs [map_INL]
        \\ Cases_on ‘map f ys’ \\ fs []
        >- (
          gvs [map_INL, Abbr ‘f’]
          \\ rename1 ‘m < LENGTH ys’
          \\ Cases_on ‘m < n’
          >- (
            first_x_assum (drule_all_then assume_tac)
            \\ first_x_assum (drule_all_then assume_tac)
            \\ first_x_assum (drule_all_then assume_tac)
            \\ first_x_assum (drule_then assume_tac)
            \\ Cases_on ‘eval_to (k - 1) (EL m xs)’ \\ gs []
            \\ Cases_on ‘eval_to (k - 1) (EL m ys)’ \\ gs []
            \\ gs [CaseEq "v"])
          \\ Cases_on ‘n < m’
          >- (
            qpat_x_assum ‘n < LENGTH ys’ assume_tac
            \\ first_x_assum (drule_all_then assume_tac)
            \\ first_x_assum (drule_all_then assume_tac)
            \\ first_x_assum (drule_all_then assume_tac)
            \\ first_x_assum (drule_then assume_tac)
            \\ Cases_on ‘eval_to (k - 1) (EL n xs)’ \\ gs []
            \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs []
            \\ gs [CaseEq "v"])
          \\ ‘m = n’ by fs []
          \\ pop_assum SUBST_ALL_TAC \\ gvs []
          \\ first_x_assum (drule_all_then assume_tac)
          \\ first_x_assum (drule_all_then assume_tac)
          \\ first_x_assum (drule_all_then assume_tac)
          \\ Cases_on ‘eval_to (k - 1) (EL n xs)’ \\ gs []
          \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs []
          \\ gs [CaseEq "v"])
        \\ drule_then assume_tac map_LENGTH
        \\ dxrule_then assume_tac map_INR
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ Cases_on ‘eval_to (k - 1) (EL n xs)’ \\ gs []
        \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs []
        \\ gs [Abbr ‘f’, CaseEq "v"])
      \\ drule_then assume_tac map_LENGTH
      \\ dxrule_then assume_tac map_INR
      \\ Cases_on ‘map f ys’ \\ fs []
      >- (
        gvs [map_INL]
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ Cases_on ‘eval_to (k - 1) (EL n xs)’ \\ gs []
        \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs []
        \\ gs [Abbr ‘f’, CaseEq "v"])
      \\ drule_then assume_tac map_LENGTH
      \\ dxrule_then assume_tac map_INR
      \\ rename1 ‘LENGTH zs = LENGTH ys’
      \\ qsuff_tac ‘y = zs’
      >- (
        rw []
        \\ CASE_TAC \\ fs []
        \\ CASE_TAC \\ fs [])
      \\ irule LIST_EQ \\ rw []
      \\ gs [Abbr ‘f’, CaseEqs ["sum", "v"]]
      \\ first_x_assum (drule_all_then assume_tac)
      \\ first_x_assum (drule_all_then assume_tac)
      \\ first_x_assum (drule_all_then assume_tac)
      \\ first_x_assum (drule_all_then assume_tac)
      \\ first_x_assum (drule_all_then assume_tac)
      \\ gs []))
QED

val _ = export_theory ();

