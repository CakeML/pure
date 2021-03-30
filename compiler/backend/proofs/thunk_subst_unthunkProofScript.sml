(*
  This stage removes some unnecessary thunk allocations that are introduced by
  the pure_to_thunk stage of the compiler.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLang_substTheory
     thunkLang_primitivesTheory dep_rewrite;
open pure_miscTheory;

val _ = new_theory "thunk_subst_unthunkProof";

val _ = numLib.prefer_num ();

Theorem exp_size_lemma[local]:
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

(* --------------------------
   INVARIANT:
   --------------------------

   All variables should be substituted with something thunked.

   --------------------------
   EXPRESSING THE INVARIANT:
   --------------------------

   The invariant is satisfied by code that looks exactly as the code produced
   by the pure_to_thunk pass.

 *)

Inductive exp_inv:
[exp_inv_Var:]
  (∀v.
     exp_inv (Var v)) ∧
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
  (∀x y.
     exp_inv x ∧
     exp_inv y ⇒
       exp_inv (Let NONE x y)) ∧
[exp_inv_If:]
  (∀x y z.
     exp_inv x ∧
     exp_inv y ∧
     exp_inv z ⇒
       exp_inv (If x y z)) ∧
[exp_inv_Prim:]
  (∀op xs. (* TODO *)
     EVERY exp_inv xs ⇒
       exp_inv (Prim op xs)) ∧
[exp_inv_Delay:]
  (∀x.
     exp_inv x ⇒
       exp_inv (Delay x)) ∧
[exp_inv_Force:]
  (∀x.
    exp_inv x ⇒
      exp_inv (Force x))
End

Theorem exp_inv_def:
  (∀v.
     exp_inv (Var v) = T) ∧
  (∀v.
     exp_inv (Value v) = F) ∧
  (∀f x.
     exp_inv (App f x) =
       (∃y. x = Delay y ∧
            exp_inv f ∧
            exp_inv y)) ∧
  (∀s x.
     exp_inv (Lam s x) =
       exp_inv x) ∧
  (∀s x y.
     exp_inv (Let s x y) =
       (s = NONE ∧
        exp_inv x ∧
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
  (∀op xs.
     exp_inv (Prim op xs) =
       (EVERY exp_inv xs)) ∧ (* TODO *)
  (∀x.
     exp_inv (Force x) =
       exp_inv x) ∧
  (∀x.
     exp_inv (Delay x) =
       exp_inv x)
Proof
  rw [] \\ rw [Once exp_inv_cases]
  \\ rw [EQ_IMP_THM]
QED

Definition v_inv_def[simp]:
  v_inv (Constructor s vs) = EVERY v_inv vs ∧
  v_inv (Closure s x) = exp_inv x ∧
  v_inv (Recclosure f n) = EVERY exp_inv (MAP SND f) ∧
  v_inv (Thunk (INL v)) = F ∧
  v_inv (Thunk (INR x)) = exp_inv x ∧
  v_inv (Atom x) = T
Termination
  WF_REL_TAC ‘measure v_size’ \\ rw []
  \\ imp_res_tac exp_size_lemma \\ fs []
End

(* --------------------------
   COMPILATION:
   --------------------------

   We can replace all occurrences of (Delay (Force (Var v))) floating around
   in the middle of expressions with (Var v), but we can't touch those that sit
   at the top of bindings such as Letrecs, because Letrecs turn into
   Recclosures, and Recclosures that look like this are used as thunks. If we
   remove the Delay's sitting directly in a Letrec declaration then the
   resulting code will get stuck when it is forced somewhere. Otherwise, we
   expect that every variable will be replaced by a thunk.

 *)

Inductive exp_rel:
[exp_rel_Var:]
  (∀v.
     exp_rel (Delay (Force (Var v))) (Var v)) ∧
[exp_rel_Value:]
  (∀v w.
     thunk_rel v w ⇒
       exp_rel (Delay (Force (Value v))) (Value w)) ∧
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
  (∀x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
       exp_rel (Let NONE x1 y1) (Let NONE x2 y2)) ∧
[exp_rel_Letrec:]
  (∀f x g y.
     LIST_REL (λ(f,x) (g,y).
                 f = g ∧
                 (∀v. x = Delay (Force (Var v)) ⇒ x = y) ∧
                 (∀v. x ≠ Delay (Force (Var v)) ⇒ exp_rel x y)) f g ∧
     exp_rel x y ⇒
       exp_rel (Letrec f x) (Letrec g y)) ∧
[exp_rel_Delay:]
  (∀x y.
     exp_rel x y ∧
     (∀v. x ≠ Force (Var v)) ⇒
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
                 (∀v. x = Delay (Force (Var v)) ⇒ x = y) ∧
                 (∀v. x ≠ Delay (Force (Var v)) ⇒ exp_rel x y) ∧
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
     v_rel (Atom x) (Atom x)) ∧
[thunk_rel_Thunk:]
  (∀x y.
     exp_rel x y ∧
     closed x ⇒
       thunk_rel (Thunk (INR x)) (Thunk (INR y))) ∧
[thunk_rel_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y).
                 fn = gn ∧
                 (∀v. x = Delay (Force (Var v)) ⇒ x = y) ∧
                 (∀v. x ≠ Delay (Force (Var v)) ⇒ exp_rel x y) ∧
                 freevars x ⊆ set (MAP FST f)) f g ⇒
      thunk_rel (Recclosure f n) (Recclosure g n))
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
                        (∀v. x = Delay (Force (Var v)) ⇒ x = y) ∧
                        (∀v. x ≠ Delay (Force (Var v)) ⇒ exp_rel x y) ∧
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
                        (∀v. x = Delay (Force (Var v)) ⇒ x = y) ∧
                        (∀v. x ≠ Delay (Force (Var v)) ⇒ exp_rel x y) ∧
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

Theorem thunk_rel_def:
  thunk_rel v w ⇔
    v_rel v w ∧
    ((∃x y.
        v = Thunk (INR x) ∧
        w = Thunk (INR y)) ∨
     (∃f g n.
        v = Recclosure f n ∧
        w = Recclosure g n))
Proof
  rw [Once exp_rel_cases]
  \\ rw [EQ_IMP_THM] \\ fs []
QED

(* TODO some thunkLang props script? *)
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

Theorem subst_recursive[local]:
  (∀xs x y. subst xs x = Delay y ⇔ ∃z. x = Delay z ∧ subst xs z = y) ∧
  (∀xs x y. subst xs x = Force y ⇔ ∃z. x = Force z ∧ subst xs z = y) ∧
  (∀xs x v. subst xs x = Var v ⇔ x = Var v ∧ ¬MEM v (MAP FST xs))
Proof
  rpt conj_tac
  \\ Cases_on ‘x’ \\ rw [subst_def, CaseEq "option", ALOOKUP_NONE]
  \\ rw [MAP_REVERSE, MEM_REVERSE, EQ_IMP_THM] \\ fs []
  \\ rename1 ‘Let s _ _’ \\ Cases_on ‘s’ \\ simp [subst_def]
QED

Theorem exp_rel_subst:
  ∀vs x ws y.
    LIST_REL thunk_rel (MAP SND vs) (MAP SND ws) ∧
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
    rw [Once exp_rel_cases])
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
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename1 ‘MEM (p,v1) f’
    \\ ‘∀v. v1 ≠ Delay (Force (Var v))’
      by (rpt strip_tac \\ rw []
          \\ first_x_assum (qspec_then ‘HD v::v’ mp_tac)
          \\ rw [Once exp_rel_cases])
    \\ gs [subst_recursive]
    \\ first_x_assum irule
    \\ simp [MAP_FST_FILTER]
    \\ first_assum (irule_at Any)
    \\ irule_at Any LIST_REL_FILTER
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ first_assum (irule_at Any)
    \\ gvs [ELIM_UNCURRY])
  >- ((* Delay *)
    rw [Once exp_rel_cases] \\ simp [subst_def, exp_rel_Value, exp_rel_Delay,
                                     subst_recursive]
    \\ ‘OPTREL thunk_rel (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
      by (irule LIST_REL_ALOOKUP
          \\ simp [EVERY2_REVERSE]
          \\ gvs [EVERY2_MAP, ELIM_UNCURRY, LIST_REL_CONJ]
          \\ pop_assum mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘ws’ \\ Induct_on ‘vs’ \\ Cases_on ‘ws’ \\ simp [])
    \\ fs [subst_def, OPTREL_def, exp_rel_Var, exp_rel_Value])
  >- ((* Box *)
    rw [Once exp_rel_cases])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Force \\ fs [])
  >- ((* Value *)
    rw [Once exp_rel_cases])
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
       dest_Recclosure v = INR (f,n) ⇒
         ∃g env.
           dest_Recclosure w = INR (g,n) ∧
           LIST_REL (λ(fn,x) (gn,y).
                       fn = gn ∧
                       (∀v. x = Delay (Force (Var v)) ⇒ x = y) ∧
                       (∀v. x ≠ Delay (Force (Var v)) ⇒ exp_rel x y) ∧
                       freevars x ⊆ set (MAP FST f)) f g ∧
           (∀x. OPTREL (λx y.
                          (∀v. x = Delay (Force (Var v)) ⇒ y = x) ∧
                          (∀v. x ≠ Delay (Force (Var v)) ⇒ exp_rel x y))
                       (ALOOKUP (REVERSE f) x) (ALOOKUP (REVERSE g) x)))
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’ \\ rw []
  \\ irule LIST_REL_ALOOKUP
  \\ rw [EVERY2_REVERSE]
  \\ irule LIST_REL_mono
  \\ first_assum (irule_at Any)
  \\ rw [ELIM_UNCURRY]
QED

Theorem SUM_REL_def[simp] = quotient_sumTheory.SUM_REL_def;

(* TODO thunkLang props? *)
Theorem closed_simps[local,simp]:
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
  (∀v. closed (Var v) ⇔ F)
Proof
  rw [closed_def, freevars_def]
  \\ simp [SUBSET_DIFF_EMPTY, AC CONJ_COMM CONJ_ASSOC]
  \\ rw [DISJ_EQ_IMP, EQ_IMP_THM]
  \\ fs [LIST_TO_SET_EQ_SING, EVERY_MAP, GSYM closed_def, SF ETA_ss]
  \\ Cases_on ‘xs’ \\ fs []
QED

Theorem exp_rel_eval_to:
  ∀k x y.
    exp_rel x y ∧
    exp_inv x ∧
    closed x ⇒
      ($= +++ (λv w. v_rel v w ∧ v_inv v)) (eval_to k x) (eval_to k y)
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac
  >- ((* Value *)
    rw [Once exp_rel_cases])
  >- ((* App *)
    rename1 ‘App x1 y1’
    \\ rw [Once exp_rel_cases]
    \\ rw [eval_to_def] \\ gvs [exp_inv_def]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ rename1 ‘exp_rel x1 x2’
    \\ rename1 ‘exp_rel (Delay y) y2’
    \\ Cases_on ‘eval_to k x1’ \\ Cases_on ‘eval_to k x2’ \\ fs []
    \\ fs [eval_to_def]
    \\ Cases_on ‘eval_to k y2’ \\ fs []
    \\ rename1 ‘eval_to k x1 = INR v1’
    \\ rename1 ‘eval_to k x2 = INR v2’
    \\ drule_then strip_assume_tac dest_Closure_v_rel
    \\ drule_then strip_assume_tac dest_Recclosure_v_rel
    \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gvs [dest_anyClosure_def]
    >- ((* Closure *)
      rename1 ‘eval_to k x1 = INR (Closure s b1)’
      \\ rename1 ‘eval_to k x2 = INR (Closure s b2)’
      \\ rename1 ‘eval_to k y2 = INR (Thunk (INR x))’
      \\ IF_CASES_TAC \\ fs []
      \\ ‘[(s,Thunk (INR x))] = [] ++ [(s,Thunk (INR x))]’ by fs []
      \\ pop_assum SUBST1_TAC
      \\ ‘[(s,Thunk (INR y))] = [] ++ [(s,Thunk (INR y))]’ by fs []
      \\ pop_assum SUBST1_TAC
      \\ first_x_assum irule \\ fs []
      \\ simp [closed_subst]
      \\ irule_at Any exp_rel_subst
      \\ simp [thunk_rel_def]
      \\ cheat (* subst preserves exp_inv *))
        (* Recclosure *)
    \\ rename1 ‘ALOOKUP _ ss’
    \\ first_x_assum (qspec_then ‘ss’ assume_tac)
    \\ fs [OPTREL_def]
    \\ Cases_on ‘∃v. x = Delay (Force (Var v))’ \\ gs []
    \\ qpat_x_assum ‘exp_rel _ _’ mp_tac
    \\ rw [Once exp_rel_cases] \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum irule
    \\ irule_at Any exp_rel_subst
    \\ fs [EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
           GSYM FST_THM, thunk_rel_def]
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ simp [FORALL_PROD]
    \\ irule_at Any LIST_EQ
    \\ rename1 ‘LIST_REL _ xs ys’
    \\ gvs [EL_MAP, LIST_REL_EL_EQN, ELIM_UNCURRY]
    \\ simp [closed_subst, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
    \\ dxrule_then strip_assume_tac ALOOKUP_SOME_EL
    \\ dxrule_then strip_assume_tac ALOOKUP_SOME_EL
    \\ gvs [EL_REVERSE]
    \\ qmatch_asmsub_abbrev_tac ‘EL m xs’
    \\ ‘m < LENGTH ys’ by fs [Abbr ‘m’]
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ gvs [freevars_def, DIFF_SUBSET, UNION_COMM]
    \\ cheat (* subst preserves exp_inv *))
  >- ((* Lam *)
    rw [Once exp_rel_cases, Once exp_inv_cases]
    \\ fs [exp_inv_def, eval_to_def])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases]
    \\ rw [eval_to_def] \\ gvs [exp_inv_def]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ rename1 ‘exp_rel x1 x2’
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ fs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_cases])
  >- ((* If *)
    rw [Once exp_rel_cases, Once exp_inv_cases]
    \\ rename1 ‘If x y z’
    \\ rw [eval_to_def] \\ gvs [exp_inv_def]
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
    \\ rw [eval_to_def] \\ gvs [exp_inv_def]
    \\ first_x_assum irule \\ fs []
    \\ fs [subst_funs_def, closed_def, freevars_subst, freevars_def]
    \\ fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, SUBSET_DIFF_EMPTY,
           GSYM FST_THM]
    \\ irule_at Any exp_rel_subst
    \\ gvs [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP, LAMBDA_PROD,
            GSYM FST_THM]
    \\ irule_at Any LIST_EQ
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ gvs [EL_MAP, LIST_REL_EL_EQN, ELIM_UNCURRY, thunk_rel_def, freevars_def,
            MAP_MAP_o, combinTheory.o_DEF]
    \\ simp [SF ETA_ss]
    \\ gvs [BIGUNION_SUBSET, MEM_EL, PULL_EXISTS, EL_MAP]
    \\ cheat (* subst preserves exp_inv *))
  >- ((* Delay *)
    rw [Once exp_rel_cases] \\ fs [exp_inv_def]
    \\ rw [eval_to_def])
  >- ((* Box *)
    rw [Once exp_rel_cases])
  >- ((* Force *)
    rw [Once exp_rel_cases, Once exp_inv_cases]
    \\ rw [eval_to_def] \\ gvs [exp_inv_def]
    \\ rename1 ‘exp_rel x y’
    \\ first_x_assum (drule_then assume_tac) \\ gs []
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ fs []
    \\ rename1 ‘eval_to k x = INR v1’
    \\ rename1 ‘eval_to k y = INR v2’
    \\ drule_then strip_assume_tac dest_Recclosure_v_rel
    \\ drule_then strip_assume_tac dest_Thunk_v_rel
    \\ reverse (Cases_on ‘v1’) \\ Cases_on ‘v2’ \\ gvs [dest_anyThunk_def]
    >- ((* Thunk *)
      IF_CASES_TAC \\ fs []
      \\ first_x_assum irule
      \\ simp [subst_funs_def])
        (* Recclosure *)
    \\ rename1 ‘ALOOKUP _ ss’
    \\ first_assum (qspec_then ‘ss’ mp_tac)
    \\ rewrite_tac [OPTREL_def]
    \\ rw [] \\ fs []
    \\ rename1 ‘x0 ≠ _ ⇒ exp_rel x0 y0’
    \\ ‘∀v. x0 ≠ Delay (Force (Var v))’
      by (rpt strip_tac \\ gvs []
          \\ first_x_assum (qspec_then ‘HD v::v’ mp_tac)
          \\ rw [Once exp_rel_cases])
    \\ gs []
    \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
    \\ rw [Once exp_rel_cases] \\ fs []
    >- ((* Values not allowed *)
      fs [EVERY_MAP, EVERY_EL]
      \\ dxrule_then strip_assume_tac ALOOKUP_SOME_EL
      \\ dxrule_then strip_assume_tac ALOOKUP_SOME_EL
      \\ gvs [EL_REVERSE]
      \\ qmatch_asmsub_abbrev_tac ‘EL m xs’
      \\ ‘m < LENGTH xs’ by fs [Abbr ‘m’, LIST_REL_LENGTH]
      \\ first_x_assum (drule_then assume_tac)
      \\ gvs [exp_inv_def])
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum irule
    \\ simp [subst_funs_def, closed_subst]
    \\ irule_at Any exp_rel_subst
    \\ simp [EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
             GSYM FST_THM]
    \\ irule_at Any LIST_EQ
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ drule_then assume_tac LIST_REL_LENGTH \\ simp []
    \\ conj_tac
    >- (
      rw []
      \\ pairarg_tac \\ gvs []
      \\ pairarg_tac \\ gvs []
      \\ rename1 ‘MEM (p,v1) l’
      \\ ‘∀v. v1 ≠ Delay (Force (Var v))’
        by (rpt strip_tac \\ rw []
            \\ first_x_assum (qspec_then ‘HD v::v’ mp_tac)
            \\ rw [Once exp_rel_cases])
      \\ gs [thunk_rel_def])
    \\ rename1 ‘LIST_REL _ xs ys’
    \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY, thunk_rel_def]
    \\ dxrule_then strip_assume_tac ALOOKUP_SOME_EL
    \\ dxrule_then strip_assume_tac ALOOKUP_SOME_EL
    \\ gvs [EL_REVERSE]
    \\ qmatch_asmsub_abbrev_tac ‘EL m xs’
    \\ ‘m < LENGTH ys’ by fs [Abbr ‘m’]
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ gvs [freevars_def]
    \\ cheat (* exp_inv under subst *))
  >- ((* Prim *)
    cheat (* TODO not really done *)) (*
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
      \\ gs [])) *)
QED

val _ = export_theory ();

