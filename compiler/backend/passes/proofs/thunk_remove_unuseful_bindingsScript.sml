(*
  Remove all unuseful bindings from an expression expressed in thunkLang
*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory arithmeticTheory;
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory;

val _ = new_theory "thunk_remove_unuseful_bindings";

Definition no_op_def:
  no_op (Lam s e) = T ∧
  no_op (Delay e) = T ∧
  no_op (Value v) = T ∧
  no_op _ = F
End

Inductive clean_rel:
[~Var:]
  (∀n. clean_rel (Var n) (Var n))
[~Value:]
  (∀v w.
     v_rel v w ⇒
       clean_rel (Value v) (Value w))
[~Prim:]
  (∀op xs ys.
     LIST_REL clean_rel xs ys ⇒
       clean_rel (Prim op xs) (Prim op ys))
[~Monad:]
  (∀mop xs ys.
     LIST_REL clean_rel xs ys ⇒
       clean_rel (Monad mop xs) (Monad mop ys))
[~App:]
  (∀f g x y.
     clean_rel f g ∧
     clean_rel x y ⇒
       clean_rel (App f x) (App g y))
[~Lam:]
  (∀s x y.
     clean_rel x y ⇒
       clean_rel (Lam s x) (Lam s y))
[~Letrec:]
  (∀f g x y.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL clean_rel (MAP SND f) (MAP SND g) ∧
     clean_rel x y ⇒
     clean_rel (Letrec f x) (Letrec g y))
[~remove_Letrec:]
  (∀f x y.
     EVERY ok_bind (MAP SND f) ∧
     clean_rel x y ∧
     EVERY (λv. v ∉ freevars x) (MAP FST f) ⇒
     clean_rel (Letrec f x) y)
[~simp_Letrec:]
  (∀f g v w x y.
     MAP FST f = MAP FST g ∧
     ok_bind w ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL clean_rel (MAP SND f) (MAP SND g) ∧
     ¬MEM v (MAP FST f) ∧
     v ∉ freevars x ∧ EVERY (λe. v ∉ freevars e) (MAP SND f) ∧
     clean_rel x y ⇒
     clean_rel (Letrec (SNOC (v, w) f) x) (Letrec g y))
[~Let:]
  (∀opt x1 y1 x2 y2.
     clean_rel x1 x2 ∧
     clean_rel y1 y2 ⇒
     clean_rel (Let opt x1 y1) (Let opt x2 y2))
[~remove_Let:]
  (∀s x y1 y2.
     clean_rel y1 y2 ∧
     s ∉ freevars y1 ∧
     no_op x ⇒
     clean_rel (Let (SOME s) x y1) y2)
[~If:]
  (∀x1 y1 z1 x2 y2 z2.
     clean_rel x1 x2 ∧
     clean_rel y1 y2 ∧
     clean_rel z1 z2 ⇒
       clean_rel (If x1 y1 z1) (If x2 y2 z2))
[~Delay:]
  (∀x y.
     clean_rel x y ⇒
       clean_rel (Delay x) (Delay y))
[~Force:]
  (∀x y.
     clean_rel x y ⇒
     clean_rel (Force x) (Force y))
[~MkTick:]
  (∀x y. clean_rel x y ⇒ clean_rel (MkTick x) (MkTick y))
[v_rel_Constructor:]
  (∀s vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws))
[v_rel_Monadic:]
  (∀mop xs ys.
     LIST_REL clean_rel xs ys ⇒
       v_rel (Monadic mop xs) (Monadic mop ys))
[v_rel_Closure:]
  (∀s x y.
     clean_rel x y ⇒
       v_rel (Closure s x) (Closure s y))
[v_rel_Recclosure:]
  (∀f g n.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL clean_rel (MAP SND f) (MAP SND g) ⇒
     v_rel (Recclosure f n) (Recclosure g n))
[v_rel_simp_Recclosure:]
  (∀f g v w n.
     MAP FST f = MAP FST g ∧
     ¬MEM v (MAP FST f) ∧
     ok_bind w ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     MEM n (MAP FST g) ∧
     LIST_REL clean_rel (MAP SND f) (MAP SND g) ∧
     EVERY (λe. v ∉ freevars e) (MAP SND f) ⇒
     v_rel (Recclosure (SNOC (v,w) f) n) (Recclosure g n))
[v_rel_Thunk:]
  (∀x y.
     clean_rel x y ⇒
     v_rel (Thunk x) (Thunk y))
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x))
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ⇒
     v_rel (DoTick v) (DoTick w))
End

Theorem clean_rel_def =
  [“clean_rel (Var v) x”,
   “clean_rel (Value v) x”,
   “clean_rel (Prim op xs) x”,
   “clean_rel (Monad mop xs) x”,
   “clean_rel (App f x) y”,
   “clean_rel (Lam s x) y”,
   “clean_rel (Letrec f x) y”,
   “clean_rel (Let s x y) z”,
   “clean_rel (If x y z) w”,
   “clean_rel (Delay x) y”,
   “clean_rel (MkTick x) y”,
   “clean_rel (Force x) y”]
  |> map (SIMP_CONV (srw_ss()) [Once clean_rel_cases])
  |> LIST_CONJ;

Theorem v_rel_def =
  [“v_rel (Constructor s vs) v”,
   “v_rel (Monadic mop xs) v”,
   “v_rel (Closure s x) v”,
   “v_rel (Recclosure f n) v”,
   “v_rel (Atom x) v”,
   “v_rel (Thunk x) v”,
   “v_rel (DoTick x) v”]
  |> map (SIMP_CONV (srw_ss()) [Once clean_rel_cases])
  |> LIST_CONJ

Theorem ok_bind_subst[simp]:
  ∀x. ok_bind x ⇒ ok_bind (subst ws x)
Proof
  Cases \\ rw [ok_bind_def] \\ gs [subst_def, ok_bind_def]
QED

Theorem clean_rel_Lams:
  ∀l x y. clean_rel x y ⇒ clean_rel (Lams l x) (Lams l y)
Proof
  Induct >> gs [clean_rel_def]
QED

Theorem clean_rel_Apps:
  ∀l1 l2 x y. clean_rel x y ∧ LIST_REL clean_rel l1 l2 ⇒ clean_rel (Apps x l1) (Apps y l2)
Proof
  Induct >> gs [clean_rel_def, PULL_EXISTS]
QED

Theorem clean_rel_refl:
  ∀x. no_value x ⇒ clean_rel x x
Proof
  Induct using freevars_ind >> gs [clean_rel_def, no_value_def]
  >- gs [MEM_EL, PULL_EXISTS, EVERY_EL, LIST_REL_EL_EQN]
  >- gs [MEM_EL, PULL_EXISTS, EVERY_EL, LIST_REL_EL_EQN]
  >- (gs [MEM_EL, PULL_EXISTS, EVERY_EL, LIST_REL_EL_EQN] >>
      rw [] >> disj1_tac >> rw [] >>
      last_x_assum irule >>
      rpt $ first_assum $ irule_at Any >>
      gs [EL_MAP] >>
      irule_at Any PAIR)
QED

Theorem clean_rel_freevars:
  ∀x y. clean_rel x y ⇒ freevars y ⊆ freevars x
Proof
  completeInduct_on ‘exp_size x’ >> Cases >>
  gvs [exp_size_def, clean_rel_def, PULL_EXISTS, freevars_def, SUBSET_DEF, PULL_FORALL] >>
  rw [] >> gvs []
  >- (rename1 ‘LIST_REL _ xs ys’
      \\ last_x_assum $ irule_at Any
      \\ gvs [MEM_EL, EL_MAP, LIST_REL_EL_EQN, PULL_EXISTS]
      \\ rpt $ last_assum $ irule_at Any
      \\ assume_tac exp_size_lemma
      \\ gvs [EL_MAP, MEM_EL, PULL_EXISTS]
      \\ rename1 ‘n < _’
      \\ first_x_assum $ qspecl_then [‘xs’, ‘n’] assume_tac \\ gvs [])
  >- (rename1 ‘LIST_REL _ xs ys’
      \\ last_x_assum $ irule_at Any
      \\ gvs [MEM_EL, EL_MAP, LIST_REL_EL_EQN, PULL_EXISTS]
      \\ rpt $ last_assum $ irule_at Any
      \\ assume_tac exp_size_lemma
      \\ gvs [EL_MAP, MEM_EL, PULL_EXISTS]
      \\ rename1 ‘n < _’
      \\ first_x_assum $ qspecl_then [‘xs’, ‘n’] assume_tac \\ gvs [])
  >- (disj1_tac \\ first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (disj2_tac \\ first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (gvs [freevars_def]
      >- (disj1_tac \\ last_x_assum irule \\ gvs []
          \\ rpt $ first_x_assum $ irule_at Any)
      \\ disj2_tac \\ last_x_assum $ irule_at Any
      \\ gvs [MEM_EL, LIST_REL_EL_EQN, EL_MAP]
      \\ last_x_assum $ irule_at Any
      \\ rpt $ first_assum $ irule_at Any
      \\ gvs [EL_MAP, SND_THM]
      \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
      \\ assume_tac exp_size_lemma
      \\ gvs [MEM_EL, PULL_EXISTS]
      \\ rename1 ‘n < _’
      \\ first_x_assum $ qspecl_then [‘FST (EL n l)’, ‘SND (EL n l)’, ‘l’, ‘n’] assume_tac \\ gvs [])
  >- gvs [freevars_def]
  >- (disj1_tac \\ last_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (rename1 ‘clean_rel y1 y2’ \\ last_x_assum $ qspecl_then [‘y1’, ‘y2’] assume_tac \\ gvs []
      \\ pop_assum $ dxrule_then assume_tac \\ strip_tac \\ gvs [EVERY_MEM])
  >- (gvs [freevars_def]
      >- (disj1_tac \\ last_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
      \\ disj2_tac
      \\ ‘∀A B. A ⇒ A ∨ B’ by gvs [] \\ pop_assum $ irule_at Any
      \\ gvs [MEM_EL, EL_MAP, SF CONJ_ss, PULL_EXISTS]
      \\ rename1 ‘n < _’ \\ qexists_tac ‘n’
      \\ gvs [LIST_REL_EL_EQN]
      \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
      \\ last_x_assum irule \\ gvs [EL_MAP]
      \\ last_x_assum $ qspec_then ‘n’ assume_tac \\ gvs [EL_SNOC, EL_MAP]
      \\ conj_tac
      >- (assume_tac exp_size_lemma \\ gvs [MEM_EL, PULL_EXISTS]
          \\ rename1 ‘f ++ [(v,w)]’
          \\ first_x_assum $ qspecl_then [‘FST (EL n f)’, ‘SND (EL n f)’, ‘f ++ [(v,w)]’, ‘n’] assume_tac
          \\ gvs [EL_APPEND_EQN])
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (gvs [freevars_def] \\ strip_tac \\ gvs [MEM_MAP, EVERY_MEM, PULL_EXISTS]
      >- (rpt $ first_x_assum $ irule_at Any \\ gvs [])
      \\ gvs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
      \\ rename1 ‘n < _ ’ \\ rpt $ first_x_assum $ qspec_then ‘n’ assume_tac \\ gs [EL_MAP]
      \\ rpt $ first_x_assum $ irule_at Any
      \\ pairarg_tac \\ gs []
      \\ rename1 ‘f ++ [(v,w)]’ \\ assume_tac exp_size_lemma \\ gvs [MEM_EL, PULL_EXISTS]
      \\ first_x_assum $ qspecl_then [‘FST (EL n f)’, ‘SND (EL n f)’, ‘f ++ [(v,w)]’, ‘n’] assume_tac
      \\ gvs [EL_APPEND_EQN])
  >- (rename1 ‘clean_rel x1 x2’ \\ rename1 ‘clean_rel y1 y2’
      \\ rename1 ‘Let opt _ _’ \\ Cases_on ‘opt’
      \\ last_assum $ qspecl_then [‘x1’, ‘x2’] assume_tac
      \\ last_x_assum $ qspecl_then [‘y1’, ‘y2’] assume_tac \\ gvs [freevars_def])
  >- (rename1 ‘clean_rel y1 y2’ \\ last_x_assum $ qspecl_then [‘y1’, ‘y2’] assume_tac \\ gvs [freevars_def]
      \\ rw [] \\ gvs [])
  >- (disj1_tac \\ disj1_tac \\ first_x_assum irule \\ gvs []
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (disj1_tac \\ disj2_tac \\ first_x_assum irule \\ gvs []
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (disj2_tac \\ first_x_assum irule \\ gvs []
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
QED

Theorem exp1_size_append:
  ∀l1 l2. exp1_size (l1 ++ l2) = exp1_size l1 + exp1_size l2
Proof
  Induct >> gs [exp_size_def]
QED

Theorem clean_rel_boundvars:
  ∀x y. clean_rel x y ⇒ boundvars y ⊆ boundvars x
Proof
  completeInduct_on ‘exp_size x’ >> Cases >>
  gvs [exp_size_def, clean_rel_def, PULL_EXISTS, boundvars_def, SUBSET_DEF, PULL_FORALL] >>
  rw [] >> gvs []
  >- (rename1 ‘LIST_REL _ xs ys’
      \\ last_x_assum $ irule_at Any
      \\ gvs [MEM_EL, EL_MAP, LIST_REL_EL_EQN, PULL_EXISTS]
      \\ rpt $ last_assum $ irule_at Any
      \\ assume_tac exp_size_lemma
      \\ gvs [EL_MAP, MEM_EL, PULL_EXISTS]
      \\ rename1 ‘n < _’
      \\ first_x_assum $ qspecl_then [‘xs’, ‘n’] assume_tac \\ gvs [])
  >- (rename1 ‘LIST_REL _ xs ys’
      \\ last_x_assum $ irule_at Any
      \\ gvs [MEM_EL, EL_MAP, LIST_REL_EL_EQN, PULL_EXISTS]
      \\ rpt $ last_assum $ irule_at Any
      \\ assume_tac exp_size_lemma
      \\ gvs [EL_MAP, MEM_EL, PULL_EXISTS]
      \\ rename1 ‘n < _’
      \\ first_x_assum $ qspecl_then [‘xs’, ‘n’] assume_tac \\ gvs [])
  >- (disj1_tac \\ first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (disj2_tac \\ first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (disj1_tac \\ last_x_assum $ irule_at Any
      \\ gs []
      \\ rpt $ first_assum $ irule_at Any)
  >- (gs [boundvars_def]
      >- (disj1_tac \\ disj1_tac
          \\ last_x_assum irule \\ simp []
          \\ rpt $ first_x_assum $ irule_at Any)
      \\ disj1_tac \\ disj2_tac
      \\ gs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
      \\ first_assum $ irule_at Any \\ gs [EL_MAP]
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ first_x_assum $ drule_then assume_tac
      \\ last_x_assum irule \\ simp []
      \\ assume_tac exp_size_lemma \\ fs [MEM_EL, PULL_EXISTS]
      \\ qpat_x_assum ‘LENGTH _ = LENGTH _’ assume_tac \\ dxrule_then assume_tac EQ_SYM
      \\ gs []
      \\ first_x_assum $ drule_then assume_tac \\ gs []
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (disj1_tac \\ disj1_tac \\ last_x_assum irule \\ simp []
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (gs [boundvars_def]
      >- (disj1_tac \\ disj1_tac
          \\ last_x_assum irule \\ simp []
          \\ rpt $ first_x_assum $ irule_at Any)
      \\ disj1_tac \\ disj2_tac
      \\ gs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
      \\ ‘∀a b. a ⇒ a ∨ b’ by simp [] \\ pop_assum $ irule_at Any
      \\ pop_assum kall_tac
      \\ first_assum $ irule_at Any \\ gs [EL_MAP]
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ first_x_assum $ drule_then assume_tac
      \\ last_x_assum irule \\ simp []
      \\ assume_tac exp_size_lemma \\ fs [MEM_EL, PULL_EXISTS]
      \\ qpat_x_assum ‘LENGTH _ = LENGTH _’ assume_tac \\ dxrule_then assume_tac EQ_SYM
      \\ gs []
      \\ first_x_assum $ drule_then assume_tac
      \\ gs [exp1_size_append]
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (rename1 ‘Let opt _ _’
      \\ Cases_on ‘opt’ \\ gs [boundvars_def]
      >- (disj1_tac \\ last_x_assum irule \\ simp []
          \\ rpt $ first_x_assum $ irule_at Any)
      >- (disj2_tac \\ last_x_assum irule \\ simp []
          \\ rpt $ first_x_assum $ irule_at Any)
      >- (disj1_tac \\ disj1_tac \\ last_x_assum irule \\ simp []
          \\ rpt $ first_x_assum $ irule_at Any)
      >- (disj1_tac \\ disj2_tac \\ last_x_assum irule \\ simp []
          \\ rpt $ first_x_assum $ irule_at Any))
  >- (gs [boundvars_def] \\ disj1_tac \\ disj2_tac
      \\ last_x_assum irule \\ simp []
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (disj1_tac \\ disj1_tac
      \\ last_x_assum irule \\ simp []
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (disj1_tac \\ disj2_tac
      \\ last_x_assum irule \\ simp []
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (disj2_tac
      \\ last_x_assum irule \\ simp []
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (last_x_assum irule \\ simp []
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (last_x_assum irule \\ simp []
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (last_x_assum irule \\ simp []
      \\ rpt $ first_x_assum $ irule_at Any)
QED

Theorem clean_rel_subst:
  ∀vs x ws y.
    MAP FST vs = MAP FST ws ∧
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    clean_rel x y ⇒
      clean_rel (subst vs x) (subst ws y)
Proof
   ‘(∀x y.
     clean_rel x y ⇒
     ∀vs ws.
       MAP FST vs = MAP FST ws ∧
       LIST_REL v_rel (MAP SND vs) (MAP SND ws) ⇒
         clean_rel (subst vs x) (subst ws y)) ∧
   (∀v w. v_rel v w ⇒ T)’
    suffices_by rw []
  \\ ho_match_mp_tac clean_rel_strongind \\ rw []
  >~ [‘Var v’] >- (
    rw [subst_def]
    \\ rename1 ‘LIST_REL v_rel (MAP SND vs) (MAP SND ws)’
    \\ ‘OPTREL v_rel (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
      by (irule LIST_REL_OPTREL
          \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
    \\ gs [OPTREL_def, clean_rel_Var, clean_rel_Value])
  >~ [‘Value v’] >- (
    rw [subst_def]
    \\ gs [clean_rel_Value])
  >~ [‘Prim op xs’] >- (
    rw [subst_def]
    \\ irule clean_rel_Prim
    \\ gs [EVERY2_MAP, LIST_REL_EL_EQN])
  >~ [‘Monad mop xs’] >- (
    rw [subst_def]
    \\ irule clean_rel_Monad
    \\ gs [EVERY2_MAP, LIST_REL_EL_EQN])
  >~ [‘App f x’] >- (
    rw [subst_def]
    \\ gs [clean_rel_App])
  >~ [‘Lam s x’] >- (
    rw [subst_def]
    \\ irule clean_rel_Lam
    \\ first_x_assum irule
    \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >~ [‘clean_rel (subst _ (Letrec f x)) (subst _ (Letrec g y))’] >- (
    rw [subst_def]
    \\ irule clean_rel_Letrec
    \\ gvs [EVERY_MAP, EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
            GSYM FST_THM]
    \\ first_x_assum (irule_at Any)
    \\ gvs [MAP_FST_FILTER]
    \\ rename1 ‘MAP FST f = MAP FST g’
    \\ qabbrev_tac ‘P = λn. ¬MEM n (MAP FST g)’ \\ gs []
    \\ irule_at Any LIST_REL_FILTER
    \\ ‘∀f x. ok_bind x ⇒ ok_bind (subst f x)’
      by (ho_match_mp_tac subst_ind
          \\ rw [subst_def])
    \\ gvs [EVERY_EL, ELIM_UNCURRY]
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ first_assum irule
    \\ gvs [MAP_FST_FILTER, LAMBDA_PROD]
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
   >~[‘Letrec _ x’] >- (
    rw [subst_def] \\ irule clean_rel_remove_Letrec \\ rw []
    >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
        \\ rw [] \\ irule ok_bind_subst \\ first_x_assum $ dxrule_then irule)
    >- gvs [EVERY_MEM, MAP_MAP_o, combinTheory.o_DEF, GSYM FST_THM, freevars_subst, LAMBDA_PROD]
    \\ qspecl_then [‘ws’, ‘y’, ‘set (MAP FST f)’] mp_tac $ GSYM subst_remove \\ impl_tac
    >- (dxrule_then assume_tac clean_rel_freevars \\ gvs [DISJOINT_ALT, EVERY_MEM, SUBSET_DEF]
        \\ rw [] \\ strip_tac \\ metis_tac [])
    \\ rw []
    \\ first_x_assum irule
    \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. ¬MEM x (MAP FST f)’ \\ fs []
    \\ irule_at Any LIST_REL_FILTER \\ fs []
    \\ irule_at Any EVERY2_mono
    \\ first_assum $ irule_at Any
    \\ gvs [])
  >~[‘Letrec _ x’] >- (
    drule_then assume_tac clean_rel_freevars \\ gvs [SUBSET_DEF]
    \\ pop_assum $ qspec_then ‘v’ assume_tac \\ gvs []
    \\ rw [subst_def, MAP_SNOC] \\ irule clean_rel_simp_Letrec \\ rw [freevars_subst]
    >- gvs [MAP_MAP_o, combinTheory.o_DEF, GSYM FST_THM, LAMBDA_PROD]
    >- gvs [MAP_MAP_o, combinTheory.o_DEF, GSYM FST_THM, LAMBDA_PROD]
    >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
        \\ rw [] \\ irule ok_bind_subst \\ first_x_assum $ dxrule_then irule)
    >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
        \\ rw [] \\ irule ok_bind_subst \\ first_x_assum $ dxrule_then irule)
    >- (gvs [MAP_MAP_o, combinTheory.o_DEF, GSYM FST_THM, LAMBDA_PROD, EVERY_MEM]
        \\ rw [] \\ gvs [MEM_MAP, PULL_EXISTS]
        \\ pairarg_tac \\ gvs [freevars_subst, FORALL_PROD]
        \\ disj1_tac \\ rpt $ first_x_assum $ irule_at Any)
    >- (qspecl_then [‘FILTER (λ(n,v). ¬MEM n (MAP FST g)) ws’, ‘y’, ‘{v}’] assume_tac $ GSYM subst_remove
        \\ gvs [FILTER_FILTER, LAMBDA_PROD]
        \\ gvs [CONJ_COMM]
        \\ first_x_assum irule
        \\ qabbrev_tac ‘P = λx. x ≠ v ∧ ¬MEM x (MAP FST g)’ \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
        \\ irule LIST_REL_FILTER \\ gs []
        \\ irule EVERY2_mono
        \\ first_assum $ irule_at Any \\ gvs [])
    \\ simp [LIST_REL_EL_EQN]
    \\ conj_asm1_tac >- gvs [LIST_REL_EL_EQN]
    \\ gvs [SNOC_APPEND, EL_APPEND_EQN, EL_MAP, GSYM LESS_EQ_IFF_LESS_SUC]
    \\ gen_tac \\ strip_tac \\ last_x_assum $ drule_then assume_tac
    \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
    \\ qpat_x_assum ‘EVERY _ (MAP SND _)’ assume_tac \\ gvs [EVERY_EL]
    \\ first_x_assum $ drule_then assume_tac
    \\ gvs [Once LIST_REL_EL_EQN]
    \\ first_x_assum $ drule_then assume_tac \\ gvs [EL_MAP]
    \\ rename1 ‘clean_rel (subst _ x1) (subst _ x2)’
    \\ qspecl_then [‘FILTER (λ(n,v). ¬MEM n (MAP FST g)) ws’, ‘x2’, ‘{v}’] mp_tac $ GSYM subst_remove
    \\ gvs [EL_MAP, FILTER_FILTER, LAMBDA_PROD]
    \\ impl_tac >- (dxrule_then assume_tac clean_rel_freevars \\ strip_tac \\ gvs [SUBSET_DEF])
    \\ rw [] \\ first_x_assum irule
    \\ qabbrev_tac ‘P = λx. x ≠ v ∧ ¬MEM x (MAP FST g)’ \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ irule LIST_REL_FILTER \\ gs []
    \\ irule EVERY2_mono
    \\ first_assum $ irule_at Any \\ gvs [])
  >~ [‘clean_rel (subst _ (Let s x y)) (subst _ (Let _ _ _))’] >- (
    Cases_on ‘s’ \\ rw [subst_def]
    \\ irule clean_rel_Let \\ gs []
    \\ first_x_assum irule
    \\ gvs [MAP_FST_FILTER]
    \\ rename1 ‘_ ≠ s’
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ gs [EVERY2_MAP]
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >~[‘Let _ _ _’] >- (
    rw [subst_def] \\ irule clean_rel_remove_Let
    \\ conj_tac >- (rename1 ‘no_op (subst _ x)’ \\ Cases_on ‘x’ \\ gvs [subst_def, no_op_def])
    \\ gvs [freevars_subst]
    \\ rename1 ‘clean_rel (subst (FILTER _ vs) y1) _’ \\ rename1 ‘s ∉ _’
    \\ qspecl_then [‘vs’, ‘y1’, ‘{s}’] mp_tac subst_remove \\ gvs [])
  >~ [‘If x y z’] >- (
    rw [subst_def]
    \\ gs [clean_rel_If])
  >~ [‘Delay x’] >- (
    rw [subst_def]
    \\ gs [clean_rel_Delay])
  >~ [‘Force x’] >- (
    rw [subst_def]
    \\ gs [clean_rel_Force])
  >~[‘MkTick x’] >- (
    rw [subst_def]
    \\ gs [clean_rel_MkTick])
QED

Theorem clean_rel_eval_to:
  ∀x y.
    clean_rel x y ⇒
      ∃j. ($= +++ v_rel) (eval_to (j + k) x) (eval_to k y)
Proof
  completeInduct_on ‘k’
  \\ Induct using freevars_ind \\ rpt gen_tac
  >~ [‘Var v’] >- (
    rw [Once clean_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘Value v’] >- (
    rw [Once clean_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘App g y’] >- (
    gvs [Once clean_rel_def, eval_to_def, PULL_EXISTS] \\ rw []
    \\ rename1 ‘clean_rel y x’ \\ rename1 ‘clean_rel g f’
    \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac)) \\ gs []
    \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j’
      \\ Cases_on ‘eval_to (j + k) y’ \\ gs [])
    \\ Cases_on ‘eval_to k x’ \\ gs []
    >~ [‘INL err’] >- (
      Cases_on ‘err’ \\ gs []
      \\ qexists_tac ‘j’
      \\ Cases_on ‘eval_to (j + k) y’ \\ gs [])
    \\ Cases_on ‘eval_to (j + k) y’ \\ gs []
    \\ rename1 ‘v_rel w1 v1’
    \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac)) \\ gs []
    \\ Cases_on ‘eval_to k f = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ Cases_on ‘eval_to k x’ \\ gs []
        \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
        \\ ‘eval_to (j + k) y = eval_to k y’
          by (irule eval_to_mono \\ gs [])
        \\ gs [])
      \\ ‘∀j. eval_to (j + k) g = eval_to k g’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k g’ \\ gs [])
    \\ Cases_on ‘eval_to k f’ \\ gs []
    >~ [‘eval_to _ _ = INL err’] >- (
      Cases_on ‘err’ \\ gs []
      \\ qexists_tac ‘j1 + j’
      \\ ‘eval_to (j1 + j + k) y = eval_to (j + k) y’
        by (irule eval_to_mono \\ gs [])
      \\ ‘eval_to (j1 + j + k) g = eval_to (j1 + k) g’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j1 + k) g’ \\ gs [])
    \\ Cases_on ‘eval_to (j1 + k) g’ \\ gs []
    \\ rename1 ‘v_rel w2 v2’
    \\ ‘∀i. eval_to (i + j + k) y = eval_to (j + k) y’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
    \\ ‘∀i. eval_to (i + j1 + k) g = eval_to (j1 + k) g’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
    \\ Cases_on ‘dest_anyClosure v2’ \\ gs []
    >- (
      Q.REFINE_EXISTS_TAC ‘SUC i’ \\ gs []
      \\ first_x_assum (qspec_then ‘SUC j’ assume_tac)
      \\ first_x_assum (qspec_then ‘SUC j1’ assume_tac)
      \\ gs [arithmeticTheory.ADD1]
      \\ qexists_tac ‘j + j1’ \\ gs []
      \\ Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ gs [dest_anyClosure_def, v_rel_def]
      >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ ‘OPTREL clean_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
          \\ gvs [OPTREL_def]
          \\ rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
          \\ last_x_assum $ dxrule_then assume_tac
          \\ qpat_x_assum ‘clean_rel x0 _’ mp_tac
          \\ rw [Once clean_rel_cases] \\ gs [ok_bind_def])
      >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ ‘OPTREL clean_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
          \\ gvs [REVERSE_APPEND]
          \\ IF_CASES_TAC \\ gvs []
          \\ gvs [OPTREL_def]
          \\ rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
          \\ last_x_assum $ dxrule_then assume_tac
          \\ qpat_x_assum ‘clean_rel x0 _’ mp_tac
          \\ rw [Once clean_rel_cases] \\ gs [ok_bind_def]))
    \\ pairarg_tac \\ gvs []
    \\ ‘∃body' binds'. dest_anyClosure w2 = INR (s,body',binds')’
      by (Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ gs [dest_anyClosure_def, v_rel_def]
          >- (rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
              \\ ‘OPTREL clean_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
                by (irule LIST_REL_OPTREL
                    \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
              \\ gvs [OPTREL_def]
              \\ rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
              \\ last_x_assum $ dxrule_then assume_tac
              \\ qpat_x_assum ‘clean_rel x0 _’ mp_tac
              \\ rw [Once clean_rel_cases] \\ gvs [CaseEqs ["option", "exp"], ok_bind_def])
          >- (rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
              \\ ‘OPTREL clean_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
                by (irule LIST_REL_OPTREL
                    \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
              \\ gvs [REVERSE_APPEND] \\ IF_CASES_TAC
              \\ gvs [OPTREL_def]
              \\ rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
              \\ last_x_assum $ dxrule_then assume_tac
              \\ qpat_x_assum ‘clean_rel x0 _’ mp_tac
              \\ rw [Once clean_rel_cases] \\ gvs [CaseEqs ["option", "exp"], ok_bind_def]))
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’ \\ gs []
      \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
      \\ drule_then (qspec_then ‘j’ assume_tac) eval_to_mono \\ gs []
      \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
      \\ drule_then (qspec_then ‘j1’ assume_tac) eval_to_mono \\ gs [])
    \\ ‘clean_rel (subst (binds' ++ [s,w1]) body') (subst (binds ++ [s,v1]) body)’
      by (Cases_on ‘v2’ \\ Cases_on ‘w2’
          \\ gvs [dest_anyClosure_def, v_rel_def, subst_APPEND]
          >- (irule clean_rel_subst \\ gvs [])
          >- (irule clean_rel_subst
              \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
              \\ ‘OPTREL clean_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
                by (irule LIST_REL_OPTREL
                    \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
              \\ irule_at Any clean_rel_subst
              \\ gvs [OPTREL_def]
              \\ rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
              \\ last_assum $ dxrule_then assume_tac
              \\ gvs [CaseEqs ["option", "exp"], v_rel_def, ok_bind_def]
              \\ gs [Once clean_rel_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                     GSYM FST_THM, EVERY2_MAP, v_rel_def]
              \\ gvs [LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP, ELIM_UNCURRY, EVERY_MEM, MEM_MAP, PULL_EXISTS])
          >- (rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
              \\ ‘OPTREL clean_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
                by (irule LIST_REL_OPTREL
                    \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
              \\ gvs [REVERSE_APPEND]
              \\ rename1 ‘¬MEM v _’ \\ rename1 ‘v = s’ \\ Cases_on ‘v = s’ \\ gvs []
              \\ gvs [OPTREL_def]
              \\ rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
              \\ last_assum $ drule_then assume_tac
              \\ first_assum $ dxrule_then assume_tac
              \\ gvs [CaseEqs ["option", "exp"], v_rel_def, ok_bind_def, MAP_APPEND, subst_APPEND]
              \\ gvs [freevars_def, subst1_notin_frees, freevars_subst]
              \\ irule clean_rel_subst \\ irule_at Any clean_rel_subst
              \\ gs [Once clean_rel_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                     GSYM FST_THM, EVERY2_MAP, v_rel_def]
              \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY, EVERY_MEM, MEM_MAP, PULL_EXISTS]
              \\ rw [] \\ irule_at Any EL_MEM \\ gvs [SF CONJ_ss]
              \\ irule_at Any EQ_REFL
              \\ ‘∀i. i < LENGTH ys ⇒ EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]))
    \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ gs []
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j2’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) (subst (binds ++ [s,v1]) body) = INL Diverge’
    >- (
      Cases_on ‘eval_to k y = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ ‘∀i. eval_to (i + k) y = eval_to k y’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k g = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ ‘∀i. eval_to (i + k) g = eval_to k g’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ gs []
      \\ qexists_tac ‘j2’
      \\ Cases_on ‘eval_to (j2 + k - 1) (subst (binds' ++ [s,w1]) body')’
      \\ gs [])
    \\ qexists_tac ‘j1 + j2 + j’ \\ gs []
    \\ first_x_assum (qspec_then ‘j + j2’ assume_tac)
    \\ first_x_assum (qspec_then ‘j1 + j2’ assume_tac) \\ gs []
    \\ ‘eval_to (j2 + k - 1) (subst (binds' ++ [s,w1]) body') ≠ INL Diverge’
      by (strip_tac
          \\ Cases_on ‘eval_to (k - 1) (subst (binds ++ [s,v1]) body)’ \\ gs [])
    \\ drule_then (qspec_then ‘j1 + j2 + j + k - 1’ assume_tac) eval_to_mono
    \\ gs [])
  >~ [‘Lam s x’] >- (
    rw [Once clean_rel_cases]
    \\ gs [eval_to_def, v_rel_def])
  >~ [‘Let NONE x y’] >- (
    rw [clean_rel_def] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ gs [])
    \\ rename1 ‘clean_rel x x2’ \\ rename1 ‘clean_rel y y2’
    \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac
    \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ gvs []
    \\ last_assum $ dxrule_then $ qx_choose_then ‘j1’ assume_tac
    \\ last_x_assum $ dxrule_then $ qx_choose_then ‘j2’ assume_tac
    \\ rename1 ‘eval_to (jx + k - 1) x’
    \\ rename1 ‘eval_to (jy + k - 1) y’
    \\ Cases_on ‘eval_to (k - 1) x2’
    >- (qexists_tac ‘jx’ \\ Cases_on ‘eval_to (jx + k - 1) x’ \\ gs [])
    \\ Cases_on ‘eval_to (k - 1) y2 = INL Diverge’ \\ gs []
    >- (qexists_tac ‘0’
        \\ Cases_on ‘eval_to (k - 1) x = INL Diverge’ \\ gs []
        \\ dxrule_then (qspecl_then [‘jx + k - 1’] assume_tac) eval_to_mono
        \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
        \\ Cases_on ‘eval_to (k - 1) y = INL Diverge’ \\ gs []
        \\ dxrule_then (qspecl_then [‘jy + k - 1’] assume_tac) eval_to_mono \\ gs [])
    \\ Cases_on ‘eval_to (jx + k - 1) x’ \\ gs []
    \\ ‘eval_to (jy + jx + k - 1) x = eval_to (jx + k - 1) x’
        by (irule eval_to_mono \\ gs [])
    \\ ‘eval_to (jx + jy + k - 1) y = eval_to (jy + k - 1) y’
      by (irule eval_to_mono
          \\ Cases_on ‘eval_to (jy + k - 1) y’
          \\ Cases_on ‘eval_to (k - 1) y2’ \\ gs [])
    \\ qexists_tac ‘jx + jy’ \\ gvs [])
  >~ [‘Let (SOME n) x y’] >- (
    rw [clean_rel_def] \\ gs []
    >~[‘no_op x’]
    >- (gvs [eval_to_def, subst1_notin_frees]
        \\ first_x_assum $ dxrule_then $ qx_choose_then ‘j’ assume_tac
        \\ qexists_tac ‘j + 1’ \\ gvs []
        \\ Cases_on ‘x’ \\ gvs [no_op_def] \\ gvs [eval_to_def])
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ gs [])
    \\ rename1 ‘clean_rel x x2’ \\ rename1 ‘clean_rel y y2’
    \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac
    \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ gvs []
    \\ first_assum $ qspecl_then [‘x’, ‘x2’] mp_tac
    \\ impl_tac >- gvs []
    \\ disch_then $ qx_choose_then ‘j1’ assume_tac
    \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    >- (qexists_tac ‘j1’ \\ Cases_on ‘eval_to (j1 + k - 1) x’ \\ gs [])
    \\ Cases_on ‘eval_to (j1 + k - 1) x’ \\ gs []
    \\ rename1 ‘v_rel v1 v2’
    \\ first_x_assum $ qspecl_then [‘subst1 n v1 y’, ‘subst1 n v2 y2’] mp_tac
    \\ impl_tac >- gvs [clean_rel_subst]
    \\ disch_then $ qx_choose_then ‘j2’ assume_tac
    \\ Cases_on ‘eval_to (k - 1) (subst1 n v2 y2) = INL Diverge’ \\ gs []
    >- (qexists_tac ‘0’
        \\ Cases_on ‘eval_to (k - 1) x = INL Diverge’ \\ gs []
        \\ dxrule_then (qspecl_then [‘j1 + k - 1’] assume_tac) eval_to_mono
        \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
        \\ Cases_on ‘eval_to (k - 1) (subst1 n v1 y) = INL Diverge’ \\ gs []
        \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono \\ gs [])
    \\ Cases_on ‘eval_to (j1 + k - 1) x’ \\ gs []
    \\ ‘eval_to (j2 + j1 + k - 1) x = eval_to (j1 + k - 1) x’
        by (irule eval_to_mono \\ gs [])
    \\ ‘eval_to (j1 + j2 + k - 1) (subst1 n v1 y) = eval_to (j2 + k - 1) (subst1 n v1 y)’
      by (irule eval_to_mono
          \\ Cases_on ‘eval_to (j2 + k - 1) (subst1 n v1 y)’
          \\ Cases_on ‘eval_to (k - 1) (subst1 n v2 y2)’ \\ gs [])
    \\ qexists_tac ‘j1 + j2’ \\ gvs [])
  >~ [‘Letrec f x’] >- (
    rw [clean_rel_def] \\ gs []
    >- (simp [eval_to_def]
        \\ IF_CASES_TAC \\ gs []
        >- (qexists_tac ‘0’ >> gs [])
        \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
        \\ first_x_assum irule
        \\ simp [subst_funs_def, closed_subst, MAP_MAP_o, combinTheory.o_DEF,
                 LAMBDA_PROD, GSYM FST_THM]
        \\ irule clean_rel_subst
        \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
        \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [v_rel_def, LIST_REL_EL_EQN, EL_MAP]
        \\ rename1 ‘MAP FST f = MAP FST g’
        \\ ‘∀i. i < LENGTH f ⇒ FST (EL i f) = FST (EL i g)’
          by (rw [] >>
              ‘i < LENGTH f’ by gs [] >>
              dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
              ‘i < LENGTH g’ by gs [] >>
              dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
              rw [])
        \\ gs [] \\ first_x_assum $ dxrule_then assume_tac \\ gvs [])
    >- (simp [eval_to_def]
        \\ first_x_assum $ dxrule_then $ qx_choose_then ‘j’ assume_tac
        \\ qexists_tac ‘j + 1’
        \\ qspecl_then [‘MAP (λ(v,e). (v, Recclosure f v)) f’, ‘x’] assume_tac subst_notin_frees
        \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
                EVERY_MEM, DISJOINT_ALT, subst_funs_def])
    >- (gvs [eval_to_def, subst_funs_def, MAP_APPEND, subst_APPEND]
        \\ IF_CASES_TAC >- (qexists_tac ‘0’ \\ gs []) \\ gs [subst1_notin_frees]
        \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ gvs [] \\ pop_assum irule
        \\ irule clean_rel_subst
        \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, EVERY2_MAP]
        \\ gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
        \\ rename1 ‘n < _’ \\ rename1 ‘MAP FST f = MAP FST g’
        \\ ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gvs [] \\ gs [EL_MAP]
        \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gvs [v_rel_def]
        \\ gvs [LIST_REL_EL_EQN, EL_MAP]
        \\ rw []
        >- (gvs [MEM_EL] \\ first_assum $ irule_at Any \\ gs [EL_MAP])
        \\ first_x_assum $ drule_then assume_tac
        \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []))
  >~ [‘If x1 y1 z1’] >- (
    rw [clean_rel_def, eval_to_def] \\ gs [eval_to_def]
    \\ Cases_on ‘k = 0’
    >- (qexists_tac ‘0’ \\ gs [])
    \\ rename1 ‘clean_rel x1 x2’
    \\ rename1 ‘clean_rel y1 y2’ \\ rename1 ‘clean_rel z1 z2’
    \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
    \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ last_x_assum kall_tac
    \\ rpt $ first_assum $ dxrule_then assume_tac
    \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ gvs []
    \\ rename1 ‘eval_to (j2 + k - 1) z1’
    \\ rename1 ‘eval_to (j1 + k - 1) y1’
    \\ rename1 ‘eval_to (j  + k - 1) x1’
    \\ Cases_on ‘eval_to (k - 1) x2’
    \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
    >~ [‘INL err’] >- (qexists_tac ‘j’ \\ simp [])
    \\ rename1 ‘v_rel v1 w1’
    \\ IF_CASES_TAC \\ gvs [v_rel_def]
    >- (
      Cases_on ‘eval_to (k - 1) y2 = INL Diverge’ \\ gs []
      >- (
        Cases_on ‘eval_to (k - 1) x1 = INL Diverge’ \\ gs []
        >- (
          qexists_tac ‘0’
          \\ gs [])
        \\ ‘∀i. eval_to (i + k - 1) x1 = eval_to (k - 1) x1’
          by (strip_tac \\ irule eval_to_mono \\ gs [])
        \\ qexists_tac ‘j1’ \\ gs []
        \\ Cases_on ‘v1’ \\ gs [v_rel_def])
      \\ ‘eval_to (j1 + k - 1) y1 ≠ INL Diverge’
        by (strip_tac \\ Cases_on ‘eval_to (k - 1) y2’ \\ gs [])
      \\ ‘eval_to (j1 + j + k - 1) x1 = eval_to (j + k - 1) x1’
        by (irule eval_to_mono \\ gs [])
      \\ drule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono
      \\ qexists_tac ‘j1 + j’ \\ gs []
      \\ Cases_on ‘v1’ \\ gs [v_rel_def])
    \\ IF_CASES_TAC \\ gvs [v_rel_def]
    >- (
      Cases_on ‘eval_to (k - 1) z2 = INL Diverge’ \\ gs []
      >- (
        Cases_on ‘eval_to (k - 1) x1 = INL Diverge’ \\ gs []
        >- (
          qexists_tac ‘0’
          \\ gs [])
        \\ ‘∀i. eval_to (i + k - 1) x1 = eval_to (k - 1) x1’
          by (strip_tac \\ irule eval_to_mono \\ gs [])
        \\ qexists_tac ‘j2’ \\ Cases_on ‘v1’ \\ gs [v_rel_def])
      \\ ‘eval_to (j2 + k - 1) z1 ≠ INL Diverge’
        by (strip_tac \\ Cases_on ‘eval_to (k - 1) z2’ \\ gs [])
      \\ ‘eval_to (j2 + j + k - 1) x1 = eval_to (j + k - 1) x1’
        by (irule eval_to_mono \\ gs [])
      \\ drule_then (qspec_then ‘j + j2 + k - 1’ assume_tac) eval_to_mono
      \\ qexists_tac ‘j2 + j’ \\ Cases_on ‘v1’ \\ gs [v_rel_def])
    \\ qexists_tac ‘j’ \\ gs []
    \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gs [v_rel_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ IF_CASES_TAC \\ gvs [])
  >~ [‘Force x’] >- (
    rw [clean_rel_def] \\ gs []
    \\ rename1 ‘clean_rel x y’
    \\ once_rewrite_tac [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ gs [])
    \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
    \\ last_x_assum $ dxrule_then $ qx_choose_then ‘j’ assume_tac
    \\ Cases_on ‘eval_to k y’ \\ Cases_on ‘eval_to (j + k) x’ \\ gs []
    >~[‘INL err’]
    >- (qexists_tac ‘j’ \\ gvs [])
    \\ rename1 ‘v_rel v w’
    \\ Cases_on ‘dest_Tick w’ \\ gs []
    >- (
      ‘dest_Tick v = NONE’
        by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
            \\ gs [Once v_rel_def])
      \\ gs []
      \\ Cases_on ‘v’ \\ gvs [dest_anyThunk_def, v_rel_def]
      >~[‘Recclosure _ _’]
      >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ ‘OPTREL clean_rel
              (ALOOKUP (REVERSE xs) s)
              (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
          \\ gs [OPTREL_def]
          >- (qexists_tac ‘j’ \\ gvs [])
          \\ rename1 ‘clean_rel x0 y0’
          \\ ‘MEM (s, x0) xs’ by (rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [])
          \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
          \\ first_assum $ dxrule_then assume_tac
          \\ Cases_on ‘x0’ \\ gvs [ok_bind_def, clean_rel_def]
          >~[‘subst_funs ys e2’]
          >- (rename1 ‘clean_rel e1 e2’
              \\ last_x_assum $ qspecl_then [‘subst_funs xs e1’, ‘subst_funs ys e2’] mp_tac
              \\ impl_tac
              >- (gvs [FORALL_PROD, subst_funs_def] \\ irule clean_rel_subst
                  \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
                  \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [v_rel_def, LIST_REL_EL_EQN, EL_MAP]
                  \\ disj1_tac \\ rename1 ‘n < _’
                  \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gs []
                  \\ gvs [EL_MAP, EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
                  \\ rw [] \\ last_x_assum $ dxrule_then assume_tac \\ gvs [])
              \\ disch_then $ qx_choose_then ‘j2’ assume_tac
              \\ Cases_on ‘eval_to (k - 1) (subst_funs ys e2) = INL Diverge’ \\ gs []
              >- (qexists_tac ‘0’
                  \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
                  \\ dxrule_then (qspecl_then [‘j + k’] assume_tac) eval_to_mono \\ gs []
                  \\ Cases_on ‘eval_to (k - 1) (subst_funs xs e1) = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono \\ gs [])
              \\ qexists_tac ‘j + j2’
              \\ ‘eval_to (j + j2 + k) x = eval_to (j + k) x’ by (irule eval_to_mono \\ gvs [])
              \\ gvs []
              \\ ‘eval_to (j + (j2 + k) - 1) (subst_funs xs e1) = eval_to (j2 + k - 1) (subst_funs xs e1)’
                by (irule eval_to_mono
                    \\ Cases_on ‘eval_to (j2 + k - 1) (subst_funs xs e1)’
                    \\ Cases_on ‘eval_to (k - 1) (subst_funs ys e2)’ \\ gvs [])
              \\ gvs [])
          \\ qexists_tac ‘j’ \\ gvs [])
      >~[‘Recclosure _ _’]
      >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ ‘OPTREL clean_rel
              (ALOOKUP (REVERSE xs) s)
              (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
          \\ gs [OPTREL_def]
          >- (qexists_tac ‘j’ \\ gvs [REVERSE_APPEND]
              \\ IF_CASES_TAC \\ gvs [])
          \\ rename1 ‘clean_rel x0 y0’
          \\ ‘MEM (s, x0) xs’ by (rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [])
          \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
          \\ first_assum $ dxrule_then assume_tac
          \\ Cases_on ‘x0’ \\ gvs [ok_bind_def, clean_rel_def]
          >~[‘subst_funs ys e2’]
          >- (rename1 ‘clean_rel e1 e2’
              \\ rename1 ‘xs ++ [(v,w)]’
              \\ last_x_assum $ qspecl_then [‘subst_funs (xs++[(v,w)]) e1’, ‘subst_funs ys e2’] mp_tac
              \\ impl_tac
              >- (gvs [FORALL_PROD, subst_funs_def, subst_APPEND, freevars_def, subst1_notin_frees]
                  \\ irule clean_rel_subst
                  \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
                  \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [v_rel_def, LIST_REL_EL_EQN, EL_MAP]
                  \\ rename1 ‘n < _’
                  \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gs []
                  \\ gvs [EL_MAP, EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
                  \\ irule_at Any $ iffRL MEM_EL \\ gvs []
                  \\ qexists_tac ‘n’ \\ gvs []
                  \\ rw []
                  >- last_x_assum $ drule_then irule
                  >- last_x_assum $ drule_then irule
                  \\ first_x_assum $ drule_then assume_tac \\ gvs [])
              \\ disch_then $ qx_choose_then ‘j2’ assume_tac
              \\ Cases_on ‘eval_to (k - 1) (subst_funs ys e2) = INL Diverge’ \\ gs []
              >- (qexists_tac ‘0’
                  \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
                  \\ dxrule_then (qspecl_then [‘j + k’] assume_tac) eval_to_mono \\ gs [REVERSE_APPEND]
                  \\ IF_CASES_TAC \\ gvs []
                  \\ Cases_on ‘eval_to (k - 1) (subst_funs (xs ++ [(v,w)]) e1) = INL Diverge’ \\ gs []
                  \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono \\ gs [])
              \\ qexists_tac ‘j + j2’
              \\ ‘eval_to (j + j2 + k) x = eval_to (j + k) x’ by (irule eval_to_mono \\ gvs [])
              \\ gvs [REVERSE_APPEND]
              \\ IF_CASES_TAC \\ gvs []
              \\ ‘eval_to (j + (j2 + k) - 1) (subst_funs (xs++[(v,w)]) e1)
                  = eval_to (j2 + k - 1) (subst_funs (xs++[(v,w)]) e1)’
                by (irule eval_to_mono
                    \\ Cases_on ‘eval_to (j2 + k - 1) (subst_funs (xs++[(v,w)]) e1)’
                    \\ Cases_on ‘eval_to (k - 1) (subst_funs ys e2)’ \\ gvs [])
              \\ gvs [])
          \\ qexists_tac ‘j’ \\ gvs [REVERSE_APPEND]
          \\ IF_CASES_TAC \\ gvs []
          \\ rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gs []
          \\ last_x_assum $ kall_tac \\ last_x_assum $ kall_tac
          \\ last_x_assum $ dxrule_then assume_tac \\ gvs [ok_bind_def])
      >~[‘subst_funs [] y2’]
      >- (rename1 ‘clean_rel x2 y2’
          \\ last_x_assum $ qspecl_then [‘x2’, ‘y2’] assume_tac \\ gs [subst_funs_def, subst_empty]
          \\ rename1 ‘eval_to (j2 + k - 1) x2’
          \\ Cases_on ‘eval_to (k - 1) y2 = INL Diverge’ \\ gs []
          >- (qexists_tac ‘0’
              \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
              \\ dxrule_then (qspecl_then [‘j + k’] assume_tac) eval_to_mono \\ gs []
              \\ Cases_on ‘eval_to (k - 1) x2 = INL Diverge’ \\ gs []
              \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono \\ gs [])
            \\ qexists_tac ‘j + j2’
            \\ ‘eval_to (j + j2 + k) x = eval_to (j + k) x’ by (irule eval_to_mono \\ gvs [])
            \\ gvs []
            \\ ‘eval_to (j + (j2 + k) - 1) x2 = eval_to (j2 + k - 1) x2’
              by (irule eval_to_mono
                  \\ Cases_on ‘eval_to (j2 + k - 1) x2’
                  \\ Cases_on ‘eval_to (k - 1) y2’ \\ gvs [])
            \\ gvs [])
      \\ qexists_tac ‘j’ \\ gvs [])
    \\ Cases_on ‘v’ \\ gs [v_rel_def, clean_rel_def, PULL_EXISTS, dest_Tick_def]
    \\ rename1 ‘v_rel v2 w2’
    \\ last_x_assum $ qspecl_then [‘Force (Value v2)’, ‘Force (Value w2)’] assume_tac
    \\ gvs [clean_rel_def]
    \\ rename1 ‘v_rel v2 w2’ \\ rename1 ‘eval_to (j2 + k - 1) (Force _)’
    \\ Cases_on ‘eval_to (k - 1) (Force (Value w2)) = INL Diverge’ \\ gs []
    >- (qexists_tac ‘0’
        \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
        \\ dxrule_then (qspecl_then [‘j + k’] assume_tac) eval_to_mono \\ gs []
        \\ Cases_on ‘eval_to (k - 1) (Force (Value v2)) = INL Diverge’ \\ gs []
        \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono \\ gs [])
    \\ qexists_tac ‘j + j2’
    \\ ‘eval_to (j + j2 + k) x = eval_to (j + k) x’ by (irule eval_to_mono \\ gvs [])
    \\ gs []
    \\ ‘eval_to (j + (j2 + k) - 1) (Force (Value v2)) = eval_to (j2 + k - 1) (Force (Value v2))’
      by (irule eval_to_mono
          \\ Cases_on ‘eval_to (j2 + k - 1) (Force (Value v2))’
          \\ Cases_on ‘eval_to (k - 1) (Force (Value w2))’ \\ gvs [])
    \\ gvs [])
  >~ [‘Delay x’] >- (
    rw [Once clean_rel_cases] \\ gs []
    \\ simp [eval_to_def, v_rel_def])
  >~ [‘MkTick x’] >- (
    rw [clean_rel_def] \\ gs [eval_to_def]
    \\ first_x_assum $ dxrule_then $ qx_choose_then ‘j’ assume_tac
    \\ qexists_tac ‘j’
    \\ rename1 ‘($= +++ v_rel) (eval_to (j + k) x) (eval_to _ y)’
    \\ Cases_on ‘eval_to (j + k) x’
    \\ Cases_on ‘eval_to k y’ \\ gvs [v_rel_def])
  >~ [‘Prim op xs’] >- (
    rw []
    \\ gvs [Once clean_rel_def, eval_to_def]
    \\ gvs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
    \\ Cases_on ‘op’ \\ gs []
    >- ((* Cons *)
      last_x_assum kall_tac
      \\ ‘∃j. ($= +++ LIST_REL v_rel) (result_map (eval_to (j + k)) xs)
                                      (result_map (eval_to k) ys)’
        suffices_by (
          disch_then (qx_choose_then ‘j’ assume_tac)
          \\ qexists_tac ‘j’ \\ gs [SF ETA_ss]
          \\ Cases_on ‘result_map (eval_to k) ys’
          \\ Cases_on ‘result_map (eval_to (j + k)) xs’ \\ gs [v_rel_def])
      \\ gvs [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
        \\ qexists_tac ‘j’
        \\ rw [] \\ gs [SF SFY_ss]
        \\ Cases_on ‘eval_to (j + k) (EL n xs)’ \\ gs [])
      \\ ‘∀n. n < LENGTH ys ⇒
            ∃j. ($= +++ v_rel) (eval_to (j + k) (EL n xs))
                               (eval_to k (EL n ys))’
        by rw []
      \\ last_x_assum kall_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        Cases_on
          ‘∃m. m < LENGTH xs ∧ eval_to k (EL m xs) = INL Type_error’ \\ gs []
        >- (
          ‘F’ suffices_by rw []
          \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
          \\ ‘eval_to k (EL m xs) ≠ INL Diverge’
            by gs []
          \\ ‘∀i. eval_to (i + k) (EL m xs) = eval_to k (EL m xs)’
            by (strip_tac \\ irule eval_to_mono \\ gs [])
          \\ Cases_on ‘eval_to k (EL m ys)’ \\ gs [])
        \\ qexists_tac ‘0’
        \\ rw [] \\ gs []
        \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
        \\ Cases_on ‘eval_to k (EL n xs) = INL Diverge’ \\ gs []
        \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono \\ gs []
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
      \\ ‘∃j. ∀n. n < LENGTH ys ⇒
                ($= +++ v_rel) (eval_to (j + k) (EL n xs))
                               (eval_to k (EL n ys))’
        by (rpt (pop_assum mp_tac)
            \\ qid_spec_tac ‘ys’
            \\ qid_spec_tac ‘xs’
            \\ Induct \\ simp []
            \\ Cases_on ‘ys’ \\ simp []
            \\ qx_gen_tac ‘x’
            \\ rename1 ‘_ (EL _ (x::xs)) (EL _ (y::ys))’
            \\ rw []
            \\ last_x_assum drule
            \\ impl_tac
            >- (
              rpt $ strip_tac
              \\ rename1 ‘n < LENGTH ys’
              \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
              \\ res_tac \\ fs [SF SFY_ss]
              \\ rpt $ first_x_assum $ qspecl_then [‘SUC n’] assume_tac
              \\ gs [])
            \\ disch_then (qx_choose_then ‘j1’ assume_tac)
            \\ ‘0 < SUC (LENGTH ys)’ by gs []
            \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
            \\ gs []
            \\ qexists_tac ‘MAX j j1’
            \\ Cases \\ rw [arithmeticTheory.MAX_DEF]
            >- (
              ‘eval_to k y ≠ INL Diverge’
                by (strip_tac
                    \\ rpt $ first_x_assum $ qspecl_then [‘0’] assume_tac
                    \\ gs [])
              \\ ‘eval_to (j + k) x ≠ INL Diverge’
                by (strip_tac \\ Cases_on ‘eval_to k y’ \\ gs [])
              \\ drule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
              \\ gs [])
            \\ gs [arithmeticTheory.NOT_LESS]
            \\ rename1 ‘m < LENGTH ys’
            \\ ‘SUC m < SUC (LENGTH ys)’ by gs []
            \\ first_x_assum (drule_then assume_tac)
            \\ first_x_assum (drule_then assume_tac) \\ gs []
            \\ ‘eval_to (j1 + k) (EL m xs) ≠ INL Diverge’
              by (strip_tac \\ Cases_on ‘eval_to k (EL m ys)’
                  \\ first_x_assum $ qspecl_then [‘SUC m’] assume_tac
                  \\ gs [])
            \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
            \\ gs [])
      \\ qexists_tac ‘j’
      \\ rw [] \\ gs [SF SFY_ss]
      >~ [‘MAP OUTR _’] >- (
        gvs [EVERY2_MAP, LIST_REL_EL_EQN] \\ rw []
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ Cases_on ‘eval_to k (EL n ys)’
        \\ Cases_on ‘eval_to (j + k) (EL n xs)’ \\ gvs []
        \\ rename1 ‘INL err’ \\ Cases_on ‘err’ \\ gs [])
      \\ first_x_assum (drule_all_then assume_tac)
      \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
    >- ((* IsEq *)
      IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘clean_rel x y’
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
      \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
      \\ qexists_tac ‘j’
      \\ Cases_on ‘eval_to (k - 1) y’
      \\ Cases_on ‘eval_to (j + k - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN, v_rel_def]
      \\ IF_CASES_TAC \\ gs []
      \\ rw [v_rel_def])
    >- ((* Proj *)
      IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘clean_rel x y’
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
      \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
      \\ qexists_tac ‘j’
      \\ Cases_on ‘eval_to (k - 1) y’
      \\ Cases_on ‘eval_to (j + k - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN, v_rel_def]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* AtomOp *)
      Cases_on ‘k = 0’ \\ gs []
      >- (
        qexists_tac ‘0’ \\ gs []
        \\ rw [result_map_def, MEM_MAP, MEM_EL, PULL_EXISTS]
        \\ Cases_on ‘ys = []’ \\ gs []
        >- (
          CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [v_rel_def])
        \\ ‘xs ≠ []’ by (strip_tac \\ gs [])
        \\ first_x_assum (qspec_then ‘0’ assume_tac) \\ gs [])
      \\ qmatch_goalsub_abbrev_tac ‘result_map g ys’
      \\ qabbrev_tac ‘f = λj x. case eval_to (j + k - 1) x of
                                INL err => INL err
                              | INR (Atom x) => INR x
                              | _ => INL Type_error’ \\ gs []
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac
      \\ last_x_assum kall_tac \\ gvs []
      \\ ‘∃j. result_map (f j) xs = result_map g ys’
        suffices_by (
          disch_then (qx_choose_then ‘j’ assume_tac)
          \\ qexists_tac ‘j’ \\ gs [SF ETA_ss]
          \\ Cases_on ‘result_map g ys’ \\ gs []
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [v_rel_def])
      \\ unabbrev_all_tac
      \\ simp [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
      \\ Cases_on ‘k’ \\ gs [arithmeticTheory.ADD1]
      \\ rename1 ‘eval_to k’
      \\ ‘∀n. n < LENGTH ys ⇒
            ∃j. ($= +++ v_rel) (eval_to (j + k) (EL n xs))
                               (eval_to k (EL n ys))’
        by rw []
      \\ qpat_x_assum ‘∀x y. clean_rel _ _ ⇒ _’ kall_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        rename1 ‘m < LENGTH ys’
        \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
        \\ qexists_tac ‘j’
        \\ rpt (first_x_assum (qspec_then ‘m’ assume_tac)) \\ gs []
        \\ rw [] \\ gs []
        \\ rpt (first_x_assum (qspec_then ‘m’ assume_tac)) \\ gs []
        \\ Cases_on ‘eval_to k (EL m ys)’
        \\ Cases_on ‘eval_to (j + k) (EL m xs)’ \\ gs []
        \\ rename1 ‘v_rel v w’
        \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [v_rel_def])
      \\ ‘∀n. n < LENGTH ys ⇒ eval_to k (EL n ys) = INL Diverge ∨
                              ∃x. eval_to k (EL n ys) = INR (Atom x)’
        by (rw [DISJ_EQ_IMP]
            \\ first_x_assum drule
            \\ rw [CaseEqs ["sum", "v"]]
            \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
            >~ [‘INL err’] >- (
              Cases_on ‘err’ \\ gs [])
            \\ rename1 ‘INR x’
            \\ Cases_on ‘x’ \\ gs [])
      \\ qpat_x_assum ‘∀n. _ ⇒ ¬( _ < _)’ kall_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        Cases_on
          ‘∃m. m < LENGTH ys ∧ eval_to k (EL m xs) = INL Type_error’ \\ gs []
        >- (
          ‘F’ suffices_by rw []
          \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
          \\ ‘eval_to k (EL m xs) ≠ INL Diverge’
            by gs []
          \\ ‘∀i. eval_to (i + k) (EL m xs) = eval_to k (EL m xs)’
            by (strip_tac \\ irule eval_to_mono \\ gs [])
          \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs []
          \\ rpt (first_x_assum (qspec_then ‘m’ assume_tac)) \\ gs [])
        \\ rename1 ‘n < LENGTH ys’
        \\ rgs [Once (CaseEq "sum"), CaseEq "v"]
        \\ qexists_tac ‘0’
        \\ rw [] \\ gs []
        >- (
          rename1 ‘m < LENGTH ys’
          \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
          \\ ‘eval_to k (EL m xs) ≠ INL Diverge’
            by (strip_tac \\ gs [])
          \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono \\ gs []
          \\ Cases_on ‘eval_to k (EL m xs)’
          \\ Cases_on ‘eval_to k (EL m ys)’ \\ gs []
          \\ first_x_assum (drule_then assume_tac) \\ gs []
          \\ rename1 ‘v_rel y _’ \\ Cases_on ‘y’ \\ gs [v_rel_def])
        >- (
          first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ ‘eval_to k (EL n xs) ≠ INL Diverge’
            by (strip_tac \\ gs [])
          \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono \\ gs []
          \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
        >- (rename1 ‘eval_to _ _ = INR v3’ \\ Cases_on ‘v3’ \\ gvs [])
        >- (rpt $ first_x_assum $ qspecl_then [‘n’] assume_tac
            \\ rename1 ‘eval_to _ _ = INR v3’ \\ Cases_on ‘v3’ \\ gvs []))
      \\ ‘∀n. n < LENGTH ys ⇒
            ∃x. eval_to k (EL n ys) = INR (Atom x)’
        by (rw []
            \\ first_x_assum (drule_then assume_tac)
            \\ first_x_assum (drule_then assume_tac) \\ gs [])
      \\ qpat_x_assum ‘∀n. _ ⇒ ¬(n < _)’ kall_tac
      \\ qpat_x_assum ‘∀n. n < _ ⇒ _ ∨ _’ kall_tac
      \\ ‘∃j. ∀n. n < LENGTH ys ⇒
                ($= +++ v_rel) (eval_to (j + k) (EL n xs))
                               (eval_to k (EL n ys))’
        by (rpt (pop_assum mp_tac)
            \\ qid_spec_tac ‘ys’
            \\ qid_spec_tac ‘xs’
            \\ Induct \\ simp []
            \\ Cases_on ‘ys’ \\ simp []
            \\ qx_gen_tac ‘x’
            \\ rename1 ‘_ (EL _ (x::xs)) (EL _ (y::ys))’
            \\ rw []
            \\ last_x_assum drule
            \\ impl_tac
            >- (
              rw []
              \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
              \\ res_tac \\ fs [SF SFY_ss]
              \\ qexists_tac ‘j’ \\ gs [])
            \\ disch_then (qx_choose_then ‘j1’ assume_tac)
            \\ ‘0 < SUC (LENGTH ys)’ by gs []
            \\ last_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
            \\ gs []
            \\ qexists_tac ‘MAX j j1’
            \\ Cases \\ rw [arithmeticTheory.MAX_DEF]
            >- (
              ‘eval_to k y ≠ INL Diverge’
                by (strip_tac
                    \\ ‘0 < SUC (LENGTH ys)’ by gs []
                    \\ first_x_assum (drule_then assume_tac) \\ gs [])
              \\ ‘eval_to (j + k) x ≠ INL Diverge’
                by (strip_tac \\ Cases_on ‘eval_to k y’ \\ gs [])
              \\ drule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
              \\ gs [])
            \\ gs [arithmeticTheory.NOT_LESS]
            \\ rename1 ‘m < LENGTH ys’
            \\ ‘SUC m < SUC (LENGTH ys)’ by gs []
            \\ first_x_assum (drule_then assume_tac)
            \\ first_x_assum (drule_then assume_tac) \\ gs []
            \\ ‘eval_to (j1 + k) (EL m xs) ≠ INL Diverge’
              by (strip_tac \\ Cases_on ‘eval_to k (EL m ys)’ \\ gs [])
            \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
            \\ gs [])
      \\ qexists_tac ‘j’
      \\ rw [] \\ gs []
      >~ [‘MAP OUTR _’] >- (
        irule LIST_EQ \\ simp [EL_MAP]
        \\ qx_gen_tac ‘n’
        \\ strip_tac
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [v_rel_def])
      \\ rename1 ‘n < LENGTH ys’
      \\ rpt (first_x_assum (drule_all_then assume_tac))
      \\ Cases_on ‘eval_to k (EL n ys)’
      \\ Cases_on ‘eval_to (j + k) (EL n xs)’ \\ gs []
      \\ rename1 ‘v_rel v0 (Atom _)’ \\ Cases_on ‘v0’ \\ gs [v_rel_def]))
  >~ [‘Monad mop xs’] >- (
    rw [Once clean_rel_cases] \\ gs []
    \\ simp [eval_to_def, v_rel_def])
QED

Theorem clean_rel_eval:
  clean_rel x y ⇒
    ($= +++ v_rel) (eval x) (eval y)
Proof
  strip_tac
  \\ simp [eval_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  >- (
    rename1 ‘_ (eval_to k x) (eval_to j y)’
    \\ drule_all_then
      (qspec_then ‘MAX k j’ (qx_choose_then ‘m’ assume_tac)) clean_rel_eval_to
    \\ ‘eval_to (m + MAX k j) x = eval_to k x’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ ‘eval_to (MAX k j) y = eval_to j y’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ gs [])
  >- (
    rename1 ‘_ _ (eval_to j y)’
    \\ drule_all_then
      (qspec_then ‘j’ (qx_choose_then ‘m’ assume_tac)) clean_rel_eval_to \\ gs [])
  \\ rename1 ‘_ _ (eval_to k x)’
  \\ drule_all_then
     (qspec_then ‘k’ (qx_choose_then ‘m’ assume_tac)) clean_rel_eval_to
  \\ dxrule_then (qspec_then ‘m + k’ assume_tac) eval_to_mono \\ gvs []
QED

Theorem clean_rel_apply_closure[local]:
  clean_rel x y ∧
  v_rel v2 w2 ∧
  (∀x y. ($= +++ v_rel) x y ⇒ next_rel v_rel clean_rel (f x) (g y)) ⇒
    next_rel v_rel clean_rel (apply_closure x v2 f) (apply_closure y w2 g)
Proof
  rw [apply_closure_def] >> simp[with_value_def] >>
  dxrule_then assume_tac clean_rel_eval >>
  Cases_on `eval x` >> Cases_on `eval y` >> gvs[]
  >- (CASE_TAC >> gvs[]) >>
  rename1 `eval x = INR v1` >> rename1 `eval y = INR w1`
  \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [v_rel_def, dest_anyClosure_def]
  >- (
    first_x_assum irule
    \\ irule clean_rel_eval
    \\ irule clean_rel_subst \\ gs [])
  >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
      \\ ‘OPTREL clean_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘clean_rel x0 _’ mp_tac
      \\ ‘ok_bind x0’ by (rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
                          \\ last_x_assum $ dxrule_then assume_tac \\ gvs [])
      \\ rw [Once clean_rel_cases] \\ gs [ok_bind_def]
      \\ drule_then assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
      \\ gvs [EVERY_EL, EL_MAP]
      \\ first_x_assum irule
      \\ irule clean_rel_eval
      \\ irule clean_rel_subst
      \\ simp [EVERY2_MAP, LAMBDA_PROD, v_rel_def, MAP_MAP_o, combinTheory.o_DEF,
               GSYM FST_THM]
      \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EVERY_EL, EL_MAP, LIST_EQ_REWRITE])
  >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
      \\ ‘OPTREL clean_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
      \\ gvs [REVERSE_APPEND] \\ IF_CASES_TAC \\ gs []
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘clean_rel x0 _’ mp_tac
      \\ ‘ok_bind x0’ by (rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
                          \\ last_x_assum $ dxrule_then assume_tac \\ gvs [])
      \\ rw [Once clean_rel_cases] \\ gs [ok_bind_def]
      \\ qpat_x_assum ‘ALOOKUP _ _ = _’ mp_tac
      \\ drule_then assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs [] \\ strip_tac
      \\ gvs [EVERY_EL, EL_MAP]
      \\ first_x_assum irule
      \\ irule clean_rel_eval
      \\ rename1 ‘clean_rel x' y'’
      \\ rename1 ‘v ∉ _’ \\ rename1 ‘subst (_ ++ _ ++ [(s2, _)]) _’
      \\ ‘v ∉ freevars (Lam s2 x')’ by (first_x_assum $ dxrule_then assume_tac \\ gvs [])
      \\ gvs [freevars_def, subst_APPEND, freevars_subst, subst1_notin_frees]
      \\ irule clean_rel_subst \\ gvs [clean_rel_subst]
      \\ simp [EVERY2_MAP, LAMBDA_PROD, v_rel_def, MAP_MAP_o, combinTheory.o_DEF,
               GSYM FST_THM]
      \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EVERY_EL, EL_MAP]
      \\ rw [MEM_EL] \\ rename1 ‘n2 < _’
      \\ ‘EL n2 (MAP FST xs) = EL n2 (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
      \\ first_assum $ irule_at Any \\ gvs [EL_MAP])
QED

Theorem clean_rel_rel_ok[local]:
  rel_ok T v_rel clean_rel
Proof
  rw [rel_ok_def, v_rel_def, clean_rel_def]
  \\ rw [clean_rel_apply_closure]
QED

Theorem clean_rel_sim_ok[local]:
  sim_ok T v_rel clean_rel
Proof
  rw [sim_ok_def, clean_rel_eval, clean_rel_subst]
QED

Theorem clean_rel_semantics:
  clean_rel x y ∧
  closed x ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ irule sim_ok_semantics \\ gs []
  \\ first_assum (irule_at Any)
  \\ qexists_tac ‘T’ \\ gs []
  \\ irule_at Any clean_rel_rel_ok
  \\ irule_at Any clean_rel_sim_ok
QED

val _ = export_theory ();
