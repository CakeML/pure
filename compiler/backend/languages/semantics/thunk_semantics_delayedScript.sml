open HolKernel Parse boolLib bossLib BasicProvers intLib;
open stringTheory optionTheory sumTheory pairTheory listTheory rich_listTheory
     alistTheory itreeTheory thunkLangTheory thunkLang_primitivesTheory
     thunk_semanticsTheory;

val _ = new_theory "thunk_semantics_delayed";

val _ = set_grammar_ancestry ["thunkLang", "thunk_semantics"];

Definition next_delayed_def:
  next_delayed (k:num) sv stack (state:state) =
    case sv of
      INL Diverge => Div
    | INL _ => Err
    | INR v =>
      case v of
        Monadic mop vs => (
          if mop = Ret ∧ LENGTH vs = 1 then
            with_value (HD vs) (λv.
              if ¬is_anyThunk v then Err else
              case stack of
                Done => Ret
              | BC f fs =>
                  if k = 0 then Div else
                    apply_closure f v (λw. next_delayed (k - 1) w fs state)
              | HC f fs =>
                  if k = 0 then Div else next_delayed (k - 1) sv fs state)
          else if mop = Raise ∧ LENGTH vs = 1  then
            with_value (HD vs) (λv.
              if ¬is_anyThunk v then Err else
              case stack of
                Done => Ret
              | BC f fs =>
                  if k = 0 then Div else next_delayed (k - 1) sv fs state
              | HC f fs =>
                  if k = 0 then Div else
                  apply_closure f v (λw. next_delayed (k - 1) w fs state))
          else if mop = Bind ∧ LENGTH vs = 2 then
            (let m = EL 0 vs in
             let f = EL 1 vs in
               if k = 0 then Div else
                 next_delayed (k - 1) (eval m) (BC f stack) state)
          else if mop = Handle ∧ LENGTH vs = 2 then
            (let m = EL 0 vs in
             let f = EL 1 vs in
               if k = 0 then Div else
                 next_delayed (k - 1) (eval m) (HC f stack) state)
          else if mop = Act ∧ LENGTH vs = 1 then
            (with_atoms vs (λas.
               case HD as of
                 Msg channel content => Act (channel, content) stack state
               | _ => Err))
          else if mop = Alloc ∧ LENGTH vs = 2 then
            (case result_map eval vs of
               INR [vl; v] =>
                (if ¬is_anyThunk v then Err else
                 (case get_atoms [vl] of
                    SOME [Int len] =>
                      let n = if len < 0 then 0 else Num len in
                      let new_state = state ++ [REPLICATE n v] in
                      if k = 0 then Div else
                      next_delayed (k-1)
                        (INR $ Monadic Ret [Delay $ Lit (Loc (LENGTH state))])
                        stack new_state
                  | _ => Err))
             | INL Diverge => Div
             | _ => Err)
          else if mop = Length ∧ LENGTH vs = 1 then
            (with_atoms vs (λas.
               case HD as of
                 Loc n =>
                   (if LENGTH state ≤ n then Err else
                    if k = 0 then Div else
                      next_delayed (k-1)
                        (INR $ Monadic Ret [
                            Delay $ Lit (Int (& (LENGTH (EL n state))))])
                        stack state)
               | _ => Err))
          else if mop = Deref ∧ LENGTH vs = 2 then
            (with_atoms vs (λas.
               case (EL 0 as, EL 1 as) of
                 (Loc n, Int i) =>
                   (if LENGTH state ≤ n then Err else
                    if k = 0 then Div else
                    if 0 ≤ i ∧ i < & LENGTH (EL n state) then
                      next_delayed (k - 1)
                        (INR $ Monadic Ret [Value $ EL (Num i) (EL n state)])
                        stack state
                    else
                      next_delayed (k - 1)
                        (INR $ Monadic Raise [Delay $ Cons "Subscript" []])
                        stack state)
               | _ => Err))
          else if mop = Update ∧ LENGTH vs = 3 then
            (case result_map eval vs of
               INR [vl; vi; v] =>
                 (if ¬is_anyThunk v then Err else
                    (case get_atoms [vl; vi] of
                       SOME [Loc n; Int i] =>
                         if LENGTH state ≤ n then Err else
                         if k = 0 then Div else
                         if 0 ≤ i ∧ i < & LENGTH (EL n state) then
                           let new_state =
                             LUPDATE (LUPDATE v (Num i) (EL n state)) n state
                           in next_delayed (k - 1)
                                (INR $ Monadic Ret [Delay $ Cons "" []])
                                stack new_state
                         else
                           next_delayed (k - 1)
                             (INR $ Monadic Raise [Delay $ Cons "Subscript" []])
                             stack state
                     | _ => Err))
             | INL Diverge => Div
             | _ => Err)
          else Err)
      | _ => Err
End

Definition next_action_delayed_def:
  next_action_delayed sv stack state =
    case some k. next_delayed k sv stack state ≠ Div of
      NONE => Div
    | SOME k => next_delayed k sv stack state
End

Definition interp'_delayed_def:
  interp'_delayed =
    itree_unfold_err
      (λ(sv,stack,state).
        case next_action_delayed sv stack state of
          Ret => Ret' pure_semantics$Termination
        | Err => Ret' pure_semantics$Error
        | Div => Div'
        | Act a new_stack new_state =>
            Vis' a
              (λy. (INR $ Monadic Ret [Delay $ Lit (Str y)],
                    new_stack, new_state)))
      ((λ_ ret. STRLEN ret ≤ max_FFI_return_size),
       pure_semantics$FinalFFI,
       λs. pure_semantics$FinalFFI s pure_semantics$FFI_failure)
End

Definition interp_delayed:
  interp_delayed sv stack state = interp'_delayed (sv, stack, state)
End

Theorem interp_delayed_def:
  interp_delayed sv stack state =
    case next_action_delayed sv stack state of
      Ret => Ret pure_semantics$Termination
    | Div => Div
    | Err => Ret pure_semantics$Error
    | Act a new_stack new_state =>
        Vis a (λs. case s of
            INL x =>
              Ret $ pure_semantics$FinalFFI a x
          | INR y =>
              if STRLEN y ≤ max_FFI_return_size then
                interp_delayed (INR $ Monadic Ret [Delay $ Lit (Str y)])
                               new_stack new_state
              else Ret $ pure_semantics$FinalFFI a pure_semantics$FFI_failure)
Proof
  rw [Once interp_delayed, interp'_delayed_def]
  \\ once_rewrite_tac [itree_unfold_err] \\ gvs []
  \\ CASE_TAC \\ gvs [combinTheory.o_DEF, FUN_EQ_THM] \\ rw []
  \\ CASE_TAC \\ gvs [] \\ CASE_TAC \\ gvs []
  \\ rw [Once interp_delayed, interp'_delayed_def]
QED

Definition semantics_delayed_def:
  semantics_delayed e stack state = interp_delayed (eval e) stack state
End

Definition itree_of_delayed_def:
  itree_of_delayed e = semantics_delayed e Done []
End

Theorem next_delayed_less_eq:
  ∀n e k st m.
    next_delayed n e k st ≠ Div ∧
    n ≤ m ⇒
      next_delayed n e k st = next_delayed m e k st
Proof
  recInduct next_delayed_ind \\ rw []
  \\ ntac 2 $ pop_assum mp_tac
  \\ once_rewrite_tac [next_delayed_def]
  \\ TOP_CASE_TAC \\ gvs [] \\ TOP_CASE_TAC \\ gvs []
  \\ rename1 ‘s = Ret’
  \\ Cases_on ‘s = Bind’ >- (gvs [] \\ rw [])
  \\ Cases_on ‘s = Handle’ >- (gvs [] \\ rw [])
  \\ Cases_on ‘s = Act’ >- (gvs [] \\ rw [])
  \\ Cases_on ‘s = Raise’ \\ gvs []
  >- (
    IF_CASES_TAC \\ gvs [] \\ simp [with_value_def]
    \\ ntac 3 (TOP_CASE_TAC \\ gvs [])
    >- (IF_CASES_TAC \\ gvs [] \\ first_x_assum drule \\ rw [])
    \\ simp [apply_closure_def, with_value_def] \\ rpt $ TOP_CASE_TAC \\ gvs []
    \\ first_x_assum drule \\ rw [])
  \\ Cases_on ‘s = Ret’ \\ gvs []
  >- (
    IF_CASES_TAC \\ gvs [] \\ simp [with_value_def]
    \\ ntac 3 (reverse TOP_CASE_TAC \\ gvs [])
    >- (IF_CASES_TAC \\ gvs [] \\ first_x_assum drule \\ rw [])
    \\ simp [apply_closure_def, with_value_def] \\ rpt $ TOP_CASE_TAC \\ gvs []
    \\ first_x_assum drule \\ rw [])
  \\ Cases_on ‘s = Alloc’ \\ gvs []
  >- (
    IF_CASES_TAC \\ gvs [] \\ rw [with_atoms_def, with_value_def]
    \\ rpt (TOP_CASE_TAC \\ gvs []) \\ first_x_assum drule \\ simp [])
  \\ Cases_on ‘s = Length’ \\ gvs []
  >- (
    IF_CASES_TAC \\ gvs [] \\ rw [with_atoms_def]
    \\ ntac 5 (TOP_CASE_TAC \\ gvs [])
    \\ first_x_assum irule \\ simp [] \\ qexists_tac ‘[Loc n]’ \\ simp [])
  \\ Cases_on ‘s = Deref’ \\ gvs []
  >- (
    IF_CASES_TAC \\ gvs [] \\ rw [with_atoms_def]
    \\ ntac 7 (TOP_CASE_TAC \\ gvs [])
    \\ first_x_assum irule \\ simp []
    \\ qexists_tac ‘[Loc n; Int i]’ \\ simp [])
  \\ Cases_on ‘s = Update’ \\ gvs []
  >- (
    IF_CASES_TAC \\ gvs [] \\ rw [with_atoms_def, with_value_def]
    \\ rpt (TOP_CASE_TAC \\ gvs [])
    \\ first_x_assum irule \\ simp []
    \\ qexists_tac ‘[Loc n; Int i]’ \\ simp [])
QED

Theorem next_delayed_next_delayed:
  next_delayed n e k st ≠ Div ∧ next_delayed m e k st ≠ Div ⇒
  next_delayed n e k st = next_delayed m e k st
Proof
  metis_tac [arithmeticTheory.LESS_EQ_CASES, next_delayed_less_eq]
QED

Definition sim_ok_delayed_def:
  sim_ok_delayed allow_error Rv Re ⇔
    (∀x y.
       Re x y ∧
       (¬allow_error ⇒ eval x ≠ INL Type_error) ⇒
         ($= +++ Rv) (eval x) (eval y)) ∧
    (∀vs ws x y.
       LIST_REL Rv (MAP SND vs) (MAP SND ws) ∧
       MAP FST vs = MAP FST ws ∧
       EVERY (λ(n,v). n ∈ freevars x ⇒ is_anyThunk v) vs ∧
       Re x y ⇒
         Re (subst vs x) (subst ws y))
End

Definition cont_rel_delayed_def[simp]:
  cont_rel_delayed Re Done Done = T ∧
  cont_rel_delayed Re (BC v c) (BC w d) = (Re v w ∧ cont_rel_delayed Re c d) ∧
  cont_rel_delayed Re (HC v c) (HC w d) = (Re v w ∧ cont_rel_delayed Re c d) ∧
  cont_rel_delayed Re _ _ = F
End

Definition state_rel_delayed_def:
  state_rel_delayed Rv =
    LIST_REL (LIST_REL (λv w. is_anyThunk v ∧ Rv v w))
End

Definition next_rel_delayed_def[simp]:
  next_rel_delayed Rv Re (thunk_semantics$Act a c s)
                         (thunk_semantics$Act b d t) =
    (a = b ∧ cont_rel_delayed Re c d ∧ state_rel_delayed Rv s t) ∧
  next_rel_delayed Rv Re Ret Ret = T ∧
  next_rel_delayed Rv Re Div Div = T ∧
  next_rel_delayed Rv Re Err Err = T ∧
  next_rel_delayed Rv Re (_: (string # string) next_res) _ = F
End

Definition rel_ok_delayed_def:
  rel_ok_delayed allow_error Rv Re ⇔
    (∀v w. Rv v w ⇒ (is_anyThunk v ⇔ is_anyThunk w)) ∧
    (∀v1 w1 v2 w2 f g.
       Re v1 w1 ∧
       Rv v2 w2 ∧
       (¬allow_error ⇒
          apply_closure v1 v2 f ≠ Err ∧
          f (INL Type_error) = Err) ∧
       is_anyThunk v2 ∧
       (∀(x : err + v) y.
              ($= +++ Rv) x y ∧
              (¬allow_error ⇒ f x ≠ Err) ⇒
                next_rel_delayed Rv Re (f x) (g y)
                ) ⇒
         next_rel_delayed Rv Re (apply_closure v1 v2 f)
                                (apply_closure w1 w2 g)) ∧
    (∀s x w.
       Rv (Closure s x) w ⇒
         (∃t y. w = Closure t y) ∨ (∃g m. w = Recclosure g m)) ∧
    (∀f n w.
       Rv (Recclosure f n) w ⇒
         (∃g m. w = Recclosure g m) ∨ (∃t y. w = Closure t y)) ∧
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
       x = y ⇒ Rv (Monadic s [Delay $ Lit x])
                  (Monadic s [Delay $ Lit y])) ∧
    (∀s t.
       Rv (Monadic s [Delay $ Cons t []])
          (Monadic s [Delay $ Cons t []])) ∧
    (∀s x y.
       Rv x y ∧
       is_anyThunk x ⇒
         Rv (Monadic s [Value x])
            (Monadic s [Value y])) ∧
    (∀mop vs w.
       Rv (Monadic mop vs) w ⇒
         (∃ws. w = Monadic mop ws ∧
               LIST_REL Re vs ws))
End

Theorem rel_ok_delayed_get_atoms:
  ∀x y.
    rel_ok_delayed ae Rv Re ∧
    LIST_REL Rv x y ∧
    (∀z. MEM z x ⇒ ∀w. z ≠ DoTick w) ⇒
       get_atoms x = get_atoms y
Proof
  ho_match_mp_tac get_atoms_ind \\ rw [] \\ fs [rel_ok_delayed_def] \\ gvs []
  >~ [ ‘get_atoms (DoTick _::_)’] >- (
    gvs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, SF DNF_ss])
  \\ qpat_x_assum ‘∀v w. Rv v w ⇒ (is_anyThunk v ⇔ is_anyThunk w)’ kall_tac
  \\ rpt (first_x_assum (drule_then assume_tac)) \\ gvs [get_atoms_def]
  \\ metis_tac []
QED

Theorem sim_ok_delayed_next_delayed:
  ∀k v c s w d t.
    rel_ok_delayed allow_error Rv Re ∧
    sim_ok_delayed allow_error Rv Re ∧
    ($= +++ Rv) v w ∧
    cont_rel_delayed Re c d ∧
    state_rel_delayed Rv s t ∧
    (¬allow_error ⇒ next_delayed k v c s ≠ Err) ⇒
      next_rel_delayed Rv Re (next_delayed k v c s) (next_delayed k w d t)
Proof
  ho_match_mp_tac next_delayed_ind \\ rw []
  \\ qpat_x_assum ‘(_ +++ _) _ _’ mp_tac
  \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ simp []
  >- (
    rw [next_delayed_def]
    \\ CASE_TAC \\ simp [])
  \\ rename1 ‘Rv v w’
  \\ Cases_on ‘(∃s x. v = Closure s x) ∨
               (∃f n. v = Recclosure f n) ∨
               (∃x. v = Thunk x) ∨ (∃x. v = Atom x) ∨
               (∃nm vs. v = Constructor nm vs)’
  >- (
    qpat_x_assum ‘rel_ok_delayed _ _ _’ mp_tac \\ rw [rel_ok_delayed_def]
    \\ rpt (first_x_assum (drule_all_then assume_tac)) \\ rw [] \\ fs []
    \\ simp [next_delayed_def])
  \\ Cases_on ‘∃x. v = DoTick x’
  >- (
    qpat_x_assum ‘rel_ok_delayed _ _ _’ mp_tac \\ rw [rel_ok_delayed_def]
    \\ gvs [Once next_delayed_def]
    \\ rpt (first_x_assum (drule_all_then assume_tac)) \\ rw [] \\ fs []
    \\ simp [Once next_delayed_def] \\ simp [Once next_delayed_def])
  \\ rfs []
  \\ ‘∃mop vs. v = Monadic mop vs’ by (
    ntac 5 (pop_assum mp_tac) \\ Cases_on ‘v’ \\ simp [] \\ fs [])
  \\ rw []
  \\ ‘∃ws. w = Monadic mop ws ∧ LIST_REL Re vs ws’
    by (qpat_x_assum ‘Rv _ _’ mp_tac
        \\ qpat_x_assum ‘rel_ok_delayed _ _ _’ mp_tac
        \\ rw [rel_ok_delayed_def]
        \\ rpt (first_x_assum drule) \\ rw [])
  \\ rw []
  \\ drule_then assume_tac LIST_REL_LENGTH
  \\ once_rewrite_tac [next_delayed_def] \\ simp []
  \\ IF_CASES_TAC \\ simp []
  >- ((* Ret *)
    gvs [LENGTH_EQ_NUM_compute] \\ simp [with_value_def] \\ rename1 ‘Re v w’
    \\ ‘($= +++ Rv) (eval v) (eval w)’ by (
      fs [rel_ok_delayed_def] \\ first_x_assum drule \\ rw []
      \\ gvs [sim_ok_delayed_def] \\ first_x_assum irule \\ simp []
      \\ rw [] \\ CCONTR_TAC \\ fs [Once next_delayed_def, with_value_def])
    \\ Cases_on ‘eval v’ \\ Cases_on ‘eval w’ \\ gvs [] >- (CASE_TAC \\ gvs [])
    \\ ‘is_anyThunk y ⇔ is_anyThunk y'’ by gvs [rel_ok_delayed_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ rw [] \\ reverse $ Cases_on ‘c’ \\ Cases_on ‘d’ \\ gvs [] \\ rw []
    >- (
      first_x_assum irule \\ rw [SF SFY_ss]
      \\ gvs [Once next_delayed_def, with_value_def])
    \\ fs [rel_ok_delayed_def]
    \\ first_x_assum irule \\ rw [] \\ gvs []
    >- (first_x_assum drule \\ rw [])
    \\ fs [Once next_delayed_def, with_value_def])
  \\ IF_CASES_TAC
  >- ((* Raise *)
    gvs [LENGTH_EQ_NUM_compute] \\ simp [with_value_def] \\ rename1 ‘Re v w’
    \\ ‘($= +++ Rv) (eval v) (eval w)’ by (
      fs [rel_ok_delayed_def] \\ first_x_assum drule \\ rw []
      \\ gvs [sim_ok_delayed_def] \\ first_x_assum irule \\ simp []
      \\ rw [] \\ CCONTR_TAC \\ fs [Once next_delayed_def, with_value_def])
    \\ Cases_on ‘eval v’ \\ Cases_on ‘eval w’ \\ gvs [] >- (CASE_TAC \\ gvs [])
    \\ ‘is_anyThunk y ⇔ is_anyThunk y'’ by gvs [rel_ok_delayed_def]
    \\ rw [] \\ Cases_on ‘c’ \\ Cases_on ‘d’ \\ gvs [] \\ rw []
    >- (first_x_assum irule \\ rw [SF SFY_ss]
        \\ gvs [Once next_delayed_def, with_value_def])
    \\ fs [rel_ok_delayed_def]
    \\ first_x_assum irule \\ rw [] \\ gvs []
    >- (first_x_assum drule \\ rw [])
    \\ fs [Once next_delayed_def, with_value_def])
  \\ IF_CASES_TAC
  >- ((* Bind *)
    rw []
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2 ⇔ x = 0 ∨ x = 1”]
    \\ fs [SF DNF_ss]
    \\ first_x_assum irule \\ rw []
    \\ fs [Once next_delayed_def]
    \\ fs [sim_ok_delayed_def]
    \\ first_x_assum irule \\ simp []
    \\ fs [rel_ok_delayed_def] \\ first_x_assum drule \\ rw []
    \\ fs [Once next_delayed_def]
    \\ Cases_on ‘eval h’ \\ gvs [] \\ Cases_on ‘x’ \\ gvs [])
  \\ IF_CASES_TAC
  >- ((* Handle *)
    rw []
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2 ⇔ x = 0 ∨ x = 1”]
    \\ fs [SF DNF_ss]
    \\ first_x_assum irule \\ rw []
    \\ fs [Once next_delayed_def]
    \\ fs [sim_ok_delayed_def]
    \\ first_x_assum irule \\ simp []
    \\ fs [rel_ok_delayed_def] \\ first_x_assum drule \\ rw []
    \\ fs [Once next_delayed_def]
    \\ Cases_on ‘eval h’ \\ gvs [] \\ Cases_on ‘x’ \\ gvs [])
  \\ IF_CASES_TAC
  >- ((* Act *)
    rw [] \\ gvs []
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute, DECIDE “∀x. x < 1 ⇔ x = 0”]
    \\ rename1 ‘Re v w’
    \\ simp [with_atoms_def, result_map_def]
    \\ ‘¬allow_error ⇒ eval v ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ gvs [Once next_delayed_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (eval v) (eval w)’ by (
      gvs [sim_ok_delayed_def] \\ first_x_assum irule
      \\ fs [rel_ok_delayed_def] \\ first_x_assum drule \\ simp [])
    \\ Cases_on ‘eval v’ \\ Cases_on ‘eval w’ \\ gvs []
    >~ [‘eval _ = INL err’] >- (Cases_on ‘err’ \\ fs [])
    \\ rename1 ‘eval v = INR a’  \\ rename1 ‘eval w = INR b’
    \\ ‘¬allow_error ⇒ get_atoms [a] ≠ NONE’ by (
      rpt strip_tac
      \\ gvs [Once next_delayed_def, with_atoms_def, result_map_def])
    \\ ‘∀x. a = Atom x ⇒ a = b’ by (rpt strip_tac \\ gvs [rel_ok_delayed_def])
    \\ reverse (Cases_on ‘∃x. a = Atom x’) \\ gvs [get_atoms_def] >- (
      ‘get_atoms [a] = NONE’ by (Cases_on ‘a’ \\ fs [get_atoms_def])
      \\ simp []
      \\ Cases_on ‘b’ \\ gvs [get_atoms_def]
      \\ Cases_on ‘a’ \\ fs [get_atoms_def, rel_ok_delayed_def]
      \\ rpt (first_x_assum (drule_then assume_tac)) \\ rw [])
    \\ CASE_TAC \\ fs [])
  \\ IF_CASES_TAC
  >- ((* Alloc *)
    rw [] \\ gvs []
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2 ⇔ x = 0 ∨ x = 1”]
    \\ gvs [SF DNF_ss]
    \\ rename1 ‘Rv (_ _ [v1; v2]) (_ _ [w1; w2])’
    \\ gvs [with_atoms_def, result_map_def]
    \\ ‘¬allow_error ⇒ eval v1 ≠ INL Type_error ∧ eval v2 ≠ INL Type_error’
      by (rpt strip_tac \\ gvs []
          \\ gvs [Once next_delayed_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (eval v1) (eval w1)’ by (
      gvs [sim_ok_delayed_def] \\ first_x_assum irule
      \\ fs [rel_ok_delayed_def] \\ first_x_assum drule \\ simp [])
    \\ ‘($= +++ Rv) (eval v2) (eval w2)’ by (
      gvs [sim_ok_delayed_def] \\ first_x_assum irule
      \\ fs [rel_ok_delayed_def] \\ first_x_assum rev_drule \\ simp [])
    \\ ‘∀err. eval v1 = INL err ⇔ eval w1 = INL err’ by (
      Cases_on ‘eval v1’ \\ Cases_on ‘eval w1’ \\ gvs [])
    \\ ‘∀err. eval v2 = INL err ⇔ eval w2 = INL err’ by (
      Cases_on ‘eval v2’ \\ Cases_on ‘eval w2’ \\ gvs [])
    \\ IF_CASES_TAC \\ gvs [] \\ IF_CASES_TAC \\ gvs []
    \\ Cases_on ‘eval v1’ \\ gvs []
    >~ [‘eval _ = INL err’] >- (Cases_on ‘err’ \\ gvs [SF DNF_ss, EQ_IMP_THM])
    \\ Cases_on ‘eval v2’ \\ gvs []
    >~ [‘eval _ = INL err’] >- (Cases_on ‘err’ \\ gvs [SF DNF_ss, EQ_IMP_THM])
    \\ Cases_on ‘eval w1’ \\ gvs [] \\ Cases_on ‘eval w2’ \\ gvs []
    \\ rename1 ‘eval v1 = INR a’  \\ rename1 ‘eval w1 = INR b’
    \\ ‘is_anyThunk y' ⇔ is_anyThunk y'3'’ by gvs [rel_ok_delayed_def]
    \\ ‘¬allow_error ⇒ get_atoms [a] ≠ NONE’ by (
      rpt strip_tac
      \\ gvs [Once next_delayed_def, with_atoms_def, result_map_def])
    \\ ‘∀x. a = Atom x ⇒ a = b’ by (rpt strip_tac \\ gvs [rel_ok_delayed_def])
    \\ reverse (Cases_on ‘∃x. a = Atom x’) \\ gvs [get_atoms_def]
    >- (
      ‘get_atoms [a] = NONE’ by (Cases_on ‘a’ \\ fs [get_atoms_def])
      \\ simp []
      \\ Cases_on ‘b’ \\ gvs [get_atoms_def]
      \\ Cases_on ‘a’ \\ fs [get_atoms_def, rel_ok_delayed_def]
      \\ rpt (first_x_assum (drule_then assume_tac)) \\ rw [])
    \\ IF_CASES_TAC \\ gvs []
    \\ BasicProvers.TOP_CASE_TAC \\ gvs []
    \\ BasicProvers.TOP_CASE_TAC \\ gvs []
    \\ first_x_assum irule
    \\ gvs [state_rel_delayed_def, LIST_REL_REPLICATE_same, LIST_REL_EL_EQN,
            rel_ok_delayed_def]
    \\ rw [] \\ gvs []
    \\ qpat_x_assum ‘next_delayed _ _ _ _ ≠ _’ mp_tac
    \\ simp [Once next_delayed_def, with_atoms_def, result_map_def,
             get_atoms_def, with_value_def])
  \\ IF_CASES_TAC
  >- ((* Length *)
    rw [] \\ gvs []
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute, DECIDE “∀x. x < 1 ⇔ x = 0”]
    \\ rename1 ‘Re v w’
    \\ simp [with_atoms_def, result_map_def]
    \\ ‘¬allow_error ⇒ eval v ≠ INL Type_error’ by (
      rpt strip_tac \\ gvs []
      \\ gvs [Once next_delayed_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (eval v) (eval w)’ by (
      gvs [sim_ok_delayed_def] \\ first_x_assum irule
      \\ fs [rel_ok_delayed_def] \\ first_x_assum drule \\ simp [])
    \\ Cases_on ‘eval v’ \\ Cases_on ‘eval w’ \\ gvs []
    >~ [‘eval _ = INL err’] >- (Cases_on ‘err’ \\ gvs [])
    \\ rename1 ‘eval v = INR a’  \\ rename1 ‘eval w = INR b’
    \\ ‘¬allow_error ⇒ get_atoms [a] ≠ NONE’ by (
      rpt strip_tac
      \\ gvs [Once next_delayed_def, with_atoms_def, result_map_def])
    \\ ‘∀x. a = Atom x ⇒ a = b’ by (rpt strip_tac \\ gvs [rel_ok_delayed_def])
    \\ reverse (Cases_on ‘∃x. a = Atom x’) \\ gvs [get_atoms_def]
    >- (
      ‘get_atoms [a] = NONE’ by (Cases_on ‘a’ \\ fs [get_atoms_def])
      \\ simp []
      \\ Cases_on ‘b’ \\ gvs [get_atoms_def]
      \\ Cases_on ‘a’ \\ fs [get_atoms_def, rel_ok_delayed_def]
      \\ rpt (first_x_assum (drule_then assume_tac)) \\ rw [])
    \\ ‘LENGTH s = LENGTH t’ by gvs [state_rel_delayed_def, LIST_REL_EL_EQN]
    \\ Cases_on ‘k = 0’ \\ fs [] \\ CASE_TAC \\ fs []
    \\ IF_CASES_TAC \\ gvs []
    \\ first_x_assum (resolve_then Any irule HD) \\ simp []
    \\ gvs [state_rel_delayed_def, LIST_REL_REPLICATE_same,  LIST_REL_EL_EQN,
            rel_ok_delayed_def]
    \\ strip_tac
    \\ gvs [Once next_delayed_def,
            with_atoms_def, result_map_def, get_atoms_def])
  \\ IF_CASES_TAC
  >- ((* Deref *)
    rw [] \\ gvs []
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2 ⇔ x = 0 ∨ x = 1”]
    \\ gvs [SF DNF_ss]
    \\ rename1 ‘Rv (_ _ [v1; v2]) (_ _ [w1; w2])’
    \\ simp [with_atoms_def, result_map_def]
    \\ ‘¬allow_error ⇒ eval v1 ≠ INL Type_error’ by (
      rpt strip_tac \\ gvs []
      \\ gvs [Once next_delayed_def, with_atoms_def, result_map_def])
    \\ ‘¬allow_error ⇒ eval v2 ≠ INL Type_error’ by (
      rpt strip_tac \\ gvs []
      \\ gvs [Once next_delayed_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (eval v1) (eval w1)’ by (
      gvs [sim_ok_delayed_def] \\ first_x_assum irule
      \\ fs [rel_ok_delayed_def] \\ first_x_assum drule \\ simp [])
    \\ ‘($= +++ Rv) (eval v2) (eval w2)’ by (
      gvs [sim_ok_delayed_def] \\ first_x_assum irule
      \\ fs [rel_ok_delayed_def] \\ first_x_assum drule \\ simp [])
    \\ Cases_on ‘eval v1’ \\ Cases_on ‘eval w1’ \\ gvs []
    >~ [‘eval _ = INL err’] >- (
      Cases_on ‘err = Type_error’ \\ fs []
      \\ Cases_on ‘eval v2’ \\ Cases_on ‘eval w2’ \\ gvs []
      >~ [‘eval _ = INL err’] >- (Cases_on ‘err’ \\ fs [])
      \\ Cases_on ‘err’ \\ fs [])
    \\ Cases_on ‘eval v2’ \\ Cases_on ‘eval w2’ \\ gvs []
    >~ [‘eval _ = INL err’] >- (Cases_on ‘err’ \\ fs [])
    \\ rename1 ‘eval v1 = INR a1’  \\ rename1 ‘eval w1 = INR b1’
    \\ rename1 ‘eval v2 = INR a2’  \\ rename1 ‘eval w2 = INR b2’
    \\ ‘¬allow_error ⇒ get_atoms [a1; a2] ≠ NONE’ by (
      rpt strip_tac
      \\ gvs [Once next_delayed_def, with_atoms_def, result_map_def])
    \\ ‘∀x. a1 = Atom x ⇒ a1 = b1’ by (
      rpt strip_tac \\ gvs [rel_ok_delayed_def])
    \\ ‘∀x. a2 = Atom x ⇒ a2 = b2’ by (
      rpt strip_tac \\ gvs [rel_ok_delayed_def])
    \\ reverse (Cases_on ‘∃x. a1 = Atom x’) \\ fs []
    >- (
      Cases_on ‘∃y. b1 = Atom y’ \\ fs []
      >- (
        rw [] \\ fs [rel_ok_delayed_def]
        \\ qpat_x_assum ‘Rv a1 b1’ assume_tac
        \\ Cases_on ‘a1’ \\ fs []
        \\ rpt (first_x_assum (drule_then assume_tac)) \\ rw []
        \\ fs [get_atoms_def])
      \\ ‘get_atoms [a1; a2] = NONE’ by (Cases_on ‘a1’ \\ fs [get_atoms_def])
      \\ ‘get_atoms [b1; b2] = NONE’ by (Cases_on ‘b1’ \\ fs [get_atoms_def])
      \\ simp [])
    \\ reverse (Cases_on ‘∃x. a2 = Atom x’) \\ fs []
    >- (
      Cases_on ‘∃y. b2 = Atom y’ \\ fs []
      >- (
        rw [] \\ fs [rel_ok_delayed_def]
        \\ qpat_x_assum ‘Rv a2 b2’ assume_tac
        \\ Cases_on ‘a2’ \\ fs []
        \\ rpt (first_x_assum (drule_then assume_tac)) \\ rw []
        \\ fs [get_atoms_def])
      \\ rw []
      \\ ‘get_atoms [a2] = NONE’ by (Cases_on ‘a2’ \\ fs [get_atoms_def])
      \\ ‘get_atoms [b2] = NONE’ by (Cases_on ‘b2’ \\ fs [get_atoms_def])
      \\ gvs [] \\ simp [get_atoms_def])
    \\ rw [] \\ simp [get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ ‘LENGTH s = LENGTH t’ by fs [state_rel_delayed_def, LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ qpat_x_assum ‘¬_ ⇒ next_delayed _ _ _ _ ≠ _’ mp_tac
    \\ simp [Once next_delayed_def, with_atoms_def, result_map_def,
             get_atoms_def]
    \\ strip_tac
    \\ ‘LENGTH (EL n t) = LENGTH (EL n s)’
      by gvs [state_rel_delayed_def, LIST_REL_EL_EQN]
    \\ rpt (first_x_assum (resolve_then Any assume_tac HD) \\ fs [])
    \\ IF_CASES_TAC \\ fs []
    >- (
      first_x_assum irule \\ gvs [SF SFY_ss]
      \\ fs [rel_ok_delayed_def]
      \\ first_x_assum irule
      \\ qpat_x_assum ‘state_rel_delayed _ _ _’ mp_tac
      \\ rw [state_rel_delayed_def]
      \\ fs [Once LIST_REL_EL_EQN]
      \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ gvs [LIST_REL_EL_EQN]
      \\ first_x_assum $ qspec_then ‘Num i’ assume_tac \\ gvs []
      \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ gvs [])
    \\ first_x_assum irule \\ gvs [SF SFY_ss]
    \\ fs [rel_ok_delayed_def] \\ intLib.COOPER_TAC)
  \\ IF_CASES_TAC
  >- ((* Update *)
    rw [] \\ gvs []
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 3 ⇔ x = 0 ∨ x = 1 ∨ x = 2”]
    \\ gvs [SF DNF_ss]
    \\ rename1 ‘Rv (_ _ [v1; v2; v3]) (_ _ [w1; w2; w3])’
    \\ simp [with_atoms_def, result_map_def]
    \\ ‘¬allow_error ⇒ eval v1 ≠ INL Type_error ∧
          eval v2 ≠ INL Type_error ∧eval v3 ≠ INL Type_error’ by (
      rpt strip_tac \\ gvs []
      \\ gvs [Once next_delayed_def, with_atoms_def, result_map_def])
    \\ ‘($= +++ Rv) (eval v1) (eval w1)’ by (
      gvs [sim_ok_delayed_def] \\ first_x_assum irule
      \\ fs [rel_ok_delayed_def] \\ first_x_assum drule \\ simp [])
    \\ ‘($= +++ Rv) (eval v2) (eval w2)’ by (
      gvs [sim_ok_delayed_def] \\ first_x_assum irule
      \\ fs [rel_ok_delayed_def] \\ first_x_assum rev_drule \\ simp [])
    \\ ‘($= +++ Rv) (eval v3) (eval w3)’ by (
      gvs [sim_ok_delayed_def] \\ first_x_assum irule
      \\ fs [rel_ok_delayed_def] \\ first_x_assum rev_drule \\ simp [])
    \\ ‘∀err. eval v1 = INL err ⇔ eval w1 = INL err’ by (
      Cases_on ‘eval v1’ \\ Cases_on ‘eval w1’ \\ gvs [])
    \\ ‘∀err. eval v2 = INL err ⇔ eval w2 = INL err’ by (
      Cases_on ‘eval v2’ \\ Cases_on ‘eval w2’ \\ gvs [])
    \\ ‘∀err. eval v3 = INL err ⇔ eval w3 = INL err’ by (
      Cases_on ‘eval v3’ \\ Cases_on ‘eval w3’ \\ gvs [])
    \\ IF_CASES_TAC \\ gvs [] \\ IF_CASES_TAC \\ gvs []
    \\ Cases_on ‘eval v1’ \\ gvs []
    >~ [‘eval _ = INL err’] >- (Cases_on ‘err’ \\ gvs [EQ_IMP_THM, SF DNF_ss])
    \\ Cases_on ‘eval v2’ \\ gvs []
    >~ [‘eval _ = INL err’] >- (Cases_on ‘err’ \\ gvs [EQ_IMP_THM, SF DNF_ss])
    \\ Cases_on ‘eval v3’ \\ gvs []
    >~ [‘eval _ = INL err’] >- (Cases_on ‘err’ \\ gvs [EQ_IMP_THM, SF DNF_ss])
    \\ Cases_on ‘eval w1’ \\ gvs [] \\ Cases_on ‘eval w2’ \\ gvs []
    \\ Cases_on ‘eval w3’ \\ gvs []
    \\ rename1 ‘eval v1 = INR a1’ \\ rename1 ‘eval w1 = INR b1’
    \\ rename1 ‘eval v2 = INR a2’ \\ rename1 ‘eval w2 = INR b2’
    \\ ‘is_anyThunk y'' ⇔ is_anyThunk y'5'’ by gvs [rel_ok_delayed_def]
    \\ ‘¬allow_error ⇒ get_atoms [a1; a2] ≠ NONE’ by (
      rpt strip_tac
      \\ gvs [Once next_delayed_def, with_atoms_def, result_map_def])
    \\ ‘∀x. a1 = Atom x ⇒ a1 = b1’ by (
      rpt strip_tac \\ gvs [rel_ok_delayed_def])
    \\ ‘∀x. a2 = Atom x ⇒ a2 = b2’ by (
      rpt strip_tac \\ gvs [rel_ok_delayed_def])
    \\ reverse (Cases_on ‘∃x. a1 = Atom x’) \\ fs []
    >- (
      Cases_on ‘∃y. b1 = Atom y’ \\ fs []
      >- (
        rw [] \\ fs [rel_ok_delayed_def]
        \\ qpat_x_assum ‘Rv a1 b1’ assume_tac
        \\ Cases_on ‘a1’ \\ fs []
        \\ rpt (first_x_assum (drule_then assume_tac)) \\ rw []
        \\ fs [get_atoms_def])
      \\ ‘get_atoms [a1; a2] = NONE’ by (Cases_on ‘a1’ \\ fs [get_atoms_def])
      \\ ‘get_atoms [b1; b2] = NONE’ by (Cases_on ‘b1’ \\ fs [get_atoms_def])
      \\ simp [])
    \\ reverse (Cases_on ‘∃x. a2 = Atom x’) \\ fs []
    >- (
      Cases_on ‘∃y. b2 = Atom y’ \\ fs []
      >- (
        rw [] \\ fs [rel_ok_delayed_def]
        \\ qpat_x_assum ‘Rv a2 b2’ assume_tac
        \\ Cases_on ‘a2’ \\ fs []
        \\ rpt (first_x_assum (drule_then assume_tac)) \\ rw []
        \\ fs [get_atoms_def])
      \\ rw []
      \\ ‘get_atoms [a2] = NONE’ by (Cases_on ‘a2’ \\ fs [get_atoms_def])
      \\ ‘get_atoms [b2] = NONE’ by (Cases_on ‘b2’ \\ fs [get_atoms_def])
      \\ gvs [] \\ simp [get_atoms_def])
    \\ rw [] \\ simp [get_atoms_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ ‘LENGTH s = LENGTH t’ by fs [state_rel_delayed_def, LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ qpat_x_assum ‘¬_ ⇒ next_delayed _ _ _ _ ≠ _’ mp_tac
    \\ simp [Once next_delayed_def, with_value_def,
             with_atoms_def, result_map_def, get_atoms_def]
    \\ fs [result_map_def, get_atoms_def]
    \\ strip_tac
    \\ ‘LENGTH (EL n t) = LENGTH (EL n s)’
      by gvs [state_rel_delayed_def, LIST_REL_EL_EQN]
    \\ IF_CASES_TAC \\ fs []
    >- (
      first_x_assum irule \\ simp [result_map_def, get_atoms_def]
      \\ gvs [state_rel_delayed_def, LIST_REL_EL_EQN, EL_LUPDATE]
      \\ rw [] \\ gvs []
      \\ rw [EL_LUPDATE] \\ fs [rel_ok_delayed_def])
    >- (last_x_assum irule \\ fs [rel_ok_delayed_def])
    >- (first_x_assum irule \\ fs [rel_ok_delayed_def]))
  \\ fs []
QED

Theorem sim_ok_delayed_next_action_delayed:
  rel_ok_delayed allow_error Rv Re ∧
  sim_ok_delayed allow_error Rv Re ∧
  ($= +++ Rv) v w ∧
  cont_rel_delayed Re c d ∧
  state_rel_delayed Rv s t ∧
  (¬allow_error ⇒ next_action_delayed v c s ≠ Err) ⇒
    next_rel_delayed Rv Re (next_action_delayed v c s)
                           (next_action_delayed w d t)
Proof
  strip_tac
  \\ rw [next_action_delayed_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ simp [PULL_FORALL]
  \\ qx_gen_tac ‘i’
  \\ qx_gen_tac ‘j’
  \\ qx_gen_tac ‘k’
  \\ ‘∀m. ¬allow_error ⇒ next_delayed m v c s ≠ Err’ by (
    rpt strip_tac \\ gvs []
    \\ gvs [next_action_delayed_def]
    \\ qpat_x_assum ‘_ ≠ Err’ mp_tac
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ simp [PULL_EXISTS]
    \\ qexists_tac ‘m’ \\ gvs []
    \\ rw []
    \\ drule_then (qspec_then ‘m’ assume_tac) next_delayed_next_delayed
    \\ gvs [])
  \\ rw []
  >- (
    first_x_assum (qspec_then ‘i’ assume_tac)
    \\ drule_all_then assume_tac sim_ok_delayed_next_delayed \\ gvs []
    \\ drule_then (qspec_then ‘i’ mp_tac) next_delayed_next_delayed
    \\ impl_tac \\ rw []
    \\ strip_tac
    \\ Cases_on ‘next_delayed i w d t’ \\ gvs [])
  >- (
    last_x_assum (qspec_then ‘i’ assume_tac)
    \\ drule_all_then assume_tac sim_ok_delayed_next_delayed \\ gvs [SF SFY_ss])
  \\ last_x_assum (qspec_then ‘k’ assume_tac)
  \\ drule_all_then assume_tac sim_ok_delayed_next_delayed \\ gvs [SF SFY_ss]
QED

Theorem sim_ok_delayed_interp_delayed:
  rel_ok_delayed allow_error Rv Re ∧
  sim_ok_delayed allow_error Rv Re ∧
  ($= +++ Rv) v w ∧
  cont_rel_delayed Re c d ∧
  state_rel_delayed Rv s t ∧
  (¬allow_error ⇒ pure_semantics$safe_itree (interp_delayed v c s)) ⇒
    interp_delayed v c s = interp_delayed w d t
Proof
  strip_tac
  \\ rw [Once itreeTheory.itree_bisimulation]
  \\ qexists
    ‘λt1 t2.
      (¬allow_error ⇒ pure_semantics$safe_itree t1) ∧
      (t1 = t2 ∨
       ∃v c s w d t.
         interp_delayed v c s = t1 ∧
         interp_delayed w d t = t2 ∧
         ($= +++ Rv) v w ∧
         cont_rel_delayed Re c d ∧
         state_rel_delayed Rv s t)’
  \\ rw []
  >~ [‘Vis a f’] >- (
    rgs [Once pure_semanticsTheory.safe_itree_cases])
  >~ [‘interp_delayed v c s = interp_delayed w d t’] >- (
    disj2_tac \\ rpt $ irule_at Any EQ_REFL \\ simp [])
  \\ ‘¬allow_error ⇒ next_action_delayed v' c' s' ≠ Err’ by (
    rpt strip_tac \\ gvs []
    \\ rgs [Once interp_delayed_def,
            Once pure_semanticsTheory.safe_itree_cases])
  \\ drule_all sim_ok_delayed_next_action_delayed \\ strip_tac
  >- (
    qpat_x_assum ‘_ = Ret _’ mp_tac
    \\ once_rewrite_tac [interp_delayed_def]
    \\ Cases_on ‘next_action_delayed v' c' s'’
    \\ Cases_on ‘next_action_delayed w' d' t''’ \\ gvs [])
  >- (
    qpat_x_assum ‘_ = Div’ mp_tac
    \\ once_rewrite_tac[interp_delayed_def]
    \\ Cases_on ‘next_action_delayed v' c' s'’
    \\ Cases_on ‘next_action_delayed w' d' t''’
    \\ gvs [])
  >- (
    qpat_x_assum ‘_ = Vis _ _ ’ mp_tac
    \\ rw [Once interp_delayed_def]
    \\ rw [Once interp_delayed_def]
    \\ Cases_on ‘next_action_delayed v' c' s'’
    \\ Cases_on ‘next_action_delayed w' d' t''’ \\ gvs []
    \\ rw [] \\ rgs [Once pure_semanticsTheory.safe_itree_cases]
    \\ CASE_TAC \\ gvs [] \\ CASE_TAC \\ gvs []
    \\ disj2_tac
    \\ rpt (irule_at Any EQ_REFL) \\ simp []
    \\ gvs [rel_ok_delayed_def])
QED

Theorem semantics_delayed_fail:
  pure_semantics$safe_itree (semantics_delayed x c s) ⇒
    eval x ≠ INL Type_error
Proof
  simp [semantics_delayed_def, Once interp_delayed_def, next_action_delayed_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ rw [] \\ strip_tac \\ gvs []
  \\ rgs [Once next_delayed_def]
  \\ rgs [Once pure_semanticsTheory.safe_itree_cases]
QED

Theorem sim_ok_delayed_semantics_delayed:
  rel_ok_delayed allow_error Rv Re ∧
  sim_ok_delayed allow_error Rv Re ∧
  Re x y ∧
  (¬allow_error ⇒ pure_semantics$safe_itree (semantics_delayed x Done [])) ⇒
    semantics_delayed x Done [] = semantics_delayed y Done []
Proof
  strip_tac
  \\ rw [semantics_delayed_def]
  \\ irule sim_ok_delayed_interp_delayed
  \\ qpat_assum ‘sim_ok_delayed _ _ _’ (irule_at Any)
  \\ gvs [cont_rel_delayed_def, state_rel_delayed_def, sim_ok_delayed_def]
  \\ first_assum (irule_at Any) \\ gvs []
  \\ rw [] \\ gvs [semantics_delayed_fail, SF SFY_ss]
  \\ gvs [semantics_delayed_def]
QED

val _ = export_theory();
