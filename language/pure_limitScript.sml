
Theory pure_limit
Ancestors
  arithmetic list option pair pure_value
Libs
  term_tactic

(*
  limit (div,div,div,div,div,...) d = div

  limit (div,div,div,div,div,4,4,4,4,4,4,4,4,4,4,4,4,...) d = 4

  limit (1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,...) d = d

  limit is used to define eval in terms of ‘∀ k . eval_to k’
  eval_to is deterministic, hence, we wouldn't need "d" in
  limit (k -> v) d. But is convenient for the proofs.
*)

Definition limit_def:
  limit (f:num->'a) default =
    (* if there is a value x that forever repeats from some
       index k onwards in sequence f, then return that x;
       in the other case we return the default value *)
    case (some x. ∃k. ∀n. k ≤ n ⇒ f n = x) of
    | SOME x => x
    | NONE => default
End

 (*
   v_seq: num -> v
   given a certain path, v_limit tries to look into a value with k any num.
  *)
Definition v_limit_def:
  v_limit v_seq path =
    limit (λk. v_lookup path (v_seq k)) (Error', 0)
End

(**** LEMMAS for limit/v_limit algebra *****)

Theorem limit_const[simp]:
  limit (λk. x) d = x
Proof
  fs [limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  THEN1 (first_x_assum (qspec_then ‘k’ mp_tac) \\ fs [])
  \\ first_x_assum (qspec_then ‘x’ mp_tac) \\ fs []
QED

Theorem limit_eq_add:
  ∀k p x f.
    limit (λn. f (n + k)) p = x ⇒
    limit f p = x
Proof
  rw [limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  THEN1
   (first_x_assum (qspec_then ‘k'+k''’ mp_tac)
    \\ first_x_assum (qspec_then ‘k+k'+k''’ mp_tac)
    \\ fs [])
  THEN1
   (first_x_assum (qspecl_then [‘f (k+k')’,‘k'’] strip_assume_tac)
    \\ first_assum (qspecl_then [‘k+k'’] strip_assume_tac) \\ fs []
    \\ first_x_assum (qspecl_then [‘n+k’] strip_assume_tac)
    \\ rfs [] \\ rw [] \\ fs [])
  THEN1
   (last_x_assum (qspecl_then [‘x’,‘k+k'’] strip_assume_tac)
    \\ first_x_assum (qspecl_then [‘n-k’] strip_assume_tac) \\ fs []
    \\ rfs [])
QED

Theorem limit_eq_add_rewrite:
  ∀k p f.
    limit (λn. f (n + k)) p = limit f p
Proof
  rw[] >>
  irule (GSYM limit_eq_add) >>
  qexists_tac `k` >> fs[]
QED

Theorem limit_if:
  ∀x y d. limit (λk. if k = 0 then x else y (k − 1)) d = limit y d
Proof
  rw [] \\ match_mp_tac limit_eq_add
  \\ qexists_tac ‘1’ \\ fs []
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
QED

Theorem v_limit_eq_add:
  ∀k p x f.
    v_limit (λn. f (n + k)) p = x ⇒
    v_limit f p = x
Proof
  rw [v_limit_def,FUN_EQ_THM]
  \\ match_mp_tac limit_eq_add
  \\ qexists_tac ‘k’ \\ fs []
QED

Theorem v_limit_if:
  v_limit (λk. if k = 0 then a else b (k − 1)) = v_limit b
Proof
  rw [v_limit_def,FUN_EQ_THM]
  \\ qspecl_then [‘v_lookup x a’,‘λk. v_lookup x (b k)’,‘(Error',0)’] mp_tac
       (GSYM limit_if)
  \\ fs [] \\ rw [] \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM] \\ rw []
QED

Theorem v_limit_exists:
  ∀ f r m path.
    (∃k. ∀n. k ≤ n ⇒ v_lookup path (f n) = (r,m))
  ⇒ v_limit f path = (r,m)
Proof
  rw [] >> fs[v_limit_def,limit_def] >> rename1 `k1 ≤ _` >>
  DEEP_INTRO_TAC some_intro >> rw [v_lookup]
  >- (
    rename1 `k2 ≤ _` >>
    rpt (first_x_assum (qspec_then `k1 + k2` assume_tac)) >> fs[] >>
    Cases_on `f (k1 + k2)` >> fs[v_lookup]
    )
  >> (
    first_x_assum (qspecl_then [`(r,m)`,`k1`] assume_tac) >> fs[] >>
    rename1 `_ ≤ k2` >>
    first_x_assum drule >>
    Cases_on `f k2` >> fs[v_lookup]
    )
QED

Theorem v_limit_not_Error:
  v_limit f path = (r,l) ∧ r ≠ Error' ⇒
  ∃k. ∀n. k ≤ n ⇒ v_lookup path (f n) = (r,l)
Proof
  fs [v_limit_def,limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw [v_lookup_def]
  \\ metis_tac []
QED

Theorem v_limit_eqn:
  ∀ f path res.
    v_limit f path = res ⇔
    (∃k. ∀n. k ≤ n ⇒ v_lookup path (f n) = res) ∨
    (res = (Error',0) ∧ ∀ r k. ∃n. k ≤ n ∧ v_lookup path (f n) ≠ r)
Proof
  rw[v_limit_def, limit_def] >>
  DEEP_INTRO_TAC some_intro >> rw[] >> eq_tac >> rw[]
  >- (DISJ1_TAC >> goal_assum drule)
  >- (
    rename1 `k1 ≤ _` >>
    rpt (first_x_assum (qspec_then `k + k1` assume_tac)) >>
    gvs[]
    )
  >- (
    first_x_assum (qspecl_then [`x`,`k`] assume_tac) >> fs[] >>
    first_x_assum drule >> gvs[]
    )
  >- (
    first_x_assum (qspecl_then [`res`,`k`] assume_tac) >> fs[] >>
    first_x_assum drule >> gvs[]
    )
QED

Theorem limit_not_default:
  limit f d = x ∧ x ≠ d ⇒ ∃k. ∀n. k ≤ n ⇒ f n = x
Proof
  fs [limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ qexists_tac ‘k’ \\ fs []
QED

Theorem limit_eq_imp:
  limit f d = x ∧ (∀n. k ≤ n ⇒ f n = y) ⇒ x = y
Proof
  rw [] \\ fs [limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  THEN1 (rpt (first_x_assum (qspec_then ‘k+k'’ mp_tac)) \\ fs [])
  \\ first_x_assum (qspecl_then [‘y’,‘k’] mp_tac) \\ rw []
  \\ res_tac
QED

Theorem limit_intro:
  ∀ f d x. (∃k. ∀n. k ≤ n ⇒ f n = x) ⇒ limit f d = x
Proof
  rw[limit_def] >>
  DEEP_INTRO_TAC some_intro >> rw[]
  >- (
    first_x_assum (qspec_then `k + k'` assume_tac) >>
    first_x_assum (qspec_then `k + k'` assume_tac) >>
    fs[]
    )
  >- (
    first_x_assum (qspecl_then [`x`,`k`] assume_tac) >> fs[] >>
    first_x_assum drule >>
    fs[]
    )
QED

Theorem limit_intro_alt:
  ∀ f d x lim . limit f d = lim ∧ (∃k. ∀n. k ≤ n ⇒ f n = x) ⇒ lim = x
Proof
  rw[] >> irule limit_intro >>
  goal_assum drule
QED

Theorem limit_eq_IMP:
  ∀ f g d.
    (∃k. ∀n. k ≤ n ⇒ f n = g n)
  ⇒ limit f d = limit g d
Proof
  rw[limit_def] >>
  DEEP_INTRO_TAC some_intro >> rw[]
  >- (
    rename1 `k1 ≤ _` >>
    DEEP_INTRO_TAC some_intro >> rw[]
    >- (
      rename1 `k2 ≤ _` >>
      rpt (first_x_assum (qspec_then `k + k1 + k2` assume_tac)) >> gvs[]
      )
    >- (
      first_x_assum (qspecl_then [`x`,`k + k1`] assume_tac) >> fs[] >>
      rename1 `_ ≤ k3` >>
      rpt (first_x_assum (qspec_then `k3` assume_tac)) >> gvs[]
      )
    )
  >- (
    DEEP_INTRO_TAC some_intro >> rw[] >> rename1 `k1 ≤ _` >>
    first_x_assum (qspecl_then [`x`,`k + k1`] assume_tac) >> fs[] >>
    rename1 `_ ≤ k2` >>
    rpt (first_x_assum (qspec_then `k2` assume_tac)) >> gvs[]
    )
QED

Theorem limit_eq_add_IMP:
  ∀ f g c d.
    (∃k. ∀n. k ≤ n ⇒ f (n + c) = g n)
  ⇒ limit f d = limit g d
Proof
  rw[] >>
  qspecl_then [`c`,`d`,`f`] assume_tac (GSYM limit_eq_add_rewrite) >> fs[] >>
  irule limit_eq_IMP >> fs[] >>
  goal_assum drule
QED

Theorem v_limit_eq_IMP:
  ∀ f g path.
    (∃k. ∀n. k ≤ n ⇒ v_lookup path (f n) = v_lookup path (g n))
  ⇒ v_limit f path = v_limit g path
Proof
  rw[v_limit_def] >>
  irule limit_eq_IMP >>
  qexists_tac `k` >>
  fs[]
QED

