(*
   Various lemmas about the eval and eval_to functions from pure_evalTheory
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite;
open pure_expTheory pure_valueTheory pure_eval_oldTheory
     pure_exp_lemmasTheory pure_limitTheory;

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "pure_eval_old_lemmas";

(* Premise not necessary, but convenient for drule:ing.
   TODO: surely this can be derived automatically somehow? *)
Theorem eval_op_cases:
  ∀op xs t.
    eval_op op xs = t ⇒
    (∃s. op = Cons s) ∨
    (∃x1 x2 x3. op = If ∧ xs = [x1;x2;x3]) ∨
    (∃s i x. op = Proj s i ∧ xs = [x]) ∨
    (∃a. op = AtomOp a) ∨
    (∃b. op = Lit b ∧ xs = []) ∨
    (op = If ∧ xs = []) ∨
    (∃x. op = If ∧ xs = [x]) ∨
    (∃x1 x2. op = If ∧ xs = [x1;x2]) ∨
    (∃x1 x2 x3 x4 xs'. op = If ∧ xs = x1::x2::x3::x4::xs') ∨
    (∃s n. op = IsEq s n ∧ xs = []) ∨
    (∃s n x. op = IsEq s n ∧ xs = [x]) ∨
    (∃s n x1 x2 xs'. op = IsEq s n ∧ xs = x1::x2::xs') ∨
    (∃s i. op = Proj s i ∧ xs = []) ∨
    (∃s i x1 x2 xs'. op = Proj s i ∧ xs = x1::x2::xs') ∨
    (∃b x xs'. op = Lit b ∧ xs = x::xs') ∨
    (op = Seq)
Proof
  ho_match_mp_tac eval_op_ind >> rw[]
QED

Theorem eval_eq_Cons_IMP:
  eval x = Constructor s xs ⇒
  ∃ts. eval x = eval (Cons s ts) ∧ MAP eval ts = xs ∧
       (closed x ⇒ closed (Cons s ts))
Proof
  strip_tac >>
  qexists_tac ‘GENLIST (λk. Proj s k x) (LENGTH xs)’ >>
  rw[eval_Cons,MAP_GENLIST,eval_thm,combinTheory.o_DEF,el_def] >>
  rw[LIST_EQ_REWRITE] >>
  gvs[closed_def,freevars_def,FLAT_EQ_NIL,EVERY_MEM,MEM_MAP,MEM_GENLIST,PULL_EXISTS]
QED

Theorem v_lookup_Error:
  v_lookup path Error = if path = [] then (Error',0) else (Diverge',0)
Proof
  Cases_on ‘path’ >> rw[v_lookup]
QED

Theorem v_lookup_Atom:
  v_lookup path (Atom a) = if path = [] then (Atom' a,0) else (Diverge',0)
Proof
  Cases_on ‘path’ >> rw[v_lookup]
QED

Theorem v_lookup_Closure:
  v_lookup path (Closure x e) = if path = [] then (Closure' x e,0) else (Diverge',0)
Proof
  Cases_on ‘path’ >> rw[v_lookup]
QED

Theorem v_lookup_Constructor:
  v_lookup path (Constructor x xs) =
  if path = [] then (Constructor' x,LENGTH xs)
  else
    case oEL (HD path) xs of
      NONE => (Diverge',0)
    | SOME x => v_lookup (TL path) x
Proof
  Cases_on ‘path’ >> rw[v_lookup]
QED

Theorem freevars_v_simps[simp]:
  (v ∈ freevars_v Error) = F ∧
  (v ∈ freevars_v Diverge) = F ∧
  (v ∈ freevars_v (Atom a)) = F ∧
  (v ∈ freevars_v (Closure x e)) = MEM v (FILTER ($<> x) (freevars e)) ∧
  (v ∈ freevars_v (Constructor x xs)) = (v ∈ BIGUNION(IMAGE freevars_v (set xs)))
Proof
  gvs[freevars_v_MEM,MEM_FILTER] >>
  gvs[v_lookup_Error,v_lookup_Diverge,v_lookup_Atom,v_lookup_Closure,
      v_lookup_Constructor,AllCaseEqs(), oEL_THM] >>
  conj_tac >- (eq_tac >> rw[]) >>
  rw[EQ_IMP_THM,MEM_EL,PULL_EXISTS]
  >- (goal_assum (drule_at (Pat ‘_ < _’)) >>
      simp[freevars_v_MEM] >>
      goal_assum drule >>
      rw[rich_listTheory.EL_MEM,MEM_FILTER])
  >- (gvs[freevars_v_MEM,LIST_TO_SET_FILTER] >>
      qexists_tac ‘n::path’ >>
      rw[] >>
      metis_tac[MEM_EL])
QED

Theorem eval_to_freevars_SUBSET:
  ∀k e1 v e2 x y.
    eval_to k e1 = v ∧ y ∈ freevars_v v ⇒
    MEM y (freevars e1)
Proof
  ho_match_mp_tac eval_to_ind >> rpt strip_tac
  >- (rename1 ‘Var’ >> gvs[eval_to_def])
  >- (rename1 ‘Prim’ >> gs[eval_to_def] >>
      drule eval_op_cases >> rw[] >>
      gvs[eval_op_def,AllCaseEqs(),MAP_EQ_CONS,DISJ_IMP_THM,FORALL_AND_THM,
          MEM_MAP,MEM_FLAT,PULL_EXISTS]
      >- metis_tac[]
      >- (rpt(PURE_FULL_CASE_TAC >> gvs[]) >> metis_tac[])
      >- (gvs[el_def,AllCaseEqs()] >>
          rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
          gvs[PULL_EXISTS,MEM_EL] >>
          metis_tac[])
      >- (PURE_FULL_CASE_TAC >> gvs[] >>
          rename1 ‘if XX then _ else _’ >>
          PURE_FULL_CASE_TAC >> gvs[])
      >- (gvs[is_eq_def] >>
          rpt(PURE_FULL_CASE_TAC >> gvs[])))
  >- (rename1 ‘Lam’ >> gvs[freevars_def,MEM_FILTER,eval_to_def])
  >- (
      rename1 ‘App’ >>
      gvs[freevars_def,MEM_FILTER,eval_to_def] >>
      rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
      res_tac >> fs[bind_single_def] >>
      PURE_FULL_CASE_TAC >> fs[freevars_subst] >>
      gvs[dest_Closure_def,AllCaseEqs(),MEM_FILTER,PULL_EXISTS]
      )
  >- (
      rename1 ‘Letrec’ >>
      gvs[freevars_def,MEM_FILTER,MEM_FLAT,MEM_MAP,PULL_EXISTS,eval_to_def] >>
      PURE_FULL_CASE_TAC >> gvs[] >>
      first_x_assum drule >> strip_tac >>
      fs[subst_funs_def,freevars_bind] >>
      reverse FULL_CASE_TAC >- fs[] >>
      gvs[MEM_FILTER, FDOM_FUPDATE_LIST, FRANGE_FLOOKUP, PULL_EXISTS] >>
      gvs[MEM_MAP, FORALL_PROD]
      )
QED

Theorem eval_to_Closure_freevars_SUBSET:
  ∀k e1 e2 x y.
    eval_to k e1 = Closure x e2 ∧ MEM y (freevars e2) ⇒
    x = y ∨ MEM y (freevars e1)
Proof
  rpt strip_tac >> drule eval_to_freevars_SUBSET >>
  simp[MEM_FILTER] >>
  metis_tac[]
QED

Theorem eval_Closure_closed:
  eval e1 = Closure x e2 ∧ closed e1 ⇒
  set(freevars e2) ⊆ {x}
Proof
  rw[eval_def,Once gen_v] >>
  gvs[AllCaseEqs()] >>
  gvs[v_limit_def,limit_def,AllCaseEqs()] >>
  gvs[some_def] >>
  qpat_x_assum ‘_ = _’ mp_tac >>
  SELECT_ELIM_TAC >>
  conj_tac >- metis_tac[] >>
  rw[] >>
  last_x_assum kall_tac >>
  first_x_assum(resolve_then (Pos hd) assume_tac LESS_EQ_REFL) >>
  gvs[v_lookup,AllCaseEqs()] >>
  drule eval_to_Closure_freevars_SUBSET >>
  rw[SUBSET_DEF] >>
  gvs[closed_def]
QED

Theorem eval_eq_Diverge:
  eval x = Diverge ⇔ ∀n. eval_to n x = Diverge
Proof
  fs [eval_def]
  \\ once_rewrite_tac [gen_v]
  \\ fs [AllCaseEqs()]
  \\ reverse eq_tac \\ rw []
  THEN1 (qexists_tac ‘0’ \\ fs [v_limit_def,v_lookup])
  \\ fs [v_limit_def]
  \\ drule limit_not_default \\ fs []
  \\ strip_tac \\ pop_assum mp_tac
  \\ simp [v_lookup,AllCaseEqs()] \\ rw []
  \\ Cases_on ‘k ≤ n’ \\ res_tac \\ fs []
  \\ Cases_on ‘eval_to n x = Diverge’ \\ fs []
  \\ ‘n ≤ k’ by fs []
  \\ imp_res_tac eval_to_not_diverge_mono
  \\ metis_tac [LESS_EQ_REFL]
QED

(*

CoInductive Diverges:
  (∀f x.
    Diverges (subst_funs f x) ⇒
    Diverges (Letrec f x))
  ∧
  (∀x y.
    Diverges x ⇒
    Diverges (App x y))
  ∧
  (∀x y s body.
    eval x = Closure s body ∧
    Diverges (bind s y body) ⇒
    Diverges (App x y))
  ∧
  (∀s n x.
    Diverges x ⇒
    Diverges (IsEq s n x))
  ∧
  (∀s i x.
    Diverges x ⇒
    Diverges (Proj s i x))
  ∧
  (∀s xs y ys x.
    eval x = eval (Cons s (xs ++ y::ys)) ∧
    Diverges y ⇒
    Diverges (Proj s (LENGTH xs) x))
  ∧
  (∀x y z.
    Diverges x ⇒
    Diverges (If x y z))
  ∧
  (∀x y z.
    Diverges y ∧ eval x = True ⇒
    Diverges (If x y z))
  ∧
  (∀x y z.
    Diverges z ∧ eval x = False ⇒
    Diverges (If x y z))
  ∧
  (∀a x xs.
    Diverges x ∧ MEM x xs ⇒
    Diverges (Prim (AtomOp a) xs))
End

Triviality LESS_LENGTH_IMP:
  ∀xs n. n < LENGTH xs ⇒ ∃ys y zs. xs = ys ++ y::zs ∧ LENGTH ys = n
Proof
  Induct \\ fs [] \\ Cases_on ‘n’ \\ fs []
  \\ rw [] \\ res_tac \\ gvs []
  \\ qexists_tac ‘h::ys’ \\ fs []
  \\ qexists_tac ‘y’ \\ fs []
  \\ qexists_tac ‘zs’ \\ fs []
QED

Theorem Diverges_iff:
  ∀e. eval e = Diverge ⇔ Diverges e
Proof
  rw [] \\ eq_tac
  THEN1
   (qid_spec_tac ‘e’
    \\ ho_match_mp_tac Diverges_coind
    \\ rw [] \\ reverse (Cases_on ‘e’) \\ fs []
    \\ TRY (fs [eval_thm] \\ NO_TAC)
    THEN1
     (rename [‘eval (App f x)’]
      \\ gvs [eval_thm,AllCaseEqs()]
      \\ Cases_on ‘eval f’ \\ fs [dest_Closure_def])
    \\ rename [‘eval (Prim p xs)’]
    \\ reverse (Cases_on ‘p’) \\ fs [eval_thm]
    \\ gvs [eval_Prim,DefnBase.one_line_ify NONE eval_op_def,
            AllCaseEqs(),MAP_EQ_CONS,is_eq_def,el_def,MEM_MAP]
    THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ pop_assum (assume_tac o GSYM) \\ fs []
    \\ drule eval_eq_Cons_IMP
    \\ fs [eval_thm] \\ rw [] \\ fs []
    \\ drule LESS_LENGTH_IMP \\ rw [] \\ fs []
    \\ qexists_tac ‘ys’
    \\ qexists_tac ‘y’
    \\ qexists_tac ‘zs’ \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ qabbrev_tac ‘qs = MAP eval ys’
    \\ ‘LENGTH ys = LENGTH qs’ by fs [Abbr‘qs’]
    \\ fs [EL_LENGTH_APPEND])
  \\ fs [eval_eq_Diverge,PULL_FORALL]
  \\ gen_tac \\ qid_spec_tac ‘e’ \\ qid_spec_tac ‘n’
  \\ ho_match_mp_tac eval_to_ind \\ reverse (rw [])
  \\ TRY (rename [‘Var’] \\ fs [Once Diverges_cases] \\ NO_TAC)
  \\ TRY (rename [‘Lam’] \\ fs [Once Diverges_cases] \\ NO_TAC)
  THEN1
   (rw [eval_to_def] \\ fs [AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    \\ last_x_assum mp_tac
    \\ simp [Once Diverges_cases] \\ fs [])
  THEN1
   (rw [eval_to_def] \\ fs [AND_IMP_INTRO]
    \\ qpat_x_assum ‘Diverges _’ mp_tac
    \\ simp [Once Diverges_cases] \\ rw []
    \\ cheat (* true *))
  \\ qpat_x_assum ‘Diverges _’ mp_tac
  \\ simp [Once Diverges_cases] \\ rw []
  THEN1 (fs [eval_to_def,eval_op_def,is_eq_def])
  THEN1 (fs [eval_to_def,eval_op_def,el_def])
  THEN1
   (fs [eval_to_def,eval_op_def,el_def,eval_thm] \\ rw []
    \\ ‘eval_to n x = Constructor s (MAP eval xs' ++ eval y::MAP eval ys)’ by cheat
    \\ fs [] \\ cheat (* sigh, not provable, I think *))
  \\ cheat
QED

*)

val _ = export_theory();
