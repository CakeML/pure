(*
   Various lemmas about the eval and eval_to functions from pure_evalTheory
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite;
open pure_expTheory pure_valueTheory pure_evalTheory
     pure_exp_lemmasTheory pure_limitTheory;

val _ = new_theory "pure_eval_lemmas";

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

Theorem eval_wh_to_freevars_SUBSET:
  ∀k e1 v y.
    eval_wh_to k e1 = v ∧ y ∈ freevars_wh v ⇒
    MEM y (freevars e1)
Proof
  ho_match_mp_tac eval_wh_to_ind >> rpt strip_tac
  >- (rename1 ‘Var’ >> gvs[eval_wh_to_def])
  >- (rename1 ‘Lam’ >> gvs[eval_wh_to_def])
  >- (
      rename1 ‘App’ >> gvs[eval_wh_to_def] >>
      pop_assum mp_tac >> IF_CASES_TAC >> gvs[] >>
      rpt (CASE_TAC >> gvs[]) >> rw[] >> res_tac >>
      Cases_on `eval_wh_to k e1` >> gvs[dest_wh_Closure_def] >>
      gvs[bind_single_def] >> FULL_CASE_TAC >> gvs[] >>
      res_tac >> gvs[freevars_subst]
      )
  >- (
      rename1 ‘Letrec’ >> gvs[eval_wh_to_def] >>
      FULL_CASE_TAC >> gvs[] >> res_tac >>
      gvs[subst_funs_def, freevars_bind] >>
      last_x_assum drule >> FULL_CASE_TAC >> fs[] >>
      simp[FDOM_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
      )
  >- (
      rename1 ‘Prim’ >> gs[eval_wh_to_def] >>
      qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
      IF_CASES_TAC >> gvs[] >- (rw[] >> gvs[freevars_wh_def]) >>
      TOP_CASE_TAC >> gvs[] >>
      gvs[AllCaseEqs(),MAP_EQ_CONS,DISJ_IMP_THM,FORALL_AND_THM] >>
      rw[] >> gvs[freevars_wh_def, EL_MAP, MEM_MAP, PULL_EXISTS]
      >- (
        first_x_assum (qspec_then `EL 1 xs` assume_tac) >> gvs[EL_MEM] >>
        res_tac >> goal_assum drule >> gvs[EL_MEM]
        )
      >- (
        first_x_assum (qspec_then `EL 2 xs` assume_tac) >> gvs[EL_MEM] >>
        res_tac >> goal_assum drule >> gvs[EL_MEM]
        )
      >- (goal_assum drule >> simp[])
      >- (
        Cases_on `xs` >> gvs[PULL_EXISTS] >>
        first_x_assum irule >> gvs[MEM_MAP, PULL_EXISTS] >>
        res_tac >>
        goal_assum (drule_at Any) >> gvs[EL_MEM]
        )
      >- (CCONTR_TAC >> gvs[])
      )
QED

Theorem eval_wh_freevars_SUBSET:
  ∀e1 v y.
    eval_wh e1 = v ∧ y ∈ freevars_wh v ⇒
    y ∈ freevars e1
Proof
  simp[eval_wh_def] >> rpt (gen_tac) >>
  DEEP_INTRO_TAC some_intro >> rw[] >>
  `∃v. eval_wh_to x e1 = v ∧ v ≠ wh_Diverge` by gvs[] >>
  drule eval_wh_to_freevars_SUBSET >>
  metis_tac[]
QED

Theorem eval_wh_to_Closure_freevars_SUBSET:
  ∀k e1 e2 x y.
    eval_wh_to k e1 = wh_Closure x e2 ∧ MEM y (freevars e2) ⇒
    x = y ∨ MEM y (freevars e1)
Proof
  rpt strip_tac >> drule eval_wh_to_freevars_SUBSET >> simp[] >>
  metis_tac[]
QED

Theorem eval_Closure_closed:
  eval e1 = Closure x e2 ∧ closed e1 ⇒
  set(freevars e2) ⊆ {x}
Proof
  rw[eval_def, v_unfold_def] >>
  fs[Once gen_v, Once follow_path_def] >>
  FULL_CASE_TAC >> gvs[eval_wh_def] >>
  pop_assum mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >>
  drule eval_wh_to_freevars_SUBSET >> simp[] >>
  rw[SUBSET_DEF] >> gvs[closed_def] >>
  metis_tac[]
QED

Theorem eval_wh_Closure_closed:
  eval_wh e1 = wh_Closure x e2 ∧ closed e1 ⇒
  set(freevars e2) ⊆ {x}
Proof
  gvs[eval_wh_def,AllCaseEqs()] >>
  DEEP_INTRO_TAC some_intro >> rw[] >>
  drule eval_wh_to_freevars_SUBSET >> simp[] >>
  rw[SUBSET_DEF] >> gvs[closed_def] >>
  metis_tac[]
QED

Theorem eval_eq_Diverge:
  eval x = Diverge ⇔ ∀n. eval_wh_to n x = wh_Diverge
Proof
  fs [eval_def, v_unfold_def]
  \\ once_rewrite_tac [gen_v, follow_path_def]
  \\ CASE_TAC \\ CASE_TAC \\ gvs[AllCaseEqs(), follow_path_def, eval_wh_def]
  \\ pop_assum mp_tac \\ DEEP_INTRO_TAC some_intro \\ rw[]
  >- (goal_assum drule)
  >- (goal_assum drule)
  >- (goal_assum drule)
  >- (gvs[])
  >- (goal_assum drule)
QED

val _ = export_theory();
