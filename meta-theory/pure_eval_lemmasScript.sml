(*
   Various lemmas about the eval and eval_to functions from pure_evalTheory
*)
Theory pure_eval_lemmas
Ancestors
  fixedPoint arithmetic list string alist option pair ltree llist
  bag pred_set relation rich_list finite_map pure_misc pure_exp
  pure_value pure_eval pure_exp_lemmas pure_limit
Libs
  term_tactic BasicProvers dep_rewrite

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
  (v ∈ freevars_v (Closure x e)) = (v ∈ freevars e DELETE x) ∧
  (v ∈ freevars_v (Constructor x xs)) = (v ∈ BIGUNION(IMAGE freevars_v (set xs)))
Proof
  gvs[freevars_v_IN] >>
  gvs[v_lookup_Error,v_lookup_Diverge,v_lookup_Atom,v_lookup_Closure,
      v_lookup_Constructor,AllCaseEqs(), oEL_THM] >>
  rw[EQ_IMP_THM,PULL_EXISTS]
  >- (
    rw[freevars_v_IN, PULL_EXISTS] >>
    goal_assum drule >> simp[EL_MEM]
    )
  >- (
    gvs[freevars_v_IN, MEM_EL] >>
    qexists_tac `n::path` >> simp[]
    )
QED

Theorem freevars_wh_equiv:
  ∀w. freevars_wh w = set (freevars_wh_l w)
Proof
  recInduct freevars_wh_ind >> rw[]
  >- (
    gvs[LIST_TO_SET_FLAT, LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF] >>
    AP_TERM_TAC >> rw[EXTENSION, freevars_equiv]
    )
  >- (
    simp[LIST_TO_SET_FILTER, EXTENSION, freevars_equiv] >> rw[] >> eq_tac >> rw[]
    )
QED

Theorem eval_wh_to_freevars_SUBSET:
  ∀k e1 v y.
    eval_wh_to k e1 = v ∧ y ∈ freevars_wh v ⇒
    y ∈ freevars e1
Proof
  ho_match_mp_tac eval_wh_to_ind >> rpt strip_tac
  >- (rename1 ‘Var’ >> gvs[eval_wh_to_def])
  >- (rename1 ‘Lam’ >> gvs[eval_wh_to_def])
  >- (
      rename1 ‘App’ >> gvs[eval_wh_to_def] >>
      pop_assum mp_tac >> IF_CASES_TAC >> gvs[] >>
      rpt (CASE_TAC >> gvs[]) >> rw[] >> res_tac >>
      Cases_on `eval_wh_to k e1` >> gvs[dest_wh_Closure_def] >>
      gvs[bind1_def] >> FULL_CASE_TAC >> gvs[] >>
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
      Cases_on `p` >> gvs[] >>
      gvs[AllCaseEqs(),MAP_EQ_CONS,DISJ_IMP_THM,FORALL_AND_THM] >>
      rw[] >> gvs[freevars_wh_def, EL_MAP, MEM_MAP, PULL_EXISTS]
      >- (
        EVERY_CASE_TAC >> gvs[freevars_wh_def] >>
        first_x_assum (qspec_then `EL 1 xs` assume_tac) >> gvs[EL_MEM] >>
        res_tac >> goal_assum drule >> gvs[EL_MEM]
        )
      >- (
        EVERY_CASE_TAC >> gvs[freevars_wh_def] >>
        first_x_assum (qspec_then `EL 2 xs` assume_tac) >> gvs[EL_MEM] >>
        res_tac >> goal_assum drule >> gvs[EL_MEM]
        )
      >- (EVERY_CASE_TAC >> gvs[freevars_wh_def])
      >- (
        EVERY_CASE_TAC >> gvs[freevars_wh_def, LENGTH_EQ_NUM_compute] >>
        res_tac >> last_x_assum irule >>
        simp[freevars_wh_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        goal_assum $ drule_at Any >> simp[EL_MEM]
        )
      >- (EVERY_CASE_TAC >> gvs[freevars_wh_def])
      >- (
        EVERY_CASE_TAC >> gvs[freevars_wh_def, LENGTH_EQ_NUM_compute] >>
        metis_tac[]
        )
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
    eval_wh_to k e1 = wh_Closure x e2 ∧ y ∈ freevars e2 ⇒
    x = y ∨ y ∈ freevars e1
Proof
  rpt strip_tac >> drule eval_wh_to_freevars_SUBSET >> simp[] >>
  metis_tac[]
QED

Theorem eval_Closure_closed:
  eval e1 = Closure x e2 ∧ closed e1 ⇒
  freevars e2 ⊆ {x}
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
  freevars e2 ⊆ {x}
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
  \\ CASE_TAC \\ CASE_TAC \\ rgs[AllCaseEqs(), follow_path_def, eval_wh_def]
  \\ pop_assum mp_tac \\ DEEP_INTRO_TAC some_intro \\ rw[]
  >- (goal_assum drule)
  >- (goal_assum drule)
  >- (goal_assum drule)
  >- (gvs[])
  >- (goal_assum drule)
QED

Theorem subst_funs_eq_subst:
  ∀f. EVERY (λe. freevars e ⊆ set (MAP FST f)) (MAP SND f)
  ⇒ subst_funs f = subst (FEMPTY |++ MAP (λ(v,e). (v,Letrec f e)) f)
Proof
  rw[] >> irule EQ_EXT >> rw[subst_funs_def, bind_def] >> gvs[] >>
  gvs[flookup_fupdate_list] >> EVERY_CASE_TAC >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> gvs[] >>
  gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> pairarg_tac >> gvs[]
  >- (last_x_assum drule >> simp[]) >>
  gvs[EXISTS_MEM, MEM_MAP]
QED

Theorem eval_Apps_Lams:
  ∀l e.
    EVERY (closed o SND) l
  ⇒ eval_wh (Apps (Lams (MAP FST l) e) (MAP SND l)) =
    eval_wh (subst (FEMPTY |++ l) e)
Proof
  Induct using SNOC_INDUCT >>
  rw[MAP_SNOC, Lams_SNOC, Apps_SNOC, FUPDATE_LIST_THM] >>
  PairCases_on `x` >> gvs[] >>
  simp[eval_wh_thm] >> gvs[SNOC_APPEND] >>
  simp[subst_def, eval_wh_thm, bind_def, FLOOKUP_UPDATE] >>
  simp[FUPDATE_LIST_APPEND, GSYM FUPDATE_EQ_FUPDATE_LIST] >>
  DEP_REWRITE_TAC[subst_subst_FUNION] >> conj_tac
  >- (
    simp[DOMSUB_FUPDATE_LIST] >> ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    simp[combinTheory.o_DEF, MEM_MAP, PULL_EXISTS, MEM_FILTER] >> rw[] >>
    gvs[EVERY_MEM]
    ) >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  rw[fmap_eq_flookup, FLOOKUP_FUNION, DOMSUB_FLOOKUP_THM, FLOOKUP_UPDATE] >>
  IF_CASES_TAC >> gvs[] >> CASE_TAC >> simp[]
QED

