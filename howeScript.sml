(*
   This file formalises Howe's method following the description of
   Pitts 2011 chapter "Howe's method for higher-order languages".
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite;
open expTheory valueTheory pure_langTheory expPropsTheory limitTheory;

val _ = new_theory "howe";


(* -- basics -- *)

val no_IN = SIMP_RULE std_ss [IN_DEF];

(* the set of all expressions with at most free variables vars *)
Definition Exps_def:
  Exps vars = { e | freevars e ⊆ vars }
End

Theorem Exps_EMPTY_closed[simp]:
  e IN Exps EMPTY ⇔ closed e
Proof
  fs [Exps_def,closed_def]
QED


(* -- applicative (bi)similarity -- *)
Definition unfold_rel_def:
  unfold_rel rel (e1, e2) ⇔
    closed e1 ∧ closed e2 ∧
    (∀x ce1.
      eval e1 = Closure x ce1
      ⇒ ∃y ce2.
          eval e2 = Closure y ce2 ∧
          ∀e. closed e ⇒ rel (subst x e ce1, subst y e ce2))
    ∧
    (∀x v1s.
      eval e1 = Constructor x v1s
       ⇒ ∃es1 es2. eval e1 = eval (Cons x es1) ∧ EVERY closed es1 ∧
                 eval e2 = eval (Cons x es2) ∧ EVERY closed es2 ∧
                 LIST_REL (CURRY rel) es1 es2)
    ∧
    (∀a. eval e1 = Atom a ⇒ eval e2 = Atom a)
    ∧
    (eval e1 = Diverge ⇒ eval e2 = Diverge)
    ∧
    (eval e1 = Error ⇒ eval e2 = Error)
End

Definition app_simulation_def:
  app_simulation S ⇔
    ∀e1 e2. S (e1, e2) ⇒ unfold_rel S (e1, e2)
End

Definition opp_def:
  opp s (x,y) ⇔ (y,x) IN s
End

Definition app_bisimulation_def:
  app_bisimulation S ⇔ app_simulation S ∧ app_simulation (opp S)
End

Definition FF_def:
  FF s = { (e1, e2) | unfold_rel s (e1, e2) }
End

Theorem FF_opp:
  FF (opp R) (a,b) ⇔ FF R (b,a)
Proof
  fs[FF_def, opp_def, unfold_rel_def] >> eq_tac >> rw[] >>
  PairCases_on `x` >> gvs[] >>
  Q.REFINE_EXISTS_TAC `(x1,x2)` >> gvs[IN_DEF]
  >- (
    Cases_on `eval a` >> gvs[eval_thm] >>
    qexists_tac `es2` >> qexists_tac `es1` >> fs[] >>
    fs[LIST_REL_EL_EQN, opp_def, IN_DEF]
    )
  >- (
    Cases_on `eval b` >> gvs[eval_thm] >>
    qexists_tac `es2` >> qexists_tac `es1` >> fs[] >>
    fs[LIST_REL_EL_EQN, opp_def, IN_DEF]
    )
QED

Triviality monotone_similarity:
  monotone FF
Proof
  fs [monotone_def,FF_def,unfold_rel_def] >>
  fs [SUBSET_DEF,FORALL_PROD,IN_DEF] >> rw[] >> fs[] >>
  qexists_tac `es1` >> qexists_tac `es2` >> fs[] >>
  fs[LIST_REL_EL_EQN]
QED

Definition app_similarity_def:
  app_similarity = gfp FF
End

val _ = set_fixity "≲" (Infixl 480);
Overload "≲" = “λx y. app_similarity (x,y)”;

Theorem app_similarity_thm =
  MATCH_MP gfp_greatest_fixedpoint monotone_similarity
  |> SIMP_RULE std_ss [GSYM app_similarity_def]

Theorem app_similarity_iff = (* result (5.4) *)
  app_similarity_thm |> CONJUNCT1 |> GSYM
    |> SIMP_RULE std_ss [FF_def,EXTENSION,FORALL_PROD,GSPECIFICATION,EXISTS_PROD]
    |> SIMP_RULE std_ss [IN_DEF];

Theorem app_simulation_SUBSET_app_similarity:
  app_simulation R ⇒ R ⊆ app_similarity
Proof
  rw [app_similarity_def,app_simulation_def]
  \\ fs [gfp_def,SUBSET_DEF,FORALL_PROD]
  \\ fs [IN_DEF,FF_def,EXISTS_PROD] \\ metis_tac []
QED

Theorem app_simulation_app_similarity:
  app_simulation app_similarity
Proof
  fs [app_simulation_def]
  \\ assume_tac app_similarity_iff
  \\ metis_tac []
QED

Triviality monotone_bisimilarity:
  monotone (λs. { (e1,e2) | (e1,e2) IN FF s ∧ (e2,e1) IN FF (opp s) })
Proof
  fs [monotone_def,FF_def,unfold_rel_def,opp_def] >>
  fs [SUBSET_DEF,FORALL_PROD,IN_DEF,opp_def] >> rw[] >> fs[] >>
  qexists_tac `es1` >> qexists_tac `es2` >> fs[] >>
  fs[LIST_REL_EL_EQN, opp_def, IN_DEF]
QED

Definition app_bisimilarity_def:
  app_bisimilarity = gfp (λs. { (e1,e2) | (e1,e2) IN FF s ∧ (e2,e1) IN FF (opp s) })
End

val _ = set_fixity "≃" (Infixl 480);
Overload "≃" = “λx y. app_bisimilarity (x,y)”;

Theorem app_bisimilarity_thm =
  MATCH_MP gfp_greatest_fixedpoint monotone_bisimilarity
  |> SIMP_RULE std_ss [GSYM app_bisimilarity_def]

Theorem app_bisimilarity_iff = (* result (5.5) *)
  app_bisimilarity_thm |> CONJUNCT1 |> GSYM
    |> SIMP_RULE std_ss [FF_def,EXTENSION,FORALL_PROD,GSPECIFICATION,EXISTS_PROD]
    |> SIMP_RULE (std_ss++boolSimps.CONJ_ss) [IN_DEF,unfold_rel_def,opp_def]
    |> REWRITE_RULE [GSYM CONJ_ASSOC];

Theorem app_bisimilarity_iff_alt =
  app_bisimilarity_thm |> CONJUNCT1 |> GSYM
    |> SIMP_RULE std_ss [FF_def,EXTENSION,FORALL_PROD,GSPECIFICATION,EXISTS_PROD]
    |> SIMP_RULE (std_ss++boolSimps.CONJ_ss) [IN_DEF,opp_def]
    |> REWRITE_RULE [GSYM CONJ_ASSOC];

Theorem app_bisimulation_SUBSET_app_bisimilarity:
  app_bisimulation R ⇒ R ⊆ app_bisimilarity
Proof
  rw [app_bisimilarity_def,app_bisimulation_def,app_simulation_def] >>
  fs [gfp_def,SUBSET_DEF,FORALL_PROD,opp_def,IN_DEF] >>
  fs [IN_DEF,FF_def,EXISTS_PROD,opp_def] >>
  rw[] >> qexists_tac `R` >> rw[]
QED

Theorem app_bisimulation_app_bisimilarity:
  app_bisimulation app_bisimilarity
Proof
  fs [app_bisimulation_def,app_simulation_def,opp_def,IN_DEF] >>
  assume_tac app_bisimilarity_iff_alt >> fs[]
QED

Theorem app_similarity_coinduct:
  ∀P.
    (∀x y. P x y ⇒ FF (UNCURRY P) (x,y))
  ⇒
  ∀x y. P x y ⇒ x ≲ y
Proof
  rpt GEN_TAC >> strip_tac >> simp[app_similarity_def] >>
  qspec_then ‘UNCURRY P’ mp_tac (MATCH_MP gfp_coinduction monotone_similarity) >>
  rw[SUBSET_DEF,IN_DEF] >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[] >>
  Cases >> rw[]
QED

Theorem app_bisimilarity_coinduct:
  ∀P.
    (∀x y. P x y ⇒ FF (UNCURRY P) (x,y) ∧
                   FF (opp(UNCURRY P)) (y,x))
  ⇒
  ∀x y. P x y ⇒ x ≃ y
Proof
  rpt GEN_TAC >> strip_tac >> simp[app_bisimilarity_def] >>
  qspec_then ‘UNCURRY P’ mp_tac (MATCH_MP gfp_coinduction monotone_bisimilarity) >>
  rw[SUBSET_DEF,IN_DEF] >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[] >>
  pop_assum kall_tac >>
  Cases >> gvs[ELIM_UNCURRY]
QED

Theorem app_similarity_closed:
  x ≲ y ⇒ closed x ∧ closed y
Proof
  rw[app_similarity_iff,Once unfold_rel_def]
QED

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
    (∃b x xs'. op = Lit b ∧ xs = x::xs')
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

Theorem eval_eq_imp_app_similarity:
  ∀x y.
    eval x = eval y ∧ closed x ∧ closed y
  ⇒ x ≲ y
Proof
  ho_match_mp_tac app_similarity_coinduct >>
  rw[FF_def] >>
  Q.REFINE_EXISTS_TAC `(x1,x2)`  >> fs[] >>
  rw[unfold_rel_def] >> gvs[]
  >- (
    drule_all eval_Closure_closed >> rw[closed_def] >>
    rename1 `subst a e1 e2` >>
    qspecl_then [`a`,`e1`,`e2`] assume_tac freevars_subst_single >> gvs[] >>
    Cases_on `freevars e2` >> gvs[]
    )
  >- (
    drule eval_eq_Cons_IMP >> strip_tac >> gvs[] >>
    qexists_tac `ts` >> qexists_tac `ts` >> fs[] >>
    fs[LIST_REL_EL_EQN, FLAT_EQ_NIL, EVERY_MAP, EVERY_EL, closed_def]
    )
QED

Theorem reflexive_app_similarity: (* exercise (5.3.3) *)
  reflexive (UNCURRY $≲) closed
Proof
  rw[set_relationTheory.reflexive_def,ELIM_UNCURRY,IN_DEF] >>
  ‘∀x y. x = y ∧ closed x ⇒ x ≲ y’ suffices_by metis_tac[] >>
  pop_assum kall_tac >>
  ho_match_mp_tac app_similarity_coinduct >>
  reverse (rw[FF_def,ELIM_UNCURRY,unfold_rel_def]) >>
  simp[]
  >- (
    drule eval_eq_Cons_IMP >> strip_tac >> Cases_on `eval x` >> gvs[] >>
    qexists_tac `ts` >> qexists_tac `ts` >>
    fs[FLAT_EQ_NIL, EVERY_MAP, LIST_REL_EL_EQN, EVERY_EL, closed_def]
    ) >>
  drule_all eval_Closure_closed >>
  simp[closed_def,freevars_subst] >>
  strip_tac >>
  rename [‘freevars (subst x e1 e2)’] >>
  ‘∀v. MEM v (freevars (subst x e1 e2)) ⇒ F’
    by(rpt strip_tac >>
       gvs[freevars_subst] >>
       drule_all SUBSET_THM >> simp[]) >>
  Cases_on ‘freevars (subst x e1 e2)’ >> gvs[FORALL_AND_THM]
QED

Theorem reflexive_app_similarity':
  closed x ⇒ x ≲ x
Proof
  mp_tac reflexive_app_similarity >>
  rw[set_relationTheory.reflexive_def,IN_DEF]
QED

(* -- Applicative simulation up-to à la Damien Pous (LICS 2016) -- *)
Definition compatible_def:
  compatible f ⇔ (∀B. f(FF B) ⊆ FF(f B))
End

Definition companion_def:
  companion R xy ⇔ ∃f. monotone f ∧ compatible f ∧ xy ∈ f(UNCURRY R)
End

Theorem companion_compatible:
  compatible ((companion o CURRY))
Proof
  mp_tac monotone_similarity >>
  rw[compatible_def,companion_def,pred_setTheory.SUBSET_DEF,IN_DEF,monotone_def] >>
  res_tac >>
  last_x_assum(match_mp_tac o MP_CANON) >>
  goal_assum(drule_at (Pos last)) >>
  rw[companion_def] >>
  qexists_tac ‘f’ >>
  rw[compatible_def,companion_def,pred_setTheory.SUBSET_DEF,IN_DEF,monotone_def] >>
  metis_tac[]
QED

Theorem companion_monotone:
  monotone(companion o CURRY)
Proof
  rw[monotone_def,pred_setTheory.SUBSET_DEF,companion_def,IN_DEF] >>
  rpt(goal_assum drule) >>
  metis_tac[]
QED

Theorem compatible_FF:
  compatible FF
Proof
  rw[compatible_def]
QED

Theorem compatible_app_similarity:
  compatible (λR. app_similarity)
Proof
  rw[compatible_def,app_similarity_def] >>
  metis_tac[gfp_greatest_fixedpoint,monotone_similarity]
QED

Theorem opp_IN:
  (x,y) ∈ opp s ⇔ (y,x) ∈ s
Proof
  rw[opp_def,IN_DEF]
QED

Theorem companion_SUBSET:
  X ⊆ companion(CURRY X)
Proof
  rw[companion_def,pred_setTheory.SUBSET_DEF,IN_DEF] >>
  qexists_tac ‘I’ >>
  rw[monotone_def,compatible_def]
QED

Theorem monotone_compose:
  monotone f ∧ monotone g ⇒ monotone(f o g)
Proof
  rw[monotone_def,pred_setTheory.SUBSET_DEF,IN_DEF] >> res_tac >> metis_tac[]
QED

Theorem compatible_compose:
  monotone f ∧ compatible f ∧ compatible g ⇒ compatible(f o g)
Proof
  rw[compatible_def,pred_setTheory.SUBSET_DEF,IN_DEF,monotone_def] >>
  first_x_assum match_mp_tac >>
  last_x_assum(match_mp_tac o MP_CANON) >>
  goal_assum(drule_at (Pos last)) >>
  metis_tac[]
QED

Theorem companion_idem:
  companion (CURRY (companion (CURRY B))) = companion(CURRY B)
Proof
  rw[companion_def,FUN_EQ_THM,EQ_IMP_THM]
  >- (qexists_tac ‘f o companion o CURRY’ >>
      simp[compatible_compose,companion_compatible,monotone_compose,companion_monotone]) >>
  qexists_tac ‘I’ >>
  simp[monotone_def,compatible_def] >>
  gvs[IN_DEF,companion_def] >> metis_tac[]
QED

Theorem gfp_companion_SUBSET:
  gfp(FF o companion o CURRY) ⊆ gfp FF
Proof
  match_mp_tac (MP_CANON gfp_coinduction) >>
  conj_tac >- ACCEPT_TAC monotone_similarity >>
  rw[pred_setTheory.SUBSET_DEF,IN_DEF] >>
  ‘monotone(FF ∘ companion ∘ CURRY)’ by simp[monotone_compose,monotone_similarity,companion_monotone] >>
  first_assum(mp_tac o GSYM o MATCH_MP (cj 1 gfp_greatest_fixedpoint)) >>
  disch_then(gs o single o Once) >>
  mp_tac monotone_similarity >>
  simp[monotone_def,pred_setTheory.SUBSET_DEF,IN_DEF] >>
  disch_then(match_mp_tac o MP_CANON) >>
  goal_assum(dxrule_at (Pos last)) >>
  rpt strip_tac >>
  first_assum(mp_tac o GSYM o MATCH_MP (cj 1 gfp_greatest_fixedpoint)) >>
  disch_then(gs o single o Once) >>
  mp_tac companion_compatible >>
  simp[compatible_def,pred_setTheory.SUBSET_DEF,IN_DEF] >>
  disch_then dxrule >>
  strip_tac >>
  gvs[companion_idem] >>
  first_assum(mp_tac o GSYM o MATCH_MP (cj 1 gfp_greatest_fixedpoint)) >>
  disch_then(simp o single o Once)
QED

Theorem app_similarity_companion_coind:
  ∀R. (∀v1 v2. R v1 v2 ⇒ FF (companion R) (v1,v2)) ⇒
      ∀v1 v2. R v1 v2 ⇒ v1 ≲ v2
Proof
  ntac 2 strip_tac >>
  rw[app_similarity_def] >>
  match_mp_tac(MP_CANON pred_setTheory.SUBSET_THM |> SIMP_RULE std_ss [IN_DEF]) >>
  irule_at (Pos hd) gfp_companion_SUBSET >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘v2’,‘v1’] >>
  simp[PFORALL_THM,ELIM_UNCURRY] >>
  simp[GSYM(pred_setTheory.SUBSET_DEF |> SIMP_RULE std_ss [IN_DEF])] >>
  CONV_TAC(DEPTH_CONV ETA_CONV) >>
  match_mp_tac (MP_CANON gfp_coinduction) >>
  simp[monotone_compose,monotone_similarity,companion_monotone] >>
  rw[pred_setTheory.SUBSET_DEF,IN_DEF,ELIM_UNCURRY] >>
  first_x_assum drule >> gs[CURRY_UNCURRY_THM |> SIMP_RULE bool_ss [ELIM_UNCURRY]]
QED

Theorem companion_refl[simp]:
  closed x ⇒ companion R (x,x)
Proof
  rw[companion_def] >>
  irule_at Any compatible_app_similarity >>
  simp[IN_DEF,monotone_def,reflexive_app_similarity']
QED

Theorem companion_v_rel:
  x ≲ y ⇒ companion R (x,y)
Proof
  rw[companion_def] >>
  irule_at Any compatible_app_similarity >>
  simp[IN_DEF,v_rel_refl,monotone_def]
QED

Theorem compatible_union:
  compatible f ∧ compatible g ⇒
  compatible(λx. f x ∪ g x)
Proof
  rw[compatible_def] >>
  rpt(first_x_assum(qspec_then ‘x’ assume_tac)) >>
  drule_then match_mp_tac SUBSET_TRANS >>
  match_mp_tac(monotone_similarity |> SIMP_RULE std_ss[monotone_def]) >>
  rw[]
QED

Triviality CURRY_thm:
  CURRY f = λ x y. f(x,y)
Proof
  rw[FUN_EQ_THM]
QED

Theorem companion_app_similarity:
  ∀e1 e2. companion ($≲) (e1,e2) ⇒ e1 ≲ e2
Proof
  ho_match_mp_tac app_similarity_companion_coind >>
  rw[companion_idem |> SIMP_RULE std_ss [CURRY_thm]] >>
  mp_tac companion_compatible >>
  rw[compatible_def,CURRY_thm,SUBSET_DEF,IN_DEF] >>
  first_x_assum match_mp_tac >>
  gvs[] >>
  gvs[FF_def,ELIM_UNCURRY,GSYM app_similarity_iff]
QED

Theorem compatible_tc:
  compatible (λR. tc(R ∪ app_similarity))
Proof
  simp[compatible_def,SUBSET_DEF] >>
  strip_tac >> Cases >>
  rename1 ‘(x,y)’ >>
  MAP_EVERY qid_spec_tac [‘y’,‘x’] >>
  ho_match_mp_tac set_relationTheory.tc_ind_left >>
  conj_tac
  >- (rw[FF_def,unfold_rel_def] >> gvs[] >> rw[]
      >- (match_mp_tac (set_relationTheory.subset_tc |> SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          rw[UNION_DEF] >> metis_tac[IN_DEF])
      >- (irule_at (Pos hd) EQ_REFL >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[] >>
          drule_at_then (Pos last) match_mp_tac EVERY2_mono >>
          rw[] >> match_mp_tac (set_relationTheory.subset_tc |> SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          rw[UNION_DEF] >> metis_tac[IN_DEF])
      >- (metis_tac[IN_DEF,app_similarity_closed])
      >- (metis_tac[IN_DEF,app_similarity_closed])
      >- (gvs[IN_DEF,Once app_similarity_iff] >>
          gvs[unfold_rel_def] >>
          rw[] >>
          match_mp_tac (set_relationTheory.subset_tc |> SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          rw[UNION_DEF] >> metis_tac[IN_DEF])
      >- (gvs[IN_DEF,Once app_similarity_iff] >>
          gvs[unfold_rel_def] >>
          gvs[eval_thm] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[] >>
          drule_at_then (Pos last) match_mp_tac EVERY2_mono >>
          rw[] >> match_mp_tac (set_relationTheory.subset_tc |> SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          rw[UNION_DEF] >> metis_tac[IN_DEF]) >>
      gvs[IN_DEF,Once app_similarity_iff] >> gvs[unfold_rel_def])
  >- (rw[FF_def,unfold_rel_def] >> gvs[]
      >- (rw[] >>
          match_mp_tac (set_relationTheory.tc_rules |> cj 2 |> SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          rpt(first_x_assum drule) >> rw[] >>
          goal_assum(drule_at (Pos last)) >>
          match_mp_tac (set_relationTheory.subset_tc |> SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          rw[UNION_DEF] >> metis_tac[IN_DEF])
      >- (gvs[eval_thm] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[] >>
          ‘LIST_REL (CURRY (tc (R ∪ app_similarity))) es2 es1'’
            by(qpat_x_assum ‘EVERY closed es2’ mp_tac >>
               qpat_x_assum ‘EVERY closed es1'’ mp_tac >>
               qpat_x_assum ‘MAP _ _ = MAP _ _’ mp_tac >>
               rpt(pop_assum kall_tac) >>
               qid_spec_tac ‘es1'’ >>
               Induct_on ‘es2’ >- rw[] >>
               strip_tac >> Cases >>
               rw[] >>
               drule_all eval_eq_imp_app_similarity >>
               strip_tac >>
               simp[Once(no_IN set_relationTheory.tc_cases)] >>
               metis_tac[IN_DEF]) >>
          match_mp_tac (MP_CANON EVERY2_trans) >>
          simp[GSYM PULL_EXISTS] >>
          conj_asm1_tac >- metis_tac[no_IN set_relationTheory.tc_rules] >>
          irule_at (Pos hd) EVERY2_mono >>
          goal_assum(drule_at (Pos (hd o tl))) >>
          conj_tac
          >- (rw[] >>
              match_mp_tac(no_IN(cj 1 set_relationTheory.tc_rules)) >>
              rw[UNION_DEF,IN_DEF]) >>
          match_mp_tac(MP_CANON EVERY2_trans) >>
          simp[] >>
          metis_tac[])
      >- metis_tac[IN_DEF,app_similarity_closed]
      >- (gvs[IN_DEF,Once app_similarity_iff] >> gvs[unfold_rel_def] >>
          rw[] >>
          match_mp_tac (set_relationTheory.tc_rules |> cj 2 |> SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          irule_at (Pos hd) (set_relationTheory.subset_tc |> SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          simp[IN_DEF] >> metis_tac[])
      >- (gvs[IN_DEF,app_similarity_iff] >>
          gvs[unfold_rel_def] >>
          gvs[eval_thm] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[] >>
          ‘LIST_REL (CURRY (tc (R ∪ app_similarity))) es2 es1'’
            by(qpat_x_assum ‘EVERY closed es2’ mp_tac >>
               qpat_x_assum ‘EVERY closed es1'’ mp_tac >>
               qpat_x_assum ‘MAP _ _ = MAP _ _’ mp_tac >>
               rpt(pop_assum kall_tac) >>
               qid_spec_tac ‘es1'’ >>
               Induct_on ‘es2’ >- rw[] >>
               strip_tac >> Cases >>
               rw[] >>
               drule_all eval_eq_imp_app_similarity >>
               strip_tac >>
               simp[Once(no_IN set_relationTheory.tc_cases)] >>
               metis_tac[IN_DEF]) >>
          match_mp_tac (MP_CANON EVERY2_trans) >>
          simp[GSYM PULL_EXISTS] >>
          conj_asm1_tac >- metis_tac[no_IN set_relationTheory.tc_rules] >>
          irule_at (Pos hd) EVERY2_mono >>
          goal_assum(drule_at (Pos (hd o tl))) >>
          conj_tac
          >- (rw[] >>
              match_mp_tac(no_IN(cj 1 set_relationTheory.tc_rules)) >>
              rw[UNION_DEF,IN_DEF]) >>
          match_mp_tac(MP_CANON EVERY2_trans) >>
          simp[] >>
          metis_tac[]) >>
      gvs[IN_DEF,app_similarity_iff] >> gvs[unfold_rel_def])
QED

Theorem companion_duplicate:
  ∀x y z. companion R (x,z) ∧ companion R (z,y) ⇒ companion R (x,y)
Proof
  rw[companion_def] >>
  Q.REFINE_EXISTS_TAC ‘_ o (_ : (exp # exp -> bool) -> exp # exp -> bool)’ >>
  irule_at Any compatible_compose >>
  irule_at Any compatible_tc >>
  irule_at Any compatible_union >>
  goal_assum dxrule >>
  goal_assum dxrule >>
  irule_at Any monotone_compose >>
  conj_tac
  >- (gvs[monotone_def,SUBSET_DEF] >> rw[] >> metis_tac[]) >>
  conj_tac
  >- (rw[monotone_def] >>
      match_mp_tac set_relationTheory.tc_mono >>
      gvs[SUBSET_DEF]) >>
  rw[] >>
  match_mp_tac(cj 2 set_relationTheory.tc_rules) >>
  irule_at (Pos hd) (cj 1 set_relationTheory.tc_rules) >>
  irule_at (Pos last) (cj 1 set_relationTheory.tc_rules) >>
  rw[] >> metis_tac[]
QED

Theorem companion_duplicate_SET:
  ∀x y z. (x,z) ∈ companion R ∧ (z,y) ∈ companion R ⇒ (x,y) ∈ companion R
Proof
  metis_tac[IN_DEF,companion_duplicate]
QED

Theorem companion_rel:
  ∀R x y. R x y ⇒ companion R (x,y)
Proof
  rw[companion_def] >>
  qexists_tac ‘I’ >> rw[monotone_def,compatible_def,IN_DEF]
QED

Theorem app_similarity_transitive_lemma:
  tc app_similarity = app_similarity
Proof
  qsuff_tac `∀x y. (x,y) ∈ tc app_similarity ⇔ (x,y) ∈ app_similarity`
  >- (
    rw[] >> irule EQ_EXT >> rw[] >>
    PairCases_on `x` >> fs[IN_DEF]
    ) >>
  rw[] >> reverse eq_tac >> rw[]
  >- (fs[Once set_relationTheory.tc_cases, IN_DEF]) >>
  gvs[IN_DEF] >>
  match_mp_tac companion_app_similarity >>
  simp[companion_def] >>
  irule_at Any compatible_tc >>
  conj_tac
  >- (simp[monotone_def] >> rw[] >>
      match_mp_tac set_relationTheory.tc_mono >>
      gvs[SUBSET_DEF,UNION_DEF]) >>
  simp[] >>
  match_mp_tac (set_relationTheory.tc_mono |> SIMP_RULE std_ss [SUBSET_DEF] |> GEN_ALL |> MP_CANON) >>
  simp[IN_DEF] >>
  goal_assum (drule_at Any) >>
  rw[]
QED

Theorem transitive_app_similarity: (* exercise (5.3.3) *)
  transitive $≲
Proof
  SUBST_ALL_TAC (GSYM app_similarity_transitive_lemma) >>
  fs[relationTheory.transitive_def] >> rw[] >>
  simp[Once (no_IN set_relationTheory.tc_cases)] >> DISJ2_TAC >>
  goal_assum drule >> fs[]
QED

Theorem app_bisimilarity_similarity: (* prop (5.3.4) *)
  e1 ≃ e2 ⇔ e1 ≲ e2 ∧ e2 ≲ e1
Proof
  eq_tac \\ rw []
  THEN1
   (assume_tac app_bisimulation_app_bisimilarity
    \\ fs [app_bisimulation_def]
    \\ imp_res_tac app_simulation_SUBSET_app_similarity
    \\ fs [SUBSET_DEF,IN_DEF])
  THEN1
   (assume_tac app_bisimulation_app_bisimilarity
    \\ fs [app_bisimulation_def]
    \\ imp_res_tac app_simulation_SUBSET_app_similarity
    \\ fs [SUBSET_DEF,IN_DEF,opp_def])
  \\ rpt(pop_assum mp_tac)
  \\ simp[AND_IMP_INTRO]
  \\ MAP_EVERY qid_spec_tac [‘e2’,‘e1’]
  \\ ho_match_mp_tac app_bisimilarity_coinduct
  \\ rpt GEN_TAC \\ strip_tac \\ fs[FF_opp]
  \\ rw[FF_def,unfold_rel_def,ELIM_UNCURRY]
  \\ imp_res_tac app_similarity_closed
  \\ rpt(qpat_x_assum ‘_ ≲ _’
      (strip_assume_tac o PURE_ONCE_REWRITE_RULE[app_similarity_iff]))
  \\ gvs[unfold_rel_def, eval_thm]
  \\ qexists_tac `es1` \\ qexists_tac `es2` \\ fs[]
  \\ fs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, EVERY_EL] \\ rw[]
  \\ gvs[] \\ rpt (first_x_assum drule \\ strip_tac)
  \\ assume_tac transitive_app_similarity \\ fs[transitive_def]
  \\ first_assum irule \\ qexists_tac `EL n es1'` \\ rw[]
     >- (irule eval_eq_imp_app_similarity \\ fs[])
  \\ first_assum irule \\ qexists_tac `EL n es2'` \\ rw[]
  \\ irule eval_eq_imp_app_similarity \\ fs[]
QED

Theorem symmetric_app_bisimilarity: (* exercise (5.3.3) *)
  symmetric $≃
Proof
  rw[app_bisimilarity_similarity,symmetric_def,EQ_IMP_THM]
QED

Theorem transitive_app_bisimilarity: (* exercise (5.3.3) *)
  transitive $≃
Proof
  rw[app_bisimilarity_similarity,transitive_def] >>
  imp_res_tac(transitive_app_similarity |> SIMP_RULE std_ss [transitive_def])
QED

(* -- more lemmas -- *)

Theorem res_eq_IMP_app_bisimilarity: (* exercise (5.3.5) *)
  ∀e1 e2 x t. eval e1 = Closure x t ∧ closed e1 ∧ closed e2 ∧ eval e2 = Closure x t ⇒ e1 ≲ e2
Proof
  simp[GSYM PULL_EXISTS] >>
  ho_match_mp_tac app_similarity_companion_coind >>
  rw[FF_def,unfold_rel_def,ELIM_UNCURRY] >> gvs[] >>
  rpt strip_tac >>
  match_mp_tac companion_refl >>
  drule eval_Closure_closed >>
  simp[] >>
  rw[closed_def] >>
  rename [‘freevars (subst x e1 e2)’] >>
  ‘∀v. MEM v (freevars (subst x e1 e2)) ⇒ F’
    by(rpt strip_tac >> gvs[freevars_subst] >>
       drule_all SUBSET_THM >> rw[]) >>
  Cases_on ‘freevars (subst x e1 e2)’ >> fs[FORALL_AND_THM]
QED

(* -- congruence -- *)

(* TODO: not sure why this is parameterised on a set of names.
   Can't we just always choose the support of the two procs involved?
   I'm sure Andy knows what he's doing though so I'll roll with it...
 *)
(* TODO: cute mixfix syntax with ⊢ and all would be cute *)
(* Substitution closure of applicative bisimilarity. *)
Definition open_similarity_def:
  open_similarity names e1 e2 ⇔
    set(freevars e1) ∪ set(freevars e2) ⊆ names ∧
    ∀f. names = FDOM f ⇒ bind f e1 ≲ bind f e2
End

Definition open_bisimilarity_def:
  open_bisimilarity names e1 e2 ⇔
    set(freevars e1) ∪ set(freevars e2) ⊆ names ∧
    ∀f. names = FDOM f ⇒ bind f e1 ≃ bind f e2
End

Theorem open_bisimilarity_eq:
  open_bisimilarity names e1 e2 ⇔
  open_similarity names e1 e2 ∧ open_similarity names e2 e1
Proof
  eq_tac
  \\ fs [open_similarity_def,open_bisimilarity_def,app_bisimilarity_similarity]
QED

Definition Ref_def:
  Ref R ⇔
    ∀vars e. e IN Exps vars ⇒ R vars e e
End

Definition Sym_def:
  Sym R ⇔
    ∀vars e1 e2.
      {e1; e2} SUBSET Exps vars ⇒
      R vars e1 e2 ⇒ R vars e2 e1
End

Definition Tra_def:
  Tra R ⇔
    ∀vars e1 e2 e3.
      {e1; e2; e3} SUBSET Exps vars ⇒
      R vars e1 e2 ∧ R vars e2 e3 ⇒ R vars e1 e3
End

Definition Com1_def:
  Com1 R ⇔
    ∀vars x.
      x IN vars ⇒
      R vars (Var x) (Var x)
End

Definition Com2_def:
  Com2 R ⇔
    ∀vars x e e'.
      ~(x IN vars) ∧ {e; e'} SUBSET Exps (x INSERT vars) ⇒
      R (x INSERT vars) e e' ⇒ R vars (Lam x e) (Lam x e')
End

Definition Com3_def:
  Com3 R ⇔
    ∀vars e1 e1' e2 e2'.
      {e1; e1'; e2; e2'} SUBSET Exps vars ⇒
      R vars e1 e1' ∧ R vars e2 e2' ⇒ R vars (App e1 e2) (App e1' e2')
End

Definition Com4_def:
  Com4 R ⇔
    ∀ vars es es' op.
      set es ∪ set es' ⊆ Exps vars ⇒
      LIST_REL (R vars) es es' ⇒ R vars (Prim op es) (Prim op es')
End

Definition Com5_def:
  Com5 R ⇔
    ∀ vars ves ves' e e'.
      {e; e'} ∪ set (MAP SND ves) ∪ set (MAP SND ves') ⊆
        Exps (vars ∪ set (MAP FST ves)) ∧
      DISJOINT (set (MAP FST ves)) vars ⇒
      MAP FST ves = MAP FST ves' ∧
      LIST_REL
        (R (vars ∪ set (MAP FST ves))) (MAP SND ves) (MAP SND ves') ∧
      R (vars ∪ set (MAP FST ves)) e e'
      ⇒ R vars (Letrec ves e) (Letrec ves' e')
End

Theorem Com_defs =
  LIST_CONJ [Com1_def,Com2_def,Com3_def,Com4_def,Com5_def];

Definition Compatible_def:
  Compatible R ⇔ Com1 R ∧ Com2 R ∧ Com3 R ∧ Com4 R ∧ Com5 R
End

Definition Precongruence_def:
  Precongruence R ⇔ Tra R ∧ Compatible R
End

Definition Congruence_def:
  Congruence R ⇔ Sym R ∧ Precongruence R
End

Theorem Ref_open_similarity:
  Ref open_similarity
Proof
  fs[Ref_def, Exps_def]
  \\ rw[open_similarity_def]
  \\ irule reflexive_app_similarity'
  \\ reverse (rw [bind_def])
  THEN1 fs [closed_def]
  \\ match_mp_tac IMP_closed_subst
  \\ fs [FLOOKUP_DEF,FRANGE_DEF,PULL_EXISTS]
QED

Theorem Ref_open_bisimilarity:
  Ref open_bisimilarity
Proof
  assume_tac Ref_open_similarity
  \\ fs [Ref_def,open_bisimilarity_eq]
QED

Theorem Sym_open_bisimilarity:
  Sym open_bisimilarity
Proof
  rw[Sym_def, open_bisimilarity_def]
  \\ assume_tac symmetric_app_bisimilarity
  \\ fs[symmetric_def]
QED

(* (Tra) in the paper has an amusing typo that renders the corresponding
   proposition a tautology *)
Theorem open_similarity_transitive:
  open_similarity names e1 e2 ∧ open_similarity names e2 e3 ⇒ open_similarity names e1 e3
Proof
  rw[open_similarity_def] >>
  metis_tac[transitive_app_similarity |> SIMP_RULE std_ss[transitive_def]]
QED

Theorem Tra_open_similarity:
  Tra open_similarity
Proof
  rw[Tra_def]
  \\ irule open_similarity_transitive
  \\ goal_assum drule \\ fs[]
QED

Theorem Tra_open_bisimilarity:
  Tra open_bisimilarity
Proof
  rw[Tra_def, open_bisimilarity_def] >>
  assume_tac transitive_app_bisimilarity >>
  fs[transitive_def] >>
  metis_tac[]
QED

(* -- Permutations and alpha-equivalence -- *)

Definition perm1_def:
  perm1 v1 v2 v = if v = v1 then v2 else if v = v2 then v1 else v
End

Definition perm_exp_def:
  (perm_exp v1 v2 (Var v) = Var (perm1 v1 v2 v))
  ∧ (perm_exp v1 v2 (Prim op l) = Prim op (MAP (perm_exp v1 v2) l))
  ∧ (perm_exp v1 v2 (App e1 e2) = App (perm_exp v1 v2 e1) (perm_exp v1 v2 e2))
  ∧ (perm_exp v1 v2 (Lam v e) = Lam (perm1 v1 v2 v) (perm_exp v1 v2 e))
  ∧ (perm_exp v1 v2 (Letrec l e) =
     Letrec
        (MAP (λ(x,z). (perm1 v1 v2 x, perm_exp v1 v2 z)) l)
        (perm_exp v1 v2 e)
     )
Termination
  WF_REL_TAC ‘measure(exp_size o SND o SND)’ >>
  rw[] >> imp_res_tac exp_size_lemma >> rw[]
End

Theorem perm1_cancel[simp]:
  perm1 v1 v2 (perm1 v1 v2 x) = x
Proof
  rw[perm1_def] >> fs[CaseEq "bool"] >> fs[]
QED

Theorem perm_exp_cancel[simp]:
  ∀v1 v2 e. perm_exp v1 v2 (perm_exp v1 v2 e) = e
Proof
  ho_match_mp_tac perm_exp_ind >>
  rw[perm_exp_def,MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
  rw[LIST_EQ_REWRITE] >>
  gvs[MEM_EL,PULL_EXISTS,EL_MAP] >>
  metis_tac[PAIR,FST,SND]
QED

Theorem perm1_eq_cancel[simp]:
  perm1 v1 v2 v3 = perm1 v1 v2 v4 ⇔ v3 = v4
Proof
  rw[perm1_def] >> simp[]
QED

Theorem perm_exp_eqvt:
  ∀fv2 fv3 e.
    MAP (perm1 fv2 fv3) (freevars e) = freevars(perm_exp fv2 fv3 e)
Proof
  ho_match_mp_tac perm_exp_ind >>
  rw[perm_exp_def,freevars_def,FILTER_MAP,combinTheory.o_DEF,MAP_MAP_o,MAP_FLAT]
  >- (AP_TERM_TAC >> rw[MAP_EQ_f])
  >- (pop_assum (assume_tac o GSYM) >>
      rw[FILTER_MAP,combinTheory.o_DEF])
  >- (rw[ELIM_UNCURRY] >>
      pop_assum (assume_tac o GSYM) >>
      simp[FILTER_APPEND] >>
      simp[FILTER_MAP,combinTheory.o_DEF] >>
      qmatch_goalsub_abbrev_tac ‘a1 ++ a2 = a3 ++ a4’ >>
      ‘a1 = a3 ∧ a2 = a4’ suffices_by simp[] >>
      unabbrev_all_tac >>
      conj_tac >- (AP_TERM_TAC >> rw[FILTER_EQ,MEM_MAP]) >>
      rw[FILTER_FLAT,MAP_FLAT,MAP_MAP_o,combinTheory.o_DEF,FILTER_FILTER] >>
      AP_TERM_TAC >>
      rw[MAP_EQ_f] >>
      PairCases_on ‘x’ >>
      first_assum (drule_then (assume_tac o GSYM o SIMP_RULE std_ss [])) >>
      simp[FILTER_MAP,combinTheory.o_DEF,MEM_MAP])
QED

Theorem closed_perm:
  closed(perm_exp v1 v2 e) = closed e
Proof
  rw[closed_def,GSYM perm_exp_eqvt]
QED

Definition perm_v_def:
  perm_v x y v =
  gen_v (λpath.
          case v_lookup path v of
            (Closure' z e, len) => (Closure' (perm1 x y z) (perm_exp x y e), len)
          | x => x)
End

Theorem perm_v_thm:
  perm_v x y v =
  case v of
    Constructor s xs => Constructor s (MAP (perm_v x y) xs)
  | Closure z e => Closure (perm1 x y z) (perm_exp x y e)
  | v => v
Proof
  ‘∀v1 v2. ((∃v. v1 = perm_v x y v ∧
               v2 = (case v of
                       Constructor s xs => Constructor s (MAP (perm_v x y) xs)
                     | Closure z e => Closure (perm1 x y z) (perm_exp x y e)
                     | v => v)) ∨ v1 = v2)
           ⇒ v1 = v2’ suffices_by metis_tac[] >>
  ho_match_mp_tac v_coinduct >>
  reverse(rw[])
  >- (Cases_on ‘v1’ >> gvs[] >> match_mp_tac EVERY2_refl >> rw[]) >>
  TOP_CASE_TAC
  >- (rw[perm_v_def] >> rw[Once gen_v,v_lookup_Atom])
  >- (rw[Once perm_v_def] >> rw[Once gen_v,v_lookup_Constructor] >>
      ‘MAP (perm_v x y) t =
       MAP (perm_v x y) (GENLIST (λx. EL x t) (LENGTH t))
      ’
       by(AP_TERM_TAC >> CONV_TAC SYM_CONV >>
          match_mp_tac GENLIST_EL >> rw[]) >>
      pop_assum SUBST_ALL_TAC >>
      simp[MAP_GENLIST] >>
      rw[LIST_REL_GENLIST,oEL_THM] >>
      simp[perm_v_def])
  >- (rw[perm_v_def] >> rw[Once gen_v,v_lookup_Closure])
  >- (rw[perm_v_def] >> rw[Once gen_v,v_lookup_Diverge] >> rw[gen_v_Diverge])
  >- (rw[perm_v_def] >> rw[Once gen_v,v_lookup_Error])
QED

Theorem perm_v_clauses:
  perm_v x y (Constructor s xs) = Constructor s (MAP (perm_v x y) xs) ∧
  perm_v x y Diverge = Diverge ∧
  perm_v x y (Atom b) = Atom b ∧
  perm_v x y Error = Error ∧
  perm_v x y (Closure z e) = Closure (perm1 x y z) (perm_exp x y e) ∧
  perm_v x y (Constructor s xs) = Constructor s (MAP (perm_v x y) xs)
Proof
  rpt conj_tac >> rw[Once perm_v_thm] >>
  PURE_ONCE_REWRITE_TAC[perm_v_thm] >>
  simp[]
QED

Theorem perm_v_cancel[simp]:
  perm_v x y (perm_v x y v) = v
Proof
  ‘∀v1 v2. v2 = perm_v x y (perm_v x y v1) ⇒ v1 = v2’ suffices_by metis_tac[] >>
  ho_match_mp_tac v_coinduct >>
  Cases >> TRY(rw[perm_v_thm] >> NO_TAC) >>
  ntac 2 (rw[Once perm_v_thm]) >>
  rw[LIST_REL_MAP2] >>
  match_mp_tac EVERY2_refl >> rw[]
QED

Definition perm_v_prefix_def:
  perm_v_prefix x y v =
  case v of
  | Closure' z e => Closure' (perm1 x y z) (perm_exp x y e)
  | v => v
End

Theorem gen_v_eqvt:
  perm_v v1 v2 (gen_v f) = gen_v(λx. (perm_v_prefix v1 v2 ## I) (f x))
Proof
  ‘∀v v' v1 v2 f. v = perm_v v1 v2 (gen_v f) ∧
                  v' = gen_v(λx. (perm_v_prefix v1 v2 ## I) (f x)) (*∨ v = v'*) ⇒ v = v'’
    suffices_by metis_tac[] >>
  Ho_Rewrite.PURE_REWRITE_TAC [GSYM PULL_EXISTS] >>
  ho_match_mp_tac v_coinduct >>
  reverse(rw[]) >> (*(Cases_on ‘v’ >> rw[] >> match_mp_tac EVERY2_refl >> simp[]) >>*)
  simp[Once gen_v] >> rpt(TOP_CASE_TAC)
  >- (rename1 ‘Atom’ >>
      disj1_tac >> simp[perm_v_def,v_lookup_Atom] >>
      simp[Once gen_v] >>
      simp[Once gen_v] >>
      simp[perm_v_prefix_def])
  >- (rename1 ‘Constructor’ >>
      disj2_tac >> disj1_tac >>
      simp[Once gen_v] >>
      simp[Once perm_v_thm] >>
      simp[Once gen_v,v_lookup_Constructor] >>
      simp[Once perm_v_prefix_def] >>
      rw[MAP_GENLIST,LIST_REL_GENLIST] >>
      qexists_tac ‘v1’ >>
      qexists_tac ‘v2’ >>
      qexists_tac ‘f o CONS n’ >>
      simp[combinTheory.o_DEF])
  >- (rename1 ‘Closure’ >>
      ntac 2 disj2_tac >> disj1_tac >>
      simp[Once gen_v] >>
      simp[Once perm_v_thm] >>
      simp[Once gen_v,v_lookup_Constructor] >>
      simp[Once perm_v_prefix_def])
  >- (rename1 ‘Diverge’ >>
      ntac 3 disj2_tac >> disj1_tac >>
      PURE_ONCE_REWRITE_TAC[gen_v] >>
      simp[] >>
      PURE_ONCE_REWRITE_TAC[perm_v_thm] >>
      simp[] >>
      PURE_ONCE_REWRITE_TAC[perm_v_prefix_def] >>
      simp[])
  >- (rename1 ‘Error’ >>
      ntac 4 disj2_tac >>
      simp[Once gen_v] >>
      simp[Once perm_v_thm] >>
      simp[Once gen_v,v_lookup_Constructor] >>
      simp[Once perm_v_prefix_def])
QED

(* Slow (~10s) *)
Theorem perm_exp_inj:
  ∀v1 v2 e e'. (perm_exp v1 v2 e = perm_exp v1 v2 e') ⇔ e = e'
Proof
  simp[EQ_IMP_THM] >>
  ho_match_mp_tac perm_exp_ind >>
  rpt conj_tac >>
  simp[GSYM RIGHT_FORALL_IMP_THM] >>
  CONV_TAC(RESORT_FORALL_CONV rev) >>
  Cases >> rw[perm_exp_def]
  >- (gvs[LIST_EQ_REWRITE,MEM_EL,PULL_EXISTS,EL_MAP])
  >- (gvs[LIST_EQ_REWRITE,MEM_EL,PULL_EXISTS,EL_MAP] >>
      rw[] >>
      qpat_x_assum ‘perm_exp _ _ _ = _’ (assume_tac o GSYM) >>
      ‘e = e'’ by metis_tac[] >>
      rpt(first_x_assum drule) >>
      rw[] >>
      rpt(pairarg_tac >> gvs[]))
QED

Theorem perm_v_inj:
 (perm_v v1 v2 v = perm_v v1 v2 v') ⇔ v = v'
Proof
  ‘∀v v'.
     perm_v v1 v2 v = perm_v v1 v2 v' ⇒
     v = v'’
    suffices_by metis_tac[] >>
  ho_match_mp_tac v_coinduct >>
  Cases >> Cases >> rw[perm_v_clauses,perm_exp_inj] >>
  pop_assum mp_tac >>
  qid_spec_tac ‘t'’ >>
  Induct_on ‘t’ >- rw[] >>
  strip_tac >> Cases >> rw[]
QED

Definition perm_subst_def:
  perm_subst v1 v2 s =
  (FUN_FMAP (λz. perm_exp v1 v2 (THE(FLOOKUP s (perm1 v1 v2 z)))) {z | perm1 v1 v2 z ∈ FDOM s})
End

Theorem perm_subst_flookup:
  FLOOKUP(perm_subst v1 v2 s) x = OPTION_MAP (perm_exp v1 v2) (FLOOKUP s (perm1 v1 v2 x))
Proof
  rw[perm_subst_def] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [FLOOKUP_FUN_FMAP] >>
  conj_tac
  >- (match_mp_tac FINITE_PRED_11 >> rw[perm1_eq_cancel]) >>
  rw[FLOOKUP_DEF]
QED

Theorem perm_subst_fdom:
  FDOM(perm_subst v1 v2 s) = {z | perm1 v1 v2 z ∈ FDOM s}
Proof
  rw[perm_subst_def] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [FDOM_FMAP] >>
  match_mp_tac FINITE_PRED_11 >> rw[perm1_eq_cancel]
QED

Theorem perm_subst_cancel[simp]:
  perm_subst v1 v2 (perm_subst v1 v2 s) = s
Proof
  rw[fmap_eq_flookup,perm_subst_flookup,OPTION_MAP_COMPOSE,combinTheory.o_DEF]
QED

Theorem fdomsub_eqvt:
  perm_subst v1 v2 (s \\ x) = (perm_subst v1 v2 s \\ perm1 v1 v2 x)
Proof
  rw[fmap_eq_flookup,perm_subst_flookup,DOMSUB_FLOOKUP_THM] >>
  rw[perm1_def] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[])
QED

Theorem FDIFF_eqvt:
  perm_subst v1 v2 (FDIFF s s') =
  FDIFF (perm_subst v1 v2 s) (IMAGE (perm1 v1 v2) s')
Proof
  rw[fmap_eq_flookup,perm_subst_flookup,DOMSUB_FLOOKUP_THM,FDIFF_def,FLOOKUP_DRESTRICT] >>
  rw[perm1_def] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
  metis_tac[]
QED

Theorem subst_eqvt:
  ∀v1 v2 s e.
    perm_exp v1 v2 (subst s e) =
    subst (perm_subst v1 v2 s) (perm_exp v1 v2 e)
Proof
  ntac 2 strip_tac >>
  ho_match_mp_tac subst_ind >>
  rw[subst_def,perm_exp_def,perm_subst_flookup,MAP_MAP_o,MAP_EQ_f,combinTheory.o_DEF,
     fdomsub_eqvt,FDIFF_eqvt]
  >- (TOP_CASE_TAC >> simp[perm_exp_def])
  >- (PairCases_on ‘x’ >> gvs[] >>
      res_tac >>
      simp[] >>
      rw[LIST_TO_SET_MAP,IMAGE_IMAGE,ELIM_UNCURRY,combinTheory.o_DEF])
  >- (rw[LIST_TO_SET_MAP,IMAGE_IMAGE,ELIM_UNCURRY,combinTheory.o_DEF])
QED

Theorem subst_single_eqvt:
  ∀v1 v2 s e1 e.
    perm_exp v1 v2 (subst s e1 e) =
    subst (perm1 v1 v2 s) (perm_exp v1 v2 e1) (perm_exp v1 v2 e)
Proof
  rw[] >>
  qspecl_then [`v1`,`v2`,`FEMPTY |+ (s,e1)`,`e`] assume_tac subst_eqvt >>
  rw[] >> MK_COMB_TAC >> rw[] >> AP_TERM_TAC >>
  rw[fmap_eq_flookup, perm_subst_flookup] >>
  rw[FLOOKUP_DEF] >> gvs[perm1_cancel]
QED

Theorem bind_eqvt:
  ∀v1 v2 s e.
    perm_exp v1 v2 (bind s e) =
    bind (perm_subst v1 v2 s) (perm_exp v1 v2 e)
Proof
  rw[] >> fs[bind_def] >>
  reverse (IF_CASES_TAC) >> gvs[]
  >- (
    fs[perm_exp_def, perm_subst_flookup, PULL_EXISTS] >>
    IF_CASES_TAC >> gvs[] >>
    first_x_assum (qspec_then `perm1 v1 v2 n` assume_tac) >>
    gvs[perm1_cancel, closed_perm]
    ) >>
  reverse (IF_CASES_TAC) >> gvs[subst_eqvt, perm_subst_flookup] >>
  last_x_assum (qspec_then `perm1 v1 v2 n` assume_tac) >> gvs[closed_perm]
QED

Theorem bind_single_eqvt:
  ∀v1 v2 n e1 e.
    perm_exp v1 v2 (bind n e1 e) =
    bind (perm1 v1 v2 n) (perm_exp v1 v2 e1) (perm_exp v1 v2 e)
Proof
  rw[] >> fs[bind_def, FLOOKUP_UPDATE, closed_perm] >>
  IF_CASES_TAC >> gvs[perm_exp_def, subst_single_eqvt]
QED

Theorem expandLets_eqvt:
  ∀v1 v2 i cn nm vs cs.
    perm_exp v1 v2 (expandLets i cn nm vs cs) =
    expandLets i cn (perm1 v1 v2 nm) (MAP (perm1 v1 v2) vs) (perm_exp v1 v2 cs)
Proof
  ntac 2 strip_tac >>
  CONV_TAC(RESORT_FORALL_CONV rev) >>
  Induct_on ‘vs’ >> rw[expandLets_def,perm_exp_def]
QED

Theorem expandCases_eqvt:
  ∀v1 v2 x nm css.
    perm_exp v1 v2 (expandCases x nm css) =
    expandCases (perm_exp v1 v2 x) (perm1 v1 v2 nm)
                (MAP (λ(x,y,z). (x,MAP (perm1 v1 v2) y,perm_exp v1 v2 z)) css)
Proof
  ntac 2 strip_tac >>
  simp[expandCases_def,perm_exp_def] >>
  ho_match_mp_tac expandRows_ind >>
  rw[perm_exp_def,expandRows_def,expandLets_eqvt]
QED

Theorem subst_funs_eqvt:
  ∀ v1 v2 fns e.
    perm_exp v1 v2 (subst_funs fns e) =
    subst_funs (MAP (perm1 v1 v2 ## perm_exp v1 v2) fns) (perm_exp v1 v2 e)
Proof
  rw[subst_funs_def, bind_eqvt] >>
  MK_COMB_TAC >> rw[] >> AP_TERM_TAC >>
  rw[fmap_eq_flookup, perm_subst_flookup, flookup_fupdate_list] >>
  gvs[GSYM MAP_REVERSE, ALOOKUP_MAP] >>
  qmatch_goalsub_abbrev_tac `ALOOKUP (MAP (foo ## bar) l) x` >>
  `ALOOKUP (MAP (foo ## bar) l) x =
    ALOOKUP (MAP (λ(p1,p2). (p1,bar p2)) l) (foo x)` by (
      unabbrev_all_tac >> rename1 `ALOOKUP (MAP _ l)` >>
      Induct_on `l` >> gvs[] >> rw[] >>
      PairCases_on `h` >> fs[] >>
      IF_CASES_TAC
      >- (qspec_then `h0` assume_tac (GEN_ALL perm1_cancel) >> gvs[]) >>
      IF_CASES_TAC >> gvs[]) >>
  rw[] >> unabbrev_all_tac >> rw[ALOOKUP_MAP] >>
  Cases_on `ALOOKUP (REVERSE fns) (perm1 v1 v2 x)` >> gvs[] >>
  fs[perm_exp_def] >>
  rw[MAP_EQ_f] >> PairCases_on `e` >> fs[]
QED

Triviality subst_funs_eqvt_alt:
  ∀ v1 v2 fns e.
    perm_exp v1 v2 (subst_funs fns e) =
    subst_funs (MAP (λ(n,x). (perm1 v1 v2 n, perm_exp v1 v2 x)) fns) (perm_exp v1 v2 e)
Proof
  rw[subst_funs_eqvt] >>
  MK_COMB_TAC >> rw[] >> AP_TERM_TAC >>
  rw[MAP_EQ_f] >> PairCases_on `e` >> fs[]
QED

Theorem eval_to_eqvt:
  ∀v1 v2 k e. perm_v v1 v2 (eval_to k e) =
              eval_to k (perm_exp v1 v2 e)
Proof
  ntac 2 strip_tac >>
  ho_match_mp_tac eval_to_ind >>
  rw[] >>
  rw[perm_v_thm,eval_to_def,perm_exp_def]
  >- (‘eval_op op (MAP (λa. eval_to k a) xs) = eval_op op (MAP (λa. eval_to k a) xs)’ by metis_tac[] >>
      dxrule eval_op_cases >> rw[] >>
      gvs[eval_op_def,MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f,MAP_EQ_CONS,MEM_MAP,PULL_EXISTS,DISJ_IMP_THM,
          FORALL_AND_THM]
      >- (‘∀x. eval_to k a = x ⇔ (perm_v v1 v2 (eval_to k a) = perm_v v1 v2 x)’
            by metis_tac[perm_v_inj] >>
          simp[perm_v_thm] >>
          pop_assum kall_tac >>
          rw[] >>
          TOP_CASE_TAC >> gvs[perm_v_thm])
      >- (rw[el_def] >> gvs[perm_v_thm] >>
          Cases_on ‘eval_to k a’ >> gvs[]
          >- (gvs[AllCaseEqs()] >> metis_tac[])
          >- (last_x_assum (assume_tac o GSYM) >>
              rw[EL_MAP] >>
              TOP_CASE_TAC >> gvs[perm_v_clauses])
          >- (gvs[AllCaseEqs()] >> metis_tac[]))
      >- (IF_CASES_TAC
          >- (simp[] >> gvs[] >>
              IF_CASES_TAC >> rw[] >>
              gvs[] >>
              rename1 ‘eval_to k e’ >>
              first_x_assum(qspec_then ‘e’ mp_tac) >>
              rw[] >>
              ‘∀x. eval_to k e = x ⇔ (perm_v v1 v2 (eval_to k e) = perm_v v1 v2 x)’
                by metis_tac[perm_v_inj] >>
              pop_assum(gvs o single) >>
              gvs[perm_v_thm]) >>
          IF_CASES_TAC
          >- (spose_not_then kall_tac >> gvs[] >> metis_tac[perm_v_clauses,perm_v_cancel]) >>
          qmatch_goalsub_abbrev_tac ‘OPTION_BIND a1’ >>
          qpat_abbrev_tac ‘a2 = getAtoms _’ >>
          ‘a1 = a2’
            by(unabbrev_all_tac >>
               ntac 2 (pop_assum kall_tac) >>
               Induct_on ‘xs’ >>
               rw[getAtoms_def] >>
               gvs[DISJ_IMP_THM,FORALL_AND_THM] >>
               Cases_on ‘eval_to k h’ >> gvs[getAtom_def,perm_v_clauses] >>
               TRY(qpat_x_assum ‘Closure _ _ = _’ (assume_tac o GSYM) >> gvs[]) >>
               TRY(qpat_x_assum ‘Constructor _ _ = _’ (assume_tac o GSYM) >> gvs[]) >>
               TRY(qpat_x_assum ‘Atom _ = _’ (assume_tac o GSYM) >> gvs[]) >>
               gvs[getAtom_def]) >>
          pop_assum(SUBST_ALL_TAC o GSYM) >>
          ntac 2 (pop_assum kall_tac) >>
          Cases_on ‘OPTION_BIND a1 (config.parAtomOp a)’ >>
          gvs[])
      >- (rw[is_eq_def]
          >- (‘∀x. eval_to k a = x ⇔ (perm_v v1 v2 (eval_to k a) = perm_v v1 v2 x)’
                by metis_tac[perm_v_inj] >>
              pop_assum(gvs o single) >>
              gvs[perm_v_thm])
          >- (TOP_CASE_TAC >> fs[MAP_MAP_o,combinTheory.o_DEF] >>
              gvs[AllCaseEqs()] >>
              ‘∀x. eval_to k a = x ⇔ (perm_v v1 v2 (eval_to k a) = perm_v v1 v2 x)’
                by metis_tac[perm_v_inj] >>
              pop_assum(gvs o single) >>
              gvs[perm_v_thm])
          >- (TOP_CASE_TAC >> fs[MAP_MAP_o,combinTheory.o_DEF] >>
              gvs[AllCaseEqs()] >>
              ‘∀x. eval_to k a = x ⇔ (perm_v v1 v2 (eval_to k a) = perm_v v1 v2 x)’
                by metis_tac[perm_v_inj] >>
              pop_assum(gvs o single) >>
              gvs[perm_v_clauses] >> gvs[perm_v_thm] >> metis_tac[LENGTH_MAP])))
  >- (gvs[perm_v_clauses])
  >- (gvs[perm_v_clauses] >>
      ‘∀x. eval_to k e = x ⇔ (perm_v v1 v2 (eval_to k e) = perm_v v1 v2 x)’
        by metis_tac[perm_v_inj] >>
      pop_assum(gvs o single) >>
      gvs[perm_v_clauses])
  >- (Cases_on ‘eval_to k e’ >> gvs[dest_Closure_def,perm_v_clauses] >>
      TRY(qpat_x_assum ‘Closure _ _ = _’ (assume_tac o GSYM) >> gvs[]) >>
      TRY(qpat_x_assum ‘Constructor _ _ = _’ (assume_tac o GSYM) >> gvs[]) >>
      TRY(qpat_x_assum ‘Atom _ = _’ (assume_tac o GSYM) >> gvs[]) >>
      rw[] >>
      simp[GSYM perm_v_thm,bind_single_eqvt])
  >- (
      simp[GSYM perm_v_thm] >>
      rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >>
      rw[subst_funs_eqvt_alt]
      )
QED

Theorem v_lookup_eqvt:
  ∀v1 v2 path v. (perm_v_prefix v1 v2 ## I) (v_lookup path v) =
                 v_lookup path (perm_v v1 v2 v)
Proof
  ntac 2 strip_tac >>
  Induct >>
  rw[v_lookup] >> TOP_CASE_TAC >> rw[perm_v_prefix_def,perm_v_thm] >>
  simp[oEL_THM] >> rw[EL_MAP,perm_v_prefix_def]
QED

Theorem eval_eqvt:
  perm_v v1 v2 (eval e) = eval (perm_exp v1 v2 e)
Proof
  simp[eval_def,gen_v_eqvt] >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM,v_limit_def] >>
  simp[limit_def] >>
  TOP_CASE_TAC
  >- (gvs[some_def] >>
      simp[Once perm_v_prefix_def] >>
      TOP_CASE_TAC >>
      gvs[AllCaseEqs()] >>
      SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
      pop_assum kall_tac >>
      rpt strip_tac >>
      last_x_assum(qspecl_then [‘(perm_v_prefix v1 v2 ## I) x’,‘k’] strip_assume_tac) >>
      first_x_assum drule >> strip_tac >>
      rename1 ‘eval_to k'’ >>
      ‘(perm_v_prefix v1 v2 ## I) (v_lookup path (eval_to k' (perm_exp v1 v2 e))) = (perm_v_prefix v1 v2 ## I) x’
        by metis_tac[] >>
      qpat_x_assum ‘_ = x’ kall_tac >>
      gvs[v_lookup_eqvt,eval_to_eqvt])
  >- (gvs[some_def] >>
      SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
      last_x_assum kall_tac >> rpt strip_tac >>
      IF_CASES_TAC
      >- (SELECT_ELIM_TAC >>
          conj_tac >- metis_tac[] >>
          pop_assum kall_tac >> rw[] >>
          first_x_assum(qspec_then ‘MAX k k'’ mp_tac) >> simp[] >>
          first_x_assum(qspec_then ‘MAX k k'’ mp_tac) >> simp[] >>
          rpt(disch_then(assume_tac o GSYM)) >>
          rw[v_lookup_eqvt,eval_to_eqvt]) >>
      gvs[] >>
      last_x_assum(qspecl_then [‘(perm_v_prefix v1 v2 ## I) x’,‘k’] strip_assume_tac) >>
      first_x_assum drule >> strip_tac >>
      rename1 ‘eval_to k'’ >>
      ‘(perm_v_prefix v1 v2 ## I) (v_lookup path (eval_to k' e)) = (perm_v_prefix v1 v2 ## I) x’
        by metis_tac[] >>
      qpat_x_assum ‘_ = x’ kall_tac >>
      gvs[v_lookup_eqvt,eval_to_eqvt])
QED

Theorem eval_perm_closure:
  eval (perm_exp v1 v2 e) = Closure x e' ⇔ eval e = Closure (perm1 v1 v2 x) (perm_exp v1 v2 e')
Proof
  simp[GSYM eval_eqvt,perm_v_thm,AllCaseEqs()] >>
  metis_tac[perm1_cancel,perm_exp_cancel]
QED

Theorem eval_perm_cons:
  eval (perm_exp v1 v2 e) = Constructor s e' ⇔ eval e = Constructor s (MAP (perm_v v1 v2) e')
Proof
  simp[GSYM eval_eqvt] >>
  simp[Once perm_v_thm,AllCaseEqs()] >>
  rw[EQ_IMP_THM,MAP_MAP_o,combinTheory.o_DEF] >>
  rw[MAP_MAP_o,combinTheory.o_DEF]
QED

Theorem eval_perm_atom:
  eval (perm_exp v1 v2 e) = Atom a ⇔ eval e = Atom a
Proof
  simp[GSYM eval_eqvt] >>
  simp[Once perm_v_thm,AllCaseEqs()]
QED

Theorem eval_perm_diverge:
  eval (perm_exp v1 v2 e) = Diverge ⇔ eval e = Diverge
Proof
  simp[GSYM eval_eqvt] >>
  PURE_ONCE_REWRITE_TAC[perm_v_thm] >>
  simp[AllCaseEqs()]
QED

Theorem eval_perm_error:
  eval (perm_exp v1 v2 e) = Error ⇔ eval e = Error
Proof
  simp[GSYM eval_eqvt] >>
  simp[Once perm_v_thm,AllCaseEqs()]
QED

Theorem compatible_perm:
  compatible (λR. {(e1,e2) | ∃v1 v2 e3 e4. e1 = perm_exp v1 v2 e3  ∧
                                           e2 = perm_exp v1 v2 e4 ∧ R(e3,e4)})
Proof
  rw[compatible_def] >> simp[SUBSET_DEF] >>
  Cases >> rw[FF_def,unfold_rel_def,ELIM_UNCURRY,eval_perm_closure] >>
  simp[closed_perm] >> gvs[eval_perm_closure,eval_perm_cons]
  >- (irule_at (Pos hd) (GSYM perm1_cancel) >>
      irule_at (Pos hd) (GSYM perm_exp_cancel) >>
      rw[] >>
      irule_at (Pos hd) (GSYM perm_exp_cancel) >>
      simp[subst_single_eqvt] >>
      PRED_ASSUM is_forall (irule_at (Pos last)) >>
      simp[subst_single_eqvt,closed_perm])
  >- (qexists_tac ‘MAP (perm_exp v1 v2) es1’ >>
      gvs[eval_thm] >>
      ‘MAP (perm_v v1 v2) (MAP (perm_v v1 v2) v1s) = MAP (perm_v v1 v2) (MAP eval es1)’
        by simp[] >>
      pop_assum(strip_assume_tac o REWRITE_RULE[MAP_MAP_o,combinTheory.o_DEF,perm_v_cancel]) >>
      gvs[MAP_MAP_o,combinTheory.o_DEF,eval_eqvt] >>
      simp[eval_perm_cons] >>
      qexists_tac ‘MAP (perm_exp v1 v2) es2’ >>
      simp[EVERY_MAP,closed_perm,MAP_MAP_o,combinTheory.o_DEF,eval_eqvt] >>
      CONV_TAC(DEPTH_CONV ETA_CONV) >>
      simp[EVERY2_MAP] >>
      drule_at_then (Pos last) match_mp_tac EVERY2_mono >>
      rw[] >>
      metis_tac[]) >>
  gvs[eval_perm_atom,eval_perm_diverge,eval_perm_error]
QED

Theorem app_similarity_eqvt:
  e1 ≲ e2 ⇒ perm_exp x y e1 ≲ perm_exp x y e2
Proof
  strip_tac >>
  match_mp_tac companion_app_similarity >>
  simp[companion_def] >>
  irule_at Any compatible_perm >>
  rw[monotone_def,SUBSET_DEF] >>
  metis_tac[IN_DEF]
QED

Inductive exp_alpha:
[~Refl:]
  (∀e. exp_alpha e e) ∧
(*[~Sym:]
  (∀e e'. exp_alpha e' e ⇒ exp_alpha e e') ∧*)
[~Trans:]
  (∀e e' e''. exp_alpha e e' ∧ exp_alpha e' e'' ⇒ exp_alpha e e'') ∧
[~Lam:]
  (∀e x e'. exp_alpha e e' ⇒ exp_alpha (Lam x e) (Lam x e')) ∧
[~Alpha:]
  (∀e x y. x ≠ y ∧ y ∉ set(freevars e) ⇒ exp_alpha (Lam x e) (Lam y (perm_exp x y e))) ∧
[~Prim:]
  (∀op es es'. LIST_REL exp_alpha es es' ⇒ exp_alpha (Prim op es) (Prim op es')) ∧
[~App:]
  (∀e1 e1' e2 e2'. exp_alpha e1 e1' ∧ exp_alpha e2 e2' ⇒ exp_alpha (App e1 e2) (App e1' e2')) ∧
[~Letrec:]
  (∀e1 e2 funs funs'.
     exp_alpha e1 e2 ∧ MAP FST funs = MAP FST funs' ∧
     LIST_REL exp_alpha (MAP SND funs) (MAP SND funs') ⇒
     exp_alpha (Letrec funs e1) (Letrec funs' e2)) ∧
[~Letrec_Alpha:]
  (∀funs1 funs2 x y e e1.
     x ≠ y ∧
     y ∉ freevars(Letrec (funs1 ++ (x,e)::funs2) e1)
     ⇒
     exp_alpha (Letrec (funs1 ++ (x,e)::funs2) e1)
               (Letrec (MAP (perm1 x y ## perm_exp x y) funs1 ++ (y,perm_exp x y e)::MAP (perm1 x y ## perm_exp x y) funs2) (perm_exp x y e1))) ∧
[~Letrec_Vacuous1:]
  (∀funs1 funs2 x y e e1.
     x ≠ y ∧
     MEM x (MAP FST funs2) ∧
     y ∉ freevars(Letrec (funs1 ++ (x,e)::funs2) e1) ∧
     ¬MEM y (MAP FST funs1) ∧
     ¬MEM y (MAP FST funs2)
     ⇒
     exp_alpha (Letrec (funs1 ++ (x,e)::funs2) e1)
               (Letrec (funs1 ++ (y,perm_exp x y e)::funs2) e1)) ∧
[~Letrec_Vacuous2:]
  (∀funs1 funs2 x y e e1.
     x ≠ y ∧
     x ∉ freevars(Letrec (funs1 ++ funs2) e1) ∧
     ¬MEM x (MAP FST funs1) ∧
     ¬MEM x (MAP FST funs2) ∧
     MEM y (MAP FST funs2) ∧
     y ∉ freevars e
     ⇒
     exp_alpha (Letrec (funs1 ++ (x,e)::funs2) e1)
               (Letrec (funs1 ++ (y,perm_exp x y e)::funs2) e1))
End

Triviality MAP_PAIR_MAP:
  MAP FST (MAP (f ## g) l) = MAP f (MAP FST l) ∧
  MAP SND (MAP (f ## g) l) = MAP g (MAP SND l)
Proof
  rw[MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f]
QED

Theorem exp_alpha_refl:
  x = y ⇒ exp_alpha x y
Proof
  metis_tac[exp_alpha_Refl]
QED

Theorem perm1_right:
  perm1 x y z = h ⇔ z = perm1 x y h
Proof
  rw[perm1_def] >> metis_tac[]
QED

Theorem MAP_MAP_perm_lemma:
  ∀f x y l.
  MAP (λz. MAP (perm1 x y) (f z)) l =
  MAP (MAP (perm1 x y)) (MAP f l)
Proof
  Induct_on ‘l’ >> rw[]
QED

Theorem closed_subst_freevars:
  ∀s x y.
    closed x ∧ closed(subst s x y) ⇒
    set(freevars y) ⊆ {s}
Proof
  rw[] >> pop_assum mp_tac >> drule freevars_subst_single >>
  disch_then(qspecl_then [‘s’,‘y’] mp_tac) >> rw[] >>
  gvs[closed_def, DELETE_DEF, SUBSET_DIFF_EMPTY]
QED

Theorem closed_freevars_subst:
  ∀s x y.
    closed x ∧ set(freevars y) ⊆ {s} ⇒
    closed(subst s x y)
Proof
  rw[] >>
  drule freevars_subst_single >> disch_then (qspecl_then [‘s’,‘y’] mp_tac) >>
  gvs[DELETE_DEF, closed_def] >> rw[] >>
  `freevars (subst s x y) = {}` suffices_by gvs[] >>
  pop_assum SUBST_ALL_TAC >>
  rw[SUBSET_DIFF_EMPTY]
QED

Theorem perm1_simps:
  perm1 x y x = y ∧
  perm1 x x y = y ∧
  perm1 y x x = y
Proof
  rw[perm1_def]
QED

Theorem exp_alpha_subst_closed':
  ∀s e s'.
    (∀e. e ∈ FRANGE s ⇒ closed e) ∧
    (∀e. e ∈ FRANGE s' ⇒ closed e) ∧
    fmap_rel exp_alpha s s'
    ⇒
    exp_alpha (subst s e) (subst s' e)
Proof
  ho_match_mp_tac subst_ind >>
  rw[subst_def,exp_alpha_Refl]
  >- (TOP_CASE_TAC >>
      imp_res_tac fmap_rel_FLOOKUP_imp >>
      simp[exp_alpha_Refl])
  >- (match_mp_tac exp_alpha_Prim >>
      simp[MAP_MAP_o,combinTheory.o_DEF,EVERY2_MAP] >>
      match_mp_tac EVERY2_refl >>
      rw[])
  >- (match_mp_tac exp_alpha_App >> metis_tac[])
  >- (match_mp_tac exp_alpha_Lam >> simp[] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      simp[] >>
      conj_tac >- metis_tac[IN_FRANGE_DOMSUB_suff] >>
      conj_tac >- metis_tac[IN_FRANGE_DOMSUB_suff] >>
      gvs[fmap_rel_def,DOMSUB_FAPPLY_THM])
  >- (match_mp_tac exp_alpha_Letrec >>
      simp[MAP_EQ_f] >>
      rw[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY]
      >- (first_x_assum (match_mp_tac o MP_CANON) >>
          conj_tac >- metis_tac[FDIFF_def,IN_FRANGE_DRESTRICT_suff] >>
          conj_tac >- metis_tac[FDIFF_def,IN_FRANGE_DRESTRICT_suff] >>
          gvs[fmap_rel_def,FDIFF_def,FDOM_DRESTRICT] >>
          simp[DRESTRICT_DEF]) >>
      simp[EVERY2_MAP] >>
      match_mp_tac EVERY2_refl >>
      Cases >> rw[] >>
      first_x_assum (drule_then match_mp_tac) >>
      conj_tac >- metis_tac[FDIFF_def,IN_FRANGE_DRESTRICT_suff] >>
      conj_tac >- metis_tac[FDIFF_def,IN_FRANGE_DRESTRICT_suff] >>
      gvs[fmap_rel_def,FDIFF_def,FDOM_DRESTRICT] >>
      simp[DRESTRICT_DEF])
QED

Theorem fdiff_fdomsub_commute:
  FDIFF (f \\ x) p = FDIFF f p \\ x
Proof
  rw[fmap_eq_flookup,FDIFF_def,FLOOKUP_DRESTRICT,DOMSUB_FLOOKUP_THM] >> rw[]
QED

Theorem fdiff_fdomsub_INSERT:
  FDIFF (f \\ x) p = FDIFF f (x INSERT p)
Proof
  rw[fmap_eq_flookup,FDIFF_def,FLOOKUP_DRESTRICT,DOMSUB_FLOOKUP_THM] >> rw[] >> gvs[]
QED

Theorem subst_fdomsub:
  ∀f e x. x ∉ freevars e ⇒ subst f e = subst (f \\ x) e
Proof
  ho_match_mp_tac subst_ind >>
  rw[subst_def,DOMSUB_FLOOKUP_THM,MAP_EQ_f,DOMSUB_IDEM]
  >- (first_x_assum(match_mp_tac o MP_CANON) >>
      gvs[MEM_MAP] >> metis_tac[])
  >- metis_tac[DOMSUB_COMMUTES,DOMSUB_IDEM]
  >- metis_tac[DOMSUB_COMMUTES,DOMSUB_IDEM]
  >- (pairarg_tac >> gvs[] >>
      simp[fdiff_fdomsub_commute] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR])
  >- (simp[fdiff_fdomsub_commute] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR])
  >- (pairarg_tac >> gvs[] >>
      simp[fdiff_fdomsub_INSERT,ABSORPTION_RWT])
  >- (simp[fdiff_fdomsub_INSERT,ABSORPTION_RWT])
QED

Theorem subst_FDIFF':
  ∀p f x. FINITE p ∧ (∀n. n ∈ p ⇒ n ∉ freevars x) ⇒ subst f x = subst (FDIFF f p) x
Proof
  Induct_on ‘FINITE’ >>
  rpt strip_tac
  >- simp[FDIFF_def,DRESTRICT_UNIV]
  >- (qpat_x_assum ‘∀f x. _ ⇒ subst _ _ = _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single o MP_CANON) >>
      conj_tac >- rw[] >>
      simp[GSYM fdiff_fdomsub_INSERT,fdiff_fdomsub_commute] >>
      match_mp_tac subst_fdomsub >>
      rw[])
QED

Theorem fdiff_bound:
  FDIFF f p = FDIFF f (p ∩ FDOM f)
Proof
  rw[FDIFF_def,fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
  rw[] >> gvs[flookup_thm]
QED

Theorem subst_FDIFF'':
  ∀p f x. (∀n. n ∈ p ⇒ n ∉ freevars x) ⇒ subst f x = subst (FDIFF f p) x
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[fdiff_bound] >>
  match_mp_tac subst_FDIFF' >>
  rw[FINITE_INTER]
QED

Theorem subst_FDIFF:
  ∀f x. subst f x = subst (DRESTRICT f (freevars x)) x
Proof
  rw[] >>
  SIMP_TAC std_ss [SimpR “$=”,Once(GSYM COMPL_COMPL)] >>
  SIMP_TAC std_ss [GSYM FDIFF_def] >>
  match_mp_tac subst_FDIFF'' >>
  rw[]
QED

Theorem exp_alpha_subst_closed'_strong:
  ∀s e s'.
    (∀e. e ∈ FRANGE s ⇒ closed e) ∧
    (∀e. e ∈ FRANGE s' ⇒ closed e) ∧
    fmap_rel exp_alpha (DRESTRICT s (freevars e)) (DRESTRICT s' (freevars e))
    ⇒
    exp_alpha (subst s e) (subst s' e)
Proof
  rw[] >>
  PURE_ONCE_REWRITE_TAC[subst_FDIFF] >>
  match_mp_tac exp_alpha_subst_closed' >>
  simp[] >>
  gvs[IN_FRANGE_FLOOKUP,FLOOKUP_DRESTRICT,PULL_EXISTS] >> metis_tac[]
QED

Theorem exp_alpha_subst_closed_single':
  ∀x e' e e''.
    closed e' ∧ closed e'' ∧ exp_alpha e' e''
    ⇒
    exp_alpha (subst x e' e) (subst x e'' e)
Proof
  rpt strip_tac >>
  match_mp_tac exp_alpha_subst_closed' >>
  rw[fmap_rel_def]
QED

Triviality APPEND_EQ_IMP:
  a = b ∧ c = d ⇒ a ++ c = b ++ d
Proof
  rw[]
QED

Theorem MAP_ID_ON:
  (∀x. MEM x l ⇒ f x = x) ⇒ MAP f l = l
Proof
  Induct_on ‘l’ >> rw[]
QED

Theorem MEM_PERM_IMP:
  MEM x l ⇒
  MEM y (MAP (perm1 x y) l)
Proof
  Induct_on ‘l’ >> rw[perm1_def]
QED

Theorem MEM_PERM_EQ:
  (MEM x (MAP (perm1 x y) l) ⇔ MEM y l) ∧
  (MEM x (MAP (perm1 y x) l) ⇔ MEM y l)
Proof
  conj_tac >> Induct_on ‘l’ >> rw[perm1_def,EQ_IMP_THM] >> simp[]
QED

Theorem MEM_PERM_EQ_GEN:
  (MEM x (MAP (perm1 y z) l) ⇔ MEM (perm1 y z x) l)
Proof
  Induct_on ‘l’ >> rw[perm1_def,EQ_IMP_THM] >> simp[]
QED

Theorem exp_alpha_freevars:
  ∀e e'.
    exp_alpha e e' ⇒ exp$freevars e = exp$freevars e'
Proof
  Induct_on ‘exp_alpha’ >>
  rw[] >>
  simp[GSYM perm_exp_eqvt,FILTER_MAP,combinTheory.o_DEF]
  >- (rename1 ‘FILTER _ l’ >>
      Induct_on ‘l’ >>
      rw[] >> gvs[] >>
      gvs[perm1_def] >> PURE_FULL_CASE_TAC >> gvs[])
  >- (AP_TERM_TAC >>
      pop_assum mp_tac >>
      MAP_EVERY qid_spec_tac [‘es'’,‘es’] >>
      ho_match_mp_tac LIST_REL_ind >>
      rw[])
  >- (ntac 3 AP_TERM_TAC >>
      gvs[EVERY2_MAP] >>
      pop_assum mp_tac >>
      MAP_EVERY qid_spec_tac [‘funs'’,‘funs’] >>
      rpt(pop_assum kall_tac) >>
      ho_match_mp_tac LIST_REL_ind >>
      rw[] >> rpt(pairarg_tac >> gvs[]))
  >- (qmatch_goalsub_abbrev_tac ‘FILTER _ a1 = FILTER _ a2’ >>
      ‘a2 = MAP (perm1 x y) a1’
        by(rw[Abbr ‘a2’,Abbr‘a1’] >>
           rpt(match_mp_tac APPEND_EQ_IMP >> conj_tac) >>
           rw[MAP_FLAT,MAP_MAP_o,combinTheory.o_DEF,PAIR_MAP,ELIM_UNCURRY,
              GSYM perm_exp_eqvt]) >>
      pop_assum SUBST_ALL_TAC >>
      ‘¬MEM y a1’
        by(unabbrev_all_tac >>
           rw[MEM_FLAT,MEM_MAP] >>
           gvs[MEM_MAP,ELIM_UNCURRY] >>
           metis_tac[MEM_MAP]) >>
      pop_assum mp_tac >>
      qpat_x_assum ‘x ≠ y’ mp_tac >>
      rpt(pop_assum kall_tac) >>
      Induct_on ‘a1’ >- rw[] >>
      rw[] >- rw[perm1_def] >>
      rw[perm1_def] >>
      gvs[] >>
      rw[DISJ_EQ_IMP] >>
      gvs[perm1_def,MEM_MAP,MEM_FILTER,PAIR_MAP] >>
      metis_tac[perm1_def,FST,SND,PAIR])
  >- (gvs[FILTER_APPEND] >>
      rpt(match_mp_tac APPEND_EQ_IMP >> conj_tac) >>
      rw[FILTER_EQ,EQ_IMP_THM]
      >- (rename1 ‘FILTER _ l’ >>
          Induct_on ‘l’ >>
          rw[] >>
          gvs[MAP_PAIR_MAP,MEM_PERM_EQ_GEN] >>
          rw[perm1_def] >> gvs[perm1_def,AllCaseEqs()])
      >- (simp[MAP_PAIR_MAP,MEM_PERM_EQ_GEN] >>
          simp[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY,GSYM perm_exp_eqvt] >>
          qspec_then ‘λx. freevars(SND x)’ (simp o single o SIMP_RULE std_ss []) MAP_MAP_perm_lemma >>
          simp[GSYM MAP_FLAT] >>
          simp[FILTER_MAP,combinTheory.o_DEF,perm1_right,perm1_simps] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MAP_ID_ON] >>
          rw[MEM_FILTER,MEM_FLAT,MEM_MAP] >>
          rw[perm1_def] >>
          gvs[MEM_MAP,PULL_EXISTS] >>
          metis_tac[FST,SND,PAIR])
      >- (simp[MAP_PAIR_MAP,MEM_PERM_EQ_GEN,FILTER_MAP,combinTheory.o_DEF,perm1_right,perm1_simps] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MAP_ID_ON] >>
          rw[MEM_FILTER,MEM_FLAT,MEM_MAP] >>
          rw[perm1_def] >>
          gvs[MEM_MAP,PULL_EXISTS] >>
          metis_tac[FST,SND,PAIR])
      >- (simp[MAP_PAIR_MAP,MEM_PERM_EQ_GEN] >>
          simp[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY,GSYM perm_exp_eqvt] >>
          qspec_then ‘λx. freevars(SND x)’ (simp o single o SIMP_RULE std_ss []) MAP_MAP_perm_lemma >>
          simp[GSYM MAP_FLAT] >>
          simp[FILTER_MAP,combinTheory.o_DEF,perm1_right,perm1_simps] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MAP_ID_ON] >>
          rw[MEM_FILTER,MEM_FLAT,MEM_MAP] >>
          rw[perm1_def] >>
          gvs[MEM_MAP,PULL_EXISTS] >>
          metis_tac[FST,SND,PAIR]))
  >- (gvs[FILTER_APPEND] >>
      rpt(match_mp_tac APPEND_EQ_IMP >> conj_tac) >>
      rw[FILTER_EQ,EQ_IMP_THM]
      >- (rename1 ‘FILTER _ l’ >>
          Induct_on ‘l’ >>
          rw[] >>
          gvs[MAP_PAIR_MAP,MEM_PERM_EQ_GEN] >>
          rw[perm1_def] >> gvs[perm1_def,AllCaseEqs()])
      >- (simp[MAP_PAIR_MAP,MEM_PERM_EQ_GEN] >>
          simp[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY,GSYM perm_exp_eqvt] >>
          qspec_then ‘λx. freevars(SND x)’ (simp o single o SIMP_RULE std_ss []) MAP_MAP_perm_lemma >>
          simp[GSYM MAP_FLAT] >>
          simp[FILTER_MAP,combinTheory.o_DEF,perm1_right,perm1_simps] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MAP_ID_ON] >>
          rw[MEM_FILTER,MEM_FLAT,MEM_MAP] >>
          rw[perm1_def] >>
          gvs[MEM_MAP,PULL_EXISTS] >>
          metis_tac[FST,SND,PAIR])
      >- (simp[MAP_PAIR_MAP,MEM_PERM_EQ_GEN,FILTER_MAP,combinTheory.o_DEF,perm1_right,perm1_simps] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MAP_ID_ON] >>
          rw[MEM_FILTER,MEM_FLAT,MEM_MAP] >>
          rw[perm1_def] >>
          gvs[MEM_MAP,PULL_EXISTS] >>
          metis_tac[FST,SND,PAIR])
      >- (simp[MAP_PAIR_MAP,MEM_PERM_EQ_GEN] >>
          simp[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY,GSYM perm_exp_eqvt] >>
          qspec_then ‘λx. freevars(SND x)’ (simp o single o SIMP_RULE std_ss []) MAP_MAP_perm_lemma >>
          simp[GSYM MAP_FLAT] >>
          simp[FILTER_MAP,combinTheory.o_DEF,perm1_right,perm1_simps] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MAP_ID_ON] >>
          rw[MEM_FILTER,MEM_FLAT,MEM_MAP] >>
          rw[perm1_def] >>
          gvs[MEM_MAP,PULL_EXISTS] >>
          metis_tac[FST,SND,PAIR]))
  >- (gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
      gvs[FILTER_APPEND] >>
      rpt(match_mp_tac APPEND_EQ_IMP >> conj_tac) >>
      rw[FILTER_EQ,EQ_IMP_THM] >>
      TRY(rename1 ‘FILTER _ _ = FILTER _ _’ >>
          simp[FILTER_MAP,combinTheory.o_DEF,perm1_right,perm1_simps] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MAP_ID_ON] >>
          conj_tac
          >- (rw[MEM_FILTER,MEM_FLAT,MEM_MAP] >>
              rw[perm1_def] >>
              gvs[MEM_MAP,PULL_EXISTS] >>
              metis_tac[FST,SND,PAIR]) >>
          rw[FILTER_EQ,EQ_IMP_THM] >>
          gvs[perm1_def] >>
          gvs[MEM_MAP,MEM_FLAT,ELIM_UNCURRY,PULL_EXISTS] >>
          metis_tac[FST,SND,PAIR]) >>
      gvs[MEM_MAP,MEM_FLAT,ELIM_UNCURRY,PULL_EXISTS] >>
      metis_tac[FST,SND,PAIR])
  >- (gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
      gvs[FILTER_APPEND] >>
      rpt(match_mp_tac APPEND_EQ_IMP >> conj_tac) >>
      rw[FILTER_EQ,EQ_IMP_THM] >>
      TRY(rename1 ‘FILTER _ _ = FILTER _ _’ >>
          simp[FILTER_MAP,combinTheory.o_DEF,perm1_right,perm1_simps] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MAP_ID_ON] >>
          conj_tac
          >- (rw[MEM_FILTER,MEM_FLAT,MEM_MAP] >>
              rw[perm1_def] >>
              gvs[MEM_MAP,PULL_EXISTS] >>
              metis_tac[FST,SND,PAIR]) >>
          rw[FILTER_EQ,EQ_IMP_THM] >>
          gvs[perm1_def] >>
          gvs[MEM_MAP,MEM_FLAT,ELIM_UNCURRY,PULL_EXISTS] >>
          metis_tac[FST,SND,PAIR]) >>
      gvs[MEM_MAP,MEM_FLAT,ELIM_UNCURRY,PULL_EXISTS] >>
      metis_tac[FST,SND,PAIR])
QED

Theorem exp_alpha_closed:
  ∀e e'.
    exp_alpha e e' ⇒ closed e = closed e'
Proof
  rw[closed_def] >> imp_res_tac exp_alpha_freevars >> rw[]
QED

Theorem perm_exp_id:
  ∀x e.
    perm_exp x x e = e
Proof
  ‘∀x y e. x = y ⇒ perm_exp x y e = e’
    suffices_by metis_tac[] >>
  ho_match_mp_tac perm_exp_ind >>
  rw[perm_exp_def,perm1_simps]
  >- gvs[LIST_EQ_REWRITE,MEM_EL,EL_MAP,PULL_EXISTS]
  >- (gvs[LIST_EQ_REWRITE,MEM_EL,EL_MAP,PULL_EXISTS,ELIM_UNCURRY] >>
      metis_tac[PAIR,FST,SND])
QED

Theorem perm1_sym:
  perm1 x y z = perm1 y x z
Proof
  rw[perm1_def]
QED

Theorem perm_exp_sym:
  ∀x y e.
    perm_exp x y e = perm_exp y x e
Proof
  ho_match_mp_tac perm_exp_ind >>
  rw[perm_exp_def,perm1_sym,MAP_EQ_f] >>
  gvs[] >> pairarg_tac >> gvs[MAP_EQ_f,perm1_sym] >> res_tac
QED

Theorem fresh_list:
  ∀s. FINITE s ⇒ ∃x. x ∉ s:('a list set)
Proof
  metis_tac[GSYM INFINITE_LIST_UNIV,NOT_IN_FINITE]
QED

Theorem exp_alpha_sym:
  ∀e e'.
    exp_alpha e e' ⇒ exp_alpha e' e
Proof
  Induct_on ‘exp_alpha’ >> rw[exp_alpha_Refl,exp_alpha_Lam,exp_alpha_Prim,exp_alpha_App]
  >- metis_tac[exp_alpha_Trans]
  >- (match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Alpha >>
      qexists_tac ‘x’ >>
      simp[GSYM perm_exp_eqvt,MEM_MAP] >>
      conj_tac >- (rw[perm1_def]) >>
      simp[perm_exp_sym,exp_alpha_Refl])
  >- (match_mp_tac exp_alpha_Prim >> simp[] >>
      drule_at_then Any match_mp_tac EVERY2_sym >>
      metis_tac[exp_alpha_Trans])
  >- (match_mp_tac exp_alpha_Letrec >> simp[] >>
      drule_at_then (Pos last) match_mp_tac EVERY2_sym >>
      metis_tac[exp_alpha_Trans])
  >- (gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
      gvs[MEM_MAP,ELIM_UNCURRY,PULL_EXISTS] >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Alpha >>
      qexists_tac ‘x’ >>
      conj_tac >- simp[] >>
      conj_tac
      >- (spose_not_then strip_assume_tac >>
          gvs[MEM_MAP,MEM_FILTER,GSYM perm_exp_eqvt,PAIR_MAP,ELIM_UNCURRY,PULL_EXISTS] >>
          metis_tac[perm1_def,PAIR,FST,SND]) >>
      simp[perm_exp_sym,perm1_sym,exp_alpha_Refl,MAP_MAP_o,combinTheory.o_DEF,PAIR_MAP])
  >- (gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
      gvs[MEM_MAP,ELIM_UNCURRY,PULL_EXISTS] >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Alpha >>
      qexists_tac ‘x’ >>
      conj_tac >- simp[] >>
      conj_tac
      >- (spose_not_then strip_assume_tac >>
          gvs[MEM_MAP,MEM_FILTER,GSYM perm_exp_eqvt,PAIR_MAP,ELIM_UNCURRY,PULL_EXISTS] >>
          metis_tac[perm1_def,PAIR,FST,SND]) >>
      simp[perm_exp_sym,perm1_sym,exp_alpha_Refl,MAP_MAP_o,combinTheory.o_DEF,PAIR_MAP])
  >- (gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
      gvs[MEM_MAP,ELIM_UNCURRY,PULL_EXISTS] >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Alpha >>
      qexists_tac ‘x’ >>
      conj_tac >- simp[] >>
      conj_tac
      >- (spose_not_then strip_assume_tac >>
          gvs[MEM_MAP,MEM_FILTER,GSYM perm_exp_eqvt,PAIR_MAP,ELIM_UNCURRY,PULL_EXISTS] >>
          metis_tac[perm1_def,PAIR,FST,SND]) >>
      simp[perm_exp_sym,perm1_sym,exp_alpha_Refl,MAP_MAP_o,combinTheory.o_DEF,PAIR_MAP])
  >- (gvs[MEM_FILTER] >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Vacuous2 >>
      qexists_tac ‘x’ >>
      gvs[MEM_FILTER,GSYM perm_exp_eqvt,MEM_PERM_EQ] >>
      simp[perm_exp_sym,exp_alpha_refl])
  >- (match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Vacuous1 >>
      qexists_tac ‘x’ >>
      gvs[MEM_FILTER,GSYM perm_exp_eqvt,MEM_PERM_EQ] >>
      simp[perm_exp_sym,exp_alpha_refl])
QED

Theorem exp_alpha_perm_irrel:
  ∀x y e.
    x ∉ freevars e ∧ y ∉ freevars e
    ⇒
    exp_alpha e (perm_exp x y e)
Proof
  ho_match_mp_tac perm_exp_ind >>
  PURE_REWRITE_TAC[perm_exp_def] >>
  rpt strip_tac
  >- gvs[perm1_def,exp_alpha_Refl]
  >- (match_mp_tac exp_alpha_Prim >>
      simp[EVERY2_MAP] >>
      match_mp_tac EVERY2_refl >>
      rw[] >> first_x_assum drule >>
      gvs[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
      metis_tac[])
  >- (match_mp_tac exp_alpha_App >> gvs[])
  >- (Cases_on ‘x = y’ >- (gvs[perm_exp_id,perm1_simps,exp_alpha_Refl]) >>
      Cases_on ‘x = x'’ >> Cases_on ‘y = x'’ >> gvs[perm1_simps]
      >- (match_mp_tac exp_alpha_Alpha >> gvs[MEM_FILTER])
      >- (PURE_ONCE_REWRITE_TAC[perm_exp_sym] >>
          match_mp_tac exp_alpha_Alpha >> gvs[MEM_FILTER])
      >- (simp[perm1_def] >> match_mp_tac exp_alpha_Lam >> gvs[MEM_FILTER]))
  >- (Cases_on ‘x = y’ >- (simp[perm_exp_id,perm1_simps,exp_alpha_Refl,ELIM_UNCURRY]) >>
      Cases_on ‘MEM x (MAP FST l)’
      >- (qpat_x_assum ‘MEM _ (MAP FST l)’ (strip_assume_tac o REWRITE_RULE[MEM_MAP]) >>
          qpat_x_assum ‘MEM _ _’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
          simp[] >>
          pairarg_tac >>
          simp[perm1_simps] >>
          simp[ELIM_UNCURRY] >>
          simp[GSYM PAIR_MAP] >>
          CONV_TAC(DEPTH_CONV ETA_CONV) >>
          match_mp_tac exp_alpha_Letrec_Alpha >>
          gvs[MEM_FILTER]) >>
      Cases_on ‘MEM y (MAP FST l)’
      >- (qpat_x_assum ‘MEM _ (MAP FST l)’ (strip_assume_tac o REWRITE_RULE[MEM_MAP]) >>
          qpat_x_assum ‘MEM _ _’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
          simp[] >>
          pairarg_tac >>
          simp[perm1_simps] >>
          simp[ELIM_UNCURRY] >>
          simp[GSYM PAIR_MAP] >>
          CONV_TAC(DEPTH_CONV ETA_CONV) >>
          rename1 ‘perm1 w v’ >>
          ‘perm1 w v = perm1 v w’ by metis_tac[perm1_sym] >>
          ‘perm_exp w v = perm_exp v w’ by metis_tac[perm_exp_sym] >>
          ntac 2 (pop_assum SUBST_ALL_TAC) >>
          match_mp_tac exp_alpha_Letrec_Alpha >>
          gvs[MEM_FILTER]) >>
      gvs[MEM_FILTER] >>
      match_mp_tac exp_alpha_Letrec >>
      simp[MAP_MAP_o,combinTheory.o_DEF,EVERY2_MAP,MAP_EQ_f] >>
      conj_tac
      >- (PairCases >> rw[] >> gvs[MEM_MAP,MEM_FLAT,ELIM_UNCURRY] >>
          metis_tac[FST,SND,PAIR,perm1_def]) >>
      match_mp_tac EVERY2_refl >>
      PairCases >> rw[] >> gvs[MEM_MAP,MEM_FLAT,ELIM_UNCURRY] >>
      metis_tac[FST,SND,PAIR,perm1_def])
QED

Theorem perm_exp_compose:
  ∀z å e x y.
    perm_exp x y (perm_exp z å e) = perm_exp (perm1 x y z) (perm1 x y å) (perm_exp x y e)
Proof
  ho_match_mp_tac perm_exp_ind >>
  rw[perm_exp_def]
  >- (rw[perm1_def] >> rw[] >> gvs[])
  >- (simp[MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f])
  >- (rw[perm1_def] >> rw[] >> gvs[])
  >- (simp[MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f] >>
      PairCases >> rw[]
      >- (rw[perm1_def] >> rw[] >> gvs[]) >>
      metis_tac[])
QED

Theorem exp_alpha_perm_closed:
  exp_alpha e e' ⇒
  exp_alpha (perm_exp x y e) (perm_exp x y e')
Proof
  Cases_on ‘x = y’ >- simp[perm_exp_id] >>
  pop_assum mp_tac >>
  Induct_on ‘exp_alpha’ >>
  PURE_REWRITE_TAC[perm_exp_def,exp_alpha_refl] >>
  rpt strip_tac
  >- metis_tac[exp_alpha_refl]
  >- metis_tac[exp_alpha_Trans]
  >- metis_tac[exp_alpha_Lam]
  >- (match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Alpha >>
      qexists_tac ‘perm1 x y y'’ >>
      simp[perm1_eq_cancel,GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
      simp[Once perm_exp_compose,SimpR “exp_alpha”] >>
      simp[exp_alpha_refl])
  >- (match_mp_tac exp_alpha_Prim >>
      simp[EVERY2_MAP] >>
      drule_at_then (Pos last) match_mp_tac EVERY2_mono >>
      rw[])
  >- (match_mp_tac exp_alpha_App >>
      simp[EVERY2_MAP] >>
      drule_at_then (Pos last) match_mp_tac EVERY2_mono >>
      rw[])
  >- (match_mp_tac exp_alpha_Letrec >>
      simp[EVERY2_MAP,MAP_MAP_o,combinTheory.o_DEF] >>
      conj_tac
      >- (qpat_x_assum ‘MAP _ _ = MAP _ _’ mp_tac >>
          rpt(pop_assum kall_tac) >>
          qid_spec_tac ‘funs'’ >>
          Induct_on ‘funs’ >- rw[] >>
          PairCases >> Cases >> rw[] >>
          pairarg_tac >> rw[]) >>
      gvs[EVERY2_MAP] >>
      drule_at_then (Pos last) match_mp_tac EVERY2_mono >>
      rw[] >>
      rw[ELIM_UNCURRY])
  >- (simp[] >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Alpha >>
      qexists_tac ‘perm1 x y y'’ >>
      simp[perm1_eq_cancel,GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
      conj_asm1_tac
      >- (gvs[MEM_FILTER] >>
          gvs[DISJ_EQ_IMP |> PURE_ONCE_REWRITE_RULE[DISJ_SYM],MEM_MAP,ELIM_UNCURRY,PULL_EXISTS,
              GSYM perm_exp_eqvt] >>
          metis_tac[FST,SND,PAIR]) >>
      simp[MAP_MAP_o,ELIM_UNCURRY,combinTheory.o_DEF] >>
      match_mp_tac exp_alpha_refl >>
      simp[] >>
      reverse conj_tac
      >- simp[SimpR “$=”,Once perm_exp_compose] >>
      rpt(match_mp_tac APPEND_EQ_IMP >> conj_tac) >>
      rw[MAP_EQ_f] >>
      TRY(rename1 ‘perm1 _ _ _ = perm1 _ _ _’ >>
          rw[perm1_def] >> gvs[] >> NO_TAC) >>
      simp[SimpR “$=”,Once perm_exp_compose])
  >- (simp[] >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Vacuous1 >>
      qexists_tac ‘perm1 x y y'’ >>
      simp[perm1_eq_cancel,GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
      cheat)
  >- (simp[] >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Vacuous2 >>
      qexists_tac ‘perm1 x y y'’ >>
      simp[perm1_eq_cancel,GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
      cheat)
QED

Theorem exp_alpha_perm_closed_sym:
  exp_alpha (perm_exp x y e) (perm_exp x y e') ⇒
  exp_alpha e e'
Proof
  metis_tac[exp_alpha_perm_closed,perm_exp_cancel]
QED

Theorem FLOOKUP_perm_keys[simp]:
  FLOOKUP (MAP_KEYS (perm1 x y) s) z =
  FLOOKUP s (perm1 x y z)
Proof
  CONV_TAC SYM_CONV >>
  qspec_then ‘perm1 x y’
             (dep_rewrite.DEP_ONCE_REWRITE_TAC o single o GSYM)
             (Q.GEN ‘f’ FLOOKUP_MAP_KEYS_MAPPED) >>
  rw[INJ_DEF]
QED

Theorem FRANGE_MEM_eqvt:
  e ∈ FRANGE (perm_subst x y s) ⇔ perm_exp x y e ∈ FRANGE (MAP_KEYS (perm1 x y) s)
Proof
  rw[IN_FRANGE_FLOOKUP,perm_subst_flookup] >>
  rw[EQ_IMP_THM] >> metis_tac[perm_exp_cancel]
QED

Theorem exp_alpha_subst_closed:
  ∀x y s e.
    x ≠ y ∧ y ∉ freevars e ∧
    x ∈ FDOM s ∧
    y ∉ FDOM s ∧
    (∀e. e ∈ FRANGE s ⇒ closed e) ⇒
    exp_alpha (subst s e) (subst (MAP_KEYS (perm1 x y) s) (perm_exp x y e))
Proof
  ntac 2 strip_tac >>
  ho_match_mp_tac subst_ind >>
  rw[subst_def,perm_exp_def] >> gvs[perm1_simps]
  >- (TOP_CASE_TAC >> simp[exp_alpha_Refl] >>
      rw[perm1_def] >>
      gvs[flookup_thm,exp_alpha_Refl])
  >- (match_mp_tac exp_alpha_Prim >>
      simp[MAP_MAP_o,combinTheory.o_DEF,EVERY2_MAP] >>
      match_mp_tac EVERY2_refl >>
      rw[] >>
      first_x_assum drule >>
      rpt(disch_then drule) >>
      simp[] >>
      gvs[SUBSET_DEF,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
      metis_tac[])
  >- (match_mp_tac exp_alpha_App >> simp[])
  >- (Cases_on ‘x = s'’
      >- (gvs[perm1_simps] >>
          match_mp_tac exp_alpha_Trans >>
          irule_at (Pos hd) exp_alpha_Alpha >>
          qexists_tac ‘y’ >>
          conj_tac >- simp[] >>
          conj_tac
          >- (dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
              rw[] >> metis_tac[IN_FRANGE_DOMSUB_suff]) >>
          simp[subst_eqvt] >>
          match_mp_tac exp_alpha_Lam >>
          match_mp_tac exp_alpha_subst_closed' >>
          conj_tac
          >- (simp[fdomsub_eqvt] >>
              ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
              simp[FRANGE_MEM_eqvt] >>
              gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
              gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
              metis_tac[closed_perm]) >>
          rw[fmap_rel_OPTREL_FLOOKUP,DOMSUB_FLOOKUP_THM,fdomsub_eqvt,perm1_simps] >>
          rw[] >>
          rw[perm_subst_flookup] >>
          rename [‘FLOOKUP s (perm1 x y z)’] >>
          Cases_on ‘FLOOKUP s (perm1 x y z)’ >>
          gvs[] >>
          match_mp_tac exp_alpha_sym >>
          match_mp_tac exp_alpha_perm_irrel >>
          gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
          res_tac >>
          fs[closed_def]) >>
      Cases_on ‘y = s'’
      >- (gvs[perm1_simps] >>
          match_mp_tac exp_alpha_Trans >>
          irule_at (Pos hd) exp_alpha_Alpha >>
          qexists_tac ‘x’ >>
          conj_tac >- simp[] >>
          conj_tac
          >- (dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
              rw[] >> metis_tac[IN_FRANGE_DOMSUB_suff]) >>
          simp[subst_eqvt] >>
          match_mp_tac exp_alpha_Lam >>
          simp[perm_exp_sym] >>
          match_mp_tac exp_alpha_subst_closed' >>
          conj_tac
          >- (simp[fdomsub_eqvt] >>
              ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
              simp[FRANGE_MEM_eqvt] >>
              gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
              gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
              metis_tac[closed_perm]) >>
          rw[fmap_rel_OPTREL_FLOOKUP,DOMSUB_FLOOKUP_THM,fdomsub_eqvt,perm1_simps] >>
          rw[] >>
          rw[perm_subst_flookup] >>
          simp[perm1_sym] >>
          rename [‘FLOOKUP s (perm1 x y z)’] >>
          Cases_on ‘FLOOKUP s (perm1 x y z)’ >>
          gvs[] >>
          match_mp_tac exp_alpha_sym >>
          match_mp_tac exp_alpha_perm_irrel >>
          gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
          res_tac >>
          fs[closed_def]) >>
      simp[perm1_def] >>
      match_mp_tac exp_alpha_Lam >>
      match_mp_tac exp_alpha_Trans >>
      first_x_assum(irule_at (Pos hd)) >>
      conj_tac >- simp[] >>
      conj_tac
      >- (ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
          gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS]) >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC[GSYM DOMSUB_MAP_KEYS] >>
      conj_tac >- (rw[BIJ_DEF,INJ_DEF,SURJ_DEF] >> metis_tac[perm1_cancel]) >>
      simp[perm1_def,exp_alpha_refl])
  >- (gvs[perm1_simps] >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Alpha >>
      qexists_tac ‘x’ >>
      conj_tac >- simp[] >>
      conj_tac
      >- (dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
          rw[] >> metis_tac[IN_FRANGE_DOMSUB_suff]) >>
      simp[subst_eqvt] >>
      match_mp_tac exp_alpha_Lam >>
      simp[perm_exp_sym] >>
      match_mp_tac exp_alpha_subst_closed' >>
      conj_tac
      >- (simp[fdomsub_eqvt] >>
          ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
          simp[FRANGE_MEM_eqvt] >>
          gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
          metis_tac[closed_perm]) >>
      conj_tac
      >- (ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
          gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
          metis_tac[closed_perm]) >>
      rw[fmap_rel_OPTREL_FLOOKUP,DOMSUB_FLOOKUP_THM,fdomsub_eqvt,perm1_simps] >>
      rw[] >>
      rw[perm_subst_flookup] >>
      simp[perm1_sym] >>
      rename [‘FLOOKUP s (perm1 x y z)’] >>
      Cases_on ‘FLOOKUP s (perm1 x y z)’ >>
      gvs[] >>
      match_mp_tac exp_alpha_sym >>
      match_mp_tac exp_alpha_perm_irrel >>
      gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
      res_tac >>
      fs[closed_def])
  >- (gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
      simp[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
      cheat)
  >- (gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
      simp[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
      cheat)
QED

Theorem exp_alpha_subst_closed_single:
  ∀y x e' e.
    x ≠ y ∧ y ∉ freevars e ∧ closed e' ⇒
    exp_alpha (subst x e' e) (subst y e' (perm_exp x y e))
Proof
  rpt strip_tac >>
  match_mp_tac exp_alpha_Trans >>
  irule_at (Pos hd) exp_alpha_subst_closed >>
  goal_assum drule >> goal_assum drule >>
  simp[] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[MAP_KEYS_FUPDATE] >>
  simp[INJ_DEF,perm1_simps,exp_alpha_refl]
QED

Theorem exp_alpha_subst_all_closed'':
  ∀f e e'.
    (∀n v. v ∈ FRANGE f ⇒ closed v) ∧ exp_alpha e e' ⇒
    exp_alpha (subst f e) (subst f e')
Proof
  cheat
(*
  Induct_on ‘exp_alpha’ >>
  rw[subst_def,exp_alpha_Refl]
  >- metis_tac[exp_alpha_Trans]
  >- (rw[] >> match_mp_tac exp_alpha_Lam >> simp[] >>
      first_x_assum match_mp_tac >>
      metis_tac[IN_FRANGE_DOMSUB_suff])
  >- (
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Alpha >>
      goal_assum drule >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
      conj_tac >- metis_tac[IN_FRANGE_DOMSUB_suff] >>
      simp[subst_eqvt,fdomsub_eqvt,perm1_simps] >>
      match_mp_tac exp_alpha_Lam >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_subst_closed >>
      goal_assum drule >>
      simp[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN,perm1_simps]

      match_mp_tac exp_alpha_subst_closed'_strong >>
      irule_at (Pos hd) exp_alpha_subst_closed'_strong >>

      conj_tac
      >- (ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
          simp[FRANGE_MEM_eqvt] >>
          gvs[IN_FRANGE_FLOOKUP] >>
          metis_tac[closed_perm]) >>
      conj_tac >- metis_tac[IN_FRANGE_DOMSUB_suff] >>
      rw[fmap_rel_OPTREL_FLOOKUP,DOMSUB_FLOOKUP_THM] >>
      simp[perm_subst_flookup]

      rw[] >>
      Cases_on ‘x = k’ >> simp[perm1_simps]
      >- (gvs[] >>
      Cases_on ‘FLOOKUP f k’ >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_subst_closed >>
      goal_assum drule >>
      simp[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN,perm1_simps]

      match_mp_tac exp_alpha_subst_closed' >>
      conj_tac
      >- (ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
          simp[FRANGE_MEM_eqvt] >>
          gvs[IN_FRANGE_FLOOKUP] >>
          metis_tac[closed_perm]) >>
      conj_tac >- metis_tac[IN_FRANGE_DOMSUB_suff] >>
      rw[fmap_rel_OPTREL_FLOOKUP,DOMSUB_FLOOKUP_THM] >>
      rw[] >>
      rw[perm_subst_flookup] >>
      Cases_

      simp[freevars_subst] >>
      simp[subst_eqvt] >>
      rw[perm1_def] >>
      dep_
     )
  cheat
(*
  >- (match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Alpha >>
      goal_assum drule >>
      simp[freevars_subst] >>
      simp[subst_eqvt] >>
      rw[perm1_def] >>

      match_mp_tac exp_alpha_Lam >>
      match_mp_tac exp_alpha_subst_closed' >>
      simp[closed_perm] >>
      match_mp_tac exp_alpha_sym >>
      match_mp_tac exp_alpha_perm_irrel >>
      gvs[closed_def]
      match_mp_tac exp_alpha_Alpha >>
      conj_tac >- cheat >>

      >- (dep_rewrite.DEP_ONCE_REWRITE_TAC [subst_ignore] >>
          simp[GSYM perm_exp_eqvt,MEM_MAP] >>
          conj_tac >- rw[perm1_def] >>
          match_mp_tac exp_alpha_Alpha >>
          rw[])
      >- (dep_rewrite.DEP_ONCE_REWRITE_TAC [subst_ignore] >>
          simp[GSYM perm_exp_eqvt,MEM_MAP] >>
          match_mp_tac exp_alpha_Alpha >>
          rw[])
      >- (match_mp_tac exp_alpha_Trans >>
          irule_at (Pos hd) exp_alpha_Alpha >>
          qexists_tac ‘y’ >>
          simp[freevars_subst] >>
          simp[subst_eqvt] >>
          rw[perm1_def] >>
          match_mp_tac exp_alpha_Lam >>
          match_mp_tac exp_alpha_subst_closed' >>
          simp[closed_perm] >>
          match_mp_tac exp_alpha_sym >>
          match_mp_tac exp_alpha_perm_irrel >>
          gvs[closed_def]))
  >- (match_mp_tac exp_alpha_Prim >>
      simp[EVERY2_MAP] >>
      drule_at_then Any match_mp_tac EVERY2_mono >>
      rw[])
  >- (match_mp_tac exp_alpha_App >> simp[])
  >- (rw[]
      >- (match_mp_tac exp_alpha_Letrec >> simp[] >> gvs[EVERY2_MAP] >>
          drule_at_then Any match_mp_tac EVERY2_mono >> rw[]) >>
      match_mp_tac exp_alpha_Letrec >>
      simp[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
      CONV_TAC(DEPTH_CONV ETA_CONV) >> gvs[] >>
      gvs[EVERY2_MAP] >>
      drule_at_then Any match_mp_tac EVERY2_mono >> rw[])
  >- (rw[] >>
      TRY(match_mp_tac exp_alpha_Letrec_Alpha >> simp[] >> NO_TAC) >>
      gvs[]
      >- (‘x' = x’
            by(gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          pop_assum SUBST_ALL_TAC >>
          Cases_on ‘MEM y (MAP FST funs1)’
          >- (gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          Cases_on ‘MEM y (MAP FST funs2)’
          >- (gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          gvs[MEM_FILTER] >>
          drule MEM_PERM_IMP >>
          disch_then(qspec_then ‘y’ assume_tac) >>
          gvs[MAP_MAP_o,combinTheory.o_DEF] >>
          simp[PAIR_MAP] >>
          ‘MAP (λx'. (perm1 x y (FST x'),subst x e' (perm_exp x y (SND x')))) funs1 =
           MAP (perm1 x y ## perm_exp x y) funs1’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ‘MAP (λx'. (perm1 x y (FST x'),subst x e' (perm_exp x y (SND x')))) funs2 =
           MAP (perm1 x y ## perm_exp x y) funs2’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ntac 2 (pop_assum SUBST_ALL_TAC) >>
          simp[subst_ignore,GSYM perm_exp_eqvt,MEM_PERM_EQ] >>
          match_mp_tac exp_alpha_Letrec_Alpha >>
          rw[freevars_def,MEM_FILTER])
      >- (Cases_on ‘MEM y (MAP FST funs1)’
          >- (gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          Cases_on ‘MEM y (MAP FST funs2)’
          >- (gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          gvs[MEM_FILTER] >>
          gvs[MAP_MAP_o,combinTheory.o_DEF] >>
          simp[PAIR_MAP] >>
          ‘MAP (λx'. (perm1 x y (FST x'),subst x e' (perm_exp x y (SND x')))) funs1 =
           MAP (perm1 x y ## perm_exp x y) funs1’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ‘MAP (λx'. (perm1 x y (FST x'),subst x e' (perm_exp x y (SND x')))) funs2 =
           MAP (perm1 x y ## perm_exp x y) funs2’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ntac 2 (pop_assum SUBST_ALL_TAC) >>
          simp[subst_ignore,GSYM perm_exp_eqvt,MEM_PERM_EQ] >>
          match_mp_tac exp_alpha_Letrec_Alpha >>
          rw[freevars_def,MEM_FILTER])
      >- (‘x' = x’
            by(gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          pop_assum SUBST_ALL_TAC >>
          Cases_on ‘MEM y (MAP FST funs1)’
          >- (gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          Cases_on ‘MEM y (MAP FST funs2)’
          >- (gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          gvs[MEM_FILTER] >>
          drule MEM_PERM_IMP >>
          disch_then(qspec_then ‘y’ assume_tac) >>
          gvs[MAP_MAP_o,combinTheory.o_DEF] >>
          simp[PAIR_MAP] >>
          ‘MAP (λx'. (perm1 x y (FST x'),subst x e' (perm_exp x y (SND x')))) funs1 =
           MAP (perm1 x y ## perm_exp x y) funs1’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ‘MAP (λx'. (perm1 x y (FST x'),subst x e' (perm_exp x y (SND x')))) funs2 =
           MAP (perm1 x y ## perm_exp x y) funs2’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ntac 2 (pop_assum SUBST_ALL_TAC) >>
          simp[subst_ignore,GSYM perm_exp_eqvt,MEM_PERM_EQ] >>
          match_mp_tac exp_alpha_Letrec_Alpha >>
          rw[freevars_def,MEM_FILTER])
      >- (‘x' = y’
            by(fs[MEM_MAP,PAIR_MAP,PULL_EXISTS] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          pop_assum SUBST_ALL_TAC >>
          gvs[MEM_FILTER] >>
          ‘MAP (λ(g,z). (g,subst y e' z)) funs1 = funs1’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac MAP_ID_ON >>
               PairCases >> rw[] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               fs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ‘MAP (λ(g,z). (g,subst y e' z)) funs2 = funs2’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac MAP_ID_ON >>
               PairCases >> rw[] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               fs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ntac 2 (pop_assum SUBST_ALL_TAC) >>
          simp[subst_ignore,GSYM perm_exp_eqvt,MEM_PERM_EQ] >>
          match_mp_tac exp_alpha_Letrec_Alpha >>
          rw[freevars_def,MEM_FILTER])
      >- (gvs[MEM_FILTER] >>
          rename1 ‘x ≠ y’ >>
          ‘MAP (λ(g,z). (g,subst y e' z)) funs1 = funs1’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac MAP_ID_ON >>
               PairCases >> rw[] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ‘MAP (λ(g,z). (g,subst y e' z)) funs2 = funs2’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac MAP_ID_ON >>
               PairCases >> rw[] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ntac 2 (pop_assum SUBST_ALL_TAC) >>
          simp[subst_ignore,GSYM perm_exp_eqvt,MEM_PERM_EQ] >>
          match_mp_tac exp_alpha_Letrec_Alpha >>
          rw[freevars_def,MEM_FILTER])
      >- (‘x' = y’
            by(gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          pop_assum SUBST_ALL_TAC >>
          gvs[MEM_FILTER] >>
          ‘MAP (λ(g,z). (g,subst y e' z)) funs1 = funs1’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac MAP_ID_ON >>
               PairCases >> rw[] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               fs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ‘MAP (λ(g,z). (g,subst y e' z)) funs2 = funs2’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac MAP_ID_ON >>
               PairCases >> rw[] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               fs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ntac 2 (pop_assum SUBST_ALL_TAC) >>
          simp[subst_ignore,GSYM perm_exp_eqvt,MEM_PERM_EQ] >>
          match_mp_tac exp_alpha_Letrec_Alpha >>
          rw[freevars_def,MEM_FILTER])
      >- (match_mp_tac exp_alpha_Trans >>
          irule_at (Pos hd) exp_alpha_Letrec_Alpha >>
          goal_assum drule >>
          conj_tac
          >- (gvs[freevars_def,MEM_FILTER] >>
              gvs[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
              CONV_TAC(DEPTH_CONV ETA_CONV) >>
              simp[] >>
              rw[freevars_subst] >>
              disj2_tac >>
              CCONTR_TAC >> gvs[MEM_FLAT,MEM_MAP,freevars_subst] >>
              metis_tac[FST,SND,PAIR]) >>
          match_mp_tac exp_alpha_Letrec >>
          conj_tac
          >- (simp[subst_eqvt,perm1_def] >>
              match_mp_tac exp_alpha_subst_closed' >>
              simp[closed_perm] >>
              match_mp_tac exp_alpha_sym >>
              match_mp_tac exp_alpha_perm_irrel >>
              gvs[closed_def]) >>
          conj_tac
          >- (simp[] >>
              rpt(match_mp_tac APPEND_EQ_IMP >> conj_tac) >>
              rw[MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f] >>
              pairarg_tac >> simp[]) >>
          simp[] >>
          match_mp_tac LIST_REL_APPEND_suff >>
          simp[EVERY2_MAP] >>
          conj_tac
          >- (match_mp_tac EVERY2_refl >>
              PairCases >> rw[subst_eqvt,perm1_def] >>
              match_mp_tac exp_alpha_subst_closed' >>
              simp[closed_perm] >>
              match_mp_tac exp_alpha_sym >>
              match_mp_tac exp_alpha_perm_irrel >>
              gvs[closed_def]) >>
          conj_tac
          >- (rw[subst_eqvt,perm1_def] >>
              match_mp_tac exp_alpha_subst_closed' >>
              simp[closed_perm] >>
              match_mp_tac exp_alpha_sym >>
              match_mp_tac exp_alpha_perm_irrel >>
              gvs[closed_def]) >>
          match_mp_tac EVERY2_refl >>
          PairCases >> rw[subst_eqvt,perm1_def] >>
          match_mp_tac exp_alpha_subst_closed' >>
          simp[closed_perm] >>
          match_mp_tac exp_alpha_sym >>
          match_mp_tac exp_alpha_perm_irrel >>
          gvs[closed_def]))
  >- cheat
  >- cheat
  *)
  *)
QED

Theorem exp_alpha_subst_closed'':
  ∀x e' e e''.
    closed e' ∧ exp_alpha e e'' ⇒
    exp_alpha (subst x e' e) (subst x e' e'')
Proof
  cheat (* TODO
  Induct_on ‘exp_alpha’ >>
  rw[subst_def,exp_alpha_Refl]
  >- metis_tac[exp_alpha_Trans]
  >- (rw[] >> match_mp_tac exp_alpha_Lam >> simp[])
  >- (rw[]
      >- (dep_rewrite.DEP_ONCE_REWRITE_TAC [subst_ignore] >>
          simp[GSYM perm_exp_eqvt,MEM_MAP] >>
          conj_tac >- rw[perm1_def] >>
          match_mp_tac exp_alpha_Alpha >>
          rw[])
      >- (dep_rewrite.DEP_ONCE_REWRITE_TAC [subst_ignore] >>
          simp[GSYM perm_exp_eqvt,MEM_MAP] >>
          match_mp_tac exp_alpha_Alpha >>
          rw[])
      >- (match_mp_tac exp_alpha_Trans >>
          irule_at (Pos hd) exp_alpha_Alpha >>
          qexists_tac ‘y’ >>
          simp[freevars_subst] >>
          simp[subst_eqvt] >>
          rw[perm1_def] >>
          match_mp_tac exp_alpha_Lam >>
          match_mp_tac exp_alpha_subst_closed' >>
          simp[closed_perm] >>
          match_mp_tac exp_alpha_sym >>
          match_mp_tac exp_alpha_perm_irrel >>
          gvs[closed_def]))
  >- (match_mp_tac exp_alpha_Prim >>
      simp[EVERY2_MAP] >>
      drule_at_then Any match_mp_tac EVERY2_mono >>
      rw[])
  >- (match_mp_tac exp_alpha_App >> simp[])
  >- (rw[]
      >- (match_mp_tac exp_alpha_Letrec >> simp[] >> gvs[EVERY2_MAP] >>
          drule_at_then Any match_mp_tac EVERY2_mono >> rw[]) >>
      match_mp_tac exp_alpha_Letrec >>
      simp[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
      CONV_TAC(DEPTH_CONV ETA_CONV) >> gvs[] >>
      gvs[EVERY2_MAP] >>
      drule_at_then Any match_mp_tac EVERY2_mono >> rw[])
  >- (rw[] >>
      TRY(match_mp_tac exp_alpha_Letrec_Alpha >> simp[] >> NO_TAC) >>
      gvs[]
      >- (‘x' = x’
            by(gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          pop_assum SUBST_ALL_TAC >>
          Cases_on ‘MEM y (MAP FST funs1)’
          >- (gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          Cases_on ‘MEM y (MAP FST funs2)’
          >- (gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          gvs[MEM_FILTER] >>
          drule MEM_PERM_IMP >>
          disch_then(qspec_then ‘y’ assume_tac) >>
          gvs[MAP_MAP_o,combinTheory.o_DEF] >>
          simp[PAIR_MAP] >>
          ‘MAP (λx'. (perm1 x y (FST x'),subst x e' (perm_exp x y (SND x')))) funs1 =
           MAP (perm1 x y ## perm_exp x y) funs1’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ‘MAP (λx'. (perm1 x y (FST x'),subst x e' (perm_exp x y (SND x')))) funs2 =
           MAP (perm1 x y ## perm_exp x y) funs2’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ntac 2 (pop_assum SUBST_ALL_TAC) >>
          simp[subst_ignore,GSYM perm_exp_eqvt,MEM_PERM_EQ] >>
          match_mp_tac exp_alpha_Letrec_Alpha >>
          rw[freevars_def,MEM_FILTER])
      >- (Cases_on ‘MEM y (MAP FST funs1)’
          >- (gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          Cases_on ‘MEM y (MAP FST funs2)’
          >- (gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          gvs[MEM_FILTER] >>
          gvs[MAP_MAP_o,combinTheory.o_DEF] >>
          simp[PAIR_MAP] >>
          ‘MAP (λx'. (perm1 x y (FST x'),subst x e' (perm_exp x y (SND x')))) funs1 =
           MAP (perm1 x y ## perm_exp x y) funs1’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ‘MAP (λx'. (perm1 x y (FST x'),subst x e' (perm_exp x y (SND x')))) funs2 =
           MAP (perm1 x y ## perm_exp x y) funs2’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ntac 2 (pop_assum SUBST_ALL_TAC) >>
          simp[subst_ignore,GSYM perm_exp_eqvt,MEM_PERM_EQ] >>
          match_mp_tac exp_alpha_Letrec_Alpha >>
          rw[freevars_def,MEM_FILTER])
      >- (‘x' = x’
            by(gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          pop_assum SUBST_ALL_TAC >>
          Cases_on ‘MEM y (MAP FST funs1)’
          >- (gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          Cases_on ‘MEM y (MAP FST funs2)’
          >- (gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          gvs[MEM_FILTER] >>
          drule MEM_PERM_IMP >>
          disch_then(qspec_then ‘y’ assume_tac) >>
          gvs[MAP_MAP_o,combinTheory.o_DEF] >>
          simp[PAIR_MAP] >>
          ‘MAP (λx'. (perm1 x y (FST x'),subst x e' (perm_exp x y (SND x')))) funs1 =
           MAP (perm1 x y ## perm_exp x y) funs1’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ‘MAP (λx'. (perm1 x y (FST x'),subst x e' (perm_exp x y (SND x')))) funs2 =
           MAP (perm1 x y ## perm_exp x y) funs2’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ntac 2 (pop_assum SUBST_ALL_TAC) >>
          simp[subst_ignore,GSYM perm_exp_eqvt,MEM_PERM_EQ] >>
          match_mp_tac exp_alpha_Letrec_Alpha >>
          rw[freevars_def,MEM_FILTER])
      >- (‘x' = y’
            by(fs[MEM_MAP,PAIR_MAP,PULL_EXISTS] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          pop_assum SUBST_ALL_TAC >>
          gvs[MEM_FILTER] >>
          ‘MAP (λ(g,z). (g,subst y e' z)) funs1 = funs1’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac MAP_ID_ON >>
               PairCases >> rw[] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               fs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ‘MAP (λ(g,z). (g,subst y e' z)) funs2 = funs2’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac MAP_ID_ON >>
               PairCases >> rw[] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               fs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ntac 2 (pop_assum SUBST_ALL_TAC) >>
          simp[subst_ignore,GSYM perm_exp_eqvt,MEM_PERM_EQ] >>
          match_mp_tac exp_alpha_Letrec_Alpha >>
          rw[freevars_def,MEM_FILTER])
      >- (gvs[MEM_FILTER] >>
          rename1 ‘x ≠ y’ >>
          ‘MAP (λ(g,z). (g,subst y e' z)) funs1 = funs1’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac MAP_ID_ON >>
               PairCases >> rw[] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ‘MAP (λ(g,z). (g,subst y e' z)) funs2 = funs2’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac MAP_ID_ON >>
               PairCases >> rw[] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               gvs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ntac 2 (pop_assum SUBST_ALL_TAC) >>
          simp[subst_ignore,GSYM perm_exp_eqvt,MEM_PERM_EQ] >>
          match_mp_tac exp_alpha_Letrec_Alpha >>
          rw[freevars_def,MEM_FILTER])
      >- (‘x' = y’
            by(gvs[MEM_MAP,PAIR_MAP] >> metis_tac[PAIR,FST,SND,perm1_def]) >>
          pop_assum SUBST_ALL_TAC >>
          gvs[MEM_FILTER] >>
          ‘MAP (λ(g,z). (g,subst y e' z)) funs1 = funs1’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac MAP_ID_ON >>
               PairCases >> rw[] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               fs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ‘MAP (λ(g,z). (g,subst y e' z)) funs2 = funs2’
            by(rw[MAP_EQ_f,PAIR_MAP] >>
               match_mp_tac MAP_ID_ON >>
               PairCases >> rw[] >>
               match_mp_tac subst_ignore >>
               gvs[GSYM perm_exp_eqvt] >>
               spose_not_then strip_assume_tac >>
               gvs[MEM_PERM_EQ] >>
               fs[MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR,perm1_def]) >>
          ntac 2 (pop_assum SUBST_ALL_TAC) >>
          simp[subst_ignore,GSYM perm_exp_eqvt,MEM_PERM_EQ] >>
          match_mp_tac exp_alpha_Letrec_Alpha >>
          rw[freevars_def,MEM_FILTER])
      >- (match_mp_tac exp_alpha_Trans >>
          irule_at (Pos hd) exp_alpha_Letrec_Alpha >>
          goal_assum drule >>
          conj_tac
          >- (gvs[freevars_def,MEM_FILTER] >>
              gvs[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
              CONV_TAC(DEPTH_CONV ETA_CONV) >>
              simp[] >>
              rw[freevars_subst] >>
              disj2_tac >>
              CCONTR_TAC >> gvs[MEM_FLAT,MEM_MAP,freevars_subst] >>
              metis_tac[FST,SND,PAIR]) >>
          match_mp_tac exp_alpha_Letrec >>
          conj_tac
          >- (simp[subst_eqvt,perm1_def] >>
              match_mp_tac exp_alpha_subst_closed' >>
              simp[closed_perm] >>
              match_mp_tac exp_alpha_sym >>
              match_mp_tac exp_alpha_perm_irrel >>
              gvs[closed_def]) >>
          conj_tac
          >- (simp[] >>
              rpt(match_mp_tac APPEND_EQ_IMP >> conj_tac) >>
              rw[MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f] >>
              pairarg_tac >> simp[]) >>
          simp[] >>
          match_mp_tac LIST_REL_APPEND_suff >>
          simp[EVERY2_MAP] >>
          conj_tac
          >- (match_mp_tac EVERY2_refl >>
              PairCases >> rw[subst_eqvt,perm1_def] >>
              match_mp_tac exp_alpha_subst_closed' >>
              simp[closed_perm] >>
              match_mp_tac exp_alpha_sym >>
              match_mp_tac exp_alpha_perm_irrel >>
              gvs[closed_def]) >>
          conj_tac
          >- (rw[subst_eqvt,perm1_def] >>
              match_mp_tac exp_alpha_subst_closed' >>
              simp[closed_perm] >>
              match_mp_tac exp_alpha_sym >>
              match_mp_tac exp_alpha_perm_irrel >>
              gvs[closed_def]) >>
          match_mp_tac EVERY2_refl >>
          PairCases >> rw[subst_eqvt,perm1_def] >>
          match_mp_tac exp_alpha_subst_closed' >>
          simp[closed_perm] >>
          match_mp_tac exp_alpha_sym >>
          match_mp_tac exp_alpha_perm_irrel >>
          gvs[closed_def]))
  >- cheat
  >- cheat
  *)
QED

Theorem exp_alpha_bind_all_closed:
  ∀x e e'.
    exp_alpha e e' ⇒
    exp_alpha (bind x e) (bind x e')
Proof
  cheat
(*  rw[bind_def,exp_alpha_Refl] >>
  metis_tac[exp_alpha_subst_all_closed'']*)
QED

val (v_alpha_rules,v_alpha_coind,v_alpha_def) = Hol_coreln
  ‘(∀v. v_alpha v v) ∧
   (∀s vs vs'. LIST_REL v_alpha vs vs' ⇒ v_alpha (Constructor s vs) (Constructor s vs')) ∧
   (∀s e1 e2. exp_alpha e1 e2 ⇒ v_alpha (Closure s e1) (Closure s e2)) ∧
   (∀x y e1 e2. x ∉ freevars e2 ∧ y ∉ freevars e1 ∧ exp_alpha e1 (perm_exp x y e2) ⇒ v_alpha (Closure x e1) (Closure y e2))
  ’

Theorem v_alpha_refl = cj 1 v_alpha_rules
Theorem v_alpha_cons = cj 2 v_alpha_rules
Theorem v_alpha_closure = cj 3 v_alpha_rules
Theorem v_alpha_alpha = cj 4 v_alpha_rules

Inductive v_prefix_alpha:
[~Refl:]
  (∀v1. v_prefix_alpha v1 v1) ∧
[~Closure:]
  (∀e1 e2 x. exp_alpha e1 e2 ⇒ v_prefix_alpha (Closure' x e1) (Closure' x e2)) ∧
[~Alpha:]
  (∀x y e1 e2. x ∉ freevars e2 ∧ y ∉ freevars e1 ∧ exp_alpha e1 (perm_exp x y e2) ⇒ v_prefix_alpha (Closure' x e1) (Closure' y e2))
End

Theorem v_alpha_trans:
  ∀v1 v2 v3. v_alpha v1 v2 ∧ v_alpha v2 v3 ⇒ v_alpha v1 v3
Proof
  CONV_TAC(QUANT_CONV(SWAP_FORALL_CONV)) >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
  ho_match_mp_tac v_alpha_coind >>
  rw[Once v_alpha_def] >>
  qhdtm_x_assum ‘v_alpha’ (strip_assume_tac o REWRITE_RULE [v_alpha_def]) >> gvs[]
  >- (disj2_tac >>
      drule_at_then Any match_mp_tac EVERY2_mono >>
      metis_tac[v_alpha_refl])
  >- (disj2_tac >>
      drule_at_then Any match_mp_tac EVERY2_mono >>
      metis_tac[v_alpha_refl])
  >- (disj2_tac >> cheat)
  >- (metis_tac[exp_alpha_Trans])
  >- (metis_tac[exp_alpha_freevars,exp_alpha_Trans])
  >- (metis_tac[exp_alpha_perm_closed,perm_exp_sym,exp_alpha_Trans,exp_alpha_freevars])
  >- (reverse(Cases_on ‘MEM x' (freevars e1')’)
      >- (‘exp_alpha (perm_exp x x' e1') e1'’
            by(match_mp_tac exp_alpha_sym >>
               match_mp_tac exp_alpha_perm_irrel >>
               simp[]) >>
          ‘exp_alpha e1 e1'’ by metis_tac[exp_alpha_Trans] >>
          drule_all exp_alpha_Trans >>
          rw[] >>
          ‘¬MEM x (freevars e1)’
            by(imp_res_tac exp_alpha_freevars >> gvs[GSYM perm_exp_eqvt]) >>
          ‘¬MEM y' (freevars e1)’
            by(imp_res_tac exp_alpha_freevars >> gvs[GSYM perm_exp_eqvt]) >>
          simp[] >>
          Cases_on ‘x = y'’
          >- (gvs[perm_exp_id] >>
              ‘¬MEM x (freevars e2')’
                by(drule exp_alpha_freevars >>
                   rw[] >> gvs[GSYM perm_exp_eqvt,MEM_MAP] >>
                   metis_tac[perm1_def]) >>
              simp[] >>
              disj2_tac >>
              match_mp_tac exp_alpha_Trans >>
              goal_assum drule >>
              match_mp_tac exp_alpha_sym >>
              match_mp_tac exp_alpha_perm_irrel >>
              rw[]) >>
          simp[] >>
          conj_asm1_tac
          >- (drule exp_alpha_freevars >>
              rw[] >> gvs[GSYM perm_exp_eqvt,MEM_MAP] >>
              metis_tac[perm1_def]) >>
          match_mp_tac exp_alpha_Trans >>
          goal_assum drule >>
          ‘¬MEM y' (freevars e2')’
            by(drule exp_alpha_freevars >>
              rw[] >> gvs[GSYM perm_exp_eqvt,MEM_MAP] >>
               metis_tac[perm1_def]) >>
          match_mp_tac exp_alpha_Trans >>
          irule_at (Pos hd) exp_alpha_sym >>
          irule_at (Pos hd) exp_alpha_perm_irrel >>
          rw[] >>
          match_mp_tac exp_alpha_perm_irrel >>
          rw[]) >>
      ‘x ≠ x'’ by metis_tac[] >>
      Cases_on ‘x = y'’
      >- (gvs[] >>
          drule exp_alpha_perm_closed >>
          disch_then(qspecl_then [‘x'’,‘x’] mp_tac) >>
          gvs[perm_exp_sym] >>
          metis_tac[exp_alpha_Trans]) >>
      simp[] >>
      conj_asm1_tac
      >- (drule exp_alpha_freevars >>
          rw[] >> gvs[GSYM perm_exp_eqvt,MEM_MAP] >>
          metis_tac[perm1_def]) >>
      conj_asm1_tac
      >- (imp_res_tac exp_alpha_freevars >>
          rw[] >> gvs[GSYM perm_exp_eqvt,MEM_MAP] >>
          metis_tac[perm1_def]) >>
      ‘MEM y' (freevars e2')’
        by(imp_res_tac exp_alpha_freevars >>
          rw[] >> gvs[GSYM perm_exp_eqvt,MEM_MAP] >>
          metis_tac[perm1_def]) >>
      ‘MEM y' (freevars e2')’
        by(imp_res_tac exp_alpha_freevars >>
          rw[] >> gvs[GSYM perm_exp_eqvt,MEM_MAP] >>
          metis_tac[perm1_def]) >>
      ‘MEM x (freevars e1)’
        by(imp_res_tac exp_alpha_freevars >>
          rw[] >> gvs[GSYM perm_exp_eqvt,MEM_MAP] >>
          metis_tac[perm1_def]) >>
      match_mp_tac exp_alpha_Trans >>
      goal_assum drule >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_perm_closed >>
      goal_assum drule >>
      simp[Once perm_exp_compose] >>
      simp[perm1_def] >>
      rw[] >> gvs[] >>
      match_mp_tac exp_alpha_perm_closed >>
      match_mp_tac exp_alpha_sym >>
      match_mp_tac exp_alpha_perm_irrel >>
      rw[])
QED

Theorem exp_alpha_eval_to:
  ∀k e1 e2. exp_alpha e1 e2 ⇒ v_alpha(eval_to k e1) (eval_to k e2)
Proof
  cheat (* TODO
  ho_match_mp_tac COMPLETE_INDUCTION >>
  strip_tac >>
  Induct_on ‘exp_alpha’ >> rw[]
  >- simp[v_alpha_refl]
  >- metis_tac[v_alpha_trans]
  >- (simp[eval_to_def] >> metis_tac[v_alpha_rules])
  >- (simp[eval_to_def] >>
      MAP_FIRST match_mp_tac (CONJUNCTS v_alpha_rules) >>
      simp[GSYM perm_exp_eqvt,MEM_PERM_EQ,exp_alpha_refl])
  >- (simp[eval_to_def] >>
      ‘eval_op op (MAP eval es) = eval_op op (MAP eval es)’ by metis_tac[] >>
      dxrule eval_op_cases >>
      rw[MAP_EQ_CONS] >> gvs[LIST_REL_CONS1] >>
      gvs[eval_op_def,v_alpha_refl]
      >- (match_mp_tac v_alpha_cons >>
          simp[EVERY2_MAP] >>
          drule_at_then Any match_mp_tac EVERY2_mono >>
          rw[])
      >- (rename1 ‘eval_to _ ee’ >>
          qpat_x_assum ‘v_alpha (eval_to _ ee) _’ (strip_assume_tac o ONCE_REWRITE_RULE[v_alpha_def]) >>
          gvs[] >> rw[v_alpha_refl] >> gvs[])
      >- (rename1 ‘eval_to _ ee’ >>
          simp[el_def] >>
          qpat_x_assum ‘v_alpha (eval_to _ ee) _’ (strip_assume_tac o ONCE_REWRITE_RULE[v_alpha_def]) >>
          gvs[] >> rw[v_alpha_refl] >>
          gvs[LIST_REL_EL_EQN])
      >- (‘MEM Diverge (MAP (λa. eval_to k a) es) ⇔ MEM Diverge (MAP (λa. eval_to k a) es')’
            by(gvs[MEM_EL,LIST_REL_EL_EQN] >> rw[EQ_IMP_THM] >>
               goal_assum drule >>
               first_x_assum drule >> rw[Once v_alpha_def] >>
               gvs[EL_MAP]) >>
          simp[] >>
          rw[v_alpha_refl] >>
          ‘getAtoms (MAP (λa. eval_to k a) es) = getAtoms (MAP (λa. eval_to k a) es')’
            by(qhdtm_x_assum ‘LIST_REL’ mp_tac >>
               rpt(pop_assum kall_tac) >>
               Induct_on ‘LIST_REL’ >>
               rw[getAtoms_def,Once v_alpha_def] >>
               gvs[getAtom_def]) >>
          simp[] >>
          TOP_CASE_TAC >> simp[v_alpha_refl])
      >- (simp[is_eq_def] >>
          rename1 ‘eval_to _ ee’ >>
          qpat_x_assum ‘v_alpha (eval_to _ ee) _’ (strip_assume_tac o ONCE_REWRITE_RULE[v_alpha_def]) >>
          gvs[] >> rw[v_alpha_refl] >> gvs[] >>
          gvs[LIST_REL_EL_EQN]))
  >- (simp[eval_to_def] >>
      ‘eval_to k e1 = Diverge ⇔ eval_to k e2 = Diverge’
        by(res_tac >>
           qpat_x_assum ‘v_alpha (eval_to _ e1) _’ (strip_assume_tac o ONCE_REWRITE_RULE[v_alpha_def]) >>
           gvs[]) >>
      TOP_CASE_TAC >> gvs[] >>
      TOP_CASE_TAC
      >- (qpat_x_assum ‘v_alpha (eval_to _ e1) _’ (strip_assume_tac o ONCE_REWRITE_RULE[v_alpha_def]) >>
          gvs[v_alpha_refl,dest_Closure_def]) >>
      qpat_x_assum ‘v_alpha (eval_to _ e1) _’ (strip_assume_tac o ONCE_REWRITE_RULE[v_alpha_def]) >>
      gvs[v_alpha_refl,dest_Closure_def,AllCaseEqs()]
      >- (rw[v_alpha_refl] >>
          first_x_assum (match_mp_tac o MP_CANON) >>
          simp[] >>
          simp[bind_def] >>
          imp_res_tac exp_alpha_closed >> gvs[] >>
          rw[exp_alpha_refl] >>
          match_mp_tac exp_alpha_subst_closed' >>
          simp[])
      >- (rw[v_alpha_refl] >>
          first_x_assum (match_mp_tac o MP_CANON) >>
          simp[] >>
          simp[bind_def] >>
          imp_res_tac exp_alpha_closed >> gvs[] >>
          rw[exp_alpha_refl] >>
          match_mp_tac exp_alpha_Trans >>
          irule_at (Pos hd) exp_alpha_subst_closed' >>
          goal_assum (drule_at (Pat ‘exp_alpha _ _’)) >>
          simp[] >>
          match_mp_tac exp_alpha_subst_closed'' >>
          simp[])
      >- (rw[v_alpha_refl] >>
          first_x_assum (match_mp_tac o MP_CANON) >>
          simp[] >>
          simp[bind_def] >>
          imp_res_tac exp_alpha_closed >> gvs[] >>
          rw[exp_alpha_refl] >>
          match_mp_tac exp_alpha_Trans >>
          irule_at (Pos hd) exp_alpha_subst_closed' >>
          simp[] >>
          first_x_assum(irule_at (Pos (hd o tl))) >>
          simp[] >>
          match_mp_tac exp_alpha_Trans >>
          irule_at (Pos hd) exp_alpha_subst_closed'' >>
          simp[] >>
          goal_assum drule >>
          Cases_on ‘x' = y’ >> gvs[perm_exp_id,exp_alpha_refl] >>
          match_mp_tac exp_alpha_Trans >>
          irule_at (Pos hd) exp_alpha_subst_closed >>
          goal_assum drule >>
          simp[exp_alpha_refl] >>
          imp_res_tac exp_alpha_freevars >>
          gvs[]))
  >- (rw[eval_to_def,v_alpha_refl] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      simp[] >>
      cheat)
  >- (rw[eval_to_def,v_alpha_refl] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      simp[] >>
      cheat)
  >- (rw[eval_to_def,v_alpha_refl] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      simp[] >>
      cheat)
  >- (rw[eval_to_def,v_alpha_refl] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      simp[] >>
      cheat)
      *)
QED

Theorem v_alpha_v_lookup_pres:
  ∀path v1 v2 v1' v2' n m.
  v_alpha v1 v2 ∧
  v_lookup path v1 = (v1',n) ∧
  v_lookup path v2 = (v2',m) ⇒
  v_prefix_alpha v1' v2' ∧ n = m
Proof
  Induct >>
  rw[v_lookup] >>
  gvs[AllCaseEqs()] >>
  gvs[Once v_alpha_def,v_prefix_alpha_cases] >>
  imp_res_tac LIST_REL_LENGTH >>
  gvs[oEL_THM]
  >- (rename1 ‘EL z vs’ >>
      ‘v_alpha (EL z vs') (EL z vs)’
        by(gvs[LIST_REL_EL_EQN]) >>
      first_x_assum drule_all >>
      strip_tac >> simp[])
  >- metis_tac[LIST_REL_EL_EQN]
QED

Theorem v_alpha_limit_pres:
  (∀k. v_alpha (f k) (g k)) ∧
  v_limit f path = (vp1,n1) ∧
  v_limit g path = (vp2,n2) ∧
  (∀k n. v_cmp path (f k) (f(k+n))) ∧
  (∀k n. v_cmp path (g k) (g(k+n)))
  ⇒ v_prefix_alpha vp1 vp2 ∧ n1 = n2
Proof
  disch_then strip_assume_tac >> gvs[v_limit_def,limit_def,some_def] >>
  qpat_x_assum ‘_ = (vp1,n1)’ mp_tac >>
  TOP_CASE_TAC
  >- (strip_tac >> gvs[] >>
      gvs[CaseEq "option",CaseEq "prod",v_prefix_alpha_Refl] >>
      gvs[] >>
      first_assum(qspecl_then [‘Diverge',0’,‘k'’] mp_tac) >>
      strip_tac >>
      gvs[] >>
      rename1 ‘k1 ≤ k2’ >>
      first_assum(qspecl_then [‘v_lookup path (f k2)’,‘k2’] mp_tac) >>
      strip_tac >>
      rename1 ‘k2 ≤ k3’ >>
      qpat_x_assum ‘∀k n. v_cmp _ (f _) _’ (qspecl_then [‘k2’,‘k3 - k2’] (mp_tac o REWRITE_RULE[v_cmp_def])) >>
      disch_then drule >>
      simp[]) >>
  strip_tac >> gvs[] >>
  gvs[CaseEq "option",CaseEq "prod",v_prefix_alpha_Refl]
  >- (first_assum(qspecl_then [‘Diverge',0’,‘k'’] mp_tac) >>
      strip_tac >>
      gvs[] >>
      rename1 ‘k1 ≤ k2’ >>
      first_assum(qspecl_then [‘v_lookup path (g k2)’,‘k2’] mp_tac) >>
      strip_tac >>
      rename1 ‘k2 ≤ k3’ >>
      qpat_x_assum ‘∀k n. v_cmp _ (g _) _’ (qspecl_then [‘k2’,‘k3 - k2’] (mp_tac o REWRITE_RULE[v_cmp_def])) >>
      disch_then drule >>
      simp[]) >>
  qpat_x_assum ‘$@ _ = _’ mp_tac >>
  SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
  ntac 3 strip_tac >>
  qpat_x_assum ‘$@ _ = _’ mp_tac >>
  SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
  ntac 3 strip_tac >>
  gvs[] >>
  qpat_x_assum ‘∀k. _ ⇒ _ = x’ kall_tac >>
  qpat_x_assum ‘∀k. _ ⇒ _ = x'’ kall_tac >>
  rename [‘k1 ≤ _’] >>
  pop_assum(fn thm => rename1 ‘k2 ≤ _’ >> assume_tac thm) >>
  ntac 2(first_x_assum(qspec_then ‘MAX k1 k2’ mp_tac)) >>
  impl_tac >- simp[] >> strip_tac >>
  impl_tac >- simp[] >> strip_tac >>
  dxrule_at (Pos last) v_alpha_v_lookup_pres >>
  disch_then(drule_at (Pos last)) >>
  impl_tac >- simp[] >>
  rw[]
QED

Theorem gen_v_alpha_pres:
  ∀v1 v2 f g.
  (∀path vp1 vp2 n1 n2. f path = (vp1,n1) ∧ g path = (vp2,n2) ⇒ v_prefix_alpha vp1 vp2 ∧ n1 = n2)
  ∧ v1 = gen_v f ∧ v2 = gen_v g
  ⇒
  v_alpha v1 v2
Proof
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
  ho_match_mp_tac v_alpha_coind >>
  rw[] >>
  simp[Once gen_v] >>
  simp[SimpR “$=”,Once gen_v] >>
  Cases_on ‘f []’ >>
  Cases_on ‘g []’ >>
  first_assum drule_all >>
  rw[Once v_prefix_alpha_cases] >> rw[]
  >- (TOP_CASE_TAC >> simp[] >>
      disj2_tac >> disj1_tac >>
      simp[Once gen_v] >>
      simp[Once gen_v] >>
      rw[LIST_REL_GENLIST] >>
      qexists_tac ‘f o CONS n’ >>
      qexists_tac ‘g o CONS n’ >>
      simp[combinTheory.o_DEF] >>
      metis_tac[]) >>
  rpt(simp[Once gen_v])
QED

Theorem exp_alpha_eval:
  ∀e1 e2. exp_alpha e1 e2 ⇒ v_alpha(eval e1) (eval e2)
Proof
  rw[eval_def] >>
  match_mp_tac gen_v_alpha_pres >>
  ntac 2 (irule_at (Pos last) EQ_REFL) >>
  rpt GEN_TAC >> disch_then strip_assume_tac >>
  gvs[] >>
  drule exp_alpha_eval_to >> strip_tac >>
  qpat_x_assum ‘v_limit _ _ = (vp1,n1)’ assume_tac >>
  dxrule_at (Pat ‘_ = (_,_)’) v_alpha_limit_pres >>
  qpat_x_assum ‘v_limit _ _ = (vp2,n2)’ assume_tac >>
  disch_then(drule_at (Pat ‘_ = (_,_)’)) >>
  simp[eval_to_res_mono_lemma]
QED

Theorem compatible_exp_alpha:
  compatible(λR (x,y). exp_alpha x y ∧ closed x ∧ closed y)
Proof
  simp[compatible_def,SUBSET_DEF] >>
  PairCases >>
  rw[ELIM_UNCURRY] >>
  gvs[FF_def,unfold_rel_def] >>
  rpt strip_tac >>
  drule exp_alpha_eval >>
  rpt strip_tac >>
  gvs[Once v_alpha_def]
  >- (rw[exp_alpha_Refl] >>
      match_mp_tac closed_freevars_subst >>
      drule_all eval_Closure_closed >>
      simp[])
  >- (rw[]
      >- (match_mp_tac exp_alpha_subst_closed'' >> metis_tac[]) >>
      match_mp_tac closed_freevars_subst >>
      rpt(drule_then dxrule eval_Closure_closed) >>
      simp[])
  >- (rw[]
      >- (Cases_on ‘x = y’
          >- (gvs[perm_exp_id] >> match_mp_tac exp_alpha_subst_closed'' >> simp[]) >>
          match_mp_tac exp_alpha_Trans >>
          irule_at (Pos hd) exp_alpha_subst_closed'' >>
          simp[] >>
          goal_assum drule >>
          match_mp_tac exp_alpha_sym >>
          PURE_ONCE_REWRITE_TAC[perm_exp_sym] >>
          match_mp_tac exp_alpha_subst_closed_single >>
          simp[]) >>
      match_mp_tac closed_freevars_subst >>
      rpt(drule_then dxrule eval_Closure_closed) >>
      simp[])
  >- cheat
  >- cheat
QED

Theorem companion_exp_alpha:
  exp_alpha x y ∧ closed x ∧ closed y ⇒ (x,y) ∈ companion R
Proof
  rw[IN_DEF,companion_def] >>
  irule_at Any compatible_exp_alpha >>
  simp[monotone_def] >>
  goal_assum drule
QED

Theorem app_similarity_Lam_Alpha:
  closed(Lam x e1) ⇒
  Lam x e1 ≲ Lam y (perm_exp x y e1)
Proof
  Cases_on ‘x = y’ >- (simp[perm_exp_id,reflexive_app_similarity']) >>
  strip_tac >>
  match_mp_tac companion_app_similarity  >>
  match_mp_tac(companion_exp_alpha |> SIMP_RULE std_ss [IN_DEF] |> GEN_ALL) >>
  conj_tac >- (match_mp_tac(GEN_ALL exp_alpha_Alpha) >> gvs[closed_def,FILTER_EQ_NIL,EVERY_MEM] >> metis_tac[]) >>
  simp[] >>
  gvs[closed_def,FILTER_EQ_NIL,GSYM perm_exp_eqvt,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  metis_tac[perm1_def]
QED

(* -- Howe's construction -- *)

Inductive Howe: (* TODO: add Cons clause *)
[Howe1:]
  (∀R vars x e2.
     R vars (Var x) e2 ⇒
     Howe R vars (Var x) e2)
  ∧
[Howe2:]
  (∀R x e1 e1' e2 vars.
     Howe R (x INSERT vars) e1 e1' ∧
     R vars (Lam x e1') e2 ∧
     ~(x IN vars) ⇒
     Howe R vars (Lam x e1) e2)
  ∧
[Howe3:]
  (∀R e1 e1' e3 vars.
     Howe R vars e1 e1' ∧
     Howe R vars e2 e2' ∧
     R vars (App e1' e2') e3 ⇒
     Howe R vars (App e1 e2) e3)
  ∧
[Howe4:]
  (∀R es es' e op vars.
    LIST_REL (Howe R vars) es es' ∧
    R vars (Prim op es') e ⇒
    Howe R vars (Prim op es) e)
  ∧
[Howe5:]
  (∀R ves ves' e e' e2.
    MAP FST ves = MAP FST ves' ∧
    DISJOINT vars (set (MAP FST ves)) ∧
    Howe R (vars ∪ set (MAP FST ves)) e e' ∧
    LIST_REL (Howe R (vars ∪ set (MAP FST ves))) (MAP SND ves) (MAP SND ves') ∧
    R vars (Letrec ves' e') e2
  ⇒ Howe R vars (Letrec ves e) e2)
End

Theorem Howe_Ref: (* 5.5.1(i) *)
  Ref R ⇒ Compatible (Howe R)
Proof
  rw[Ref_def, Compatible_def]
  >- (
    rw[Com1_def] >>
    irule Howe1 >>
    first_x_assum irule >> fs[Exps_def]
    )
  >- (
    rw[Com2_def] >>
    irule Howe2 >> fs[] >>
    goal_assum (drule_at Any) >>
    first_x_assum irule >>
    fs[Exps_def, LIST_TO_SET_FILTER, SUBSET_DEF] >>
    metis_tac[]
    )
  >- (
    rw[Com3_def] >>
    irule Howe3 >>
    rpt (goal_assum (drule_at Any)) >>
    first_x_assum irule >> fs[Exps_def]
    )
  >- (
    rw[Com4_def] >>
    irule Howe4 >>
    rpt (goal_assum (drule_at Any)) >>
    first_x_assum irule >> fs[Exps_def] >>
    gvs[SUBSET_DEF, MEM_FLAT, MEM_MAP] >> rw[] >>
    first_x_assum irule >>
    goal_assum drule >> fs[]
    )
  >- (
    rw[Com5_def] >>
    irule Howe5 >>
    gvs[DISJOINT_SYM] >>
    rpt (goal_assum (drule_at Any)) >> fs[] >>
    first_x_assum irule >> fs[Exps_def] >>
    fs[LIST_TO_SET_FILTER, SUBSET_DEF] >> rw[]
    >- (last_x_assum drule >> fs[]) >>
    gvs[MEM_FLAT] >>
    qpat_x_assum `¬ MEM _ _` mp_tac >>
    simp[IMP_DISJ_THM, Once DISJ_SYM] >>
    first_x_assum irule >> gvs[MEM_MAP] >>
    PairCases_on `y` >> gvs[] >>
    rpt (goal_assum (drule_at Any)) >> fs[]
    )
QED

Definition term_rel_def:
  term_rel R ⇔
    ∀vars e1 e2. R vars e1 e2 ⇒ e1 ∈ Exps vars ∧ e2 ∈ Exps vars
End

Theorem term_rel_Howe:
  term_rel R ⇒ term_rel (Howe R)
Proof
  fs[term_rel_def] >>
  Induct_on `Howe` >> rw[]
  >- metis_tac[]
  >- metis_tac[]
  >- (
    last_x_assum drule >>
    rw[Exps_def] >>
    fs[LIST_TO_SET_FILTER, SUBSET_DEF] >>
    metis_tac[]
    )
  >- metis_tac[]
  >- (
    last_x_assum drule >>
    last_x_assum drule >>
    rw[Exps_def]
    )
  >- metis_tac[]
  >- (
    fs[LIST_REL_EL_EQN] >>
    first_assum drule >> rw[Exps_def] >>
    gvs[SUBSET_DEF, MEM_FLAT, MEM_MAP] >> rw[] >>
    qpat_x_assum `MEM _ es` mp_tac >> simp[MEM_EL] >> strip_tac >> gvs[] >>
    last_x_assum drule >> strip_tac >> first_x_assum drule >>
    simp[Exps_def, SUBSET_DEF]
    )
  >- metis_tac[]
  >- (
    fs[LIST_REL_EL_EQN] >>
    first_assum drule >> rw[Exps_def] >>
    fs[LIST_TO_SET_FILTER, SUBSET_DEF] >> rw[]
    >- (
      last_x_assum drule >> fs[Exps_def, SUBSET_DEF] >> strip_tac >>
      first_x_assum drule >> fs[]
      ) >>
    gvs[] >>
    qpat_x_assum `MEM s _` mp_tac >> simp[MEM_MAP, MEM_EL] >>
    strip_tac >> gvs[] >>
    first_x_assum (qspec_then `n` mp_tac) >>
    disch_then drule >> strip_tac >>
    pop_assum drule >> simp[EL_MAP, Exps_def] >> strip_tac >>
    Cases_on `EL n ves` >> gvs[SUBSET_DEF] >>
    first_x_assum drule >> fs[]
    )
  >- metis_tac[]
QED

Theorem Howe_Tra: (* 5.5.1(ii) *)
  Tra R ∧ term_rel R ⇒
  ∀vars e1 e2 e3.
    e1 ∈ Exps vars ∧ e2 ∈ Exps vars ∧ e3 ∈ Exps vars ∧
    Howe R vars e1 e2 ∧ R vars e2 e3 ⇒ Howe R vars e1 e3
Proof
  rw[Tra_def] >>
  qpat_x_assum `Howe _ _ _ _` mp_tac >>
  simp[Once Howe_cases] >> rw[]
  >- (
    irule Howe1 >>
    first_x_assum irule >> fs[Exps_def] >>
    qexists_tac `e2` >> fs[]
    )
  >- (
    irule Howe2 >> fs[] >>
    goal_assum (drule_at Any) >>
    first_x_assum irule >>
    fs[term_rel_def] >> res_tac >> fs[] >>
    qexists_tac `e2` >> fs[]
    )
  >- (
    irule Howe3 >>
    rpt (goal_assum (drule_at Any)) >>
    first_x_assum irule >> fs[] >> rw[]
    >- (imp_res_tac term_rel_def >> fs[Exps_def]) >>
    qexists_tac `e2` >> fs[]
    )
  >- (
    irule Howe4 >>
    rpt (goal_assum (drule_at Any)) >>
    first_x_assum irule >> fs[] >> rw[]
    >- (imp_res_tac term_rel_def >> fs[Exps_def]) >>
    qexists_tac `e2` >> fs[]
    )
  >- (
    irule Howe5 >> gvs[] >>
    rpt (goal_assum (drule_at Any)) >> gvs[] >>
    first_x_assum irule >> gvs[] >> rw[]
    >- (imp_res_tac term_rel_def >> fs[Exps_def]) >>
    qexists_tac `e2` >> fs[]
    )
QED

Theorem Howe_Ref_Tra: (* 5.5.1(iii) *)
  Ref R ⇒
  ∀vars e1 e2. R vars e1 e2 ⇒ Howe R vars e1 e2
Proof
  cheat
QED

Definition Sub_def: (* Sub = substitutive *)
  Sub R ⇔
    ∀vars x e1 e1' e2 e2'.
      x ∉ vars ∧
      {e1; e1'} SUBSET Exps (x INSERT vars) ∧ {e2; e2'} SUBSET Exps vars ⇒
      R (x INSERT vars) e1 e1' ∧ R vars e2 e2' ⇒
      R vars (subst x e2 e1) (subst x e2' e1')
  (* TODO: we should use a capture avoiding subst here! *)
End

Definition Cus_def: (* closed under value-substitution *)
  Cus R ⇔
    ∀vars x e1 e1' e2.
      x ∉ vars ∧
      {e1; e1'} SUBSET Exps (x INSERT vars) ∧ e2 IN Exps vars ⇒
      R (x INSERT vars) e1 e1' ⇒
      R vars (subst x e2 e1) (subst x e2 e1')
  (* TODO: we should use a capture avoiding subst here! *)
End

Theorem Sub_Ref_IMP_Cus:
  Sub R ∧ Ref R ⇒ Cus R
Proof
  rw[Sub_def, Ref_def, Cus_def]
QED

Theorem Cus_open_similarity:
  Cus open_similarity
Proof
  cheat
QED

Theorem Cus_open_bisimilarity:
  Cus open_bisimilarity
Proof
  cheat
QED

Theorem IMP_Howe_Sub: (* 5.5.3 *)
  Ref R ∧ Tra R ∧ Cus R ⇒ Sub (Howe R)
Proof
  cheat (* errata: says use 5.5.1(ii), i.e. Howe_Tra *)
QED

Theorem Ref_Howe:
  Ref R ⇒ Ref (Howe R)
Proof
(*  Unprovable for now, need moar clauses
  strip_tac >>
  gvs[Ref_def,Exps_def,PULL_FORALL] >>
  CONV_TAC SWAP_FORALL_CONV >>
  qsuff_tac ‘∀e vars vars'. ALL_DISTINCT(vars ++ vars') ∧ set (freevars e) ⊆ set vars ⇒ Howe R vars e e’
  >- (rpt strip_tac >> first_x_assum match_mp_tac >>
      rw[] >> qexists_tac ‘[]’ >> rw[]) >>
  Induct_on ‘e’
  >- (rename1 ‘Var’ >>
      rw[Once Howe_cases,ALL_DISTINCT_APPEND])
  >- (rename1 ‘Prim’ >>
      cheat)
  >- (rename1 ‘App’ >>
      rw[Once Howe_cases] >>
      first_x_assum drule_all >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      rpt(goal_assum drule) >>
      first_x_assum match_mp_tac >>
      rw[freevars_def] >> gvs[ALL_DISTINCT_APPEND])
  >- (rename1 ‘Lam’ >>
      cheat)
 *)
  cheat
QED

Theorem Cus_Howe_open_similarity:
  Cus (Howe open_similarity)
Proof
  match_mp_tac Sub_Ref_IMP_Cus \\ rw []
  \\ metis_tac [Ref_Howe,Ref_open_similarity,IMP_Howe_Sub,
       Cus_open_similarity,Tra_open_similarity,Ref_open_similarity]
QED

Theorem KeyLemma: (* key lemma 5.5.4 *)
  eval e1 = Closure x e ∧ Howe open_similarity {} e1 e2 ⇒
  ∃e'. eval e2 = Closure x e' ∧ Howe open_similarity {x} e e'
Proof
  cheat
QED

Theorem Howe_vars:
  Howe open_similarity vars e1 e2 ⇒
  freevars e1 ⊆ vars ∧ freevars e2 ⊆ vars
Proof
  qsuff_tac ‘∀R vars e1 e2.
     Howe R vars e1 e2 ⇒ R = open_similarity ⇒
     freevars e1 ⊆ vars ∧ freevars e2 ⊆ vars’ THEN1 metis_tac []
  \\ ho_match_mp_tac Howe_ind \\ rw []
  \\ fs [open_similarity_def]
  \\ fs [SUBSET_DEF,MEM_FILTER,MEM_FLAT,MEM_MAP,PULL_EXISTS]
  THEN1 metis_tac []
  THEN1 cheat
  THEN1 cheat
QED

Theorem app_simulation_Howe_open_similarity: (* or replace with the lemma below *)
  app_simulation (UNCURRY (Howe open_similarity {}))
Proof
  fs [app_simulation_def,unfold_rel_def]
  \\ cheat (* KeyLemma? *)
QED

Theorem Howe_open_similarity_app_similarity: (* has better concl than above *)
  (UNCURRY (Howe open_similarity ∅)) ⊆ app_similarity
Proof
  fs [SUBSET_DEF,FORALL_PROD,IN_DEF]
  \\ ho_match_mp_tac app_similarity_companion_coind
  \\ fs [FF_def,EXISTS_PROD,unfold_rel_def]
  \\ fs [eval_Cons]
  \\ cheat
QED

Theorem IMP_open_similarity_INSERT:
  (∀e. e IN Exps vars ⇒ open_similarity vars (subst h e e1) (subst h e e2)) ∧
  h ∉ vars ∧ e1 IN Exps (h INSERT vars) ∧ e2 IN Exps (h INSERT vars) ⇒
  open_similarity (h INSERT vars) e1 e2
Proof
  cheat (*
  fs [open_similarity_def] \\ rw [] \\ fs [Exps_def]
  \\ Cases_on ‘exps’ \\ fs [] \\ fs []
  \\ fs [subst_bind,bind_def]
  \\ ‘set (freevars h') ⊆ set vars’ by fs [closed_def]
  \\ fs [PULL_FORALL,AND_IMP_INTRO] *)
QED

Theorem open_similarity_inter:
  open_similarity vars e1 e2 =
  open_similarity (vars INTER freevars (App e1 e2)) e1 e2
Proof
  fs [open_similarity_def] \\ rw [] \\ eq_tac \\ rw []
  \\ cheat (* easy *)
QED

Theorem Howe_inter:
  ∀R vars e1 e2.
    Howe R vars e1 e2 ⇒
    ∀t. (∀vars e1 e2. R vars e1 e2 ⇒ R (vars INTER t e1 e2) e1 e2) ⇒
        Howe R (vars INTER t e1 e2) e1 e2
Proof
  cheat
QED

Theorem Howe_open_similarity: (* key property *)
  Howe open_similarity = open_similarity
Proof
  simp [FUN_EQ_THM] \\ rw []
  \\ rename [‘Howe open_similarity vars e1 e2’]
  \\ reverse eq_tac \\ rw []
  THEN1 (metis_tac [Howe_Ref_Tra,Ref_open_similarity,Tra_open_similarity])
  \\ assume_tac Cus_Howe_open_similarity \\ fs [Cus_def]
  \\ first_x_assum (qspec_then ‘{}’ mp_tac) \\ fs [] \\ rw []
  \\ assume_tac app_simulation_Howe_open_similarity
  \\ drule app_simulation_SUBSET_app_similarity
  \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ rw [SUBSET_DEF,IN_DEF,FORALL_PROD]
  \\ last_x_assum mp_tac
  \\ once_rewrite_tac [open_similarity_inter]
  \\ strip_tac \\ drule Howe_inter
  \\ disch_then (qspec_then ‘λe1 e2. freevars (App e1 e2)’ mp_tac)
  \\ fs [] \\ impl_tac THEN1 simp [Once open_similarity_inter]
  \\ ‘FINITE (vars ∩ (freevars (App e1 e2)))’ by
        (match_mp_tac FINITE_INTER \\ fs [])
  \\ fs [] \\ rename [‘FINITE t’]
  \\ qid_spec_tac ‘e2’
  \\ qid_spec_tac ‘e1’
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ qid_spec_tac ‘t’
  \\ Induct_on ‘FINITE’ \\ rw []
  THEN1
   (fs [open_similarity_def,FDOM_EQ_EMPTY] \\ res_tac
    \\ imp_res_tac Howe_vars \\ fs [])
  \\ assume_tac Cus_Howe_open_similarity \\ fs [Cus_def,AND_IMP_INTRO]
  \\ pop_assum (first_assum o mp_then Any mp_tac)
  \\ rw [] \\ simp []
  \\ match_mp_tac IMP_open_similarity_INSERT
  \\ imp_res_tac Howe_vars \\ fs [] \\ rw []
  \\ fs [Exps_def]
  \\ first_x_assum match_mp_tac
  \\ first_x_assum match_mp_tac
  \\ fs [Exps_def]
QED

Theorem Precongruence_open_similarity: (* part 1 of 5.5.5 *)
  Precongruence open_similarity
Proof
  fs [Precongruence_def] \\ rw [Tra_open_similarity]
  \\ once_rewrite_tac [GSYM Howe_open_similarity]
  \\ match_mp_tac Howe_Ref
  \\ fs [open_similarity_def,Ref_open_similarity]
QED

Theorem Congruence_open_bisimilarity: (* part 2 of 5.5.5 *)
  Congruence open_bisimilarity
Proof
  fs [Congruence_def,Sym_open_bisimilarity]
  \\ assume_tac Precongruence_open_similarity
  \\ fs [Precongruence_def,Tra_open_bisimilarity]
  \\ fs [Compatible_def] \\ rw []
  \\ fs [Com_defs,open_bisimilarity_def,open_similarity_def]
  \\ fs [app_bisimilarity_similarity]
  THEN1 metis_tac []
  THEN1 metis_tac []
  THEN1 metis_tac []
  \\ cheat
QED

(* -- contextual equivalence -- *)

Definition exp_eq_def:
  exp_eq x y ⇔
    ∀f. freevars x ∪ freevars y ⊆ FDOM f ⇒ bind f x ≃ bind f y
End

val _ = set_fixity "≅" (Infixl 480);
Overload "≅" = “exp_eq”;

Theorem exp_eq_open_bisimilarity:
  exp_eq x y ⇔ ∃vars. open_bisimilarity vars x y ∧
                      FINITE vars ∧ freevars x ∪ freevars y ⊆ vars
Proof
  eq_tac \\ rw []
  THEN1
   (fs [open_bisimilarity_def,SUBSET_DEF]
    \\ rw [] \\ fs [exp_eq_def]
    \\ qexists_tac ‘freevars (App x y)’ \\ fs []
    \\ rw [] \\ first_x_assum match_mp_tac
    \\ first_x_assum (assume_tac o GSYM) \\ fs [])
  \\ fs [exp_eq_def,open_bisimilarity_def] \\ rw []
  \\ fs [bind_def]
  \\ reverse IF_CASES_TAC \\ fs []
  THEN1
   (simp [Once app_bisimilarity_iff] \\ fs [eval_thm,closed_def])
  \\ first_x_assum (qspec_then ‘FUN_FMAP
        (λn. if n IN FDOM f then f ' n else Fail) vars’ mp_tac)
  \\ once_rewrite_tac [subst_FDIFF]
  \\ fs [FLOOKUP_FUN_FMAP]
  \\ reverse IF_CASES_TAC
  THEN1
   (fs [] \\ gvs [FLOOKUP_DEF] \\ Cases_on ‘n IN FDOM f’ \\ gvs []
    \\ res_tac \\ fs [closed_def]) \\ fs []
  \\ match_mp_tac (METIS_PROVE []
       “x1 = y1 ∧ x2 = y2 ⇒ f x1 x ≃ f x2 y ⇒ f y1 x ≃ f y2 y”)
  \\ fs [fmap_EXT,EXTENSION,DRESTRICT_DEF,FUN_FMAP_DEF,SUBSET_DEF]
  \\ metis_tac []
QED

Theorem open_bisimilarity_SUBSET:
  ∀x y vars vars'.
    open_bisimilarity vars x y ∧ vars SUBSET vars' ⇒
    open_bisimilarity vars' x y
Proof
  fs [open_bisimilarity_def] \\ rw []
  \\ imp_res_tac SUBSET_TRANS \\ fs []
  \\ rw [bind_def]
  \\ last_x_assum (qspec_then ‘FDOM f’ mp_tac) \\ rw []
  \\ last_x_assum (qspec_then ‘DRESTRICT f vars’ mp_tac)
  \\ fs [FDOM_DRESTRICT]
  \\ impl_tac THEN1 (fs [EXTENSION,SUBSET_DEF] \\ metis_tac [])
  \\ reverse (rw [bind_def])
  THEN1 (fs [FLOOKUP_DRESTRICT] \\ res_tac \\ fs [])
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [subst_FDIFF]
  \\ fs [DRESTRICT_DRESTRICT]
  \\ ‘vars ∩ freevars x = freevars x ∧
      vars ∩ freevars y = freevars y’ by (fs [EXTENSION,SUBSET_DEF] \\ metis_tac [])
  \\ fs []
QED

Theorem exp_eq_open_bisimilarity_freevars:
  exp_eq x y ⇔ open_bisimilarity (freevars x ∪ freevars y) x y
Proof
  fs [exp_eq_open_bisimilarity] \\ reverse eq_tac \\ rw []
  THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
  \\ fs [open_bisimilarity_def] \\ rw []
  \\ rw [bind_def]
  \\ first_x_assum (qspec_then ‘FUNION (DRESTRICT f vars) (FUN_FMAP (K Fail) vars)’ mp_tac)
  \\ impl_tac
  THEN1 (fs [fmap_EXT,EXTENSION,FDOM_DRESTRICT] \\ metis_tac [])
  \\ reverse (rw [bind_def])
  THEN1
   (gvs [FLOOKUP_FUNION,AllCaseEqs(),FLOOKUP_DEF,FUN_FMAP_DEF,FDOM_DRESTRICT]
    \\ fs [closed_def] \\ res_tac \\ gvs [DRESTRICT_DEF])
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [subst_FDIFF]
  \\ match_mp_tac (METIS_PROVE []
     “m1 = m1' ∧ m2 = m2' ⇒ subst m1 x ≃ subst m2 y ⇒ subst m1' x ≃ subst m2' y”)
  \\ fs [fmap_EXT,DRESTRICT_DEF,FUNION_DEF]
  \\ fs [EXTENSION,SUBSET_DEF] \\ rw []
  \\ metis_tac []
QED

Theorem exp_eq_perm:
  ~MEM x (freevars e) ∧ ~MEM y (freevars e) ⇒ e ≅ perm_exp x y e
Proof
  rw[exp_eq_open_bisimilarity] >>
  qexists_tac ‘freevars e’ >>
  rw[open_bisimilarity_def,GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN,SUBSET_DEF] >>
  TRY(gvs[perm1_def] >> every_case_tac >> gvs[] >> NO_TAC) >>
  rw[app_bisimilarity_similarity] >>
  match_mp_tac companion_app_similarity >>
  match_mp_tac(no_IN companion_exp_alpha) >>
  (reverse conj_tac >-
    (rw [bind_def] \\ TRY (fs [closed_def] \\ NO_TAC)
     \\ match_mp_tac IMP_closed_subst
     \\ fs [GSYM perm_exp_eqvt,SUBSET_DEF,MEM_MAP,PULL_EXISTS,perm1_def]
     \\ fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS] \\ rw [])) >>
  match_mp_tac exp_alpha_bind_all_closed >>
  MAP_FIRST match_mp_tac [exp_alpha_perm_irrel,exp_alpha_sym] >>
  TRY(match_mp_tac exp_alpha_perm_irrel) >>
  simp[]
QED

Theorem app_bisimilarity_eq:
  x ≃ y ⇔ x ≅ y ∧ closed x ∧ closed y
Proof
  fs [exp_eq_def,closed_def] \\ reverse eq_tac
  THEN1 (rw [] \\ fs [] \\ first_x_assum (qspec_then ‘FEMPTY’ mp_tac) \\ fs [])
  \\ strip_tac
  \\ ‘closed x ∧ closed y’ by fs [Once app_bisimilarity_iff,closed_def]
  \\ fs [bind_def,closed_def]
  \\ reverse (rw [])
  \\ fs [Once app_bisimilarity_iff,closed_def,eval_thm]
QED

Theorem fail[simp]:
  Fail ≃ Fail
Proof
  once_rewrite_tac [app_bisimilarity_iff] \\ fs [eval_thm,closed_def]
QED

Theorem exp_eq_refl:
  ∀x. x ≅ x
Proof
  fs [exp_eq_open_bisimilarity] \\ rw []
  \\ qexists_tac ‘freevars x’ \\ fs []
  \\ assume_tac Ref_open_bisimilarity
  \\ fs [Ref_def]
  \\ first_x_assum match_mp_tac
  \\ fs [Exps_def]
QED

Theorem exp_eq_sym:
  ∀x y. x ≅ y ⇔ y ≅ x
Proof
  qsuff_tac ‘∀x y. x ≅ y ⇒ y ≅ x’ THEN1 metis_tac []
  \\ fs [exp_eq_open_bisimilarity] \\ rw []
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ assume_tac Sym_open_bisimilarity
  \\ fs [Sym_def,PULL_FORALL,AND_IMP_INTRO]
  \\ first_x_assum match_mp_tac
  \\ fs [Exps_def]
QED

Theorem exp_eq_trans:
  ∀x y z. x ≅ y ∧ y ≅ z ⇒ x ≅ z
Proof
  fs [exp_eq_open_bisimilarity] \\ rw []
  \\ qexists_tac ‘vars UNION vars'’ \\ fs [SUBSET_DEF]
  \\ assume_tac Tra_open_bisimilarity
  \\ fs [Tra_def,PULL_FORALL,AND_IMP_INTRO]
  \\ first_x_assum match_mp_tac
  \\ fs [Exps_def,SUBSET_DEF]
  \\ qexists_tac ‘y’ \\ fs [] \\ rw []
  \\ match_mp_tac open_bisimilarity_SUBSET
  \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs [SUBSET_DEF]
QED

Theorem Congruence_exp_eq:
  Congruence (K $≅)
Proof
  mp_tac Congruence_open_bisimilarity
  \\ rw [Congruence_def,Precongruence_def]
  \\ fs [Sym_def,Tra_def]
  THEN1 metis_tac [exp_eq_sym]
  THEN1 metis_tac [exp_eq_trans]
  \\ fs [exp_eq_def]
  \\ fs [Compatible_def] \\ rw []
  \\ fs [Com1_def,Com2_def,Com3_def,Com4_def,Com5_def] \\ rw []
  THEN1 (fs [exp_eq_open_bisimilarity] \\ qexists_tac ‘{x}’ \\ fs [])
  THEN1
   (fs [exp_eq_open_bisimilarity_freevars,AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
    \\ simp [Exps_def,SUBSET_DEF]
    \\ match_mp_tac open_bisimilarity_SUBSET
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ fs [SUBSET_DEF])
  THEN1
   (fs [exp_eq_open_bisimilarity_freevars,AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
    \\ simp [Exps_def,SUBSET_DEF] \\ rw []
    \\ match_mp_tac open_bisimilarity_SUBSET
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ fs [SUBSET_DEF])
  THEN1
   (fs [exp_eq_open_bisimilarity_freevars,AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
    \\ simp [Exps_def,SUBSET_DEF,MEM_MAP,PULL_EXISTS] \\ rw []
    THEN1 metis_tac []
    THEN1 metis_tac []
    \\ qmatch_goalsub_abbrev_tac ‘open_bisimilarity vars1’
    \\ ‘BIGUNION (set (MAP (λe. freevars e) es)) SUBSET vars1 ∧
        BIGUNION (set (MAP (λe. freevars e) es')) SUBSET vars1’ by
           fs [Abbr‘vars1’]
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘es'’
    \\ qid_spec_tac ‘es’
    \\ Induct \\ fs [PULL_EXISTS] \\ rw []
    \\ fs [exp_eq_open_bisimilarity_freevars,AND_IMP_INTRO]
    \\ match_mp_tac open_bisimilarity_SUBSET
    \\ goal_assum (first_x_assum o mp_then (Pos hd) mp_tac)
    \\ fs [SUBSET_DEF])
  THEN1
   (fs [exp_eq_open_bisimilarity_freevars,AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
    \\ conj_tac
    THEN1
     (fs [Exps_def,SUBSET_DEF,MEM_MAP,PULL_EXISTS,FORALL_PROD,EXISTS_PROD]
      \\ rw []
      \\ cheat)
    \\ fs [] \\ reverse conj_tac
    THEN1
     (match_mp_tac open_bisimilarity_SUBSET
      \\ goal_assum (first_x_assum o mp_then (Pos hd) mp_tac)
      \\ fs [SUBSET_DEF] \\ metis_tac [])
    \\ qmatch_goalsub_abbrev_tac ‘open_bisimilarity vars1’
    \\ ‘BIGUNION (set (MAP (λ(_,e). freevars e) ves)) SUBSET vars1 ∧
        BIGUNION (set (MAP (λ(_,e). freevars e) ves')) SUBSET vars1’ by
           (fs [Abbr‘vars1’] \\ fs [SUBSET_DEF] \\ metis_tac [])
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ves'’
    \\ qid_spec_tac ‘ves’
    \\ Induct \\ fs [PULL_EXISTS,MAP_EQ_CONS,FORALL_PROD]
    \\ rw []
    \\ fs [exp_eq_open_bisimilarity_freevars,AND_IMP_INTRO]
    \\ match_mp_tac open_bisimilarity_SUBSET
    \\ goal_assum (first_x_assum o mp_then (Pos hd) mp_tac)
    \\ fs [SUBSET_DEF])
QED

Theorem open_similarity_Lam_IMP:
  open_similarity vars (Lam x e1) (Lam x e2) ∧ vars SUBSET vars1 ∧ x IN vars1 ⇒
  open_similarity vars1 e1 e2
Proof
  cheat
QED

Theorem exp_eq_Lam_lemma[local]:
  Lam x e1 ≅ Lam x e2 ⇔
  ∀y1 y2.
    y1 ≅ y2 ∧ closed y1 ∧ closed y2 ⇒
    subst x y1 e1 ≅ subst x y2 e2
Proof
  assume_tac Ref_open_similarity
  \\ drule IMP_Howe_Sub
  \\ fs [Cus_open_similarity,Tra_open_similarity,Howe_open_similarity]
  \\ fs [Sub_def] \\ rw []
  \\ eq_tac \\ rw []
  \\ fs [exp_eq_open_bisimilarity]
  \\ fs [bind_def,PULL_EXISTS]
  THEN1
   (fs [SUBSET_DEF,MEM_FILTER,freevars_subst]
    \\ fs [closed_def] \\ fs [GSYM closed_def]
    \\ qexists_tac ‘vars DELETE x’ \\ fs [AND_IMP_INTRO]
    \\ fs [open_bisimilarity_eq] \\ rw []
    \\ first_x_assum match_mp_tac
    \\ fs [Exps_def,SUBSET_DEF]
    \\ rw [] \\ gvs [closed_def]
    \\ TRY (match_mp_tac open_similarity_Lam_IMP \\ fs [SUBSET_DEF] \\ NO_TAC)
    \\ TRY (rpt (qpat_x_assum ‘open_similarity _ _ _’ mp_tac)
            \\ once_rewrite_tac [open_similarity_inter] \\ fs [] \\ NO_TAC)
    \\ metis_tac [])
  \\ qexists_tac ‘freevars (App e1 e2)’ \\ fs []
  \\ fs [SUBSET_DEF,MEM_FILTER] \\ rw []
  \\ rw [open_bisimilarity_eq] \\ rw []
  \\ cheat
QED

Theorem exp_eq_forall_subst:
  ∀v. x ≅ y ⇔ ∀z. closed z ⇒ subst v z x ≅ subst v z y
Proof
  fs [exp_eq_def] \\ rw [] \\ eq_tac \\ rw []
  THEN1
   (rw [bind_def] \\ fs []
    \\ ‘(∀x. x ∈ FRANGE (FEMPTY |+ (v,z)) ⇒ closed x)’ by fs [FRANGE_DEF]
    \\ drule subst_subst_FUNION \\ fs [] \\ rw []
    \\ last_x_assum (qspec_then ‘FEMPTY |+ (v,z) ⊌ f’ mp_tac)
    \\ impl_tac THEN1 (fs [SUBSET_DEF,freevars_subst] \\ metis_tac [])
    \\ rw [bind_def]
    \\ gvs [FLOOKUP_FUNION,FLOOKUP_UPDATE,AllCaseEqs()] \\ res_tac)
  \\ reverse (Cases_on ‘v IN FDOM f’)
  THEN1
   (‘~(MEM v (freevars x)) ∧ ~(MEM v (freevars y))’ by (fs [SUBSET_DEF] \\ metis_tac [])
    \\ gvs [subst_ignore_single]
    \\ fs [PULL_FORALL,AND_IMP_INTRO]
    \\ first_x_assum irule \\ fs [] \\ qexists_tac ‘Fail’ \\ fs [closed_def])
  \\ rw [bind_def] \\ fs []
  \\ first_x_assum (qspec_then ‘f ' v’ mp_tac)
  \\ impl_keep_tac
  THEN1 (first_x_assum match_mp_tac \\ qexists_tac ‘v’ \\ fs [FLOOKUP_DEF])
  \\ disch_then (qspec_then ‘f’ mp_tac)
  \\ impl_tac THEN1 fs [SUBSET_DEF,freevars_subst]
  \\ fs [bind_def]
  \\ IF_CASES_TAC \\ fs []
  \\ res_tac \\ fs []
  \\ ‘(∀x. x ∈ FRANGE (FEMPTY |+ (v,f ' v)) ⇒ closed x)’ by fs [FRANGE_DEF]
  \\ drule subst_subst_FUNION \\ fs [] \\ rw [] \\ gvs []
  \\ qsuff_tac ‘FEMPTY |+ (v,f ' v) ⊌ f = f’ \\ rw [] \\ fs []
  \\ fs [fmap_EXT,FUNION_DEF] \\ rw []
  \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
QED

Theorem exp_eq_free:
  ~MEM v (freevars y) ⇒
  (x ≅ y ⇔ ∀z. closed z ⇒ subst v z x ≅ y)
Proof
  metis_tac [exp_eq_forall_subst,subst_ignore_single]
QED

Theorem exp_eq_perm_IMP:
  ∀x y e e'.
    ~(MEM x (freevars e')) ∧ ~(MEM y (freevars e')) ∧ e ≅ perm_exp x y e' ⇒ e ≅ e'
Proof
  metis_tac [exp_eq_perm,exp_eq_sym,exp_eq_trans]
QED

Theorem exp_eq_subst_perm_exp:
  closed e' ⇒ subst y e' e ≅ subst y (perm_exp x y e') e
Proof
  cheat (* might follow from exp_eq_perm and congruence *)
QED

Triviality Lam_Lam:
  Lam x e1 ≅ Lam y e2 ⇔
  ∀xv yv. closed xv ∧ closed yv ⇒ subst y yv (Lam x e1) ≅ subst x xv (Lam y e2)
Proof
  Cases_on ‘x=y’ \\ fs [subst_def]
  \\ ‘closed Fail’ by fs [closed_def]
  THEN1 metis_tac []
  \\ ‘~MEM y (freevars (Lam y e2))’ by fs [MEM_FILTER]
  \\ drule exp_eq_free
  \\ disch_then (once_rewrite_tac o single)
  \\ simp [subst_def]
  \\ ‘∀e1. ~MEM x (freevars (Lam x e1))’ by fs [MEM_FILTER]
  \\ ‘(∀e1 x'. Lam x e1 ≅ x' ⇔ ∀z. closed z ⇒ Lam x e1 ≅ subst x z x')’
         by metis_tac [exp_eq_sym,exp_eq_free]
  \\ pop_assum (simp o single o Once)
  \\ fs [subst_def,PULL_FORALL,AND_IMP_INTRO]
  \\ metis_tac []
QED

Triviality subst_subst_lemma:
  closed y1 ∧ closed y2 ⇒
  (subst x y1 e1 ≅ subst y y2 e2 ⇔
   ∀xv yv. closed xv ∧ closed yv ⇒
           subst y yv (subst x y1 e1) ≅ subst x xv (subst y y2 e2))
Proof
  strip_tac
  \\ Cases_on ‘x=y’ \\ fs [subst_def,subst_subst_eq]
  THEN1 metis_tac []
  \\ ‘closed Fail’ by fs [closed_def]
  \\ simp [subst_def]
  \\ ‘~MEM y (freevars (subst y y2 e2))’ by fs [freevars_subst]
  \\ drule exp_eq_free
  \\ disch_then (once_rewrite_tac o single)
  \\ drule_at (Pos last) subst_subst_single
  \\ disch_then (simp o single)
  \\ ‘∀e1. ~MEM x (freevars (subst x y1 e1))’ by fs [freevars_subst]
  \\ ‘(∀e1 x'. subst x y1 e1 ≅ x' ⇔ ∀z. closed z ⇒ subst x y1 e1 ≅ subst x z x')’
         by metis_tac [exp_eq_sym,exp_eq_free]
  \\ pop_assum (simp o single o Once)
  \\ fs [subst_def,PULL_FORALL,AND_IMP_INTRO]
  \\ metis_tac []
QED

Theorem exp_eq_Lam:
  Lam x e1 ≅ Lam y e2 ⇔
  ∀y1 y2.
    y1 ≅ y2 ∧ closed y1 ∧ closed y2 ⇒
    subst x y1 e1 ≅ subst y y2 e2
Proof
  Cases_on ‘x = y’ THEN1 metis_tac [exp_eq_Lam_lemma]
  \\ fs [Lam_Lam]
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [subst_def])) \\ fs []
  \\ CONV_TAC (RAND_CONV (SIMP_CONV std_ss [Once subst_subst_lemma])) \\ fs []
  \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ ‘∀t xv. closed xv ⇒ (t ≅ Lam y (subst x xv e2) ⇔
                          t ≅ Lam x (subst y (perm_exp x y xv) (perm_exp x y e2)))’ by
   (rw [] \\ eq_tac \\ rw []
    \\ match_mp_tac exp_eq_perm_IMP
    \\ qexists_tac ‘x’ \\ qexists_tac ‘y’
    \\ fs [MEM_FILTER,freevars_subst,closed_perm]
    \\ fs [perm_exp_def,perm1_def,subst_single_eqvt])
  \\ fs [exp_eq_Lam_lemma,DOMSUB_FUPDATE_THM]
  \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ drule_at Any subst_subst_single
  \\ disch_then (simp o single o GSYM)
  \\ pop_assum kall_tac
  \\ eq_tac \\ rw [] \\ fs [AC CONJ_ASSOC CONJ_COMM]
  \\ first_x_assum (first_x_assum o mp_then (Pos last) mp_tac)
  THEN1
   (disch_then (qspecl_then [‘xv’,‘yv’] assume_tac) \\ gvs []
    \\ drule_at (Pos last) subst_subst_single
    \\ fs [] \\ disch_then kall_tac
    \\ match_mp_tac exp_eq_trans
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ match_mp_tac exp_eq_perm_IMP
    \\ qexists_tac ‘x’ \\ qexists_tac ‘y’ \\ fs []
    \\ fs [freevars_subst,subst_single_eqvt,perm1_def]
    \\ drule_at (Pos last) subst_subst_single
    \\ fs [closed_perm] \\ disch_then kall_tac
    \\ rename [‘subst _ _ e ≅ _’]
    \\ once_rewrite_tac [perm_exp_sym]
    \\ fs [exp_eq_subst_perm_exp])
  THEN1
   (disch_then (qspecl_then [‘xv’,‘yv’] assume_tac) \\ gvs []
    \\ match_mp_tac exp_eq_trans
    \\ ‘y ≠ x’ by fs []
    \\ drule_at (Pos last) subst_subst_single
    \\ fs [closed_perm]
    \\ disch_then (qspecl_then [‘e1’,‘y1’,‘yv’] assume_tac) \\ rfs []
    \\ pop_assum (rewrite_tac o single)
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ drule_at (Pos last) subst_subst_single
    \\ fs [closed_perm]
    \\ disch_then (qspecl_then [‘e2’,‘xv’,‘y2’] assume_tac) \\ rfs []
    \\ pop_assum (rewrite_tac o single)
    \\ match_mp_tac exp_eq_perm_IMP
    \\ qexists_tac ‘x’ \\ qexists_tac ‘y’ \\ fs []
    \\ fs [freevars_subst,subst_single_eqvt,perm1_def, closed_perm]
    \\ fs [exp_eq_subst_perm_exp])
QED

Theorem exp_eq_Lam:
  Lam v1 e1 ≅ Lam v2 e2 ⇔
  ∀x1 x2. x1 ≃ x2 ⇒ subst v1 x1 e1 ≅ subst v2 x2 e2
Proof
  metis_tac [exp_eq_Lam,app_bisimilarity_eq]
QED

Theorem exp_eq_Lam_cong:
  e ≅ e' ⇒ Lam x e ≅ Lam x e'
Proof
  assume_tac Congruence_exp_eq
  \\ fs [Congruence_def,Precongruence_def,Compatible_def,Com2_def]
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ qexists_tac ‘freevars (App (Lam x e) (Lam x e'))’
  \\ fs [Exps_def,SUBSET_DEF] \\ fs [MEM_FILTER]
QED

Theorem exp_eq_App_cong:
  f ≅ f' ∧ e ≅ e' ⇒ App f e ≅ App f' e'
Proof
  assume_tac Congruence_exp_eq
  \\ fs [Congruence_def,Precongruence_def,Compatible_def,Com3_def]
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ qexists_tac ‘freevars (App f (App f' (App e e')))’
  \\ fs [Exps_def,SUBSET_DEF]
QED

val _ = export_theory();
