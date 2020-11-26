(*
   This file formalises Howe's method following the description of
   Pitts 2011 chapter "Howe's method for higher-order languages".
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory
     expTheory valueTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     pure_langTheory pred_setTheory relationTheory
     BasicProvers pure_langPropsTheory;

val _ = new_theory "howe";


(* -- basics -- *)

(* the set of all values with at most free variables vars *)
Definition Vals_def:
  Vals vars = { v | freevars_v v ⊆ set vars }
End

(* the set of all expressions with at most free variables vars *)
Definition Exps_def:
  Exps vars = { e | set (freevars e) ⊆ set vars }
End

Theorem Exps_EMPTY_closed[simp]:
  e IN Exps [] ⇔ closed e
Proof
  fs [Exps_def,closed_def]
QED


(* -- applicative (bi)similarity -- *)

Definition unfold_rel_def:
  unfold_rel rel (e1, e2) ⇔
    closed e1 ∧ closed e2 ∧
    (* this follows the paper directly *)
    (∀x e1'. eval e1 = Closure x e1' ⇒
             ∃e2'. eval e2 = Closure x e2' ∧
                   ∀e. closed e ⇒ rel (subst x e e1', subst x e e2'))
    (* but I think we need one such conjunct for each result alternative, e.g.
    ∧
    (∀x xs.
       eval e1 = Constructor x xs ⇒
       ∃es1 es2. eval e1 = eval (Cons x es1) ∧ EVERY closed es1 ∧
                 eval e2 = eval (Cons x es2) ∧ EVERY closed es2 ∧
                 LIST_REL (CURRY rel) es1 es2)
    ∧
    (∀a. eval e1 = Atom a ⇒ eval e2 = Atom a)
    ∧
    (eval e1 = Diverge ⇒ eval e2 = Diverge)
    ∧
    (eval e1 = Error ⇒ eval e2 = Error) *)
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

Triviality monotone_similarity:
  monotone FF
Proof
  fs [monotone_def,FF_def,unfold_rel_def]
  \\ fs [SUBSET_DEF,FORALL_PROD,IN_DEF]
  \\ metis_tac []
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
  fs [monotone_def,FF_def,unfold_rel_def,opp_def]
  \\ fs [SUBSET_DEF,FORALL_PROD,IN_DEF,opp_def]
  \\ metis_tac []
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

Theorem app_bisimulation_SUBSET_app_bisimilarity:
  app_bisimulation R ⇒ R ⊆ app_bisimilarity
Proof
  rw [app_bisimilarity_def,app_bisimulation_def,app_simulation_def]
  \\ fs [gfp_def,SUBSET_DEF,FORALL_PROD,opp_def,IN_DEF]
  \\ fs [IN_DEF,FF_def,EXISTS_PROD,unfold_rel_def,opp_def]
  \\ rw [] \\ qexists_tac ‘R’ \\ rw []
  \\ res_tac \\ fs []
QED

Theorem app_bisimulation_app_bisimilarity:
  app_bisimulation app_bisimilarity
Proof
  fs [app_bisimulation_def,app_simulation_def,opp_def,IN_DEF,unfold_rel_def]
  \\ assume_tac app_bisimilarity_iff
  \\ metis_tac [unfold_rel_def]
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
  gvs[v_lookup_Error,v_lookup_Diverge,v_lookup_Atom,v_lookup_Closure,v_lookup_Constructor,AllCaseEqs(),
      oEL_THM] >>
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
      gvs[eval_op_def,AllCaseEqs(),MAP_EQ_CONS,DISJ_IMP_THM,FORALL_AND_THM,MEM_MAP,MEM_FLAT,PULL_EXISTS]
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
  >- (rename1 ‘App’ >>
      gvs[freevars_def,MEM_FILTER,eval_to_def] >>
      rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
      res_tac >> fs[bind_def] >>
      PURE_FULL_CASE_TAC >> fs[freevars_subst] >>
      gvs[dest_Closure_def,AllCaseEqs(),MEM_FILTER,PULL_EXISTS])
  >- (rename1 ‘Letrec’ >>
      gvs[freevars_def,MEM_FILTER,MEM_FLAT,MEM_MAP,PULL_EXISTS,eval_to_def] >>
      PURE_FULL_CASE_TAC >> gvs[] >>
      first_x_assum drule >> strip_tac >> fs[subst_funs_def,freevars_bind] >>
      reverse FULL_CASE_TAC >- fs[] >>
      gvs[MEM_FILTER] >>
      gvs[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
      metis_tac[MEM_MAP,FST])
  >- (rename1 ‘Case’ >>
      gvs[freevars_def,MEM_FILTER,MEM_FLAT,MEM_MAP,PULL_EXISTS,eval_to_def] >>
      PURE_FULL_CASE_TAC >> gvs[] >>
      res_tac >>
      drule freevars_expandCases >> strip_tac >>
      gvs[MEM_FILTER] >>
      disj2_tac >>
      goal_assum drule >>
      rw[MEM_FILTER])
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

Theorem reflexive_app_similarity: (* exercise (5.3.3) *)
  reflexive (UNCURRY $≲) closed
Proof
  rw[set_relationTheory.reflexive_def,ELIM_UNCURRY,IN_DEF] >>
  ‘∀x y. x = y ∧ closed x ⇒ x ≲ y’ suffices_by metis_tac[] >>
  pop_assum kall_tac >>
  ho_match_mp_tac app_similarity_coinduct >>
  rw[FF_def,ELIM_UNCURRY,unfold_rel_def] >>
  simp[] >>
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

Theorem transitive_app_similarity: (* exercise (5.3.3) *)
  transitive $≲
Proof
  rw[transitive_def,ELIM_UNCURRY,IN_DEF] >>
  rpt(first_x_assum mp_tac) >>
  simp[AND_IMP_INTRO] >>
  rename [‘x ≲ y ∧ y ≲ z’] >>
  MAP_EVERY qid_spec_tac [‘y’,‘z’,‘x’] >>
  simp[GSYM PULL_EXISTS] >>
  ho_match_mp_tac app_similarity_coinduct >>
  rw[ELIM_UNCURRY,FF_def,unfold_rel_def] >>
  imp_res_tac app_similarity_closed >>
  rpt(qpat_x_assum ‘_ ≲ _’ (strip_assume_tac o PURE_ONCE_REWRITE_RULE[app_similarity_iff])) >>
  gvs[unfold_rel_def] >>
  metis_tac[]
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
  \\ rpt GEN_TAC
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘FF R’
  \\ ‘opp R = R’ by(simp[FUN_EQ_THM] >> Cases >> rw[opp_def,Abbr‘R’,ELIM_UNCURRY,EQ_IMP_THM])
  \\ pop_assum SUBST_ALL_TAC
  \\ rw[Abbr ‘R’,FF_def,unfold_rel_def,ELIM_UNCURRY]
  \\ imp_res_tac app_similarity_closed
  \\ rpt(qpat_x_assum ‘_ ≲ _’ (strip_assume_tac o PURE_ONCE_REWRITE_RULE[app_similarity_iff]))
  \\ gvs[unfold_rel_def]
QED

Theorem reflexive_app_bisimilarity: (* exercise (5.3.3) *)
  reflexive (UNCURRY $≃) closed
Proof
  rw[set_relationTheory.reflexive_def,app_bisimilarity_similarity,ELIM_UNCURRY] >>
  imp_res_tac(reflexive_app_similarity |> SIMP_RULE std_ss [set_relationTheory.reflexive_def,ELIM_UNCURRY]) >>
  gvs[]
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

Theorem compatible_app_similarity:
  compatible (λR. app_similarity)
Proof
  rw[compatible_def,app_similarity_def] >>
  metis_tac[gfp_greatest_fixedpoint,monotone_similarity]
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

Theorem FF_trans:
  ∀R S x y z.
    (x,z) ∈ FF R ∧ (z,y) ∈ FF S ⇒ (x,y) ∈ FF {(x,y) | ∃z. (x,z) ∈ R ∧ (z,y) ∈ S}
Proof
  rw[FF_def,IN_DEF,ELIM_UNCURRY,unfold_rel_def] >>
  metis_tac[]
QED

Theorem companion_duplicate:
  ∀x y z. companion R (x,z) ∧ companion R (z,y) ⇒ companion R (x,y)
Proof
  rw[companion_def] >>
  qexists_tac ‘λR. {(x,y) | ∃z. (x,z) ∈ f R ∧ (z,y) ∈ f' R}’ >>
  gvs[monotone_def,compatible_def,pred_setTheory.SUBSET_DEF] >>
  conj_tac >- (rw[] >> metis_tac[]) >>
  reverse conj_tac >- metis_tac[] >>
  rw[] >>
  res_tac >>
  metis_tac[FF_trans]
QED

Theorem companion_rel:
  ∀R x y. R x y ⇒ companion R (x,y)
Proof
  rw[companion_def] >>
  qexists_tac ‘I’ >> rw[monotone_def,compatible_def,IN_DEF]
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
    set(freevars e1) ⊆ set names ∧
    set(freevars e2) ⊆ set names ∧
    ALL_DISTINCT names ∧
    ∀exps.
      LENGTH exps = LENGTH names ∧
      EVERY closed exps
      ⇒
      bind (ZIP(names,exps)) e1 ≲ bind (ZIP(names,exps)) e2
End

Definition open_bisimilarity_def:
  open_bisimilarity names e1 e2 ⇔
    set(freevars e1) ⊆ set names ∧
    set(freevars e2) ⊆ set names ∧
    ALL_DISTINCT names ∧
    ∀exps.
      LENGTH exps = LENGTH names ∧
      EVERY closed exps
      ⇒
      bind (ZIP(names,exps)) e1 ≃ bind (ZIP(names,exps)) e2
End

Definition Ref_def:
  Ref R ⇔
    ∀vars e. ALL_DISTINCT vars ∧ e IN Exps vars ⇒ R vars e e
End

Definition Sym_def:
  Sym R ⇔
    ∀vars e1 e2.
      ALL_DISTINCT vars ∧ {e1; e2} SUBSET Exps vars ⇒
      R vars e1 e2 ⇒ R vars e2 e1
End

Definition Tra_def:
  Tra R ⇔
    ∀vars e1 e2 e3.
      ALL_DISTINCT vars ∧ {e1; e2; e3} SUBSET Exps vars ⇒
      R vars e1 e2 ∧ R vars e2 e3 ⇒ R vars e1 e3
End

Definition Com1_def:
  Com1 R ⇔
    ∀vars x.
      ALL_DISTINCT vars ∧ MEM x vars ⇒
      R vars (Var x) (Var x)
End

Definition Com2_def:
  Com2 R ⇔
    ∀vars x e e'.
      ALL_DISTINCT vars ∧ ~(MEM x vars) ∧ {e; e'} SUBSET Exps (x::vars) ⇒
      R (x::vars) e e' ⇒ R vars (Lam x e) (Lam x e')
End

Definition Com3_def:
  Com3 R ⇔
    ∀vars e1 e1' e2 e2'.
      ALL_DISTINCT vars ∧ {e1; e1'; e2; e2'} SUBSET Exps vars ⇒
      R vars e1 e1' ∧ R vars e2 e2' ⇒ R vars (App e1 e2) (App e1' e2')
End

Definition Compatible_def:
  Compatible R ⇔ Com1 R ∧ Com2 R ∧ Com3 R
End

Definition Precongruence_def:
  Precongruence R ⇔ Tra R ∧ Compatible R
End

Definition Congruence_def:
  Congruence R ⇔ Sym R ∧ Precongruence R
End

Theorem open_similarity_reflexive:
  set(freevars e1) ⊆ set names ∧ ALL_DISTINCT names ⇒ open_similarity names e1 e1
Proof
  cheat
QED

Theorem Ref_open_similarity:
  Ref open_similarity
Proof
  cheat
QED

Theorem Sym_open_similarity:
  Sym open_bisimilarity
Proof
  cheat
QED

(* (Tra) in the paper has an amusing typo that renders the corresponding proposition a tautology *)
Theorem open_similarity_transitive:
  open_similarity names e1 e2 ∧ open_similarity names e2 e3 ⇒ open_similarity names e1 e3
Proof
  rw[open_similarity_def] >>
  metis_tac[transitive_app_similarity |> SIMP_RULE std_ss[transitive_def]]
QED

Theorem Tra_open_similarity:
  Tra open_similarity
Proof
  cheat
QED

(* (Com1) in Pitts *)
Theorem open_similarity_var_refl:
  MEM x names ∧ ALL_DISTINCT names ⇒ open_similarity names (Var x) (Var x)
Proof
  rw[open_similarity_def,bind_def,bind_Var_lemma,MAP_ZIP] >>
  TOP_CASE_TAC >- (gvs[ALOOKUP_NONE,MEM_MAP,MEM_ZIP,MEM_EL] >> metis_tac[FST,SND]) >>
  imp_res_tac ALOOKUP_MEM >>
  drule_at(Pos last) MEM_ZIP_MEM_MAP >>
  impl_tac >- rw[] >>
  rw[] >>
  gvs[EVERY_MEM,reflexive_app_similarity']
QED

(* (Com2) in Pitts *)
Theorem open_similarity_Lam_pres:
  open_similarity (x::names) e1 e2 ⇒
  open_similarity names (Lam x e1) (Lam x e2)
Proof
  rw[open_similarity_def,SUBSET_DEF,MEM_FILTER] >>
  TRY(res_tac >> gvs[] >> NO_TAC) >>
  simp[bind_Lam,MAP_ZIP] >>
  simp[app_similarity_iff] >>
  simp[unfold_rel_def] >>
  conj_tac >- cheat >>
  conj_tac >- cheat >>
  rw[eval_thm] >>
  first_x_assum(qspec_then ‘e::exps’ mp_tac) >>
  simp[bind_def]
QED

(* (Com3L) in Pitts *)
Theorem open_similarity_App_pres1:
  open_similarity names e1 e2 ∧ set(freevars e3) ⊆ set names ⇒
  open_similarity names (App e1 e3) (App e2 e3)
Proof
  rw[open_similarity_def,SUBSET_DEF,MEM_FILTER] >> gvs[bind_App,MAP_ZIP] >>
  simp[app_similarity_iff] >>
  simp[unfold_rel_def] >>
  conj_tac >- cheat >>
  conj_tac >- cheat >>
  rpt strip_tac >>
  gvs[eval_App,AllCaseEqs(),PULL_FORALL,dest_Closure_def] >>
  last_x_assum drule_all >>
  simp[Once app_similarity_iff] >>
  rw[unfold_rel_def] >>
  simp[GSYM PULL_FORALL] >>
  gvs[bind_def] >>
  reverse IF_CASES_TAC >- cheat >>
  gvs[] >>
  first_assum drule >>
  SIMP_TAC std_ss [Once app_similarity_iff] >>
  rw[unfold_rel_def]
QED

(* (Com3R) in Pitts *)
Theorem open_similarity_App_pres2:
  set(freevars e1) ⊆ set names ∧ open_similarity names e2 e3 ⇒
  open_similarity names (App e1 e2) (App e1 e3)
Proof
  (* This one seems more complicated than the preceding thms. Probably requires Howe's construction ;) *)
  cheat
QED

(* -- Howe's construction -- *)

Inductive Howe:
[Howe1:]
  (∀R vars e1 e2.
     R vars e1 e2 ⇒
     Howe R vars e1 e2)
  ∧
[Howe2:]
  (∀R x e1 e1' e2 vars.
     Howe R (x::vars) e1 e1' ∧
     R vars (Lam x e1') e2 ∧
     ~(MEM x vars) ⇒
     Howe R vars (Lam x e1) e2)
  ∧
[Howe3:]
  (∀R e1 e1' e3 vars.
     Howe R vars e1 e1' ∧
     Howe R vars e2 e2' ∧
     R vars (App e1' e2') e3 ⇒
     Howe R vars (App e1 e2) e3)
End

Theorem Howe_Ref: (* 5.5.1(i) *)
  Ref R ⇒ Compatible (Howe R)
Proof
  cheat
QED

Theorem Howe_Tra: (* 5.5.1(ii) *)
  Tra R ⇒
  ∀vars e1 e2 e3.
    Howe R vars e1 e2 ∧ R vars e2 e3 ⇒ Howe R vars e1 e3
Proof
  cheat
QED

Theorem Howe_Ref_Tra: (* 5.5.1(iii) *)
  Ref R ∧ Tra R ⇒
  ∀vars e1 e2. R vars e1 e2 ⇒ Howe R vars e1 e2
Proof
  cheat
QED

Definition Sub_def: (* Sub = substitutive *)
  Sub R ⇔
    ∀vars x e1 e1' e2 e2'.
      ALL_DISTINCT vars ∧ ~MEM x vars ∧
      {e1; e1'} SUBSET Exps (x::vars) ∧ {e2; e2'} SUBSET Exps vars ⇒
      R (x::vars) e1 e1' ∧ R vars e2 e2' ⇒
      R vars (subst x e2 e1) (subst x e2' e1')
  (* TODO: we should use a capture avoiding subst here! *)
End

Definition Cus_def: (* closed under value-substitution *)
  Cus R ⇔
    ∀vars x e1 e1' e2.
      ALL_DISTINCT vars ∧ ~MEM x vars ∧
      {e1; e1'} SUBSET Exps (x::vars) ∧ e2 IN Exps vars ⇒
      R (x::vars) e1 e1' ⇒
      R vars (subst x e2 e1) (subst x e2 e1')
  (* TODO: we should use a capture avoiding subst here! *)
End

Theorem Sub_Ref_IMP_Cus:
  Sub R ∧ Ref R ⇒ Cus R
Proof
  cheat
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
  cheat
QED

Theorem Cus_Howe_open_similarity:
  Cus (Howe open_similarity)
Proof
  cheat
QED

Theorem IMP_Howe_Sub: (* key lemma 5.5.4 *)
  eval e1 = Closure x e ∧ Howe open_similarity [] e1 e2 ⇒
  ∃e'. eval e2 = Closure x e' ∧ Howe open_similarity [x] e e'
Proof
  cheat
QED

Theorem Howe_vars:
  Howe open_similarity vars e1 e2 ⇒
  set (freevars e1) SUBSET set vars ∧
  set (freevars e2) SUBSET set vars ∧ ALL_DISTINCT vars
Proof
  cheat
QED

Theorem IMP_open_similarity_CONS:
  (∀e. e IN Exps vars ⇒ open_similarity vars (subst h e e1) (subst h e e2)) ∧
  ~MEM h vars ∧ e1 IN Exps (h::vars) ∧ e2 IN Exps (h::vars) ∧ ALL_DISTINCT vars ⇒
  open_similarity (h::vars) e1 e2
Proof
  fs [open_similarity_def] \\ rw [] \\ cheat
QED

Theorem Howe_open_similarity: (* key property *)
  Howe open_similarity = open_similarity
Proof
  simp [FUN_EQ_THM] \\ rw []
  \\ rename [‘Howe open_similarity vars e1 e2’]
  \\ reverse eq_tac \\ rw []
  THEN1 (once_rewrite_tac [Howe_cases] \\ fs [])
  \\ assume_tac Cus_Howe_open_similarity \\ fs [Cus_def]
  \\ first_x_assum (qspec_then ‘[]’ mp_tac) \\ fs [] \\ rw []
  \\ ‘app_simulation (UNCURRY (Howe open_similarity []))’ by
        cheat (* based on IMP_Howe_Sub *)
  \\ drule app_simulation_SUBSET_app_similarity
  \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ rw [SUBSET_DEF,IN_DEF,FORALL_PROD]
  \\ last_x_assum mp_tac
  \\ EVERY (map qid_spec_tac [‘e2’,‘e1’,‘vars’])
  \\ Induct \\ rw []
  THEN1
   (fs [open_similarity_def,bind_def]
    \\ imp_res_tac Howe_vars \\ fs [])
  \\ assume_tac Cus_Howe_open_similarity \\ fs [Cus_def,AND_IMP_INTRO]
  \\ pop_assum (first_assum o mp_then Any mp_tac)
  \\ rw [] \\ simp []
  \\ match_mp_tac IMP_open_similarity_CONS
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

Theorem Congruence_open_bisimilarity: (* part 1 of 5.5.5 *)
  Congruence open_bisimilarity
Proof
  cheat
QED

(* -- contextual equivalence -- *)



val _ = export_theory();
