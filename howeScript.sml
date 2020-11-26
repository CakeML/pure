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
    ∀x e1'. eval e1 = Closure x e1' ⇒
            ∃e2'. eval e2 = Closure x e2' ∧
                  ∀e. closed e ⇒ rel (subst x e e1', subst x e e2')
    (* but I think we need one such conjunct for each result alternative *)
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
      res_tac >> cheat)
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

(* -- congruence -- *)


(* -- Howe's construction -- *)


(* -- contextual equivalence -- *)



val _ = export_theory();
