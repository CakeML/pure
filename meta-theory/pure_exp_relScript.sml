(*
   This file defines three forms of relations between expressions.
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_miscTheory;

val _ = new_theory "pure_exp_rel";

val no_IN = SIMP_RULE std_ss [IN_DEF];

(* -- basics -- *)

Definition Exps_def:
  Exps vars = { e | freevars e ⊆ vars }
End

Theorem Exps_EMPTY_closed[simp]:
  e IN Exps EMPTY ⇔ closed e
Proof
  fs [Exps_def,closed_def]
QED

Theorem Exps_simps:
  (∀v vars. Var v ∈ Exps vars ⇔ v ∈ vars) ∧
  (∀op l vars. Prim op l ∈ Exps vars ⇔ EVERY (λe. e ∈ Exps vars) l) ∧
  (∀e1 e2 vars. App e1 e2 ∈ Exps vars ⇔ e1 ∈ Exps vars ∧ e2 ∈ Exps vars) ∧
  (∀x e vars. Lam x e ∈ Exps vars ⇔ e ∈ Exps (x INSERT vars)) ∧
  (∀fns e vars. Letrec fns e ∈ Exps vars ⇔
                  e ∈ Exps (vars ∪ set (MAP FST fns)) ∧
                  EVERY (λe. e ∈ Exps (vars ∪ set (MAP FST fns))) (MAP SND fns))
Proof
  rw[Exps_def, GSYM SUBSET_INSERT_DELETE]
  >- (
    rw[SUBSET_DEF, PULL_EXISTS, MEM_MAP, EVERY_MEM,
       PULL_FORALL, AND_IMP_INTRO] >>
    metis_tac[]
    )
  >- (
    rw[SUBSET_DEF, PULL_EXISTS, MEM_MAP, EVERY_MEM, EXISTS_PROD] >>
    metis_tac[]
    )
QED

Theorem Exps_SUBSET:
  ∀e vars vars'. e ∈ Exps vars ∧ vars ⊆ vars' ⇒ e ∈ Exps vars'
Proof
  rw[Exps_def, SUBSET_DEF]
QED


(* -- applicative (bi)similarity -- *)

Definition unfold_rel_def:
  unfold_rel rel (e1, e2) ⇔
    closed e1 ∧ closed e2 ∧
    (∀x ce1.
      eval_wh e1 = wh_Closure x ce1
      ⇒ ∃y ce2.
          eval_wh e2 = wh_Closure y ce2 ∧
          ∀e. closed e ⇒ rel (subst x e ce1, subst y e ce2))
    ∧
    (∀x e1s.
      eval_wh e1 = wh_Constructor x e1s
       ⇒ ∃e2s. eval_wh e2 = wh_Constructor x e2s ∧
               LIST_REL (CURRY rel) e1s e2s)
    ∧
    (∀a. eval_wh e1 = wh_Atom a ⇒ eval_wh e2 = wh_Atom a)
    ∧
    (eval_wh e1 = wh_Error ⇒ eval_wh e2 = wh_Error)
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
  fs [monotone_def,FF_def,unfold_rel_def] >>
  fs [SUBSET_DEF,FORALL_PROD,IN_DEF, LIST_REL_EL_EQN] >> rw[] >> fs[]
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
  qpat_x_assum `LIST_REL _ _ _` mp_tac >> rw[LIST_REL_EL_EQN, opp_def, IN_DEF]
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

Theorem eval_eq_imp_app_similarity:
  ∀x y.
    eval x = eval y ∧ closed x ∧ closed y
  ⇒ x ≲ y
Proof
  ho_match_mp_tac app_similarity_coinduct >>
  rw[FF_def] >>
  Q.REFINE_EXISTS_TAC `(x1,x2)`  >> fs[] >>
  reverse (rw[unfold_rel_def]) >> gvs[eval_def]
  >- (gvs[v_unfold] >> FULL_CASE_TAC >> gvs[])
  >- (gvs[v_unfold] >> FULL_CASE_TAC >> gvs[])
  >- (
    simp[GSYM eval_def] >>
    gvs[v_unfold] >> FULL_CASE_TAC >> gvs[] >>
    gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >> rw[] >>
    gvs[GSYM eval_def] >>
    imp_res_tac eval_wh_freevars_SUBSET >>
    gvs[freevars_wh_def, MEM_MAP, PULL_EXISTS, closed_def] >>
    gvs[pure_miscTheory.NIL_iff_NOT_MEM, DISJ_COMM] >>
    gvs[GSYM IMP_DISJ_THM]
    >- (first_x_assum irule >> gvs[EL_MEM])
    >- (last_x_assum irule >> gvs[EL_MEM])
    )
  >- (
    simp[GSYM eval_def] >>
    gvs[v_unfold] >> FULL_CASE_TAC >> gvs[] >> rw[] >>
    imp_res_tac eval_wh_freevars_SUBSET >> gvs[freevars_wh_def] >>
    drule freevars_subst_single >> simp[closed_def, EXTENSION] >>
    gvs[closed_def, pure_miscTheory.NIL_iff_NOT_MEM]
    )
QED

Theorem reflexive_app_similarity: (* exercise (5.3.3) *)
  reflexive (UNCURRY $≲) closed
Proof
  rw[set_relationTheory.reflexive_def,ELIM_UNCURRY,IN_DEF] >>
  ‘∀x y. x = y ∧ closed x ⇒ x ≲ y’ suffices_by metis_tac[] >>
  pop_assum kall_tac >>
  ho_match_mp_tac app_similarity_coinduct >>
  reverse (rw[FF_def,ELIM_UNCURRY,unfold_rel_def]) >> simp[]
  >- (
    rw[LIST_REL_EL_EQN] >>
    imp_res_tac eval_wh_freevars_SUBSET >>
    gvs[freevars_wh_def, closed_def, pure_miscTheory.NIL_iff_NOT_MEM, MEM_MAP] >>
    rw[] >> rename1 `MEM vars _` >>
    pop_assum (qspecl_then [`vars`,`freevars (EL n e1s)`] assume_tac) >> gvs[] >>
    pop_assum (qspec_then `EL n e1s` assume_tac) >> gvs[EL_MEM]
    ) >>
  imp_res_tac eval_wh_freevars_SUBSET >> gvs[freevars_wh_def] >>
  drule freevars_subst_single >> simp[closed_def, EXTENSION] >>
  gvs[closed_def, pure_miscTheory.NIL_iff_NOT_MEM]
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

Theorem companion_app_similarity_IMP:
  x ≲ y ⇒ companion R (x,y)
Proof
  rw[companion_def] >>
  irule_at Any compatible_app_similarity >>
  simp[IN_DEF,monotone_def]
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
      >- (match_mp_tac (set_relationTheory.subset_tc |>
                        SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          rw[UNION_DEF] >> metis_tac[IN_DEF])
      >- (
        gvs[LIST_REL_EL_EQN] >> rw[] >>
        match_mp_tac (set_relationTheory.subset_tc |>
                      SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
        rw[IN_DEF]
        )
      >- (metis_tac[IN_DEF,app_similarity_closed])
      >- (metis_tac[IN_DEF,app_similarity_closed])
      >- (gvs[IN_DEF,Once app_similarity_iff] >>
          gvs[unfold_rel_def] >>
          rw[] >>
          match_mp_tac (set_relationTheory.subset_tc |>
                        SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          rw[UNION_DEF] >> metis_tac[IN_DEF])
      >- (
          gvs[IN_DEF,Once app_similarity_iff] >>
          gvs[unfold_rel_def] >>
          gvs[LIST_REL_EL_EQN] >> rw[] >>
          match_mp_tac (set_relationTheory.subset_tc |>
                        SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          rw[IN_DEF]
          ) >>
      gvs[IN_DEF,Once app_similarity_iff] >> gvs[unfold_rel_def]
      )
  >- (rw[FF_def,unfold_rel_def] >> gvs[]
      >- (rw[] >>
          match_mp_tac (set_relationTheory.tc_rules |> cj 2 |>
                        SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          rpt(first_x_assum drule) >> rw[] >>
          goal_assum(drule_at (Pos last)) >>
          match_mp_tac (set_relationTheory.subset_tc |>
                        SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          rw[UNION_DEF] >> metis_tac[IN_DEF])
      >- (
          gvs[LIST_REL_EL_EQN] >> rw[] >>
          once_rewrite_tac [no_IN set_relationTheory.tc_cases_left] >>
          DISJ2_TAC >>
          rpt (first_x_assum drule >> strip_tac) >> rw[IN_DEF] >>
          goal_assum (drule_at Any) >> simp[]
          )
      >- metis_tac[IN_DEF,app_similarity_closed]
      >- (gvs[IN_DEF,Once app_similarity_iff] >> gvs[unfold_rel_def] >>
          rw[] >>
          match_mp_tac (set_relationTheory.tc_rules |> cj 2 |>
                        SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          irule_at (Pos hd) (set_relationTheory.subset_tc |>
                             SIMP_RULE std_ss [SUBSET_DEF,IN_DEF]) >>
          simp[IN_DEF] >> metis_tac[])
      >- (
          gvs[IN_DEF,app_similarity_iff] >>
          gvs[unfold_rel_def] >>
          gvs[LIST_REL_EL_EQN] >> rw[] >>
          once_rewrite_tac [no_IN set_relationTheory.tc_cases_left] >>
          DISJ2_TAC >>
          rpt (first_x_assum drule >> strip_tac) >> rw[IN_DEF] >>
          goal_assum (drule_at Any) >> simp[]
        ) >>
      gvs[IN_DEF,app_similarity_iff] >> gvs[unfold_rel_def]
      )
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
  \\ rpt GEN_TAC \\ strip_tac
  \\ rw[FF_def,unfold_rel_def,ELIM_UNCURRY,opp_def]
  \\ imp_res_tac app_similarity_closed
  \\ rpt(qpat_x_assum ‘_ ≲ _’
      (strip_assume_tac o PURE_ONCE_REWRITE_RULE[app_similarity_iff]))
  \\ gvs[unfold_rel_def, LIST_REL_EL_EQN] \\ rw[opp_def]
QED

Theorem app_bisimilarity_diverge:
  e1 ≃ e2 ∧ eval_wh e1 = wh_Diverge ⇒ eval_wh e2 = wh_Diverge
Proof
  rw[app_bisimilarity_similarity,app_similarity_iff] >>
  gvs[unfold_rel_def, eval_def, v_unfold_def] >>
  pop_assum mp_tac >> once_rewrite_tac[gen_v] >>
  Cases_on ‘eval_wh e2’ >> gvs[]
QED

Theorem app_bisimilarity_diverge_lemma:
  e1 ≃ e2 ∧ eval e1 = Diverge ⇒ eval e2 = Diverge
Proof
  rw[app_bisimilarity_similarity,app_similarity_iff] >>
  gvs[unfold_rel_def, eval_def, v_unfold_def] >>
  pop_assum mp_tac >> once_rewrite_tac[gen_v] >>
  gvs[follow_path_def] >>
  Cases_on ‘eval_wh e2’ >> gvs[]
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

Theorem app_bisimilarity_trans:
  ∀x y z. x ≃ y ∧ y ≃ z ⇒ x ≃ z
Proof
  assume_tac transitive_app_bisimilarity
  \\ fs [transitive_def]
QED

Theorem res_eq_IMP_app_bisimilarity: (* exercise (5.3.5) *)
  ∀e1 e2 x t.
    eval e1 = Closure x t ∧
    closed e1 ∧ closed e2 ∧
    eval e2 = Closure x t
  ⇒ e1 ≲ e2
Proof
  metis_tac[eval_eq_imp_app_similarity]
QED

Theorem reflexive_app_bisimilarity:
  closed x ⇒ x ≃ x
Proof
  fs [app_bisimilarity_similarity,reflexive_app_similarity']
QED


(* -- applicative (bi)similarity for open expressions -- *)

Definition open_similarity_def:
  open_similarity names e1 e2 ⇔
    freevars e1 ∪ freevars e2 ⊆ names ∧
    ∀f. freevars e1 ∪ freevars e2 ⊆ FDOM f ⇒ bind f e1 ≲ bind f e2
End

Definition open_bisimilarity_def:
  open_bisimilarity names e1 e2 ⇔
    freevars e1 ∪ freevars e2 ⊆ names ∧
    ∀f. freevars e1 ∪ freevars e2 ⊆ FDOM f ⇒ bind f e1 ≃ bind f e2
End

Theorem open_bisimilarity_eq:
  open_bisimilarity names e1 e2 ⇔
  open_similarity names e1 e2 ∧ open_similarity names e2 e1
Proof
  eq_tac
  \\ fs [open_similarity_def,open_bisimilarity_def,app_bisimilarity_similarity]
QED

Theorem fail[simp]:
  Fail ≃ Fail ∧ Fail ≲ Fail
Proof
  fs [app_similarity_iff,Once unfold_rel_def]
  \\ once_rewrite_tac [app_bisimilarity_iff]
  \\ fs [eval_wh_thm,closed_def]
QED

Theorem open_bisimilarity_suff:
  (∀f. FDOM f = freevars e1 ∪ freevars e2 ⇒ bind f e1 ≃ bind f e2) ⇒
  open_bisimilarity (freevars e1 ∪ freevars e2) e1 e2
Proof
  rw[open_bisimilarity_def] >> rw[bind_def] >>
  qabbrev_tac `g = DRESTRICT f (freevars e1 ∪ freevars e2)` >>
  `subst f e1 = subst g e1` by (
    unabbrev_all_tac >> once_rewrite_tac[subst_FDIFF] >> simp[INTER_UNION]) >>
  `subst f e2 = subst g e2` by (
    unabbrev_all_tac >> once_rewrite_tac[subst_FDIFF] >> simp[INTER_UNION]) >>
  last_x_assum (qspec_then `g` mp_tac) >> unabbrev_all_tac >>
  simp[FDOM_DRESTRICT] >> impl_tac
  >- (gvs[EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
  rw[bind_def] >> gvs[FLOOKUP_DRESTRICT] >> metis_tac[]
QED

(* (Tra) in the paper has an amusing typo that renders the corresponding
   proposition a tautology *)
Theorem open_similarity_transitive:
  open_similarity names e1 e2 ∧ open_similarity names e2 e3 ⇒ open_similarity names e1 e3
Proof
  rw[open_similarity_def]
  \\ rw [bind_def]
  \\ rpt (first_x_assum (qspec_then ‘FUNION f (FUN_FMAP (K Fail) (freevars e2))’ mp_tac))
  \\ fs [FUNION_DEF]
  \\ impl_tac THEN1 fs [SUBSET_DEF] \\ strip_tac
  \\ impl_tac THEN1 fs [SUBSET_DEF] \\ strip_tac
  \\ ntac 2 (pop_assum mp_tac)
  \\ fs [bind_def]
  \\ reverse IF_CASES_TAC
  THEN1
   (gvs [FLOOKUP_DEF,FUNION_DEF]
    \\ Cases_on ‘n ∈ FDOM f’ \\ fs [] \\ res_tac \\ fs []
    \\ fs [FUN_FMAP_DEF] \\ fs [closed_def])
  \\ fs [] \\ once_rewrite_tac [subst_FDIFF]
  \\ qmatch_goalsub_abbrev_tac
       ‘subst f1 _ ≲ _ ⇒ _ ≲ subst f3 _ ⇒ subst f1' _ ≲ subst f3' _’
  \\ qsuff_tac ‘f1 = f1' ∧ f3 = f3'’
  THEN1
   (assume_tac transitive_app_similarity
    \\ fs [relationTheory.transitive_def]
    \\ metis_tac [])
  \\ unabbrev_all_tac \\ rw [fmap_EXT]
  \\ fs [DRESTRICT_DEF,EXTENSION,SUBSET_DEF,FUN_FMAP_DEF,FUNION_DEF]
  \\ metis_tac []
QED


(* expression relation without freevars argument *)

Definition exp_eq_def:
  exp_eq x y ⇔
    ∀f. freevars x ∪ freevars y ⊆ FDOM f ⇒ bind f x ≃ bind f y
End

val _ = set_fixity "≅" (Infixl 480);
Overload "≅" = “exp_eq”;

Theorem exp_eq_open_bisimilarity:
  x ≅ y ⇔ ∃vars. open_bisimilarity vars x y ∧
                 FINITE vars ∧ freevars x ∪ freevars y ⊆ vars
Proof
  fs [exp_eq_def,open_bisimilarity_def]
  \\ eq_tac \\ rw []
  \\ qexists_tac ‘freevars x UNION freevars y’ \\ fs []
QED

Theorem open_bisimilarity_SUBSET:
  ∀x y vars vars'.
    open_bisimilarity vars x y ∧ vars SUBSET vars' ⇒
    open_bisimilarity vars' x y
Proof
  fs [open_bisimilarity_def] \\ rw []
  \\ imp_res_tac SUBSET_TRANS \\ fs []
QED

Theorem exp_eq_open_bisimilarity_freevars:
  x ≅ y ⇔ open_bisimilarity (freevars x ∪ freevars y) x y
Proof
  fs [exp_eq_def,open_bisimilarity_def]
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

Theorem app_similarity_closed:
  x ≲ y ⇒ closed x ∧ closed y
Proof
  fs [app_similarity_iff,Once unfold_rel_def]
QED

Theorem open_similarity_EMPTY:
  open_similarity ∅ x y = x ≲ y
Proof
  rw [open_similarity_def] \\ eq_tac \\ rw []
  THEN1 (first_x_assum (qspec_then ‘FEMPTY’ mp_tac) \\ fs [])
  \\ imp_res_tac app_similarity_closed
  \\ TRY (fs [closed_def] \\ NO_TAC)
  \\ rw [bind_def]
QED

Theorem eval_IMP_app_bisimilarity:
  eval x = eval y ∧ closed x ∧ closed y ⇒ x ≃ y
Proof
  rw[app_bisimilarity_similarity] >>
  metis_tac[eval_eq_imp_app_similarity]
QED

Definition eval_to_sim_def:
  eval_to_sim rel ⇔
    ∀e1 k e2.
      rel e1 e2 ∧ closed e1 ∧ closed e2 ⇒
      ∃ck.
        case eval_wh_to k e1 of
        | wh_Closure v x =>
           (∃y. eval_wh_to (k+ck) e2 = wh_Closure v y ∧ rel x y ∧
                ∀e. closed e ⇒ rel (subst v e x) (subst v e y))
        | wh_Constructor a xs =>
           (∃ys. eval_wh_to (k+ck) e2 = wh_Constructor a ys ∧ LIST_REL rel xs ys)
        | res => eval_wh_to (k+ck) e2 = res
End

Theorem eval_to_sim_thm:
  ∀x y. eval_to_sim rel ∧ rel x y ∧ closed x ∧ closed y ⇒ x ≃ y
Proof
  ho_match_mp_tac app_bisimilarity_coinduct
  \\ Cases_on ‘eval_to_sim rel’ \\ fs []
  \\ fs [FF_def,EXISTS_PROD]
  \\ fs [unfold_rel_def,opp_def,IN_DEF]
  \\ rw []
  THEN1
   (fs [eval_wh_eq,PULL_EXISTS]
    \\ fs [eval_to_sim_def]
    \\ first_x_assum drule_all
    \\ disch_then (qspec_then ‘k’ mp_tac) \\ fs []
    \\ rw [] \\ fs []
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ rw [] \\ fs []
    \\ irule IMP_closed_subst
    \\ fs [FRANGE_DEF]
    \\ imp_res_tac eval_wh_to_Closure_freevars_SUBSET
    \\ fs [SUBSET_DEF] \\ rw []
    \\ res_tac \\ fs []
    \\ gvs [closed_def])
  THEN1
   (fs [eval_wh_eq,PULL_EXISTS]
    \\ fs [eval_to_sim_def]
    \\ first_x_assum drule_all
    \\ disch_then (qspec_then ‘k’ mp_tac) \\ fs []
    \\ rw [] \\ fs []
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ fs [LIST_REL_EL_EQN]
    \\ strip_tac \\ strip_tac
    \\ imp_res_tac eval_wh_to_freevars_SUBSET
    \\ fs[closed_def, PULL_EXISTS, MEM_MAP] \\ gvs[]
    \\ ntac 2 (pop_assum mp_tac)
    \\ once_rewrite_tac[DISJ_COMM]
    \\ simp[DISJ_EQ_IMP, NIL_iff_NOT_MEM] \\ rw[]
      >- (first_x_assum irule >> simp[EL_MEM])
      >- (last_x_assum irule >> simp[EL_MEM])
    )
  THEN1
   (fs [eval_wh_eq,PULL_EXISTS,eval_to_sim_def]
    \\ first_x_assum drule_all
    \\ disch_then (qspec_then ‘k’ mp_tac) \\ fs [] \\ rw [] \\ fs []
    \\ goal_assum (first_assum o mp_then Any mp_tac))
  THEN1
   (fs [eval_wh_eq,PULL_EXISTS,eval_to_sim_def]
    \\ first_x_assum drule_all
    \\ disch_then (qspec_then ‘k’ mp_tac) \\ fs [] \\ rw [] \\ fs []
    \\ goal_assum (first_assum o mp_then Any mp_tac))
  THEN1
   (fs [eval_wh_eq,PULL_EXISTS]
    \\ fs [eval_to_sim_def]
    \\ first_x_assum drule_all
    \\ disch_then (qspec_then ‘k’ mp_tac) \\ fs []
    \\ rw [] \\ fs []
    \\ ‘eval_wh_to k y ≠ wh_Diverge’ by fs []
    \\ drule eval_wh_inc
    \\ disch_then (qspec_then ‘ck+k’ mp_tac) \\ fs []
    \\ strip_tac
    \\ fs [] \\ Cases_on ‘eval_wh_to k x’ \\ fs []
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ rw []
    \\ irule IMP_closed_subst
    \\ fs [FRANGE_DEF]
    \\ imp_res_tac eval_wh_to_Closure_freevars_SUBSET
    \\ fs [SUBSET_DEF] \\ rw []
    \\ res_tac \\ fs []
    \\ gvs [closed_def])
  THEN1 (
    fs[eval_wh_eq, PULL_EXISTS, eval_to_sim_def] >>
    first_x_assum drule_all >> disch_then (qspec_then `k` assume_tac) >> fs[] >>
    qspecl_then [`ck + k`,`y`,`k`] assume_tac eval_wh_inc >> gvs[] >>
    EVERY_CASE_TAC >> gvs[] >> goal_assum drule >>
    gvs[LIST_REL_EL_EQN] >> simp[opp_def, IN_DEF] >> strip_tac >> strip_tac >>
    imp_res_tac eval_wh_to_freevars_SUBSET >>
    fs[closed_def, PULL_EXISTS, MEM_MAP] >> gvs[] >>
    ntac 2 (pop_assum mp_tac) >> once_rewrite_tac[DISJ_COMM] >>
    simp[DISJ_EQ_IMP, NIL_iff_NOT_MEM] >> rw[]
    >- (last_x_assum irule >> simp[EL_MEM])
    >- (first_x_assum irule >> simp[EL_MEM])
    )
  >> (
    fs[eval_wh_eq, PULL_EXISTS, eval_to_sim_def] >>
    first_x_assum drule_all >> disch_then (qspec_then `k` assume_tac) >> fs[] >>
    qspecl_then [`ck + k`,`y`,`k`] assume_tac eval_wh_inc >> gvs[] >>
    EVERY_CASE_TAC >> gvs[] >> goal_assum drule
    )
QED

Theorem eval_IMP_exp_eq:
  (∀f. (∀n v. FLOOKUP f n = SOME v ⇒ closed v) ∧
       freevars x ⊆ FDOM f ∧ freevars y ⊆ FDOM f ⇒
       eval (subst f x) = eval (subst f y)) ⇒
  x ≅ y
Proof
  fs [exp_eq_def] \\ rw [bind_def]
  \\ match_mp_tac eval_IMP_app_bisimilarity
  \\ rw [] THEN1 metis_tac []
  \\ irule IMP_closed_subst
  \\ fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS]
QED

Theorem eval_wh_IMP_exp_eq:
  (∀f. (∀n v. FLOOKUP f n = SOME v ⇒ closed v) ∧
       freevars x ⊆ FDOM f ∧ freevars y ⊆ FDOM f ⇒
       eval_wh (subst f x) = eval_wh (subst f y)) ⇒
  x ≅ y
Proof
  rw [] \\ irule eval_IMP_exp_eq
  \\ rw [] \\ first_x_assum drule \\ fs []
  \\ fs [eval_def]
  \\ once_rewrite_tac [v_unfold] \\ fs []
QED

val _ = export_theory();
