(*
   This file defines three forms of relations between expressions.
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory;

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
  \\ once_rewrite_tac [app_bisimilarity_iff] \\ fs [eval_thm,closed_def]
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

val _ = export_theory();
