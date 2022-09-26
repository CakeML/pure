(*
   This file formalises Howe's method following the description of
   Pitts 2011 chapter "Howe's method for higher-order languages".
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_exp_relTheory
     pure_alpha_equivTheory pure_miscTheory;

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "pure_congruence";


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
     (* ~(x IN vars) ∧ *) {e; e'} SUBSET Exps (x INSERT vars) ⇒
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
        Exps (vars ∪ set (MAP FST ves)) ⇒
      fmap_rel
        (R (vars ∪ set (MAP FST ves))) (FEMPTY |++ ves) (FEMPTY |++ ves') ∧
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
  ∀b. Ref (open_similarity b)
Proof
  fs[Ref_def, Exps_def]
  \\ rw[open_similarity_def]
  \\ irule reflexive_app_similarity'
  \\ reverse (rw [bind_def])
  \\ match_mp_tac IMP_closed_subst
  \\ fs [FLOOKUP_DEF,FRANGE_DEF,PULL_EXISTS]
QED

Theorem Ref_open_bisimilarity:
  ∀b. Ref (open_bisimilarity b)
Proof
  assume_tac Ref_open_similarity
  \\ fs [Ref_def,open_bisimilarity_eq]
QED

Theorem Sym_open_bisimilarity:
  ∀b. Sym (open_bisimilarity b)
Proof
  rw[Sym_def, open_bisimilarity_def]
  \\ assume_tac symmetric_app_bisimilarity
  \\ fs[symmetric_def]
QED

Theorem Tra_open_similarity:
  ∀b. Tra (open_similarity b)
Proof
  rw[Tra_def]
  \\ irule open_similarity_transitive
  \\ goal_assum drule \\ fs[]
QED

Theorem Tra_open_bisimilarity:
  ∀b. Tra (open_bisimilarity b)
Proof
  fs [Tra_def] \\ metis_tac [open_similarity_transitive,open_bisimilarity_eq]
QED


(* -- Howe's construction -- *)

Inductive Howe:
[Howe1:]
  (∀vars x e2.
     R vars (Var x) e2 ⇒
     Howe R vars (Var x) e2)
  ∧
[Howe2:]
  (∀x e1 e1' e2 vars.
     Howe R (x INSERT vars) e1 e1' ∧
     R vars (Lam x e1') e2 ⇒
     Howe R vars (Lam x e1) e2)
  ∧
[Howe3:]
  (∀e1 e1' e3 vars.
     Howe R vars e1 e1' ∧
     Howe R vars e2 e2' ∧
     R vars (App e1' e2') e3 ⇒
     Howe R vars (App e1 e2) e3)
  ∧
[Howe4:]
  (∀es es' e op vars.
    LIST_REL (Howe R vars) es es' ∧
    R vars (Prim op es') e ⇒
    Howe R vars (Prim op es) e)
  ∧
[Howe5:]
  (∀ves ves' e e' e2.
    Howe R (vars ∪ set (MAP FST ves)) e e' ∧
    EVERY (λe. e ∈ Exps (vars ∪ set (MAP FST ves))) (MAP SND ves) ∧
    fmap_rel
      (Howe R (vars ∪ set (MAP FST ves))) (FEMPTY |++ ves) (FEMPTY |++ ves') ∧
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
    rw[Com5_def] >> imp_res_tac fmap_rel_fupdate_list_MAP_FST >> gvs[] >>
    irule Howe5 >> gvs[] >>
    conj_tac >- (simp[EVERY_MEM] >> gvs[SUBSET_DEF]) >>
    rpt (goal_assum (drule_at Any)) >> fs[] >>
    first_x_assum irule >> simp[Exps_simps] >>
    gvs[SUBSET_DEF, EVERY_MEM]
    )
QED

Definition term_rel_def:
  term_rel R ⇔
    (∀vars e1 e2. R vars e1 e2 ⇒ e1 ∈ Exps vars ∧ e2 ∈ Exps vars ∧
       ∀vars'. vars ⊆ vars' ⇒ R vars' e1 e2)
End

Theorem term_rel_open_similarity:
  ∀b. term_rel (open_similarity b)
Proof
  fs [term_rel_def] >> rw[open_similarity_def,Exps_def] >> gvs[SUBSET_DEF]
QED

Theorem term_rel_Howe:
  term_rel R ⇒ term_rel (Howe R)
Proof
  fs[term_rel_def] >>
  Induct_on `Howe` >> rw[]
  >- metis_tac[]
  >- metis_tac[]
  >- (irule Howe1 >> metis_tac[])
  >- (last_x_assum drule >> gvs[Exps_simps])
  >- metis_tac[]
  >- (
    irule Howe2 >> qexists_tac `e2` >>
    rw[] >- metis_tac[] >>
    last_x_assum drule >>
    strip_tac >>
    pop_assum irule >> fs[SUBSET_DEF]
    )
  >- (
    last_x_assum drule >>
    last_x_assum drule >>
    simp[Exps_simps]
    )
  >- metis_tac[]
  >- (
    irule Howe3 >> qexists_tac `e2'` >> qexists_tac `e2` >>
    rw[] >- metis_tac[] >>
    last_x_assum drule >>
    last_x_assum drule >>
    strip_tac >> strip_tac >>
    first_x_assum irule >> fs[SUBSET_DEF]
    )
  >- (
    simp[Exps_simps, EVERY_EL] >> rw[] >>
    fs[LIST_REL_EL_EQN] >>
    last_x_assum drule >> strip_tac >>
    pop_assum drule >> simp[]
    )
  >- metis_tac[]
  >- (
    irule Howe4 >> qexists_tac `es'` >>
    rw[] >- metis_tac[] >>
    gvs[LIST_REL_EL_EQN] >> rw[] >>
    last_x_assum drule >> strip_tac >>
    pop_assum drule >> strip_tac >>
    pop_assum irule >> fs[SUBSET_DEF]
    )
  >- (
    simp[Exps_simps] >>
    last_x_assum drule >> simp[]
    )
  >- metis_tac[]
  >- (
    irule Howe5 >>
    conj_tac
    >- (
      gvs[EVERY_MEM] >> rw[] >>
      irule Exps_SUBSET >>
      qexists_tac `vars ∪ set (MAP FST ves)` >> simp[] >>
      gvs[SUBSET_DEF]
      ) >>
    qexistsl_tac [`e2`,`ves'`] >>
    first_assum drule >> strip_tac >> pop_assum drule >> strip_tac >> simp[] >>
    conj_tac
    >- (
      gvs[fmap_rel_def] >> rw[] >>
      res_tac >>
      first_x_assum irule >> simp[] >>
      gvs[SUBSET_DEF]
      )
    >- (
      last_x_assum drule >> strip_tac >> pop_assum irule >>
      gvs[SUBSET_DEF]
      )
    )
QED

Theorem open_similarity_min_freevars:
  ∀e1 e2 vars b.
    open_similarity b vars e1 e2
  ⇒ open_similarity b (freevars e1 ∪ freevars e2) e1 e2
Proof
  rw[open_similarity_def]
QED

Theorem open_similarity_alt_def:
  ∀vars e1 e2 b.
    open_similarity b vars e1 e2 ⇔
    freevars e1 ∪ freevars e2 ⊆ vars ∧
    ∀f. freevars e1 ∪ freevars e2 = FDOM f ⇒ (bind f e1 ≲ bind f e2) b
Proof
  rw[] >> eq_tac >> rw[] >> gvs[open_similarity_def] >> rw[]
  >- (first_x_assum irule >> gvs[SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
  first_x_assum (qspec_then `DRESTRICT f (freevars e1 ∪ freevars e2)` mp_tac) >>
  simp[FDOM_DRESTRICT] >> impl_tac
  >- (gvs[EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
  gvs[bind_def, FLOOKUP_DRESTRICT] >>
  reverse (rw[]) >> gvs[] >- res_tac >- res_tac >>
  qmatch_asmsub_abbrev_tac `subst f' _` >>
  qsuff_tac `subst f e1 = subst f' e1 ∧ subst f e2 = subst f' e2` >> simp[] >>
  once_rewrite_tac[subst_FDIFF] >> unabbrev_all_tac >>
  gvs[INTER_UNION]
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
  Ref R ∧ term_rel R ⇒
  ∀vars e1 e2. R vars e1 e2 ⇒ Howe R vars e1 e2
Proof
  strip_tac
  \\ imp_res_tac Howe_Ref
  \\ simp [Once SWAP_FORALL_THM]
  \\ ho_match_mp_tac freevars_ind \\ rw []
  THEN1 (simp [Once Howe_cases])
  THEN1 (
    simp [Once Howe_cases]
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ fs [term_rel_def] \\ last_x_assum drule
    \\ pop_assum kall_tac
    \\ strip_tac
    \\ ‘∀e. MEM e es ⇒ e IN Exps vars’ by
      (fs [Exps_def,SUBSET_DEF,MEM_MAP,PULL_EXISTS]
       \\ rw [] \\ res_tac \\ fs [])
    \\ rw[LIST_REL_EL_EQN]
    \\ first_x_assum irule
    \\ gvs[Ref_def, MEM_EL]
    \\ metis_tac[])
  THEN1 (
    simp [Once Howe_cases]
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ fs [term_rel_def] \\ last_x_assum drule
    \\ strip_tac \\ fs [] \\ rw []
    \\ first_x_assum match_mp_tac
    \\ fs [Ref_def] \\ first_assum (match_mp_tac o MP_CANON) \\ fs []
    \\ fs [Exps_def,SUBSET_DEF]
    )
  THEN1
   (simp [Once Howe_cases]
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ fs [term_rel_def] \\ last_x_assum drule
    \\ strip_tac \\ fs [] \\ rw []
    \\ first_x_assum match_mp_tac
    \\ fs [Ref_def] \\ first_assum (match_mp_tac o MP_CANON) \\ fs []
    \\ fs [Exps_def,SUBSET_DEF] \\ metis_tac [])
  \\ simp [Once Howe_cases]
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs [term_rel_def] \\ last_x_assum drule
  \\ strip_tac \\ fs [] \\ rw []
  THEN1
   (first_x_assum match_mp_tac
    \\ fs [Ref_def] \\ first_assum (match_mp_tac o MP_CANON) \\ fs []
    \\ fs [Exps_def,SUBSET_DEF] \\ metis_tac [])
  THEN1 (fs[Exps_simps])
  \\ ‘∀fn e1. MEM (fn,e1) lcs ⇒ e1 IN Exps (vars UNION set (MAP FST lcs))’ by
   (fs [Exps_def,SUBSET_DEF,FORALL_PROD,EXISTS_PROD,MEM_MAP,PULL_EXISTS]
    \\ rw [] \\ Cases_on ‘∃p_2. MEM (x,p_2) lcs’
    THEN1 metis_tac [] \\ disj1_tac
    \\ last_x_assum match_mp_tac \\ fs [] \\ metis_tac [])
  \\ irule fmap_rel_FUPDATE_LIST_same \\ simp[]
  \\ rw[LIST_REL_EL_EQN]
  \\ last_x_assum irule \\ simp[EL_MAP] \\ conj_tac
    >- (
      qexists_tac `FST (EL n lcs)` \\ simp[EL_MEM]
      )
  \\ gvs[Ref_def] \\ last_x_assum irule \\ first_x_assum irule
  \\ qexists_tac `FST (EL n lcs)` \\ simp[EL_MEM]
QED

Definition Sub_def: (* Sub = substitutive *)
  Sub R ⇔
    ∀vars x e1 e1' e2 e2'.
      (* x ∉ vars ∧ *)
      {e1; e1'} ⊆ Exps (x INSERT vars) ∧ {e2; e2'} ⊆ Exps {} ⇒
      R (x INSERT vars) e1 e1' ∧ R {} e2 e2' ⇒
      R vars (subst1 x e2 e1) (subst1 x e2' e1')
  (* This definition has been tweaked to only insert closed expressions e2, e2' *)
End

Definition Cus_def: (* closed under value-substitution *)
  Cus R ⇔
    ∀vars x e1 e1' e2.
      (* x ∉ vars ∧ *)
      {e1; e1'} SUBSET Exps (x INSERT vars) ∧ e2 IN Exps {} ⇒
      R (x INSERT vars) e1 e1' ⇒
      R vars (subst1 x e2 e1) (subst1 x e2 e1')
  (* This definition has been tweaked to only insert closed expressions e2 *)
End

Theorem Sub_Ref_IMP_Cus:
  Sub R ∧ Ref R ⇒ Cus R
Proof
  rw[Sub_def, Ref_def, Cus_def]
  \\ fs [AND_IMP_INTRO]
  \\ first_x_assum match_mp_tac \\ fs []
  \\ first_x_assum match_mp_tac
  \\ fs [Exps_def,closed_def]
QED

Theorem Cus_open_similarity:
  ∀b. Cus (open_similarity b)
Proof
  fs [Cus_def] \\ rw []
  \\ fs [open_similarity_def]
  \\ fs [SUBSET_DEF,freevars_subst]
  \\ conj_tac THEN1 (metis_tac [])
  \\ rw [bind_def]
  \\ ‘(∀v. v ∈ FRANGE (FEMPTY |+ (x,e2)) ⇒ closed v)’ by fs [FRANGE_DEF]
  \\ drule subst_subst_FUNION \\ fs []
  \\ disch_then kall_tac
  \\ first_x_assum (qspec_then ‘FEMPTY |+ (x,e2) ⊌ f’ mp_tac)
  \\ impl_tac THEN1 (fs [FUNION_DEF] \\ metis_tac [])
  \\ simp [bind_def] \\ IF_CASES_TAC \\ fs []
  \\ gvs [FLOOKUP_DEF,FUNION_DEF] \\ metis_tac []
QED

Theorem Cus_open_bisimilarity:
  ∀b. Cus (open_bisimilarity b)
Proof
  assume_tac Cus_open_similarity
  \\ fs [Cus_def,open_bisimilarity_eq]
QED

Theorem IMP_Howe_Sub: (* 5.5.3 *)
  Ref R ∧ Tra R ∧ Cus R ∧ term_rel R ⇒ Sub (Howe R)
Proof
  fs [Sub_def,PULL_FORALL] >>
  qsuff_tac ‘
     ∀x_vars e1 e1'.
       Howe R x_vars e1 e1' ⇒
       ∀vars x e2 e2'. x_vars = x INSERT vars ∧
          Ref R ∧ Tra R ∧ Cus R ∧ term_rel R ∧
          (e1 ∈ Exps (x INSERT vars) ∧ e1' ∈ Exps (x INSERT vars)) ∧
          closed e2 ∧ closed e2' ∧ Howe R {} e2 e2' ⇒
          Howe R vars (subst1 x e2 e1) (subst1 x e2' e1')’
  >- fs [PULL_FORALL] >>
  ho_match_mp_tac Howe_strongind >> rw[] >> fs[]
  >- (
    gvs[subst1_def] >> reverse (rw[])
    >- (
      irule Howe1 >>
      gvs[Cus_def] >>
      first_x_assum (drule_at (Pos last)) >>
      simp[subst1_def]
      ) >>
    irule Howe_Tra >> simp[PULL_EXISTS] >>
    qexists_tac ‘e2'’ >>
    gvs[Exps_def, freevars_subst1, closed_def] >> rw[SUBSET_DEF]
    >- (gvs[IN_DEF, SUBSET_DEF] >> metis_tac[])
    >- (
      gvs[Cus_def] >>
      first_x_assum (drule_at (Pos last)) >>
      simp[subst1_def] >> disch_then irule >>
      simp[closed_def, Exps_def]
      )
    >- (
      imp_res_tac term_rel_Howe >>
      gvs[term_rel_def] >> res_tac >>
      first_x_assum irule >> fs[]
      )
    )
  >- (
    fs[subst1_def] >> rw[]
    >- (
      irule Howe2 >> fs[] >>
      goal_assum (drule_at Any) >>
      gvs[Cus_def] >>
      first_x_assum (drule_at (Pos last)) >>
      simp[subst1_def] >>
      disch_then irule >> simp[] >>
      drule term_rel_Howe >> simp[term_rel_def] >> disch_then imp_res_tac >>
      gvs[Exps_def, SUBSET_INSERT_DELETE]
      ) >>
    irule Howe2 >>
    qexists_tac `subst1 x' e2' e1'` >>
    conj_tac
    >- (
      gvs[Cus_def] >>
      first_x_assum (drule_at (Pos last)) >> simp[subst1_def] >>
      disch_then irule >> gvs[] >>
      gvs[term_rel_def] >> res_tac
      ) >>
    first_x_assum irule >> gvs[INSERT_COMM] >>
    drule term_rel_Howe >> simp[term_rel_def] >> disch_then imp_res_tac >>
    gvs[SUBSET_INSERT_DELETE]
    )
  >- (
    gvs[subst1_def] >>
    rename1 `Howe _ _ (App (subst1 x e ea) (subst1 x e eb)) (subst1 x e' ec)` >>
    rename1 `R (_ INSERT _) (App ed ef) _` >>
    irule Howe3 >>
    qexists_tac `subst1 x e' ed` >> qexists_tac `subst1 x e' ef` >>
    gvs[term_rel_def] >> first_x_assum drule >>
    rw[] >- (gvs[Cus_def] >> simp[GSYM subst1_def]) >>
    first_x_assum irule >> gvs[Exps_def]
    )
  >- (
    gvs[subst1_def] >>
    irule Howe4 >> qexists_tac `MAP (λe. subst1 x e2' e) es'` >>
    gvs[term_rel_def] >> first_x_assum drule >> rw[]
    >- (gvs[Cus_def] >> simp[GSYM subst1_def]) >>
    gvs[LIST_REL_EL_EQN] >> rw[] >>
    simp[EL_MAP] >>
    last_x_assum drule >> strip_tac >>
    pop_assum irule >> gvs[Exps_def] >>
    gvs[SUBSET_DEF, PULL_EXISTS, MEM_MAP] >> rw[]
    >- (last_x_assum irule >> qexists_tac `EL n es` >> gvs[EL_MEM])
    >- (first_x_assum irule >> qexists_tac `EL n es'` >> gvs[EL_MEM])
    )
  >- (
    gvs[subst1_def] >> rw[]
    >- (
      gvs[INSERT_UNION] >>
      irule Howe5 >> simp[] >>
      goal_assum (drule_at Any) >> qexists_tac `ves'` >>
      imp_res_tac fmap_rel_fupdate_list_MAP_FST >>
      gvs[fmap_rel_def, Cus_def] >>
      first_x_assum (drule_at (Pos last)) >>
      simp[subst1_def] >> disch_then irule >>
      drule term_rel_Howe >> gvs[term_rel_def] >> disch_then imp_res_tac >>
      gvs[Exps_simps, INSERT_UNION] >>
      first_x_assum drule >> simp[Exps_simps, INSERT_UNION]
      ) >>
    irule Howe5 >>
    conj_tac
    >- (
      gvs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> fs[] >>
      gvs[EVERY_EL, EL_MAP] >> rw[] >> last_x_assum drule >> simp[Exps_def] >>
      imp_res_tac freevars_subst1 >> simp[] >>
      simp[INSERT_UNION, GSYM SUBSET_INSERT_DELETE]
      ) >>
    qexists_tac `subst1 x e2' e1'` >>
    qexists_tac `MAP (λ(g,z). (g, subst1 x e2' z)) ves'` >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >> fs[] >>
    imp_res_tac fmap_rel_fupdate_list_MAP_FST >> gvs[] >>
    imp_res_tac term_rel_def >> rw[]
    >- (
      gvs[Cus_def] >>
      first_x_assum (drule_at (Pos last)) >>
      simp[subst1_def]
      )
    >- (
      gvs[fmap_rel_OPTREL_FLOOKUP, flookup_fupdate_list, GSYM MAP_REVERSE] >>
      simp[ALOOKUP_MAP_2] >> rw[] >>
      first_x_assum (qspec_then `k` assume_tac) >>
      Cases_on `ALOOKUP (REVERSE ves) k` >>
      Cases_on `ALOOKUP (REVERSE ves') k` >> gvs[OPTREL_THM] >>
      first_x_assum irule >> simp[INSERT_UNION] >>
      gvs[Exps_simps, EVERY_MEM, INSERT_UNION] >>
      gvs[MEM_MAP, PULL_EXISTS] >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_REVERSE, FORALL_PROD] >>
      metis_tac[]
      )
    >- (
      last_x_assum irule >> gvs[INSERT_UNION_EQ] >>
      drule term_rel_Howe >> simp[term_rel_def] >> disch_then imp_res_tac >>
      simp[]
      )
    )
QED

Theorem Ref_Howe:
  Ref R ⇒ Ref (Howe R)
Proof
  strip_tac
  \\ gvs[Ref_def,PULL_FORALL]
  \\ CONV_TAC SWAP_FORALL_CONV
  \\ ho_match_mp_tac freevars_ind \\ rw []
  THEN1 (rename [‘Var’] \\ rw[Once Howe_cases])
  THEN1 (rename [‘Prim’] \\ rw[Once Howe_cases]
         \\ qexists_tac ‘es’ \\ fs []
         \\ Induct_on ‘es’ \\ fs [Exps_simps])
  THEN1 (rename [‘App’] \\ rw[Once Howe_cases] \\ metis_tac[Exps_simps])
  THEN1 (rename [‘Lam’] \\ rw[Once Howe_cases] \\ metis_tac[Exps_simps])
  \\ rename [‘Letrec’] \\ rw[Once Howe_cases]
  \\ qexists_tac ‘lcs’
  \\ qexists_tac ‘e’ \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  THEN1 (metis_tac[Exps_simps])
  THEN1 (metis_tac[Exps_simps])
  \\ irule fmap_rel_FUPDATE_LIST_same \\ simp[] \\ rw[LIST_REL_EL_EQN]
  \\ first_x_assum irule \\ reverse conj_tac
    >- (
      qexists_tac `FST (EL n lcs)` >> simp[EL_MAP, EL_MEM]
      )
  \\ gvs[Exps_simps, EVERY_EL]
QED

Theorem Howe_shrink_vars_lemma:
  ∀vs.
    FINITE vs ⇒
  ∀ R vars x e1 e2.
    Ref R ∧ Tra R ∧ Cus R ∧ term_rel R ∧
    Howe R (vs ∪ vars) e1 e2 ∧
    (∀x. x ∈ vs ⇒ x ∉ freevars e1 ∧ x ∉ freevars e2)
  ⇒ Howe R vars e1 e2
Proof
  pred_setLib.SET_INDUCT_TAC >> rw[] >>
  first_x_assum irule >> simp[] >>
  drule IMP_Howe_Sub >> rpt (disch_then drule) >>
  simp[Sub_def] >>
  disch_then (qspecl_then [`s ∪ vars`,`e`,`e1`,`e2`,`Fail`,`Fail`] mp_tac) >>
  simp[] >> dep_rewrite.DEP_REWRITE_TAC[subst1_ignore] >> simp[] >>
  disch_then irule >>
  drule term_rel_Howe >> simp[term_rel_def] >> disch_then imp_res_tac >>
  gvs[INSERT_UNION_EQ] >>
  drule Ref_Howe >> rw[Ref_def] >>
  last_x_assum irule >> gvs[GSYM INSERT_UNION_EQ]
QED

Theorem Howe_min_freevars:
  ∀R vars x e1 e2.
    Ref R ∧ Tra R ∧ Cus R ∧ term_rel R ∧
    Howe R vars e1 e2 ∧ FINITE vars
  ⇒ Howe R (freevars e1 ∪ freevars e2) e1 e2
Proof
  rw[] >>
  `∃ vars'.
    vars = vars' ∪ (freevars e1 ∪ freevars e2) ∧
    FINITE vars' ∧
    DISJOINT vars' (freevars e1 ∪ freevars e2)` by (
    drule term_rel_Howe >> simp[term_rel_def] >> disch_then imp_res_tac >>
    gvs[Exps_def] >>
    qexists_tac `vars DIFF freevars e1 DIFF freevars e2` >>
    gvs[EXTENSION, SUBSET_DEF, DISJOINT_DEF] >> metis_tac[]) >>
  gvs[] >>
  drule Howe_shrink_vars_lemma >> rpt (disch_then drule) >> disch_then irule >>
  gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem Sub_Howe_open_similarity:
  ∀b. Sub (Howe (open_similarity b))
Proof
  metis_tac [Ref_Howe,Ref_open_similarity,IMP_Howe_Sub,
       Cus_open_similarity,Tra_open_similarity,Ref_open_similarity,
       term_rel_Howe, term_rel_open_similarity]
QED

Theorem Cus_Howe_open_similarity:
  ∀b. Cus (Howe (open_similarity b))
Proof
  gen_tac
  \\ match_mp_tac Sub_Ref_IMP_Cus
  \\ rw [Sub_Howe_open_similarity]
  \\ metis_tac[Ref_Howe, Ref_open_similarity]
QED

Theorem Howe_open_similarity_IMP_freevars:
  Howe (open_similarity b) s x y ⇒ freevars x ⊆ s ∧ freevars y ⊆ s
Proof
  rw [] \\ ‘term_rel (open_similarity b)’ by fs [term_rel_open_similarity]
  \\ imp_res_tac term_rel_Howe
  \\ fs [term_rel_def]
  \\ res_tac \\ fs [] \\ rw []
  \\ fs [Exps_def]
QED

Theorem Howe_open_similarity_IMP_closed:
  Howe (open_similarity b) ∅ x y ⇒ closed x ∧ closed y
Proof
  rw [] \\ imp_res_tac Howe_open_similarity_IMP_freevars
  \\ fs [closed_def]
QED

Theorem LIST_REL_Howe_open_similarity_IMP_closed:
  ∀xs ys b.
    LIST_REL (Howe (open_similarity b) ∅) xs ys ⇒
    EVERY closed xs ∧ EVERY closed ys
Proof
  Induct \\ fs [PULL_EXISTS] \\ rw [] \\ res_tac
  \\ imp_res_tac Howe_open_similarity_IMP_closed
QED

Triviality perm_exp_IN_Exps:
  freevars ce2 ⊆ {y} ⇒ perm_exp x y ce2 ∈ Exps {x}
Proof
  fs [Exps_def]
  \\ rewrite_tac [freevars_eqvt]
  \\ fs [SUBSET_DEF,MEM_MAP,PULL_EXISTS,perm1_def,closed_def,
         FILTER_EQ_NIL,EVERY_MEM]
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem exp_alpha_subst_lemma[local]:
  closed (Lam y e5) ∧ closed e4 ⇒
  exp_alpha (subst1 x e4 (perm_exp x y e5)) (subst1 y e4 e5)
Proof
  rw [] \\ match_mp_tac exp_alpha_Trans
  \\ qexists_tac ‘perm_exp x y (subst1 x e4 (perm_exp x y e5))’
  \\ rw [] THEN1 (
    match_mp_tac exp_alpha_perm_irrel
    \\ fs [freevars_subst,freevars_eqvt,MEM_MAP,closed_def,FILTER_EQ_NIL,
           EVERY_MEM,perm1_def, PULL_FORALL, SUBSET_DEF]
    \\ CCONTR_TAC \\ gvs[])
  \\ fs [subst1_eqvt,perm1_def]
  \\ match_mp_tac exp_alpha_subst1_closed'
  \\ fs [closed_perm]
  \\ match_mp_tac exp_alpha_sym
  \\ match_mp_tac exp_alpha_perm_irrel
  \\ fs [closed_def]
QED

Theorem Sub_lift:
  ∀R. Sub R ⇒
    ∀f f' e1 e1' e2 e2' vars.
      {e1; e1'} ⊆ Exps (FDOM f ∪ vars) ∧
      R (FDOM f ∪ vars) e1 e1' ∧
      FDOM f = FDOM f' ∧
      (∀k. k ∈ FDOM f ⇒
        f ' k ∈ Exps ∅ ∧ f' ' k ∈ Exps ∅ ∧
        R {} (f ' k) (f' ' k))
    ⇒ R vars (subst f e1) (subst f' e1')
Proof
  strip_tac >> strip_tac >>
  Induct >> rw[]
  >- (Cases_on `f'` >> gvs[]) >>
  `∃g y'. f' = g |+ (x,y') ∧ x ∉ FDOM g ∧ R {} y y'` by (
    qexists_tac `f' \\ x` >> qexists_tac `f' ' x` >> gvs[] >>
    first_x_assum (qspec_then `x` assume_tac) >> gvs[] >>
    irule (GSYM FUPDATE_ELIM)>> gvs[IN_DEF, EXTENSION] >> metis_tac[]) >>
  gvs[] >>
  once_rewrite_tac[FUPDATE_EQ_FUNION] >>
  `∀v. v ∈ FRANGE (FEMPTY |+ (x,y)) ⇒ closed v` by (
    gvs[] >> first_x_assum (qspec_then `x` assume_tac) >> gvs[]) >>
  drule (GSYM subst_subst_FUNION) >> simp[] >> strip_tac >>
  pop_assum kall_tac >>
  drule_at Any subst_subst >>
  disch_then (qspecl_then [`e1`,`f`] mp_tac) >> impl_tac
  >- (
    simp[DISJOINT_DEF, INTER_DEF, EXTENSION] >> rw[] >>
    fs[IN_FRANGE] >>
    first_x_assum (qspec_then `k` assume_tac) >> gvs[FAPPLY_FUPDATE_THM] >>
    FULL_CASE_TAC >> gvs[]
    ) >>
  disch_then (rw o single o GSYM) >> pop_assum kall_tac >>
  `∀v. v ∈ FRANGE (FEMPTY |+ (x,y')) ⇒ closed v` by (
    gvs[] >> first_x_assum (qspec_then `x` assume_tac) >> gvs[]) >>
  drule (GSYM subst_subst_FUNION) >> simp[] >> strip_tac >>
  pop_assum kall_tac >>
  drule_at Any subst_subst >>
  disch_then (qspecl_then [`e1'`,`g`] mp_tac) >> impl_tac
  >- (
    simp[DISJOINT_DEF, INTER_DEF, EXTENSION] >> rw[] >>
    fs[IN_FRANGE] >>
    first_x_assum (qspec_then `k` assume_tac) >> gvs[FAPPLY_FUPDATE_THM] >>
    `k ∈ FDOM f` by (gvs[EXTENSION, INSERT_DEF] >> metis_tac[]) >> gvs[] >>
    FULL_CASE_TAC >> gvs[]
    ) >>
  disch_then (rw o single o GSYM) >> pop_assum kall_tac >>
  gvs[Sub_def] >>
  last_x_assum irule >> gvs[] >> rw[]
  >- (first_x_assum (qspec_then `x` mp_tac) >> simp[])
  >- (first_x_assum (qspec_then `x` mp_tac) >> simp[])
  >- (
    gvs[Exps_def] >>
    `∀v. v ∈ FRANGE f ⇒ closed v` by (
      rw[IN_FRANGE] >>
      first_x_assum (qspec_then `k` assume_tac) >> gvs[FAPPLY_FUPDATE_THM] >>
      FULL_CASE_TAC >> gvs[]) >>
    drule freevars_subst >> rw[] >>
    gvs[DIFF_DEF, SUBSET_DEF, INSERT_DEF, EXTENSION] >> rw[] >>
    last_x_assum drule >> strip_tac >> gvs[] >>
    qpat_x_assum `∀x. _ ⇔ _` (qspec_then `x'` assume_tac) >> gvs[]
    )
  >- (
    gvs[Exps_def] >>
    `∀v. v ∈ FRANGE g ⇒ closed v` by (
      rw[IN_FRANGE] >>
      first_x_assum (qspec_then `k` assume_tac) >> gvs[FAPPLY_FUPDATE_THM] >>
      `k ∈ FDOM f` by (gvs[EXTENSION, INSERT_DEF] >> metis_tac[]) >> gvs[] >>
      FULL_CASE_TAC >> gvs[]) >>
    drule freevars_subst >> rw[] >>
    gvs[DIFF_DEF, SUBSET_DEF, INSERT_DEF, EXTENSION] >> rw[] >>
    last_x_assum drule >> strip_tac >> gvs[]
    ) >>
  first_x_assum irule >> conj_tac
  >- (
    gen_tac >> strip_tac >>
    first_x_assum (qspec_then `k` assume_tac) >> gvs[FAPPLY_FUPDATE_THM] >>
    FULL_CASE_TAC >> gvs[] >>
    first_x_assum drule >> disch_then (qspec_then `{x}` mp_tac) >>
    once_rewrite_tac[UNION_COMM] >>
    simp[GSYM INSERT_SING_UNION]
    ) >>
  conj_asm1_tac
  >- (gvs[INSERT_DEF, IN_DEF, EXTENSION] >> rw[] >> gvs[] >> metis_tac[])
  >- (gvs[] >> metis_tac[UNION_COMM, UNION_ASSOC, INSERT_SING_UNION])
QED

Triviality closed_Letrec_funs:
  ∀ fs e f.
    closed (Letrec fs e) ∧
    MEM f fs
  ⇒ closed (Letrec fs (SND f))
Proof
  rw[EVERY_MEM] >>
  gvs[MEM_MAP, PULL_EXISTS]
QED

Theorem open_similarity_larger:
  ∀vars e1 e2 vars1 b.
    open_similarity b vars e1 e2 ∧ vars SUBSET vars1 ⇒ open_similarity b vars1 e1 e2
Proof
  fs [open_similarity_def]
  \\ rw [] \\ imp_res_tac SUBSET_TRANS \\ fs []
QED

Theorem Howe_larger:
  ∀vars e2 e1 vars1 b.
     Howe (open_similarity b) vars e1 e2 ∧ vars ⊆ vars1 ⇒
     Howe (open_similarity b) vars1 e1 e2
Proof
  rw[] >>
  ‘term_rel (open_similarity b)’ by fs [term_rel_open_similarity] >>
  imp_res_tac term_rel_Howe >>
  gvs[term_rel_def] >>
  metis_tac[]
QED

Theorem LIST_REL_Howe_larger:
  ∀vs ws es ys b.
    LIST_REL (Howe (open_similarity b) vs) es ys ∧ vs SUBSET ws ⇒
    LIST_REL (Howe (open_similarity b) ws) es ys
Proof
  rw [] \\ last_x_assum mp_tac
  \\ match_mp_tac LIST_REL_mono \\ rw []
  \\ match_mp_tac Howe_larger
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs [SUBSET_DEF]
QED

Theorem open_similarity_finite:
  ∀vars e1 e2 b.
    open_similarity b vars e1 e2 ⇒ ∃vs. open_similarity b vs e1 e2 ∧ FINITE vs
Proof
  fs [open_similarity_def] \\ rw []
  \\ qexists_tac ‘freevars e1 UNION freevars e2’ \\ fs []
QED

Theorem Howe_finite:
  Howe R vars e1 e2 ⇒ R = open_similarity b ⇒
  ∃ws. Howe R ws e1 e2 ∧ FINITE ws
Proof
  Induct_on ‘Howe’ \\ rw []
  THEN1
   (simp [Once Howe_cases]
    \\ imp_res_tac open_similarity_finite
    \\ qexists_tac ‘vs’ \\ fs [])
  THEN1
   (simp [Once Howe_cases,PULL_EXISTS]
    \\ imp_res_tac open_similarity_finite
    \\ qexists_tac ‘x INSERT (ws UNION vs)’ \\ fs []
    \\ qexists_tac ‘e2’ \\ fs [] \\ rw []
    THEN1
     (match_mp_tac Howe_larger
      \\ goal_assum (first_assum o mp_then Any mp_tac)
      \\ fs [SUBSET_DEF])
    \\ match_mp_tac open_similarity_larger
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ fs [SUBSET_DEF])
  THEN1
   (simp [Once Howe_cases,PULL_EXISTS]
    \\ imp_res_tac open_similarity_finite
    \\ qexists_tac ‘vs UNION ws UNION ws'’ \\ fs []
    \\ qexists_tac ‘e2’ \\ fs [] \\ rw []
    \\ qexists_tac ‘e2'’ \\ fs [] \\ rw []
    \\ TRY (match_mp_tac Howe_larger)
    \\ TRY (match_mp_tac open_similarity_larger)
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ fs [SUBSET_DEF])
  THEN1
   (simp [Once Howe_cases,PULL_EXISTS]
    \\ imp_res_tac open_similarity_finite
    \\ ‘∃ws1. LIST_REL (Howe (open_similarity b) ws1) es es' ∧ FINITE ws1 ∧ vs SUBSET ws1’ by
     (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
      \\ qid_spec_tac ‘es'’ \\ qid_spec_tac ‘es’
      \\ Induct \\ fs []
      THEN1 (goal_assum (first_assum o mp_then (Pos hd) mp_tac) \\ fs [])
      \\ fs [PULL_EXISTS] \\ rw []
      \\ first_x_assum drule \\ rw []
      \\ qexists_tac ‘ws UNION ws1’ \\ fs [] \\ rw []
      \\ TRY (match_mp_tac Howe_larger)
      \\ TRY (match_mp_tac LIST_REL_Howe_larger)
      \\ TRY (goal_assum (first_assum o mp_then Any mp_tac))
      \\ fs [SUBSET_DEF])
    \\ goal_assum (first_assum o mp_then (Pos hd) mp_tac) \\ fs []
    \\ TRY (match_mp_tac open_similarity_larger)
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ fs [SUBSET_DEF])
  \\ imp_res_tac open_similarity_finite
  \\ imp_res_tac fmap_rel_fupdate_list_MAP_FST \\ gvs[]
  \\ `fmap_rel (λe1 e2. ∃ws. Howe (open_similarity b) ws e1 e2 ∧ FINITE ws)
                  (FEMPTY |++ ves) (FEMPTY |++ ves')` by gvs[fmap_rel_def]
  \\ `∃ws1. FINITE ws1 ∧
        fmap_rel (Howe (open_similarity b) (ws1 ∪ set (MAP FST ves)))
                        (FEMPTY |++ ves) (FEMPTY |++ ves')` by (
        rename1 `fmap_rel _ f1 f2` >>
        pop_assum mp_tac >> qid_spec_tac `f2` >> qid_spec_tac `f1` >>
        ho_match_mp_tac fmap_rel_ind >> rw[]
        >- (qexists_tac `{}` >> simp[]) >>
        simp[GSYM fmap_rel_FUPDATE_EQN] >>
        rename1 `Howe _ ws2 _ _` >> qexists_tac `ws1 ∪ ws2` >> simp[] >>
        irule_at Any Howe_larger >> goal_assum drule >> simp[SUBSET_DEF] >>
        irule fmap_rel_mono >> goal_assum (drule_at Any) >> rw[] >>
        irule Howe_larger >> goal_assum (drule_at Any) >> simp[SUBSET_DEF])
  \\ `∃ws2. FINITE ws2 ∧
        EVERY (λe. e ∈ Exps (ws2 ∪ set (MAP FST ves'))) (MAP SND ves)` by (
        qpat_x_assum `EVERY _ _` mp_tac >> qid_spec_tac `ves` >>
        Induct >> rw[] >- (qexists_tac `{}` >> simp[]) >> gvs[] >>
        qexists_tac `freevars (SND h) ∪ ws2` >> gvs[Exps_def, SUBSET_DEF] >>
        gvs[EVERY_MEM] >> rw[] >> metis_tac[])
  \\ simp [Once Howe_cases,PULL_EXISTS]
  \\ qexistsl_tac [`ws ∪ vs ∪ ws1 ∪ ws2 ∪ set (MAP FST ves)`,`ves'`,`e2`] >>
     irule_at Any Howe_larger >> goal_assum drule >> simp[GSYM UNION_ASSOC] >>
     irule_at Any open_similarity_larger >>
     goal_assum drule >> simp[SUBSET_DEF] >>
     irule_at Any fmap_rel_mono >> goal_assum (drule_at Any) >>
     conj_tac
     >- (
      rw[] >> irule Howe_larger >> goal_assum (drule_at Any) >> simp[SUBSET_DEF]
      ) >>
    gvs[EVERY_MEM] >> rw[] >> first_x_assum drule >> strip_tac >>
    irule Exps_SUBSET >> goal_assum drule >> simp[SUBSET_DEF]
QED

Theorem Howe_finite = GEN_ALL Howe_finite |> SIMP_RULE std_ss [] |> MP_CANON;

Theorem Howe_open_similarity_min_freevars:
  ∀R vars x e1 e2 b.
    Howe (open_similarity b) vars e1 e2
  ⇒ Howe (open_similarity b) (freevars e1 ∪ freevars e2) e1 e2
Proof
  rw[] >>
  drule Howe_finite >> strip_tac >>
  irule Howe_min_freevars >>
  simp[Cus_open_similarity, Ref_open_similarity,
      Tra_open_similarity, term_rel_open_similarity] >>
  goal_assum drule >> simp[]
QED

Theorem Sub_subst_funs:
  ∀R f1 f2 e1 e2.
    Sub R ∧
    term_rel R ∧
    Com5 R ∧
    fmap_rel (R (set (MAP FST f1))) (FEMPTY |++ f1) (FEMPTY |++ f2) ∧
    R (set (MAP FST f2)) e1 e2 ∧
    closed (Letrec f1 e1) ∧ closed (Letrec f2 e2) ∧
    (∀vars ea eb. R vars ea eb ⇒ R (freevars ea ∪ freevars eb) ea eb)
  ⇒ R {} (subst_funs f1 e1) (subst_funs f2 e2)
Proof
  rw[subst_funs_def] >>
  simp[bind_def] >>
  reverse (IF_CASES_TAC)
  >- (
    CCONTR_TAC >>
    qpat_x_assum `¬ ∀n v. _` mp_tac >> simp[] >> rw[] >>
    gvs[flookup_fupdate_list] >>
    pop_assum mp_tac >> CASE_TAC >> gvs[] >> strip_tac >> gvs[] >>
    drule ALOOKUP_MEM >> simp[MEM_REVERSE, MEM_MAP] >> strip_tac >>
    PairCases_on `y` >> gvs[] >>
    gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
    last_x_assum irule >> goal_assum drule
    ) >>
  reverse (IF_CASES_TAC)
  >- (
    CCONTR_TAC >>
    qpat_x_assum `¬ ∀n v. _` mp_tac >> simp[] >> rw[] >>
    gvs[flookup_fupdate_list] >>
    pop_assum mp_tac >> CASE_TAC >> gvs[] >> strip_tac >> gvs[] >>
    drule ALOOKUP_MEM >> simp[MEM_REVERSE, MEM_MAP] >> strip_tac >>
    PairCases_on `y` >> gvs[] >>
    gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
    first_x_assum irule >> goal_assum drule
    ) >>
  imp_res_tac fmap_rel_fupdate_list_MAP_FST >> gvs[] >>
  irule Sub_lift >>
  gvs[FDOM_FUPDATE_LIST, FLOOKUP_DEF, MAP_MAP_o, combinTheory.o_DEF,
      LAMBDA_PROD, FST_THM, MEM_MAP, EXISTS_PROD, PULL_EXISTS] >>
  reverse (conj_tac)
  >- (gvs[term_rel_def] >> res_tac >> gvs[]) >>
  rpt (gen_tac) >> strip_tac >>
  `∃p_1. MEM (k,p_1) f1` by (
    gvs[EXTENSION, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  first_x_assum drule >> first_x_assum drule >>
  DEP_REWRITE_TAC[fupdate_list_map] >>
  simp[FDOM_FUPDATE_LIST, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
  goal_assum drule >> goal_assum drule >> rw[] >>
  `∃v1. ALOOKUP (REVERSE f1) k = SOME v1` by (
    rw[ALOOKUP_LEAST_EL, MEM_MAP, EXISTS_PROD] >> goal_assum drule) >>
  `∃v2. ALOOKUP (REVERSE f2) k = SOME v2` by (
    rw[ALOOKUP_LEAST_EL, MEM_MAP, EXISTS_PROD] >> goal_assum drule) >>
  imp_res_tac FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME >> gvs[FLOOKUP_DEF] >>
  ntac 2 (pop_assum kall_tac) >>
  gvs[Com5_def] >> last_x_assum irule >>
  gvs[FST_THM, Exps_def] >>
  gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD, FST_THM, SUBSET_DEF,
      MEM_MAP, PULL_EXISTS] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  gvs[fmap_rel_OPTREL_FLOOKUP, flookup_fupdate_list] >>
  last_x_assum (qspec_then `k` assume_tac) >> gvs[]
QED

Theorem Howe_open_similarity_IMP:
  Howe (open_similarity b) ∅ e1 e2 ∧ closed e1 ∧ closed e2 ⇒
  (∀x ce1.
       eval_wh e1 = wh_Closure x ce1 ⇒
       ∃y ce2.
           eval_wh e2 = wh_Closure y ce2 ∧
           Howe (open_similarity b) {x} ce1 (perm_exp x y ce2)) ∧
  (∀x e1s.
       eval_wh e1 = wh_Constructor x e1s ⇒
       ∃e2s.
          eval_wh e2 = wh_Constructor x e2s ∧
          LIST_REL (Howe (open_similarity b) ∅) e1s e2s) ∧
  (∀a. eval_wh e1 = wh_Atom a ⇒ eval_wh e2 = wh_Atom a) ∧
  ((b ∧ eval_wh e1 = wh_Error) ⇒ eval_wh e2 = wh_Error)
Proof
  Cases_on ‘eval_wh e1 = wh_Diverge’ >> fs [] >>
  qspec_then `e1` assume_tac (GEN_ALL eval_wh_eq_Diverge) >> rgs[] >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`e2`,`e1`,`k`] >>
  ho_match_mp_tac eval_wh_to_ind >> rpt (conj_tac)
  >- fs[closed_def]
  >- (
    rename1 `Lam` >>
    simp[Once Howe_cases] >>
    fs[eval_wh_to_def, eval_wh_thm, closed_def] >> rw[] >>
    fs[open_similarity_EMPTY, app_similarity_iff] >>
    fs[unfold_rel_def, eval_wh_thm] >>
    irule Howe_Tra >> simp[Tra_open_similarity, term_rel_open_similarity] >>
    simp[PULL_EXISTS] >> goal_assum (drule_at Any) >> simp[] >> rw[]
    >- (gvs[Exps_def, SUBSET_DEF] >> rw[] >> gvs[FILTER_EQ_NIL, EVERY_MEM])
    >- (
      irule perm_exp_IN_Exps >>
      drule_all eval_wh_Closure_closed >> simp[]
      )
    >- (
      gvs[Exps_def, closed_def, SUBSET_DEF] >> rw[] >>
      gvs[FILTER_EQ_NIL, EVERY_MEM]
      ) >>
    rw[open_similarity_def]
    >- (
      irule (perm_exp_IN_Exps |> SIMP_RULE (srw_ss()) [Exps_def]) >>
      drule_all eval_wh_Closure_closed >> simp[]
      ) >>
    simp[bind_def] >> IF_CASES_TAC >> gvs[closed_def] >>
    rename1 `subst _ e3` >>
    imp_res_tac Howe_open_similarity_IMP_freevars >>
    drule eval_wh_Closure_closed >> simp[closed_def] >> rw[] >>
    reverse (Cases_on `s ∈ FDOM f`)
    >- (
      `closed e3 ∧ closed ce2` by (
        gvs[closed_def, freevars_def, EXTENSION] >>
        gvs[SUBSET_DEF, freevars_eqvt, MEM_MAP, PULL_EXISTS] >>
        metis_tac[perm1_def]) >>
      fs[closed_subst, closed_perm] >>
      irule (SIMP_RULE std_ss [transitive_def] transitive_app_similarity) >>
      qexists_tac `ce2` >> gvs[] >> rw[]
      >- (first_x_assum irule >> qexists_tac `Fail` >> simp[closed_def]) >>
      irule exp_alpha_app_similarity >> gvs[closed_perm] >>
      irule exp_alpha_perm_irrel >> gvs[closed_def]
      ) >>
    qabbrev_tac `e = f ' s` >>
    `freevars e = {}` by gvs[FLOOKUP_DEF, Abbr `e`] >>
    first_x_assum drule >>
    `subst f e3 = subst1 s e e3` by (
      once_rewrite_tac [subst_FDIFF] >> AP_THM_TAC >> AP_TERM_TAC >>
      gvs[fmap_EXT, DRESTRICT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
    rw[] >>
    irule (SIMP_RULE std_ss [transitive_def] transitive_app_similarity) >>
    goal_assum drule >>
    `subst f (perm_exp s y ce2) = subst1 s e (perm_exp s y ce2)` by (
      once_rewrite_tac [subst_FDIFF] >> AP_THM_TAC >> AP_TERM_TAC >>
      gvs[fmap_EXT, DRESTRICT_DEF, EXTENSION, SUBSET_DEF, freevars_eqvt] >>
      gvs[MEM_MAP, PULL_EXISTS] >> rw[] >> fs[perm1_def] >> metis_tac[]) >>
    rw[] >>
    irule exp_alpha_app_similarity >> reverse (rw[])
    >- (
      irule exp_alpha_sym >>
      irule exp_alpha_subst_lemma >>
      fs[closed_def, FILTER_EQ_NIL, EVERY_MEM, SUBSET_DEF]
      ) >>
    irule IMP_closed_subst >> fs[FRANGE_DEF, closed_def, SUBSET_DEF] >>
    gvs[freevars_eqvt, MEM_MAP, PULL_EXISTS, perm1_simps]
    )
  >- (
    rename1 `App` >>
    rpt gen_tac >> strip_tac >> strip_tac >>
    rename1 `Howe (open_similarity b) {} (App e3 e4) e5` >>
    simp[Once Howe_cases, eval_wh_to_def, AllCaseEqs()] >>
    Cases_on `eval_wh_to k e3 ≠ wh_Diverge` >> fs[PULL_FORALL, PULL_EXISTS] >>
    simp[GSYM IMP_DISJ_THM, PULL_FORALL] >>
    Cases_on `dest_wh_Closure (eval_wh_to k e3)` >> gvs[]
    >- (
      rpt gen_tac >> strip_tac >>
      `dest_wh_Closure (eval_wh e3) = NONE` by (
        simp[eval_wh_def, eval_wh_to_def] >>
        DEEP_INTRO_TAC some_intro >> rw[] >>
        imp_res_tac eval_wh_to_agree >> rgs[]) >>
      `eval_wh (App e3 e4) = wh_Error` by (
        simp[Once eval_wh_thm] >>
        Cases_on `eval_wh e3` >> gvs[dest_wh_Closure_def] >>
        gvs[eval_wh_def] >> pop_assum mp_tac >>
        DEEP_INTRO_TAC some_intro >> rw[] >> goal_assum drule) >>
      simp[] >>
      Cases_on ‘b’ >> fs [] >>
      rename1 `Howe (open_similarity T) {} e3 e6` >>
      imp_res_tac Howe_open_similarity_IMP_closed >>
      first_x_assum drule >> simp[] >> strip_tac >>
      qpat_x_assum `open_similarity _ _ _ _` mp_tac >>
      simp[open_similarity_def, bind_def] >> strip_tac >>
      pop_assum (qspec_then `FEMPTY` mp_tac) >> gvs[] >>
      simp[app_similarity_iff, Once unfold_rel_def] >> strip_tac >>
      first_x_assum irule >>
      simp[Once eval_wh_thm] >>
      qsuff_tac `
        eval_wh e6 ≠ wh_Diverge ∧ dest_wh_Closure (eval_wh e6) = NONE` >>
      gvs[] >>
      `eval_wh e3 ≠ wh_Diverge` by (
        simp[eval_wh_def] >> DEEP_INTRO_TAC some_intro >> rw[] >>
        goal_assum drule) >>
      Cases_on `eval_wh e3` >> gvs[dest_wh_Closure_def]
      ) >>
    PairCases_on `x` >>
    `eval_wh e3 = wh_Closure x0 x1` by (
      simp[eval_wh_def] >> DEEP_INTRO_TAC some_intro >> reverse (rw[])
      >- goal_assum drule >>
      imp_res_tac eval_wh_to_agree >> rgs[] >>
      Cases_on `eval_wh_to x e3` >> gvs[]) >>
    rpt gen_tac >> disch_then (qspecl_then [`x0`,`x1`] mp_tac) >>
    ntac 2 (once_rewrite_tac[]) >> strip_tac >>
    last_x_assum (qspecl_then [`x0`,`x1`] mp_tac) >>
    ntac 2 (once_rewrite_tac[]) >> asm_rewrite_tac[] >>
    strip_tac >> strip_tac >>
    rename1 `Howe _ _ e3 e6` >> rename1 `Howe _ _ e4 e7` >>
    imp_res_tac Howe_open_similarity_IMP_closed >>
    last_x_assum drule >> simp[] >> strip_tac >>
    rename1 `eval_wh e6 = wh_Closure y0 y1` >>
    assume_tac Sub_Howe_open_similarity >> fs[Sub_def, AND_IMP_INTRO] >>
    pop_assum (qspecl_then [
      `b`,`{}`,`x0`,`x1`,`perm_exp x0 y0 y1`,`e4`,`e7`] mp_tac) >>
    fs[Exps_def] >>
    drule_all eval_wh_Closure_closed >> strip_tac >>
    qpat_x_assum `eval_wh e3 = _` assume_tac >>
    drule_all eval_wh_Closure_closed >> strip_tac >> gvs[bind1_def] >>
    impl_keep_tac >- (imp_res_tac Howe_open_similarity_IMP_freevars) >>
    strip_tac >>
    simp[eval_wh_App, bind_def, FLOOKUP_UPDATE] >>
    first_x_assum irule >> simp[] >> rw[]
    >- (irule closed_freevars_subst1 >> simp[]) >>
    irule Howe_Tra >>
    fs[open_similarity_EMPTY, Tra_open_similarity, term_rel_open_similarity] >>
    rw[] >- (irule closed_freevars_subst1 >> simp[]) >>
    qexists_tac `subst1 x0 e7 (perm_exp x0 y0 y1)` >> simp[] >>
    rw[] >- (irule closed_freevars_subst1 >> simp[]) >>
    irule (SIMP_RULE std_ss [transitive_def] transitive_app_similarity) >>
    qexists_tac `subst1 y0 e7 y1` >> rw[]
    >- (
      irule exp_alpha_app_similarity >>
      imp_res_tac Howe_open_similarity_IMP_closed >>
      fs[exp_alpha_subst_lemma] >> rw[]
      >- (irule closed_freevars_subst1 >> simp[]) >>
      irule exp_alpha_sym >>
      Cases_on `y0 = x0` >> gvs[perm_exp_id, exp_alpha_Refl] >>
      drule exp_alpha_subst1_closed >>
      rewrite_tac[Once perm_exp_sym] >>
      disch_then irule >> simp[] >> gvs[SUBSET_DEF, EXTENSION] >>
      CCONTR_TAC >> gvs[]
      ) >>
    qpat_x_assum `(_ ≲ _) _` mp_tac >>
    rewrite_tac[app_similarity_iff] >> once_rewrite_tac[unfold_rel_def] >>
    fs[eval_wh_App, eval_wh_Cons, bind1_def] >>
    rw[] >> irule IMP_closed_subst >> fs[FRANGE_DEF]
    )
  >- (
    rename1 `Letrec` >>
    rpt gen_tac >> strip_tac >> gen_tac >> ntac 2 strip_tac >>
    gvs[eval_wh_thm, eval_wh_to_def] >>
    Cases_on `k = 0` >> gvs[] >>
    qpat_x_assum `Howe _ _ _ _` mp_tac >>
    rename1 `Letrec fa ea` >> simp[Once Howe_cases] >> strip_tac >>
    rename1 `Letrec fb eb` >>
    pop_assum mp_tac >>
    fs[open_similarity_EMPTY, app_similarity_iff] >>
    simp[unfold_rel_def] >> strip_tac >> gvs[eval_wh_thm] >>
    imp_res_tac fmap_rel_fupdate_list_MAP_FST >> gvs[] >>
    `Howe (open_similarity b) {} (subst_funs fa ea) (subst_funs fb eb)` by (
      irule Sub_subst_funs >>
      qspecl_then [‘b’] assume_tac term_rel_open_similarity >>
      simp[term_rel_Howe, Sub_Howe_open_similarity] >>
      qspecl_then [‘b’] assume_tac Ref_open_similarity >> drule Howe_Ref >>
      rw[Compatible_def] >>
      irule Howe_open_similarity_min_freevars >>
      goal_assum drule) >>
    first_x_assum drule >>
    impl_tac
    >- (
      qspecl_then [‘b’] assume_tac term_rel_open_similarity >>
      drule term_rel_Howe >> simp[term_rel_def] >> disch_then imp_res_tac >>
      gvs[closed_def, Exps_def]
      ) >>
    strip_tac >>
    Cases_on `eval_wh (subst_funs fa ea)` >> gvs[]
    >- (
      gvs[LIST_REL_EL_EQN] >> rw[] >>
      irule Howe_Tra >> qspecl_then [‘b’] assume_tac term_rel_open_similarity >>
      simp[Tra_open_similarity] >>
      first_x_assum drule >> strip_tac >>
      drule term_rel_Howe >> simp[term_rel_def] >> disch_then imp_res_tac >>
      gvs[Exps_def] >>
      first_x_assum drule >> strip_tac >>
      drule app_similarity_closed >> strip_tac >> simp[] >>
      simp[open_similarity_EMPTY] >>
      qexists_tac `EL n e2s` >>
      simp[]
      ) >>
    rename1 `wh_Closure xa cea` >>
    rename1 `eval_wh (subst_funs fb _) = wh_Closure xb ceb` >>
    rename1 `eval_wh e2 = wh_Closure xc cec` >>
    irule Howe_Tra >> qspecl_then [‘b’] assume_tac  term_rel_open_similarity >>
    simp[Tra_open_similarity] >>
    drule term_rel_Howe >> simp[term_rel_def] >> disch_then imp_res_tac >>
    simp[] >> gvs[Exps_def] >>
    conj_asm1_tac
    >- (
      rw[SUBSET_DEF] >>
      rename1 `_ ∈ freevars (_ foo)` >>
      last_x_assum (qspec_then `Fail` mp_tac) >> rw[] >>
      imp_res_tac app_similarity_closed >> rename1 `subst1 bar _ foo` >>
      `freevars foo ⊆ {bar}` by (
        irule closed_subst1_freevars >>
        goal_assum (drule_at (Pos last)) >> simp[]) >>
      gvs[freevars_eqvt, MEM_MAP] >>
      pop_assum mp_tac >> simp[SUBSET_DEF, perm1_simps]
      ) >>
    last_x_assum (qspec_then `{xa}` assume_tac) >> gvs[] >>
    goal_assum (drule_at (Pos last)) >> simp[] >>
    rw[open_similarity_alt_def] >> rw[bind_def] >>
    `FDOM f ⊆ {xa}` by (gvs[EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
    assume_tac transitive_app_similarity >> gvs[transitive_def] >>
    Cases_on `f` >> gvs[]
    >- (
      irule app_similarity_perm_exp_left >>
      irule app_similarity_perm_exp_right >>
      `closed (perm_exp xa xc cec) ∧
       closed (perm_exp xa xb ceb)` by simp[closed_def] >> gvs[closed_perm] >>
      last_x_assum irule >> qexists_tac `Fail` >> simp[]
      ) >>
    rename1 `_ |+ (xa,esub)` >>
    `g |+ (xa,esub) = FEMPTY |+ (xa,esub)` by (
      rw[fmap_eq_flookup, FLOOKUP_UPDATE, FLOOKUP_DEF] >>
      fs[SUBSET_DEF] >> metis_tac[]) >>
    gvs[FLOOKUP_UPDATE] >> pop_assum kall_tac >>
    first_x_assum (qspec_then `xa` assume_tac) >> gvs[] >>
    simp[subst1_eqvt_alt, perm1_def] >>
    irule app_similarity_perm_exp_left >>
    irule app_similarity_perm_exp_right >>
    first_assum irule >>
    qexists_tac `subst1 xc (perm_exp xa xb esub) cec` >>
    last_assum (irule_at Any) >> simp[closed_perm] >>
    irule companion_app_similarity  >>
    irule (companion_exp_alpha |> SIMP_RULE std_ss [IN_DEF]) >>
    rpt (irule_at Any closed_freevars_subst1) >> simp[closed_perm] >> rw[]
    >- (
      qpat_x_assum `freevars (perm_exp _ _ cec) ⊆ _` mp_tac >>
      simp[SUBSET_DEF, freevars_eqvt, MEM_MAP, PULL_EXISTS] >> rw[] >>
      first_x_assum drule >> simp[perm1_def] >>
      IF_CASES_TAC >> simp[] >> IF_CASES_TAC >> simp[]
      ) >>
    irule exp_alpha_subst1_closed' >> simp[closed_perm] >>
    irule exp_alpha_Trans >>
    irule_at Any exp_alpha_perm_irrel >>
    qexistsl_tac [`xb`,`xa`] >> simp[] >>
    irule_at Any exp_alpha_perm_irrel >>
    gvs[closed_def, freevars_eqvt]
    ) >>
  rename1 `Prim` >>
  rpt gen_tac >> ntac 4 strip_tac >>
  Cases_on `p` >> rgs[eval_wh_Prim_alt, eval_wh_to_def]
  >- ( (* If *)
    qpat_x_assum `_ ≠ wh_Diverge` mp_tac >>
    qpat_x_assum `Howe _ _ _ _` mp_tac >> simp[Once Howe_cases] >>
    simp[open_similarity_EMPTY, app_similarity_iff] >>
    simp[Once unfold_rel_def, eval_wh_Prim_alt] >>
    strip_tac >>
    ntac 4 (pop_assum mp_tac) >>
    imp_res_tac LIST_REL_LENGTH >>
    IF_CASES_TAC >> gvs[] >>
    `∃x1 x2 x3. xs = [x1;x2;x3]` by gvs[LENGTH_EQ_NUM_compute] >>
    `∃es1 es2 es3. es' = [es1;es2;es3]` by fs[] >>
    rpt VAR_EQ_TAC >> ntac 2 (pop_assum kall_tac) >> simp[] >>
    qpat_x_assum `LIST_REL _ _ _` mp_tac >> simp[] >> strip_tac >>
    Cases_on `k = 0` >> simp[] >>
    qpat_x_assum `∀e. _` mp_tac >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
    strip_tac >>
    qspecl_then [‘b’] assume_tac  term_rel_open_similarity >>
    drule term_rel_Howe >> simp[term_rel_def] >>
    disch_then imp_res_tac >>
    FULL_SIMP_TAC std_ss [Exps_EMPTY_closed] >>
    Cases_on `eval_wh_to (k - 1) x1 = wh_Diverge` >> simp[] >>
    `eval_wh x1 ≠ wh_Diverge` by (
      simp[eval_wh_neq_Diverge] >> goal_assum drule) >>
    simp[] >>
    first_assum drule >> disch_then drule >> simp[] >>
    Cases_on `eval_wh x1 = wh_True` >> simp[]
    >- (
      strip_tac >>
      `eval_wh_to (k - 1) x1 = wh_True` by (
        rgs[eval_wh_eq] >>
        qspecl_then [`k''`,`k - 1`,`x1`] assume_tac (GEN_ALL eval_wh_to_agree) >>
        rgs[]) >>
      simp[] >> ntac 5 strip_tac >>
      last_x_assum drule >> disch_then drule >> simp[] >>
      Cases_on `eval_wh x2` >> gvs[] >> strip_tac >> rgs[] >~[‘LIST_REL _ _ _’]
      >- (
        gvs[LIST_REL_EL_EQN] >> rw[] >>
        irule Howe_Tra >> qspecl_then [‘b’] assume_tac term_rel_open_similarity >>
        simp[Tra_open_similarity, PULL_EXISTS] >>
        first_x_assum drule >> strip_tac >>
        goal_assum (drule_at (Pos last)) >> simp[open_similarity_EMPTY] >>
        drule term_rel_Howe >> simp[term_rel_def] >> disch_then imp_res_tac >>
        gvs[Exps_def] >>
        first_x_assum drule >> strip_tac >>
        imp_res_tac app_similarity_closed
        ) >>
      irule Howe_Tra >> qspecl_then [‘b’] assume_tac term_rel_open_similarity >>
      simp[Tra_open_similarity, Exps_def, PULL_EXISTS] >>
      goal_assum (drule_at (Pos last)) >>
      imp_res_tac eval_wh_Closure_closed >> simp[freevars_eqvt] >>
      conj_asm1_tac
      >- (
        qpat_x_assum `freevars ce2' ⊆ _` mp_tac >>
        simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS, perm1_simps]
        ) >>
      conj_asm1_tac
      >- (
        qpat_x_assum `freevars ce2 ⊆ _` mp_tac >>
        simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS, perm1_simps]
        ) >>
      fs[GSYM freevars_eqvt] >>
      rw[open_similarity_alt_def, bind_def] >>
      IF_CASES_TAC >> simp[] >>
      rename1 `(_ (perm_exp xa xc cec) ≲ _ (perm_exp xa xb ceb)) b` >>
      Cases_on `f` >> rgs[]
      >- (
        irule app_similarity_perm_exp_left >>
        irule app_similarity_perm_exp_right >>
        `closed (perm_exp xa xc cec) ∧
         closed (perm_exp xa xb ceb)` by simp[closed_def] >> gvs[closed_perm] >>
        last_x_assum irule >> qexists_tac `Fail` >> simp[]
        ) >>
      `x = xa` by (
        pop_assum kall_tac >> ntac 3 (pop_assum mp_tac) >>
        simp[SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
      gvs[] >>
      rename1 `_ |+ (xa,esub)` >>
      `g |+ (xa,esub) = FEMPTY |+ (xa,esub)` by (
        rw[fmap_eq_flookup, FLOOKUP_UPDATE, FLOOKUP_DEF] >>
        IF_CASES_TAC >> simp[] >> CCONTR_TAC >> gvs[EXTENSION] >>
        res_tac >>
        rpt (qpat_x_assum `freevars (perm_exp _ _ _) ⊆ _` mp_tac) >>
        PURE_REWRITE_TAC[SUBSET_DEF, IN_SING] >> strip_tac >> strip_tac >>
        metis_tac[]) >>
      pop_assum SUBST_ALL_TAC >> gvs[FLOOKUP_UPDATE] >>
      simp[subst1_eqvt_alt, perm1_simps] >>
      irule app_similarity_perm_exp_left >>
      irule app_similarity_perm_exp_right >>
      assume_tac transitive_app_similarity >> gvs[transitive_def] >>
      first_assum irule >>
      qexists_tac `subst1 xb (perm_exp xa xc esub) ceb` >>
      last_x_assum (irule_at Any) >> simp[closed_perm] >>
      irule companion_app_similarity  >>
      irule (companion_exp_alpha |> SIMP_RULE std_ss [IN_DEF]) >>
      rpt (irule_at Any closed_freevars_subst1) >> simp[closed_perm] >>
      irule exp_alpha_subst1_closed' >> simp[closed_perm] >>
      irule exp_alpha_Trans >>
      irule_at Any exp_alpha_perm_irrel >>
      qexistsl_tac [`xc`,`xa`] >> simp[] >>
      irule_at Any exp_alpha_perm_irrel >>
      gvs[closed_def, freevars_eqvt]
      ) >>
    simp[] >>
    Cases_on `eval_wh x1 = wh_False` >> simp[]
    >- (
      strip_tac >>
      `eval_wh_to (k - 1) x1 = wh_False` by (
        rgs[eval_wh_eq] >>
        qspecl_then [`k''`,`k - 1`,`x1`] assume_tac (GEN_ALL eval_wh_to_agree) >>
        rgs[]) >>
      simp[] >> ntac 5 strip_tac >>
      last_x_assum drule >> disch_then drule >> simp[] >> strip_tac >>
      Cases_on `eval_wh x3` >> gvs[] >~[‘LIST_REL _ _ _’]
      >- (
        gvs[LIST_REL_EL_EQN] >> rw[] >>
        irule Howe_Tra >> qspecl_then [‘b’] assume_tac term_rel_open_similarity >>
        simp[Tra_open_similarity, PULL_EXISTS] >>
        first_x_assum drule >> strip_tac >>
        goal_assum (drule_at (Pos last)) >> simp[open_similarity_EMPTY] >>
        drule term_rel_Howe >> simp[term_rel_def] >> disch_then imp_res_tac >>
        gvs[Exps_def] >>
        first_x_assum drule >> strip_tac >>
        imp_res_tac app_similarity_closed
        ) >>
      irule Howe_Tra >> qspecl_then [‘b’] assume_tac term_rel_open_similarity >>
      simp[Tra_open_similarity, Exps_def, PULL_EXISTS] >>
      goal_assum (drule_at (Pos last)) >>
      imp_res_tac eval_wh_Closure_closed >> simp[freevars_eqvt] >>
      conj_asm1_tac
      >- (
        qpat_x_assum `freevars ce2' ⊆ _` mp_tac >>
        simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS, perm1_simps]
        ) >>
      conj_asm1_tac
      >- (
        qpat_x_assum `freevars ce2 ⊆ _` mp_tac >>
        simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS, perm1_simps]
        ) >>
      fs[GSYM freevars_eqvt] >>
      rw[open_similarity_alt_def, bind_def] >>
      IF_CASES_TAC >> simp[] >>
      rename1 `(_ (perm_exp xa xc cec) ≲ _ (perm_exp xa xb ceb)) _` >>
      Cases_on `f` >> gvs[]
      >- (
        irule app_similarity_perm_exp_left >>
        irule app_similarity_perm_exp_right >>
        `closed (perm_exp xa xc cec) ∧
         closed (perm_exp xa xb ceb)` by simp[closed_def] >> gvs[closed_perm] >>
        last_x_assum irule >> qexists_tac `Fail` >> simp[]
        ) >>
      `x = xa` by (
        pop_assum kall_tac >> ntac 3 (pop_assum mp_tac) >>
        simp[SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
      gvs[] >>
      rename1 `_ |+ (xa,esub)` >>
      `g |+ (xa,esub) = FEMPTY |+ (xa,esub)` by (
        rw[fmap_eq_flookup, FLOOKUP_UPDATE, FLOOKUP_DEF] >>
        IF_CASES_TAC >> simp[] >> CCONTR_TAC >> gvs[EXTENSION] >>
        res_tac >>
        rpt (qpat_x_assum `freevars (perm_exp _ _ _) ⊆ _` mp_tac) >>
        PURE_REWRITE_TAC[SUBSET_DEF, IN_SING] >> strip_tac >> strip_tac >>
        metis_tac[]) >>
      pop_assum SUBST_ALL_TAC >> gvs[FLOOKUP_UPDATE] >>
      simp[subst1_eqvt_alt, perm1_simps] >>
      irule app_similarity_perm_exp_left >>
      irule app_similarity_perm_exp_right >>
      assume_tac transitive_app_similarity >> gvs[transitive_def] >>
      first_assum irule >>
      qexists_tac `subst1 xb (perm_exp xa xc esub) ceb` >>
      last_x_assum (irule_at Any) >> simp[closed_perm] >>
      irule companion_app_similarity  >>
      irule (companion_exp_alpha |> SIMP_RULE std_ss [IN_DEF]) >>
      rpt (irule_at Any closed_freevars_subst1) >> simp[closed_perm] >>
      irule exp_alpha_subst1_closed' >> simp[closed_perm] >>
      irule exp_alpha_Trans >>
      irule_at Any exp_alpha_perm_irrel >>
      qexistsl_tac [`xc`,`xa`] >> simp[] >>
      irule_at Any exp_alpha_perm_irrel >>
      gvs[closed_def, freevars_eqvt]
      ) >>
    simp[] >> rpt strip_tac >>
    first_x_assum irule >> rw[] >> fs[] >>
    Cases_on `eval_wh x1` >> fs[]
    )
  >- ( (* Cons *)
    qpat_x_assum `Howe _ _ _ _` mp_tac >> simp[Once Howe_cases] >>
    simp[open_similarity_EMPTY, app_similarity_iff] >>
    simp[Once unfold_rel_def, eval_wh_Prim_alt] >> strip_tac >> simp[] >>
    gvs[LIST_REL_EL_EQN] >> rw[] >>
    irule Howe_Tra >> simp[Tra_open_similarity, term_rel_open_similarity] >>
    gvs[EVERY_EL] >> rpt (first_x_assum drule >> strip_tac) >>
    imp_res_tac app_similarity_closed >> simp[] >>
    goal_assum (drule_at (Pos last)) >> simp[open_similarity_EMPTY]
    )
  >- ( (* IsEq *)
    qpat_x_assum `Howe _ _ _ _` mp_tac >> simp[Once Howe_cases] >>
    simp[open_similarity_EMPTY, app_similarity_iff] >>
    simp[Once unfold_rel_def, eval_wh_Prim_alt] >> strip_tac >>
    imp_res_tac LIST_REL_LENGTH >>
    IF_CASES_TAC >> gvs[] >>
    Cases_on `xs` >> gvs[] >>
    rename1 ‘open_similarity boolean’ >>
    rename1 `Howe _ _ a b` >>
    Cases_on `k = 0` >> gvs[] >>
    `eval_wh_to (k − 1) a ≠ wh_Diverge` by (CCONTR_TAC >> gvs[]) >>
    `eval_wh a ≠ wh_Diverge` by (
      simp[eval_wh_neq_Diverge] >> goal_assum drule) >>
    gvs[] >>
    last_x_assum drule >> disch_then drule >> simp[] >> strip_tac >>
    Cases_on `eval_wh a` >> gvs[] >>
    IF_CASES_TAC >> gvs[] >>
    IF_CASES_TAC >> gvs[] >>
    drule LIST_REL_LENGTH >> gvs[] >>
    IF_CASES_TAC >> gvs[]
    )
  >- ( (* Proj *)
    qpat_x_assum `Howe _ _ _ _` mp_tac >> simp[Once Howe_cases] >>
    simp[open_similarity_EMPTY, app_similarity_iff] >>
    simp[Once unfold_rel_def, eval_wh_Prim_alt] >> strip_tac >>
    imp_res_tac LIST_REL_LENGTH >>
    IF_CASES_TAC >> fs[] >> Cases_on `xs` >> fs[] >>
    gvs[] >>
    rename1 ‘open_similarity boolean’ >>
    rename1 `Howe _ _ a b` >>
    Cases_on `k = 0` >> gvs[] >>
    `eval_wh_to (k − 1) a ≠ wh_Diverge` by (CCONTR_TAC >> fs[]) >>
    `eval_wh a ≠ wh_Diverge` by (
      simp[eval_wh_neq_Diverge] >> goal_assum drule) >>
    fs[] >>
    last_x_assum drule >> disch_then drule >> simp[] >> strip_tac >>
    Cases_on `eval_wh a` >> fs[] >>
    imp_res_tac LIST_REL_LENGTH >> rgs[] >>
    IF_CASES_TAC >> rgs[] >>
    `eval_wh_to (k - 1) a = eval_wh a` by (
      gvs[eval_wh_eq] >> irule_at Any EQ_REFL) >> gvs[] >>
    gvs[LIST_REL_EL_EQN] >>
    first_x_assum drule >> strip_tac >>
    qspecl_then [‘boolean’] assume_tac term_rel_open_similarity >>
    drule term_rel_Howe >>
    simp[term_rel_def] >> disch_then imp_res_tac >> rfs[Exps_def] >>
    last_x_assum drule >> simp[] >> strip_tac >>
    Cases_on `eval_wh (EL n l)` >> gvs[]
    >- (
      rw[] >> first_x_assum drule >> strip_tac >>
      last_x_assum drule >> strip_tac >>
      qspecl_then [‘boolean’] assume_tac term_rel_open_similarity >>
      drule term_rel_Howe >>
      simp[term_rel_def] >> disch_then imp_res_tac >> rfs[Exps_def] >>
      irule Howe_Tra >>
      simp[Tra_open_similarity, term_rel_open_similarity, Exps_def] >>
      imp_res_tac app_similarity_closed >> simp[] >>
      simp[open_similarity_EMPTY] >>
      goal_assum (drule_at (Pos last)) >> simp[]
      ) >>
    irule Howe_Tra >>
    simp[Tra_open_similarity, term_rel_open_similarity, Exps_def] >>
    imp_res_tac eval_wh_Closure_closed >> simp[] >> conj_asm1_tac
    >- gvs[freevars_eqvt, SUBSET_DEF, MEM_MAP, PULL_EXISTS, perm1_def] >>
    goal_assum (drule_at (Pos last)) >> conj_asm1_tac
    >- gvs[freevars_eqvt, SUBSET_DEF, MEM_MAP, PULL_EXISTS, perm1_def] >>
    simp[open_similarity_alt_def] >> rw[bind_def] >>
    rename1 `(subst _ (perm_exp xa xc cec) ≲ subst _ (perm_exp xa xb ceb)) _` >>
    Cases_on `f` >> rgs[]
    >- (
      `closed (perm_exp xa xc cec) ∧
       closed (perm_exp xa xb ceb)` by simp[closed_def] >>
      gvs[closed_perm] >>
      irule app_similarity_perm_exp_left >>
      irule app_similarity_perm_exp_right >>
      last_x_assum irule >> qexists_tac `Fail` >> simp[]
      ) >>
    `x = xa` by (
      pop_assum mp_tac >> pop_assum kall_tac >>
      ntac 2 (pop_assum mp_tac) >> simp[SUBSET_DEF, EXTENSION] >>
      metis_tac[]) >>
    gvs[] >>
    rename1 `_ |+ (xa,esub)` >>
    `g |+ (xa,esub) = FEMPTY |+ (xa,esub)` by (
      rw[fmap_eq_flookup, FLOOKUP_UPDATE, FLOOKUP_DEF] >>
      fs[SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
    pop_assum SUBST_ALL_TAC >> gvs[FLOOKUP_UPDATE] >> pop_assum kall_tac >>
    simp[subst1_eqvt_alt, perm1_simps] >>
    irule app_similarity_perm_exp_left >>
    irule app_similarity_perm_exp_right >>
    assume_tac transitive_app_similarity >> gvs[transitive_def] >>
    first_assum irule >>
    qexists_tac `subst1 xb (perm_exp xa xc esub) ceb` >>
    last_x_assum (irule_at Any) >> simp[closed_perm] >>
    irule companion_app_similarity  >>
    irule (companion_exp_alpha |> SIMP_RULE std_ss [IN_DEF]) >>
    rpt (irule_at Any closed_freevars_subst1) >> simp[closed_perm] >>
    irule exp_alpha_subst1_closed' >> simp[closed_perm] >>
    irule exp_alpha_Trans >>
    irule_at Any exp_alpha_perm_irrel >>
    qexistsl_tac [`xc`,`xa`] >> simp[] >>
    irule_at Any exp_alpha_perm_irrel >>
    gvs[closed_def, freevars_eqvt]
    )
  >- ( (* AtomOp *)
    qpat_x_assum `Howe _ _ _ _` mp_tac >> simp[Once Howe_cases] >>
    simp[open_similarity_EMPTY, app_similarity_iff] >>
    simp[Once unfold_rel_def, eval_wh_Prim_alt] >> strip_tac >>
    Cases_on `k = 0` >> gvs[]
    >- (
      gs [get_atoms_def, EXISTS_MAP, EVERY_MAP, MEM_MAP, MAP_MAP_o,
          combinTheory.o_DEF]
      \\ gs [EVERY_MEM, EXISTS_MEM]
      \\ Cases_on ‘xs’ \\ gvs [SF DNF_ss]
      \\ Cases_on ‘eval_op a []’ \\ gvs [pure_configTheory.eval_op_SOME]) >>
    Cases_on `get_atoms (MAP (λa. eval_wh_to (k − 1) a) xs)` >> gvs[] >>
    drule get_atoms_eval_wh_SOME >> strip_tac >> gvs[] >>
    CASE_TAC >> gvs[] >>
    `x' = x` by (
      ntac 2 $ pop_assum mp_tac >>
      CONV_TAC $ DEPTH_CONV ETA_CONV >> simp[]) >>
    VAR_EQ_TAC >> reverse $ CASE_TAC >> gvs[]
    >- (
      qsuff_tac `get_atoms (MAP eval_wh es') = SOME (SOME x')`
      >- (strip_tac >> gvs[] >> EVERY_CASE_TAC >> gvs[]) >>
      gvs[get_atoms_SOME_SOME_eq, LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
      last_x_assum (qspec_then `EL n xs` mp_tac) >> simp[EL_MEM] >>
      last_x_assum drule >> strip_tac >>
      disch_then $ drule_at Any >> simp[] >> impl_tac >> simp[] >>
      gvs[EVERY_EL]
      ) >>
    Cases_on ‘b’ >> fs [] >>
    qsuff_tac `get_atoms (MAP eval_wh es') = SOME NONE` >> gvs[] >>
    pop_assum mp_tac >> simp[get_atoms_SOME_NONE_eq] >> strip_tac >>
    pop_assum mp_tac >>
    rw [EXISTS_MAP, EXISTS_MEM, MEM_EL, PULL_EXISTS] >>
    qexists_tac `n` >> gvs[LIST_REL_EL_EQN, EL_MAP] >>
    last_assum (qspec_then `EL n xs` mp_tac) >> simp[EL_MEM] >>
    last_assum drule >> strip_tac >>
    disch_then $ drule_at Any >> gvs[EVERY_EL] >> strip_tac >>
    ‘eval_wh_to (k - 1) (EL n xs) ≠ wh_Diverge ’
      by (Cases_on ‘eval_wh_to (k - 1) (EL n xs) = wh_Diverge ’ >> gs []) >>
    `∀a. eval_wh (EL n xs) ≠ wh_Atom a` by (
      CCONTR_TAC >> gvs[] >> rgs[eval_wh_eq] >>
      first_x_assum (qspec_then `n` assume_tac) >> gvs[] >>
      drule eval_wh_to_agree >>
      disch_then (qspec_then `k'` assume_tac) >> gvs[] >>
      Cases_on ‘eval_wh_to (k - 1) (EL n xs)’ >> gvs[]) >>
    `eval_wh (EL n xs) ≠ wh_Diverge` by (
      gvs[eval_wh_neq_Diverge] >>
      goal_assum drule) >>
    rgs [] >>
    first_x_assum drule >> strip_tac >>
    Cases_on ‘eval_wh (EL n xs)’ >> gvs []
    )
  >- ( (* Seq *)
    qpat_x_assum `_ ≠ wh_Diverge` mp_tac >>
    qpat_x_assum `Howe _ _ _ _` mp_tac >> simp[Once Howe_cases] >>
    simp[open_similarity_EMPTY, app_similarity_iff] >>
    simp[Once unfold_rel_def, eval_wh_Prim_alt] >>
    strip_tac >> ntac 4 (pop_assum mp_tac) >>
    imp_res_tac LIST_REL_LENGTH >> IF_CASES_TAC >> gvs[] >>
    `∃x1 x2. xs = [x1;x2]` by gvs[LENGTH_EQ_NUM_compute] >>
    `∃es1 es2. es' = [es1;es2]` by fs[] >>
    rpt VAR_EQ_TAC >> ntac 2 (pop_assum kall_tac) >> simp[] >>
    Cases_on `k = 0` >> simp[] >>
    qpat_x_assum `LIST_REL _ _ _` mp_tac >> simp[] >> strip_tac >>
    qpat_x_assum `∀e. _` mp_tac >>
    simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
    first_assum (qspec_then `x1` mp_tac) >>
    first_x_assum (qspec_then `x2` mp_tac) >> strip_tac >> strip_tac >>
    Cases_on `eval_wh_to (k - 1) x1 = wh_Error`
    >- (
      `eval_wh x1 = wh_Error` by (
        simp[eval_wh_eq] >> goal_assum drule) >>
      simp[] >> gvs[]
      ) >>
    Cases_on `eval_wh_to (k − 1) x1 = wh_Diverge` >> simp[] >>
    Cases_on `eval_wh_to (k − 1) x2 = wh_Diverge` >> simp[] >>
    `eval_wh x1 ≠ wh_Error ∧ eval_wh x1 ≠ wh_Diverge ∧
     eval_wh x2 ≠ wh_Diverge` by (
      simp[eval_wh_eq] >> rw[]
      >- (
        Cases_on `eval_wh_to k' x1 = wh_Diverge` >> simp[] >>
        qspecl_then [`k'`,`k - 1`] mp_tac $ GEN_ALL eval_wh_to_agree >> simp[]
        )
      >- goal_assum drule
      >- goal_assum drule
      ) >>
    ntac 2 (qpat_x_assum `EVERY _ _` mp_tac >> simp[] >> strip_tac) >>
    ntac 2 $ first_x_assum $ drule_all_then assume_tac >>
    Cases_on `eval_wh x1` >> gvs[] >> Cases_on `eval_wh x2` >> rgs[] >>
    rw[] >> simp[] >> gvs[LIST_REL_EL_EQN] >> rw[] >>
    irule Howe_Tra >> qspecl_then [‘b’] assume_tac term_rel_open_similarity >>
    simp[Tra_open_similarity, PULL_EXISTS]
    THEN_LT Q.SELECT_GOALS_LT_THEN [`closed _`]
      (
      rpt $ first_x_assum $ drule_then assume_tac >>
      goal_assum $ drule_at $ Pos last >> simp[open_similarity_EMPTY] >>
      imp_res_tac app_similarity_closed >> simp[] >>
      drule term_rel_Howe >> simp[term_rel_def] >> disch_then imp_res_tac >>
      rgs[Exps_EMPTY_closed] >> NO_TAC
      ) >>
    (
      gvs[Exps_def] >>
      imp_res_tac eval_wh_Closure_closed >> gvs[Exps_def] >>
      goal_assum $ drule_at $ Pos last >> simp[open_similarity_EMPTY] >>
      simp[] >> conj_asm1_tac
      >- (
        rename1 `freevars (_ d) ⊆ _` >>
        qpat_x_assum `freevars d ⊆ _` mp_tac >>
        simp[freevars_eqvt, SUBSET_DEF, MEM_MAP, PULL_EXISTS, perm1_def]
        ) >>
      conj_asm1_tac
      >- (
        rename1 `freevars (_ d) ⊆ _` >>
        qpat_x_assum `freevars d ⊆ _` mp_tac >>
        simp[freevars_eqvt, SUBSET_DEF, MEM_MAP, PULL_EXISTS, perm1_def]
        ) >>
      simp[open_similarity_alt_def] >> rw[bind_def] >>
      rename1 `(subst _ (perm_exp xa xc cec) ≲ subst _ (perm_exp xa xb ceb)) _` >>
      Cases_on `f` >> gvs[]
      >- (
        `closed (perm_exp xa xc cec) ∧
         closed (perm_exp xa xb ceb)` by simp[closed_def] >>
        gvs[closed_perm] >>
        irule app_similarity_perm_exp_left >>
        irule app_similarity_perm_exp_right >>
        last_x_assum irule >> qexists_tac `Fail` >> simp[]
        ) >>
      `x = xa` by (
        pop_assum mp_tac >> pop_assum kall_tac >>
        ntac 2 (pop_assum mp_tac) >> simp[SUBSET_DEF, EXTENSION] >>
        metis_tac[]) >>
      gvs[] >>
      rename1 `_ |+ (xa,esub)` >>
      `g |+ (xa,esub) = FEMPTY |+ (xa,esub)` by (
        rw[fmap_eq_flookup, FLOOKUP_UPDATE, FLOOKUP_DEF] >>
        IF_CASES_TAC >> simp[] >>
        ntac 5 $ pop_assum mp_tac >> simp[SUBSET_DEF, EXTENSION] >> metis_tac[]
        ) >>
      pop_assum SUBST_ALL_TAC >> gvs[FLOOKUP_UPDATE] >> pop_assum kall_tac >>
      simp[subst1_eqvt_alt, perm1_simps] >>
      irule app_similarity_perm_exp_left >>
      irule app_similarity_perm_exp_right >>
      assume_tac transitive_app_similarity >> gvs[transitive_def] >>
      first_assum irule >>
      qexists_tac `subst1 xb (perm_exp xa xc esub) ceb` >>
      last_x_assum (irule_at Any) >> simp[closed_perm] >>
      irule companion_app_similarity  >>
      irule (companion_exp_alpha |> SIMP_RULE std_ss [IN_DEF]) >>
      rpt (irule_at Any closed_freevars_subst1) >> simp[closed_perm] >>
      irule exp_alpha_subst1_closed' >> simp[closed_perm] >>
      irule exp_alpha_Trans >>
      irule_at Any exp_alpha_perm_irrel >>
      qexistsl_tac [`xc`,`xa`] >> simp[] >>
      irule_at Any exp_alpha_perm_irrel >>
      gvs[closed_def, freevars_eqvt]
    )
    )
QED

Theorem Howe_open_similarity_SUBSET_app_simulation:
  ∀b. UNCURRY(Howe (open_similarity b) {}) ⊆  app_similarity b
Proof
  gen_tac
  \\ simp[SUBSET_DEF,IN_DEF,FORALL_PROD]
  \\ ho_match_mp_tac app_similarity_companion_coind
  \\ simp[FF_def,unfold_rel_def,ELIM_UNCURRY]
  \\ rpt gen_tac \\ strip_tac
  \\ drule Howe_open_similarity_IMP_closed \\ strip_tac \\ fs []
  \\ drule Howe_open_similarity_IMP \\ fs []
  \\ reverse (rw []) \\ fs []
  >- (
    gvs[LIST_REL_EL_EQN] >> rw[] >>
    irule companion_rel >> simp[]
    ) >>
  rename [‘wh_Closure’]
  \\ qspecl_then [‘b’] assume_tac Cus_Howe_open_similarity \\ fs [Cus_def,AND_IMP_INTRO]
  \\ pop_assum (first_x_assum o mp_then (Pos last) mp_tac) \\ rw []
  \\ first_x_assum (first_assum o mp_then (Pos last) mp_tac)
  \\ impl_keep_tac
  THEN1 (imp_res_tac eval_wh_Closure_closed
      \\ imp_res_tac perm_exp_IN_Exps \\ fs [Exps_def])
  \\ rw []
  \\ match_mp_tac companion_rel
  \\ simp[]
  \\ rw [] \\ match_mp_tac (MP_CANON Howe_Tra |> GEN_ALL)
  \\ fs [open_similarity_EMPTY]
  \\ fs [Tra_open_similarity,term_rel_open_similarity]
  \\ fs [AC CONJ_ASSOC CONJ_SYM]
  \\ goal_assum (first_assum o mp_then (Pos last) mp_tac)
  \\ rewrite_tac [CONJ_ASSOC]
  \\ reverse conj_asm1_tac
  THEN1 (match_mp_tac exp_alpha_app_similarity \\ rw []
      \\ match_mp_tac exp_alpha_subst_lemma \\ fs []
      \\ imp_res_tac eval_wh_Closure_closed \\ simp [closed_def]
      \\ fs [closed_def,SUBSET_DEF,FILTER_EQ_NIL,EVERY_MEM])
  \\ rw [] \\ match_mp_tac IMP_closed_subst
  \\ fs [FRANGE_DEF]
  \\ imp_res_tac eval_wh_Closure_closed
  \\ fs [closed_def,SUBSET_DEF,FILTER_EQ_NIL,EVERY_MEM]
  \\ rewrite_tac [freevars_eqvt]
  \\ fs [SUBSET_DEF,MEM_MAP,PULL_EXISTS,perm1_def,closed_def,
      FILTER_EQ_NIL,EVERY_MEM]
QED

Theorem IMP_open_similarity_INSERT:
  (* This has been modified to only subst in closed expressions *)
  (∀e. closed e ⇒ open_similarity b vars (subst1 h e e1) (subst1 h e e2)) ∧
  h ∉ vars ∧ e1 IN Exps (h INSERT vars) ∧ e2 IN Exps (h INSERT vars) ⇒
  open_similarity b (h INSERT vars) e1 e2
Proof
  fs [open_similarity_def] \\ rw [] \\ fs [Exps_def]
  \\ rw [bind_def]
  \\ reverse (Cases_on ‘h IN FDOM f’)
  THEN1
   (‘~(h IN freevars e1) ∧ ~(h IN freevars e2)’ by (fs [SUBSET_DEF] \\ metis_tac [])
    \\ fs [subst1_ignore]
    \\ ‘closed Fail’ by fs[closed_def]
    \\ first_x_assum drule
    \\ disch_then drule_all
    \\ fs [] \\ fs [bind_def]
    \\ metis_tac [])
  \\ ‘∃e. FLOOKUP f h = SOME e ∧ closed e’ by
        (fs [FLOOKUP_DEF,EXTENSION] \\ metis_tac [])
  \\ last_x_assum drule \\ rw []
  \\ first_x_assum (qspec_then ‘f’ mp_tac)
  \\ impl_tac THEN1 (fs [SUBSET_DEF,freevars_subst])
  \\ fs [bind_def,FLOOKUP_DRESTRICT]
  \\ reverse IF_CASES_TAC THEN1 metis_tac [] \\ fs []
  \\ ‘(∀v. v ∈ FRANGE (FEMPTY |+ (h,e)) ⇒ closed v)’ by fs [FRANGE_DEF,FLOOKUP_DEF]
  \\ drule subst_subst_FUNION \\ fs []
  \\ qsuff_tac ‘FEMPTY |+ (h,e) ⊌ f = f’ THEN1 fs []
  \\ fs [fmap_EXT,FUNION_DEF,EXTENSION,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ metis_tac []
QED

Theorem Howe_open_similarity: (* key property *)
  ∀b. Howe (open_similarity b) = open_similarity b
Proof
  simp[FUN_EQ_THM] >> rw[] >> rename1 `Howe _ vars e1 e2` >>
  reverse eq_tac >> rw[]
  >- metis_tac [Howe_Ref_Tra,Ref_open_similarity,Tra_open_similarity,
                term_rel_open_similarity] >>
  imp_res_tac Howe_open_similarity_IMP_freevars >>
  qspecl_then [‘b’] assume_tac Sub_Howe_open_similarity >>
  rw[open_similarity_def, bind_def] >> IF_CASES_TAC >> simp[] >>
  mp_tac Howe_open_similarity_SUBSET_app_simulation >>
  simp[SUBSET_DEF, FORALL_AND_THM, FORALL_PROD, IN_DEF] >>
  disch_then irule >>
  drule Sub_lift >> disch_then irule >> simp[Exps_def] >>
  reverse conj_tac
  >- (
    imp_res_tac Howe_open_similarity_min_freevars >>
    irule Howe_larger >> goal_assum (drule_at (Pos last)) >> simp[]
    ) >>
  strip_tac >> strip_tac >>
  first_x_assum (qspec_then `k` assume_tac) >> gvs[FLOOKUP_DEF] >>
  qspecl_then [‘b’] assume_tac Ref_open_similarity >> drule Ref_Howe >> simp[Ref_def]
QED

Theorem Precongruence_open_similarity: (* part 1 of 5.5.5 *)
  ∀b. Precongruence (open_similarity b)
Proof
  fs [Precongruence_def] \\ rw [Tra_open_similarity]
  \\ once_rewrite_tac [GSYM Howe_open_similarity]
  \\ match_mp_tac Howe_Ref
  \\ fs [open_similarity_def,Ref_open_similarity]
QED

Theorem LIST_REL_open_bisimilarity:
  ∀es es' b.
    LIST_REL (open_bisimilarity b vars) es es' ⇔
    LIST_REL (open_similarity b vars) es es' ∧
    LIST_REL (open_similarity b vars) es' es
Proof
  Induct \\ Cases_on ‘es'’ \\ fs [PULL_EXISTS]
  \\ fs [open_bisimilarity_eq] \\ metis_tac []
QED

Theorem fmap_rel_open_bisimilarity:
  ∀f1 f2 vars b.
    fmap_rel (open_bisimilarity b vars) f1 f2 ⇔
    fmap_rel (open_similarity b vars) f1 f2 ∧
    fmap_rel (open_similarity b vars) f2 f1
Proof
  rw[fmap_rel_OPTREL_FLOOKUP] >> eq_tac >> rw[] >>
  rpt (pop_assum (qspec_then `k` mp_tac)) >>
  Cases_on `FLOOKUP f1 k` >> Cases_on `FLOOKUP f2 k` >> gvs[] >>
  gvs[open_bisimilarity_eq]
QED

Theorem Congruence_open_bisimilarity: (* part 2 of 5.5.5 *)
  ∀b. Congruence (open_bisimilarity b)
Proof
  gen_tac
  \\ fs [Congruence_def,Sym_open_bisimilarity]
  \\ qspecl_then [‘b’] assume_tac Precongruence_open_similarity
  \\ fs [Precongruence_def,Tra_open_bisimilarity]
  \\ fs [Compatible_def] \\ rw []
  \\ fs [Com_defs,open_bisimilarity_def,open_similarity_def]
  \\ fs [app_bisimilarity_similarity]
  THEN1 metis_tac []
  THEN1 metis_tac []
  THEN1 metis_tac []
  THEN1
   (fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
    \\ qpat_x_assum ‘∀x. _’ kall_tac
    \\ qpat_x_assum ‘∀x. _’ mp_tac
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
    \\ fs [LIST_REL_open_bisimilarity]
    \\ metis_tac [])
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ fs [LIST_REL_open_bisimilarity, fmap_rel_open_bisimilarity]
  \\ fs [GSYM PULL_FORALL]
  THEN1 (metis_tac [])
  THEN1 (metis_tac [])
  \\ fs [GSYM CONJ_ASSOC]
  THEN1
   (first_x_assum (qspecl_then [‘vars’,‘ves’,‘ves'’,‘e’,‘e'’] mp_tac)
    \\ impl_tac THEN1 gvs [] \\ rw [])
  THEN1 (
    imp_res_tac fmap_rel_fupdate_list_MAP_FST \\ gvs[]
    \\ first_x_assum (qspecl_then [‘vars’,‘ves'’,‘ves’,‘e'’,‘e’] mp_tac)
    \\ impl_tac THEN1 gvs [] \\ rw [])
QED

(* -- contextual equivalence -- *)

Theorem exp_eq_refl:
  ∀x b. (x ≅? x) b
Proof
  fs [exp_eq_open_bisimilarity] \\ rw []
  \\ qexists_tac ‘freevars x’ \\ fs []
  \\ assume_tac Ref_open_bisimilarity
  \\ fs [Ref_def]
  \\ first_x_assum match_mp_tac
  \\ fs [Exps_def]
QED

Theorem exp_eq_sym:
  ∀x y b. (x ≅? y) b ⇔ (y ≅? x) b
Proof
  qsuff_tac ‘∀x y b. (x ≅? y) b ⇒ (y ≅? x) b’ THEN1 metis_tac []
  \\ fs [exp_eq_open_bisimilarity] \\ rw []
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ qspecl_then [‘b’] assume_tac Sym_open_bisimilarity
  \\ fs [Sym_def,PULL_FORALL,AND_IMP_INTRO]
  \\ first_x_assum match_mp_tac
  \\ fs [Exps_def]
QED

Theorem exp_eq_trans:
  ∀x y z b. (x ≅? y) b ∧ (y ≅? z) b ⇒ (x ≅? z) b
Proof
  fs [exp_eq_open_bisimilarity] \\ rw []
  \\ qexists_tac ‘vars UNION vars'’ \\ fs [SUBSET_DEF]
  \\ qspecl_then [‘b’] assume_tac Tra_open_bisimilarity
  \\ fs [Tra_def,PULL_FORALL,AND_IMP_INTRO]
  \\ first_x_assum match_mp_tac
  \\ fs [Exps_def,SUBSET_DEF]
  \\ qexists_tac ‘y’ \\ fs [] \\ rw []
  \\ match_mp_tac open_bisimilarity_SUBSET
  \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs [SUBSET_DEF]
QED

Theorem Congruence_exp_eq:
  ∀b. Congruence (K (λx y. (x ≅? y) b))
Proof
  gen_tac
  \\ qspecl_then [‘b’] mp_tac Congruence_open_bisimilarity
  \\ rw [Congruence_def,Precongruence_def]
  \\ fs [Sym_def,Tra_def]
  THEN1 metis_tac [exp_eq_sym]
  THEN1 metis_tac [exp_eq_trans]
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
    \\ qmatch_goalsub_abbrev_tac ‘open_bisimilarity b vars1’
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
   (imp_res_tac fmap_rel_fupdate_list_MAP_FST \\ fs[]
    \\ fs [exp_eq_open_bisimilarity_freevars,AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac) \\ gvs[]
    \\ conj_tac
    THEN1
     (fs [Exps_def,SUBSET_DEF,MEM_MAP,PULL_EXISTS,FORALL_PROD,EXISTS_PROD]
      \\ rw [] \\ fs [IN_DISJOINT,MEM_MAP,FORALL_PROD,EXISTS_PROD]
      \\ imp_res_tac (METIS_PROVE []
            “MAP f xs = MAP f xs' ⇒ ∀y. MEM y (MAP f xs) = MEM y (MAP f xs')”)
      \\ fs [MEM_MAP,FORALL_PROD,EXISTS_PROD,PULL_EXISTS]
      \\ metis_tac [])
    \\ fs [] \\ reverse conj_tac
    THEN1
     (match_mp_tac open_bisimilarity_SUBSET
      \\ goal_assum (first_x_assum o mp_then (Pos hd) mp_tac)
      \\ fs [SUBSET_DEF] \\ metis_tac [])
    \\ qmatch_goalsub_abbrev_tac ‘open_bisimilarity b vars1’
    \\ ‘BIGUNION (set (MAP (λ(_,e). freevars e) ves)) SUBSET vars1 ∧
        BIGUNION (set (MAP (λ(_,e). freevars e) ves')) SUBSET vars1’ by
           (fs [Abbr‘vars1’] \\ fs [SUBSET_DEF] \\ metis_tac [])
    \\ ntac 2 (pop_assum mp_tac) \\ ntac 3 (pop_assum kall_tac) \\ rw[]
    \\ gvs[fmap_rel_OPTREL_FLOOKUP, flookup_fupdate_list] \\ rw[]
    \\ first_x_assum (qspec_then `k` assume_tac)
    \\ EVERY_CASE_TAC >> gvs[]
    \\ imp_res_tac ALOOKUP_MEM
    \\ fs [exp_eq_open_bisimilarity_freevars]
    \\ irule open_bisimilarity_SUBSET \\ goal_assum (drule_at (Pos last))
    \\ gvs[SUBSET_DEF, MEM_MAP, PULL_EXISTS, FORALL_PROD]
    \\ metis_tac[]
    )
QED

Theorem exp_eq_Var_cong:
  (Var v ≅? Var v) b
Proof
  qspecl_then [‘b’] assume_tac Congruence_exp_eq >>
  fs[Congruence_def, Precongruence_def, Compatible_def, Com1_def] >>
  first_x_assum irule >> qexists_tac `{v}` >> simp[]
QED

Theorem exp_eq_Lam_cong:
  (e ≅? e') b ⇒ (Lam x e ≅? Lam x e') b
Proof
  qspecl_then [‘b’] assume_tac Congruence_exp_eq
  \\ fs [Congruence_def,Precongruence_def,Compatible_def,Com2_def]
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ qexists_tac ‘freevars (App (Lam x e) (Lam x e'))’
  \\ fs [Exps_def,SUBSET_DEF] \\ fs [MEM_FILTER]
QED

Theorem exp_eq_App_cong:
  (f ≅? f') b ∧ (e ≅? e') b ⇒ (App f e ≅? App f' e') b
Proof
  qspecl_then [‘b’] assume_tac Congruence_exp_eq
  \\ fs [Congruence_def,Precongruence_def,Compatible_def,Com3_def]
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ qexists_tac ‘freevars (App f (App f' (App e e')))’
  \\ fs [Exps_def,SUBSET_DEF]
QED

Theorem exp_eq_Prim_cong:
  LIST_REL (λx y. (x ≅? y) b) xs xs' ⇒
  (Prim p xs ≅? Prim p xs') b
Proof
  qspecl_then [‘b’] assume_tac Congruence_exp_eq
  \\ fs [Congruence_def,Precongruence_def,Compatible_def,Com4_def]
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ qexists_tac ‘freevars (App (Prim p xs) (Prim p xs'))’
  \\ fs [Exps_def,SUBSET_DEF]
  \\ rw [] \\ fs [MEM_MAP,EXISTS_PROD,FORALL_PROD,PULL_EXISTS]
  \\ metis_tac []
QED

Theorem exp_eq_Letrec_cong:
  LIST_REL (λx y. (x ≅? y) b) (MAP SND xs) (MAP SND xs') ∧ (e ≅? e') b ∧ MAP FST xs = MAP FST xs' ⇒
  (Letrec xs e ≅? Letrec xs' e') b
Proof
  qspecl_then [‘b’] assume_tac Congruence_exp_eq
  \\ fs [Congruence_def,Precongruence_def,Compatible_def,Com5_def]
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ qexists_tac ‘freevars (App (Letrec xs e) (Letrec xs' e'))’
  \\ fs [Exps_def,SUBSET_DEF]
  \\ reverse (rw []) \\ fs [MEM_MAP,EXISTS_PROD,FORALL_PROD,PULL_EXISTS]
    >- (irule fmap_rel_FUPDATE_LIST_same >> simp[])
  \\ metis_tac []
QED

Theorem exp_eq_Letrec_cong2:
  fmap_rel (λx y. (x ≅? y) b) (FEMPTY |++ xs) (FEMPTY |++ xs') ∧ (e ≅? e') b ⇒
  (Letrec xs e ≅? Letrec xs' e') b
Proof
  qspecl_then [‘b’] assume_tac Congruence_exp_eq >>
  fs[Congruence_def, Precongruence_def, Compatible_def, Com5_def] >>
  rw[] >> first_x_assum irule >> simp[] >>
  qexists_tac `freevars (App (Letrec xs e) (Letrec xs' e'))` >>
  gvs[Exps_def, SUBSET_DEF] >>
  imp_res_tac fmap_rel_fupdate_list_MAP_FST >> gvs[] >>
  rw[] >> gvs[MEM_MAP, EXISTS_PROD, FORALL_PROD, PULL_EXISTS] >> metis_tac[]
QED

Theorem exp_eq_subst_all:
  ∀e m1 m2.
    FDOM m1 = FDOM m2 ∧
    (∀k v1 v2.
      FLOOKUP m1 k = SOME v1 ∧ FLOOKUP m2 k = SOME v2 ⇒
      (v1 ≅? v2) b ∧ closed v1 ∧ closed v2) ⇒
    (subst m1 e ≅? subst m2 e) b
Proof
  ho_match_mp_tac freevars_ind \\ rw []
  >- (fs [subst_def] \\ CASE_TAC \\ fs [FLOOKUP_DEF] \\ gvs [exp_eq_refl])
  >- (fs [subst_def] \\ match_mp_tac exp_eq_Prim_cong \\ fs []
      \\ Induct_on ‘es’ \\ fs [] \\ rw []
      \\ first_x_assum irule \\ fs [SF SFY_ss])
  >- (fs [subst_def] \\ match_mp_tac exp_eq_App_cong \\ fs [] \\ rw []
      \\ first_x_assum irule \\ fs [SF SFY_ss])
  >- (fs [subst_def]
      \\ match_mp_tac exp_eq_Lam_cong
      \\ first_x_assum irule \\ fs [SF SFY_ss,DOMSUB_FLOOKUP_THM])
  \\ fs [subst_def]
  \\ match_mp_tac exp_eq_Letrec_cong
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
  \\ reverse conj_tac
  >- (first_x_assum irule
      \\ fs [FLOOKUP_FDIFF,SF SFY_ss,FDOM_FDIFF,EXTENSION])
  \\ fs [LIST_REL_MAP_MAP]
  \\ fs [EVERY_MEM,FORALL_PROD]
  \\ rw [] \\ last_x_assum $ drule_then irule
  \\ fs [FLOOKUP_FDIFF,SF SFY_ss,FDOM_FDIFF,EXTENSION]
QED

Theorem exp_eq_subst:
  (y1 ≅? y2) b ∧ closed y1 ∧ closed y2 ⇒
  (subst1 x y1 e1 ≅? subst1 x y2 e1) b
Proof
  rw [] \\ irule exp_eq_subst_all
  \\ fs [FLOOKUP_UPDATE]
QED

Theorem exp_eq_Lam_basic_lemma[local]:
  (Lam x e1 ≅? Lam x e2) b ⇔
  ∀y. closed y ⇒ (subst1 x y e1 ≅? subst1 x y e2) b
Proof
  fs [exp_eq_def] \\ eq_tac \\ rw []
  THEN1 (
    rw [bind_def]
    \\ first_x_assum (qspec_then ‘f’ mp_tac)
    \\ fs [bind_def]
    \\ reverse IF_CASES_TAC THEN1 (rfs [] \\ res_tac \\ fs [])
    \\ fs [] \\ impl_tac THEN1 (gvs [freevars_subst,SUBSET_DEF])
    \\ fs [subst_def]
    \\ simp [Once app_bisimilarity_iff] \\ fs [eval_wh_thm]
    \\ rw []
    \\ last_x_assum assume_tac \\ first_x_assum drule
    \\ ‘(∀v. v ∈ FRANGE (f \\ x) ⇒ closed v)’ by
         fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS,DOMSUB_FAPPLY_THM]
    \\ drule subst_subst_FUNION
    \\ ‘(∀v. v ∈ FRANGE (FEMPTY |+ (x,y)) ⇒ closed v)’ by
         fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS,DOMSUB_FAPPLY_THM]
    \\ drule subst_subst_FUNION \\ fs []
    \\ ntac 2 strip_tac
    \\ qmatch_goalsub_abbrev_tac ‘subst m1’ \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac ‘subst m2’
    \\ qsuff_tac ‘m1 = m2’ \\ rw [] \\ fs []
    \\ unabbrev_all_tac
    \\ fs [fmap_EXT,FUNION_DEF,FAPPLY_FUPDATE_THM,EXTENSION,DOMSUB_FAPPLY_THM]
    \\ metis_tac []
    )
  \\ rw [bind_def]
  \\ fs [subst_def,PULL_FORALL,AND_IMP_INTRO]
  \\ simp [Once app_bisimilarity_iff] \\ fs [eval_wh_thm]
  \\ fs [GSYM subst_def,CONJ_ASSOC]
  \\ conj_tac
  THEN1 (
    rw [] \\ rewrite_tac [GSYM closed_simps, GSYM subst_def]
    \\ match_mp_tac IMP_closed_subst
    \\ fs [FLOOKUP_DEF,FRANGE_DEF,PULL_EXISTS]
    )
  \\ rw []
  \\ first_x_assum (qspecl_then [‘e’,‘f \\ x’] mp_tac)
  \\ impl_tac THEN1
   (res_tac \\ fs [] \\ fs [SUBSET_DEF]
    \\ simp [freevars_subst,SUBSET_DEF])
  \\ fs [bind_def]
  \\ reverse IF_CASES_TAC \\ fs []
  THEN1 (fs [DOMSUB_FAPPLY_THM,FLOOKUP_DEF] \\ res_tac \\ gvs [])
  \\ ‘(∀v. v ∈ FRANGE (f \\ x) ⇒ closed v)’ by
    fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS,DOMSUB_FAPPLY_THM]
  \\ drule subst_subst_FUNION
  \\ ‘(∀v. v ∈ FRANGE (FEMPTY |+ (x,e)) ⇒ closed v)’ by
    fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS,DOMSUB_FAPPLY_THM]
  \\ drule subst_subst_FUNION \\ fs []
  \\ ntac 2 strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘subst m1’ \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘subst m2’
  \\ qsuff_tac ‘m1 = m2’ \\ rw [] \\ fs []
  \\ unabbrev_all_tac
  \\ fs [fmap_EXT,FUNION_DEF,FAPPLY_FUPDATE_THM,EXTENSION,DOMSUB_FAPPLY_THM]
  \\ metis_tac []
QED

Theorem exp_eq_Lam_lemma[local]:
  (Lam x e1 ≅? Lam x e2) b ⇔
  ∀y1 y2.
    (y1 ≅? y2) b ∧ closed y1 ∧ closed y2 ⇒
    (subst1 x y1 e1 ≅? subst1 x y2 e2) b
Proof
  fs [exp_eq_Lam_basic_lemma] \\ reverse eq_tac \\ rw []
  THEN1 (first_x_assum match_mp_tac \\ fs [exp_eq_refl])
  \\ match_mp_tac exp_eq_trans
  \\ first_x_assum drule \\ rw []
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ match_mp_tac exp_eq_subst \\ fs []
QED

Theorem exp_eq_forall_subst:
  ∀v. (x ≅? y) b ⇔ ∀z. closed z ⇒ (subst1 v z x ≅? subst1 v z y) b
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
   (‘v ∉ freevars x ∧ v ∉ freevars y’ by (fs [SUBSET_DEF] \\ metis_tac [])
    \\ gvs [subst1_ignore]
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

Theorem exp_eq_Lam_removed:
  ∀s e1 e2 b. (Lam s e1 ≅? Lam s e2) b ⇔ (e1 ≅? e2) b
Proof
  rw []
  \\ eq_tac
  \\ strip_tac
  \\ gvs [exp_eq_Lam_cong]
  \\ irule $ iffRL exp_eq_forall_subst
  \\ rename1 ‘Lam s _’
  \\ qexists_tac ‘s’
  \\ rw []
  \\ fs [exp_eq_Lam_lemma]
  \\ first_x_assum irule
  \\ fs [exp_eq_refl]
QED

Theorem exp_eq_free:
  v ∉ freevars y ⇒
  ((x ≅? y) b ⇔ ∀z. closed z ⇒ (subst1 v z x ≅? y) b)
Proof
  metis_tac [exp_eq_forall_subst,subst1_ignore]
QED

Theorem exp_eq_perm_IMP:
  ∀x y e e' b.
    x ∉ freevars e' ∧ y NOTIN freevars e' ∧ (e ≅? perm_exp x y e') b ⇒ (e ≅? e') b
Proof
  metis_tac [exp_eq_perm,exp_eq_sym,exp_eq_trans]
QED

Theorem exp_eq_subst_perm_exp:
  closed e' ⇒ (subst1 y e' e ≅? subst1 y (perm_exp x y e') e) b
Proof
  rw [] \\ match_mp_tac exp_eq_subst \\ fs [closed_perm]
  \\ match_mp_tac exp_eq_perm \\ fs [closed_def]
QED

Triviality Lam_Lam:
  (Lam x e1 ≅? Lam y e2) b ⇔
  ∀xv yv. closed xv ∧ closed yv ⇒ (subst1 y yv (Lam x e1) ≅? subst1 x xv (Lam y e2)) b
Proof
  Cases_on ‘x=y’ \\ fs [subst_def]
  \\ ‘closed Fail’ by fs [closed_def]
  THEN1 metis_tac []
  \\ ‘y ∉ freevars (Lam y e2)’ by fs[]
  \\ drule exp_eq_free
  \\ disch_then (once_rewrite_tac o single)
  \\ simp [subst_def]
  \\ ‘∀e1. x ∉ freevars (Lam x e1)’ by fs []
  \\ ‘(∀e1 x'. (Lam x e1 ≅? x') b ⇔ ∀z. closed z ⇒ (Lam x e1 ≅? subst1 x z x') b)’
         by metis_tac [exp_eq_sym,exp_eq_free]
  \\ pop_assum (simp o single o Once)
  \\ fs [subst_def,PULL_FORALL,AND_IMP_INTRO]
  \\ metis_tac []
QED

Triviality subst_subst_lemma:
  closed y1 ∧ closed y2 ⇒
  ((subst1 x y1 e1 ≅? subst1 y y2 e2) b ⇔
   ∀xv yv. closed xv ∧ closed yv ⇒
           (subst1 y yv (subst1 x y1 e1) ≅? subst1 x xv (subst1 y y2 e2)) b)
Proof
  strip_tac
  \\ Cases_on ‘x=y’ \\ fs [subst_def,subst1_subst1_eq]
  THEN1 metis_tac []
  \\ ‘closed Fail’ by fs [closed_def]
  \\ simp [subst_def]
  \\ ‘y ∉  freevars (subst1 y y2 e2)’ by fs [freevars_subst]
  \\ drule exp_eq_free
  \\ disch_then (once_rewrite_tac o single)
  \\ drule_at (Pos last) subst1_subst1
  \\ disch_then (simp o single)
  \\ ‘∀e1. x ∉  freevars (subst1 x y1 e1)’ by fs [freevars_subst]
  \\ ‘(∀e1 x'. (subst1 x y1 e1 ≅? x') b ⇔ ∀z. closed z ⇒ (subst1 x y1 e1 ≅? subst1 x z x') b)’
         by metis_tac [exp_eq_sym,exp_eq_free]
  \\ pop_assum (simp o single o Once)
  \\ fs [subst_def,PULL_FORALL,AND_IMP_INTRO]
  \\ metis_tac []
QED

Theorem exp_eq_Lam:
  (Lam x e1 ≅? Lam y e2) b ⇔
  ∀y1 y2.
    (y1 ≅? y2) b ∧ closed y1 ∧ closed y2 ⇒
    (subst1 x y1 e1 ≅? subst1 y y2 e2) b
Proof
  Cases_on ‘x = y’ THEN1 metis_tac [exp_eq_Lam_lemma]
  \\ fs [Lam_Lam]
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [subst_def])) \\ fs []
  \\ CONV_TAC (RAND_CONV (SIMP_CONV std_ss [Once subst_subst_lemma])) \\ fs []
  \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ ‘∀t xv. closed xv ⇒ ((t ≅? Lam y (subst1 x xv e2)) b ⇔
                          (t ≅? Lam x (subst1 y (perm_exp x y xv) (perm_exp x y e2))) b)’ by
   (rw [] \\ eq_tac \\ rw []
    \\ match_mp_tac exp_eq_perm_IMP
    \\ qexists_tac ‘x’ \\ qexists_tac ‘y’
    \\ fs [MEM_FILTER,freevars_subst1,closed_perm]
    \\ fs [perm_exp_def,perm1_def,subst1_eqvt])
  \\ fs [exp_eq_Lam_lemma,DOMSUB_FUPDATE_THM]
  \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ drule_at Any subst1_subst1
  \\ disch_then (simp o single o GSYM)
  \\ pop_assum kall_tac
  \\ eq_tac \\ rw [] \\ fs [AC CONJ_ASSOC CONJ_COMM]
  \\ first_x_assum (first_x_assum o mp_then (Pos last) mp_tac)
  THEN1
   (disch_then (qspecl_then [‘xv’,‘yv’] assume_tac) \\ gvs []
    \\ drule_at (Pos last) subst1_subst1
    \\ fs [] \\ disch_then kall_tac
    \\ match_mp_tac exp_eq_trans
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ match_mp_tac exp_eq_perm_IMP
    \\ qexists_tac ‘x’ \\ qexists_tac ‘y’ \\ fs []
    \\ fs [freevars_subst,subst1_eqvt,perm1_def]
    \\ drule_at (Pos last) subst1_subst1
    \\ fs [closed_perm] \\ disch_then kall_tac
    \\ rename [‘(subst1 _ _ e ≅? _) _’]
    \\ once_rewrite_tac [perm_exp_sym]
    \\ fs [exp_eq_subst_perm_exp])
  THEN1
   (disch_then (qspecl_then [‘xv’,‘yv’] assume_tac) \\ gvs []
    \\ match_mp_tac exp_eq_trans
    \\ ‘y ≠ x’ by fs []
    \\ drule_at (Pos last) subst1_subst1
    \\ fs [closed_perm]
    \\ disch_then (qspecl_then [‘e1’,‘y1’,‘yv’] assume_tac) \\ rfs []
    \\ pop_assum (rewrite_tac o single)
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ drule_at (Pos last) subst1_subst1
    \\ fs [closed_perm]
    \\ disch_then (qspecl_then [‘e2’,‘xv’,‘y2’] assume_tac) \\ rfs []
    \\ pop_assum (rewrite_tac o single)
    \\ match_mp_tac exp_eq_perm_IMP
    \\ qexists_tac ‘x’ \\ qexists_tac ‘y’ \\ fs []
    \\ fs [freevars_subst,subst1_eqvt,perm1_def, closed_perm]
    \\ fs [exp_eq_subst_perm_exp])
QED

Theorem exp_eq_Lam_strong:
  (Lam x e1 ≅? Lam y e2) b ⇔
  ∀e.  closed e ⇒ (subst1 x e e1 ≅? subst1 y e e2) b
Proof
  Cases_on `x = y` >> gvs[]
  >- simp[exp_eq_Lam_basic_lemma] >>
  simp[exp_eq_Lam] >> eq_tac >> rw[]
  >- (first_x_assum irule >> simp[exp_eq_refl]) >>
  res_tac >>
  irule exp_eq_trans >> goal_assum drule >>
  irule exp_eq_subst >> simp[]
QED

Theorem beta_equality_frees:
  ∀x e1 e2. DISJOINT (freevars e2) (boundvars e1) ==>
  (App (Lam x e1) e2 ≅? subst1 x e2 e1) b
Proof
  rw[exp_eq_def, bind_def] >> IF_CASES_TAC >> simp[] >>
  irule eval_IMP_app_bisimilarity >> rw[] >>
  simp [IMP_closed_subst, IN_FRANGE_FLOOKUP] >>
  simp[subst_def, eval_thm, bind_def, FLOOKUP_UPDATE] >>
  simp [IMP_closed_subst, IN_FRANGE_FLOOKUP] >>
  srw_tac [SatisfySimps.SATISFY_ss] [subst1_distrib]
QED

Theorem beta_equality:
  ∀x e1 e2. closed e2 ⇒ (App (Lam x e1) e2 ≅? subst1 x e2 e1) b
Proof
  rw []
  \\ irule beta_equality_frees
  \\ fs [closed_def]
QED

Theorem beta_equality_Letrec:
  ∀fns e.
    EVERY (λe. freevars e ⊆ set (MAP FST fns)) (MAP SND fns)
  ⇒ (Letrec fns e ≅? subst_funs fns e) b
Proof
  rw[exp_eq_def, bind_def] >> IF_CASES_TAC >> simp[] >>
  irule eval_IMP_app_bisimilarity >> rw[]
  >- (irule IMP_closed_subst >> simp[IN_FRANGE_FLOOKUP])
  >- (irule IMP_closed_subst >> simp[IN_FRANGE_FLOOKUP]) >>
  simp[subst_def, eval_thm, bind_def, FLOOKUP_UPDATE] >>
  AP_TERM_TAC >> simp[subst_funs_def, bind_def] >>
  `(MAP (λ(f',e). (f',subst (FDIFF f (set (MAP FST fns))) e)) fns) = fns` by (
    irule MAP_ID_ON >> rw[] >> PairCases_on `x` >> simp[] >>
    irule subst_ignore >> gvs[DISJOINT_DEF, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    last_x_assum drule >>
    simp[EXTENSION, SUBSET_DEF, FDOM_FDIFF, DISJ_EQ_IMP]) >>
  gvs[] >> IF_CASES_TAC >> gvs[] >>
  dep_rewrite.DEP_REWRITE_TAC[subst_subst_FUNION] >>
  simp[FDIFF_def, IN_FRANGE_FLOOKUP, PULL_EXISTS, FLOOKUP_DRESTRICT] >>
  rw[] >- res_tac >>
  AP_THM_TAC >> AP_TERM_TAC >>
  simp[fmap_eq_flookup, FLOOKUP_FUNION, FLOOKUP_DRESTRICT,
       flookup_fupdate_list] >>
  qmatch_goalsub_abbrev_tac `ALOOKUP l` >> rw[]
  >- (
    `ALOOKUP l x = NONE` by (
      gvs[ALOOKUP_NONE] >> unabbrev_all_tac >>
      simp[MAP_REVERSE, MAP_MAP_o, combinTheory.o_DEF,
           LAMBDA_PROD, GSYM FST_THM]) >>
    gvs[] >> CASE_TAC >> simp[]
    )
  >- (
    CASE_TAC >> gvs[] >> CCONTR_TAC >>
    qpat_x_assum `ALOOKUP _ _ = _` mp_tac >> simp[ALOOKUP_NONE] >>
    unabbrev_all_tac >>
    simp[MAP_REVERSE, MAP_MAP_o, combinTheory.o_DEF,
         LAMBDA_PROD, GSYM FST_THM]
    )
QED

Theorem beta_equality_Letrec_alt:
  DISJOINT (boundvars e)
    (BIGUNION (set (MAP (λ(fn,e'). freevars e') fns)) DIFF set (MAP FST fns))
  ⇒ (Letrec fns e ≅? subst (FEMPTY |++ (MAP (λ(g,x). (g,Letrec fns x)) fns)) e) b
Proof
  rw[exp_eq_open_bisimilarity] >>
  irule_at Any SUBSET_REFL >>
  irule_at Any FINITE_DIFF >> simp[MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
  reverse $ conj_asm2_tac
  >- (
    irule SUBSET_TRANS >> irule_at Any freevars_subst_SUBSET >>
    simp[DIFF_SUBSET, FDOM_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    rw[FST_THM] >- simp[SUBSET_DEF] >>
    simp[BIGUNION_SUBSET] >> rw[] >>
    gvs[IN_FRANGE_FLOOKUP, flookup_fupdate_list] >> FULL_CASE_TAC >> gvs[] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >> pairarg_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `freevars x' ∪ foo DIFF _` >>
    qsuff_tac `freevars x' ∪ foo = foo` >- (rw[] >> simp[FST_THM, SUBSET_DEF]) >>
    simp[GSYM SUBSET_UNION_ABSORPTION] >>
    unabbrev_all_tac >> rw[SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD, SF SFY_ss]
    ) >>
  irule open_bisimilarity_suff' >> reverse $ rw[bind_def]
  >- (irule_at Any FINITE_DIFF >> simp[MEM_MAP, PULL_EXISTS, FORALL_PROD]) >>
  qmatch_goalsub_abbrev_tac `subst _ (subst fns_map _)` >> simp[subst_def] >>
  `FDIFF f (set (MAP FST fns)) = f` by (
    rw[fmap_eq_flookup, FLOOKUP_FDIFF] >> rw[FLOOKUP_DEF] >> gvs[]) >>
  simp[app_bisimilarity_eq] >> reverse $ rpt $ conj_asm2_tac
  >- (irule IMP_closed_subst >> simp[IN_FRANGE_FLOOKUP])
  >- (
    simp[EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    rw[EVERY_MEM] >> pairarg_tac >> gvs[] >>
    irule SUBSET_TRANS >> irule_at Any freevars_subst_SUBSET >> rw[DIFF_SUBSET]
    >- (simp[FST_THM] >> rw[SUBSET_DEF, SF DNF_ss, MEM_MAP, EXISTS_PROD, SF SFY_ss])
    >- (
      rw[BIGUNION_SUBSET, PULL_EXISTS, IN_FRANGE_FLOOKUP] >>
      first_x_assum drule >> rw[closed_def]
      )
    )
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    irule SUBSET_TRANS >> irule_at Any freevars_subst_SUBSET >> rw[DIFF_SUBSET]
    >- (simp[FST_THM] >> rw[SUBSET_DEF, SF DNF_ss, MEM_MAP, EXISTS_PROD, SF SFY_ss])
    >- (
      rw[BIGUNION_SUBSET, PULL_EXISTS, IN_FRANGE_FLOOKUP] >>
      first_x_assum drule >> rw[closed_def]
      )
    ) >>
  irule exp_eq_trans >> irule_at Any beta_equality_Letrec >> gvs[] >>
  DEP_REWRITE_TAC[subst_funs_eq_subst] >> simp[] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  qspecl_then [`e`,`fns_map`,`f`] mp_tac subst_distrib >> simp[] >>
  simp[PULL_EXISTS] >> impl_tac
  >- (
    rw[] >> gvs[] >- res_tac >>
    unabbrev_all_tac >> drule $ SRULE [SUBSET_DEF] FRANGE_FUPDATE_LIST_SUBSET >>
    rw[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    qmatch_goalsub_abbrev_tac `_ ∪ foo DIFF _` >>
    `freevars p_2' ∪ foo = foo` by (
      rw[GSYM SUBSET_UNION_ABSORPTION] >>
      unabbrev_all_tac >> simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
      rw[] >> simp[SF SFY_ss]) >>
    simp[Once DISJOINT_SYM]
    ) >>
  rw[] >> unabbrev_all_tac >> simp[o_f_FUPDATE_LIST] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, subst_def] >>
  qmatch_goalsub_abbrev_tac `FDIFF f foo` >>
  qsuff_tac `FDIFF f foo = f` >> rw[exp_eq_refl] >>
  unabbrev_all_tac >> rw[fmap_eq_flookup, FLOOKUP_FDIFF, FDOM_FUPDATE_LIST] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> gvs[FST_THM, FLOOKUP_DEF] >>
  IF_CASES_TAC >> gvs[]
QED

Theorem Let_Seq:
  (Let w e (Seq x y) ≅? Seq (Let w e x) (Let w e y)) b
Proof
  irule eval_wh_IMP_exp_eq \\ rw []
  \\ fs [subst_def,eval_wh_Seq]
  \\ fs [eval_wh_App,eval_wh_Lam,bind1_def]
  \\ rw [] \\ fs [] \\ fs [subst1_def,eval_wh_Seq]
QED

Theorem Seq_assoc:
  (Seq (Seq x y) z ≅? Seq x (Seq y z)) b
Proof
  irule eval_wh_IMP_exp_eq \\ rw []
  \\ fs [subst_def,eval_wh_Seq]
  \\ every_case_tac \\ fs []
QED

Theorem Let_Var:
  (Let w e (Var w) ≅? e) b
Proof
  irule eval_wh_IMP_exp_eq
  \\ fs [subst_def,eval_wh_Seq] \\ rw [] \\ fs []
  \\ fs [eval_wh_App,eval_wh_Lam,bind1_def]
  \\ fs [subst1_def]
  \\ qsuff_tac ‘closed (subst f e)’ \\ fs []
  \\ irule IMP_closed_subst
  \\ fs [FLOOKUP_DEF,FRANGE_DEF,PULL_EXISTS]
QED

Theorem Let_Var2:
  v ≠ w ⇒ (Let w e (Var v) ≅? Var v) b
Proof
  rw [] \\ irule eval_wh_IMP_exp_eq
  \\ fs [subst_def,eval_wh_Seq] \\ rw [] \\ fs []
  \\ fs [eval_wh_App,eval_wh_Lam,bind1_def]
  \\ ‘closed (subst f e)’ by
    (irule IMP_closed_subst
     \\ fs [FLOOKUP_DEF,FRANGE_DEF,PULL_EXISTS])
  \\ fs [DOMSUB_FLOOKUP_THM]
  \\ CASE_TAC \\ fs []
  \\ fs [subst1_def]
  \\ res_tac \\ fs [closed_subst]
QED

Theorem Let_App:
  ∀w e e1 e2 b. (Let w e (App e1 e2) ≅? App (Let w e e1) (Let w e e2)) b
Proof
  rw[exp_eq_def, bind_def] >> rw[] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, subst_def] >>
  gvs[GSYM SUBSET_INSERT_DELETE, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >>
  simp[app_bisimilarity_eq] >> reverse conj_asm2_tac
  >- (
    rename1 ‘subst (f \\ w)’ >>
    ‘∀v. v ∈ FRANGE (f \\ w) ⇒ closed v’
     by (rw [] \\ first_x_assum irule
         \\ gvs [FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM] \\ pop_assum $ irule_at Any) >>
    gvs [IMP_closed_subst, freevars_subst, FRANGE_FLOOKUP] >>
    gvs [SUBSET_DEF, IN_DIFF] >> rw [] >> metis_tac []) >>
  gvs[] >> irule exp_eq_trans >> irule_at Any beta_equality >> simp[] >>
  simp[subst_def] >> irule exp_eq_App_cong >>
  conj_tac >>
  irule eval_IMP_exp_eq >>
  rw[eval_Let, bind1_def] >>
  AP_TERM_TAC >>
  irule closed_subst >>
  irule closed_freevars_subst1 >>
  gvs [freevars_subst]
QED

Theorem Letrec_App:
  ∀l e1 e2 b. (Letrec l (App e1 e2) ≅? App (Letrec l e1) (Letrec l e2)) b
Proof
  rw[exp_eq_def, bind_def] >> rw[] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, subst_def] >>
  gvs[GSYM SUBSET_INSERT_DELETE, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >>
  simp[app_bisimilarity_eq] >> reverse conj_asm2_tac
  >- (rw [MAP_MAP_o, combinTheory.o_DEF, EVERY_EL, EL_MAP] >>
      ‘∀v. v ∈ FRANGE (FDIFF f (set (MAP FST l))) ⇒ closed v’
        by (rw [] >> first_x_assum irule >>
            gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
            pop_assum $ irule_at Any) >>
      gvs [LAMBDA_PROD] >>~[‘EL n l’]
      >- (qabbrev_tac ‘p = EL n l’ >> PairCases_on ‘p’ >>
          gvs [freevars_subst, SUBSET_DEF] >> rpt strip_tac >>
          last_x_assum kall_tac >>
          last_x_assum $ qspecl_then [‘x’] assume_tac >> gvs [MEM_MAP]
          >- (pop_assum $ qspecl_then [‘freevars p1’] assume_tac >> gvs [] >>
              pop_assum $ qspecl_then [‘EL n l’] assume_tac >> gvs [EL_MEM]) >>
          first_x_assum $ irule_at Any >>
          PairCases_on ‘y’ >> fs [])
      >- (qabbrev_tac ‘p = EL n l’ >> PairCases_on ‘p’ >>
          gvs [freevars_subst, SUBSET_DEF] >> rpt strip_tac >>
          last_x_assum kall_tac >>
          last_x_assum $ qspecl_then [‘x’] assume_tac >> gvs [MEM_MAP]
          >- (pop_assum $ qspecl_then [‘freevars p1’] assume_tac >> gvs [] >>
              pop_assum $ qspecl_then [‘EL n l’] assume_tac >> gvs [EL_MEM]) >>
          first_x_assum $ irule_at Any >>
          PairCases_on ‘y’ >> fs [])
      >- (qabbrev_tac ‘p = EL n l’ >> PairCases_on ‘p’ >>
          gvs [freevars_subst, SUBSET_DEF] >> rpt strip_tac >>
          last_x_assum kall_tac >>
          last_x_assum $ qspecl_then [‘x’] assume_tac >> gvs [MEM_MAP]
          >- (pop_assum $ qspecl_then [‘freevars p1’] assume_tac >> gvs [] >>
              pop_assum $ qspecl_then [‘EL n l’] assume_tac >> gvs [EL_MEM]) >>
          first_x_assum $ irule_at Any >>
          PairCases_on ‘y’ >> fs []) >>
      gvs [freevars_subst, SUBSET_DEF, IN_DIFF] >> rw [] >>
      gvs [MEM_MAP, EXISTS_PROD] >>
      rename1 ‘MEM (x, _) _’ >>
      rpt $ first_x_assum $ qspecl_then [‘x’] assume_tac >> gvs [] >>
      first_x_assum $ irule_at Any) >>
  gvs[] >> irule exp_eq_trans >> irule_at Any beta_equality_Letrec >> simp[] >>
  simp[subst_funs_def, bind_def, subst_def] >> IF_CASES_TAC
  >- (irule exp_eq_App_cong >>
      conj_tac >>
      irule exp_eq_trans >>
      irule_at (Pos last) $ iffLR exp_eq_sym >>
      irule_at Any beta_equality_Letrec >>
      gvs [exp_eq_refl, subst_funs_def, bind_def] >>
      rw [exp_eq_refl] >> gvs []) >>
  qsuff_tac ‘F’ >> fs [] >>
  pop_assum irule >>
  ‘∀f. FLOOKUP f n = SOME v ⇒ v ∈ FRANGE f’ by (rw [FRANGE_FLOOKUP] >> pop_assum $ irule_at Any) >>
  pop_assum $ dxrule_then assume_tac >>
  ‘∀(f : string |-> exp) l v. v ∈ FRANGE (f |++ l) ⇒ v ∈ FRANGE f ∪ set (MAP SND l)’
    by (rpt strip_tac >> irule $ iffLR SUBSET_DEF >> irule_at Any FRANGE_FUPDATE_LIST_SUBSET >> fs []) >>
  pop_assum $ dxrule_then assume_tac >>
  gvs [FRANGE_FEMPTY, MEM_EL, EL_MAP, closed_def] >>
  rename1 ‘EL n l’ >> qabbrev_tac ‘p = EL n l’ >> PairCases_on ‘p’ >>
  gvs [SUBSET_DIFF_EMPTY, BIGUNION_SUBSET, SUBSET_DEF, MEM_EL] >> rw [] >>
  gvs [EVERY_MEM, EL_MAP] >>
  first_x_assum irule
  >- (pop_assum $ irule_at Any >>
      gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MEM_EL] >>
      first_assum $ irule_at Any >> fs [EL_MAP]) >>
  rename1 ‘EL n2 l’ >> qabbrev_tac ‘p = EL n2 l’ >> PairCases_on ‘p’ >> fs [MEM_EL] >>
  first_x_assum $ irule_at Any >>
  first_assum $ irule_at Any >> fs [EL_MAP]
QED

Theorem Let_Prim:
  ∀xs b. (Let w e (Prim p xs) ≅? Prim p (MAP (Let w e) xs)) b
Proof
  rw[exp_eq_def, bind_def] >> rw[] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, subst_def] >>
  gvs[GSYM SUBSET_INSERT_DELETE, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >>
  simp[app_bisimilarity_eq] >> reverse conj_asm2_tac
  >- (
    gvs[EVERY_MAP, EVERY_MEM, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >>
    DEP_REWRITE_TAC[freevars_subst, IMP_closed_subst] >>
    simp[IN_FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM] >>
    conj_asm1_tac >- (rw[] >> res_tac) >> rw[] >>
    DEP_REWRITE_TAC[freevars_subst] >>
    simp[IN_FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM] >>
    gvs[SUBSET_DEF] >> metis_tac[]
    ) >>
  gvs[] >> irule exp_eq_trans >> irule_at Any beta_equality >> simp[] >>
  simp[subst_def] >> irule exp_eq_Prim_cong >>
  rw[LIST_REL_EL_EQN, EL_MAP] >>
  irule $ iffLR exp_eq_sym >> irule exp_eq_trans >>
  irule_at Any beta_equality >> simp[exp_eq_refl]
QED

Theorem Let_Prim_alt:
  (Let w e (Prim p []) ≅? Prim p []) param ∧
  (Let w e (Prim p [a]) ≅? Prim p [Let w e a]) param ∧
  (Let w e (Prim p [a;b]) ≅? Prim p [Let w e a; Let w e b]) param ∧
  (Let w e (Prim p [a;b;c]) ≅? Prim p [Let w e a; Let w e b; Let w e c]) param
Proof
  qspec_then ‘[]’ mp_tac Let_Prim \\ rw []
  \\ qspec_then ‘[a]’ mp_tac Let_Prim \\ rw []
  \\ qspec_then ‘[a;b]’ mp_tac Let_Prim \\ rw []
  \\ qspec_then ‘[a;b;c]’ mp_tac Let_Prim \\ rw []
QED

Triviality Letrec_Prim_closed:
  ∀l p xs b. EVERY (λfb. freevars (SND fb) ⊆ set (MAP FST l)) l
         /\ EVERY (\e. freevars e ⊆ set (MAP FST l)) xs ==>
    (Letrec l (Prim p xs) ≅? Prim p (MAP (Letrec l) xs)) b
Proof
  rw []
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality_Letrec
  \\ simp [EVERY_MAP, subst_funs_eq_subst]
  \\ simp [subst_def]
  \\ irule exp_eq_Prim_cong
  \\ rw [LIST_REL_MAP1, LIST_REL_MAP2, combinTheory.o_DEF, EVERY2_refl_EQ]
  \\ ONCE_REWRITE_TAC [exp_eq_sym]
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality_Letrec
  \\ simp [EVERY_MAP, subst_funs_eq_subst]
  \\ irule exp_eq_refl
QED

Theorem Letrec_Prim:
  ∀l ope eL b. (Letrec l (Prim ope eL) ≅? Prim ope (MAP (Letrec l) eL)) b
Proof
  rw[exp_eq_def, bind_def]
  \\ rw []
  \\ simp [subst_def]
  \\ fs [BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, DIFF_SUBSET, FORALL_PROD]
  \\ simp [app_bisimilarity_eq]
  \\ irule_at Any exp_eq_trans \\ irule_at Any Letrec_Prim_closed
  \\ csimp [EVERY_MAP]
  \\ irule_at Any exp_eq_Prim_cong
  \\ conj_tac
  >- (
    simp [LIST_REL_MAP1, LIST_REL_MAP2, combinTheory.o_DEF, EVERY2_refl_EQ]
    \\ simp [subst_def, exp_eq_refl]
  )
  \\ simp [subst_def]
  \\ fs [EVERY_MEM, FORALL_PROD, MEM_MAP, PULL_EXISTS, EXISTS_PROD, BIGUNION_SUBSET]
  \\ rw [] \\ DEP_REWRITE_TAC [freevars_subst]
  \\ simp [FRANGE_FLOOKUP, PULL_EXISTS, FLOOKUP_FDIFF]
  \\ srw_tac [SatisfySimps.SATISFY_ss] []
  \\ fs [SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD]
  \\ metis_tac []
QED

Theorem Proj_Seq:
  (Proj n i e ≅? Seq e (Proj n i e)) b
Proof
  irule eval_wh_IMP_exp_eq
  \\ fs [subst_def,eval_wh_Seq] \\ rw [] \\ fs []
  \\ fs [eval_wh_Proj]
QED

Theorem Seq_id:
  ∀b x. (Seq x x ≅? x) b
Proof
  rpt gen_tac
  \\ irule eval_wh_IMP_exp_eq
  \\ fs [subst_def,eval_wh_Seq] \\ rw [] \\ fs []
QED

Theorem Proj_Cons:
  (Proj s (LENGTH xs) (Cons s (xs ++ y::ys)) ≅? y) b
Proof
  irule eval_wh_IMP_exp_eq \\ rw [subst_def,eval_wh_thm]
  \\ ‘LENGTH xs = LENGTH (MAP (λa. subst f a) xs)’ by fs []
  \\ pop_assum (rewrite_tac o single)
  \\ simp_tac std_ss [EL_LENGTH_APPEND,NULL,HD]
QED

Theorem exp_eq_Tick_cong:
  x ≅ y ⇒ Tick x ≅ y
Proof
  strip_tac
  \\ irule exp_eq_trans
  \\ first_assum (irule_at Any)
  \\ irule eval_wh_IMP_exp_eq
  \\ simp [subst_def, eval_wh_thm, subst_funs_def, FUPDATE_LIST_THM]
QED

Theorem eval_wh_to_Lit[simp]:
  eval_wh_to k (Lit l) = wh_Atom l
Proof
  simp[eval_wh_to_def, get_atoms_def]
QED

Theorem eval_wh_to_atom2:
  eval_wh_to k (Prim (AtomOp opn) [Lit l1; Lit l2]) =
  if k = 0 then wh_Diverge
  else case eval_op opn [l1; l2] of
         NONE => wh_Error
       | SOME (INL v) => wh_Atom v
       | SOME (INR T) => wh_True
       | SOME (INR F) => wh_False
Proof
  rw[eval_wh_to_def] >> simp[get_atoms_def, dest_Atom_def]
QED

Theorem case_someT:
  option_CASE (some x. T) none (λy. v) = v
Proof
  DEEP_INTRO_TAC optionTheory.some_intro >> simp[]
QED

Theorem exp_eq_Add:
  (Prim (AtomOp Add) [Lit (Int i); Lit (Int j)] ≅? Lit (Int (i + j))) b
Proof
  irule eval_wh_IMP_exp_eq >>
  simp[freevars_def, subst_def, eval_wh_def, case_someT, eval_wh_to_atom2] >>
  rpt strip_tac >>
  DEEP_INTRO_TAC optionTheory.some_intro >> simp[AllCaseEqs()]
QED

val _ = export_theory();
