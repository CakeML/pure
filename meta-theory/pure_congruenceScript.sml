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
     pure_exp_lemmasTheory pure_limitTheory
     pure_exp_relTheory pure_alpha_equivTheory;

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

Theorem LIST_REL_open_bisimilarity:
  ∀es es'.
    LIST_REL (open_bisimilarity vars) es es' ⇔
    LIST_REL (open_similarity vars) es es' ∧
    LIST_REL (open_similarity vars) es' es
Proof
  Induct \\ Cases_on ‘es'’ \\ fs [PULL_EXISTS]
  \\ fs [open_bisimilarity_eq] \\ metis_tac []
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
  THEN1
   (fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
    \\ qpat_x_assum ‘∀x. _’ kall_tac
    \\ qpat_x_assum ‘∀x. _’ mp_tac
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
    \\ fs [LIST_REL_open_bisimilarity]
    \\ metis_tac [])
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ fs [LIST_REL_open_bisimilarity]
  \\ metis_tac []
QED

(* -- contextual equivalence -- *)

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

Theorem exp_eq_Prim_cong:
  LIST_REL $≅ xs xs' ⇒
  Prim p xs ≅ Prim p xs'
Proof
  assume_tac Congruence_exp_eq
  \\ fs [Congruence_def,Precongruence_def,Compatible_def,Com4_def]
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ qexists_tac ‘freevars (App (Prim p xs) (Prim p xs'))’
  \\ fs [Exps_def,SUBSET_DEF]
  \\ rw [] \\ fs [MEM_MAP,EXISTS_PROD,FORALL_PROD,PULL_EXISTS]
  \\ metis_tac []
QED

Theorem exp_eq_Letrec_cong:
  LIST_REL $≅ (MAP SND xs) (MAP SND xs') ∧ e ≅ e' ∧ MAP FST xs = MAP FST xs' ⇒
  Letrec xs e ≅ Letrec xs' e'
Proof
  assume_tac Congruence_exp_eq
  \\ fs [Congruence_def,Precongruence_def,Compatible_def,Com5_def]
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ qexists_tac ‘freevars (App (Letrec xs e) (Letrec xs' e'))’
  \\ fs [Exps_def,SUBSET_DEF]
  \\ reverse conj_tac
  THEN1 (fs [IN_DISJOINT] \\ metis_tac [])
  \\ rw [] \\ fs [MEM_MAP,EXISTS_PROD,FORALL_PROD,PULL_EXISTS]
  \\ metis_tac []
QED

Theorem exp_eq_subst:
  y1 ≅ y2 ∧ closed y1 ∧ closed y2 ⇒
  subst x y1 e1 ≅ subst x y2 e1
Proof
  rw [] \\ qid_spec_tac ‘e1’
  \\ ho_match_mp_tac freevars_ind \\ rw []
  THEN1 (fs [subst_def,FLOOKUP_UPDATE] \\ rw [exp_eq_refl])
  THEN1 (fs [subst_def] \\ match_mp_tac exp_eq_Prim_cong \\ fs []
         \\ Induct_on ‘es’ \\ fs [])
  THEN1 (fs [subst_def] \\ match_mp_tac exp_eq_App_cong \\ fs [])
  THEN1 (fs [subst_def,DOMSUB_FUPDATE_THM] \\ rw [exp_eq_refl]
         \\ match_mp_tac exp_eq_Lam_cong \\ fs [])
  \\ fs [subst_def]
  \\ match_mp_tac exp_eq_Letrec_cong
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
  \\ ‘∀y s. FDIFF (FEMPTY |+ (x,y:exp)) s =
            if x IN s then FEMPTY else FEMPTY |+ (x,y)’ by
   (fs [fmap_EXT] \\ rw [FDOM_FDIFF,EXTENSION]
    THEN1 (rw [] \\ eq_tac \\ rw [])
    \\ fs [FDIFF_def])
  \\ fs [] \\ IF_CASES_TAC \\ fs [exp_eq_refl]
  THEN1 (qid_spec_tac ‘lcs’ \\ Induct \\ fs [exp_eq_refl,FORALL_PROD])
  \\ Induct_on ‘lcs’ \\ fs [FORALL_PROD] \\ rw []
  \\ fs [PULL_FORALL]
  \\ first_x_assum match_mp_tac
  \\ metis_tac []
QED

Theorem exp_eq_Lam_basic_lemma[local]:
  Lam x e1 ≅ Lam x e2 ⇔
  ∀y. closed y ⇒ subst x y e1 ≅ subst x y e2
Proof
  fs [exp_eq_def] \\ eq_tac \\ rw []
  THEN1
   (rw [bind_def]
    \\ first_x_assum (qspec_then ‘f’ mp_tac)
    \\ fs [bind_def]
    \\ reverse IF_CASES_TAC THEN1 (rfs [] \\ res_tac \\ fs [])
    \\ fs [] \\ impl_tac THEN1 (gvs [freevars_subst,SUBSET_DEF])
    \\ fs [subst_def]
    \\ simp [Once app_bisimilarity_iff] \\ fs [eval_thm]
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
    \\ metis_tac [])
  \\ rw [bind_def]
  \\ fs [subst_def,PULL_FORALL,AND_IMP_INTRO]
  \\ simp [Once app_bisimilarity_iff] \\ fs [eval_thm]
  \\ fs [GSYM subst_def,CONJ_ASSOC]
  \\ conj_tac
  THEN1
   (rw [] \\ match_mp_tac IMP_closed_subst
    \\ fs [FLOOKUP_DEF,FRANGE_DEF,PULL_EXISTS])
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
  Lam x e1 ≅ Lam x e2 ⇔
  ∀y1 y2.
    y1 ≅ y2 ∧ closed y1 ∧ closed y2 ⇒
    subst x y1 e1 ≅ subst x y2 e2
Proof
  fs [exp_eq_Lam_basic_lemma] \\ reverse eq_tac \\ rw []
  THEN1 (first_x_assum match_mp_tac \\ fs [exp_eq_refl])
  \\ match_mp_tac exp_eq_trans
  \\ first_x_assum drule \\ rw []
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ match_mp_tac exp_eq_subst \\ fs []
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
  rw [] \\ match_mp_tac exp_eq_subst \\ fs [closed_perm]
  \\ match_mp_tac exp_eq_perm \\ fs [closed_def]
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

val _ = export_theory();
