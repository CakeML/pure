(*
   Verification of pure_letrec, i.e. simplification of Letrec.
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_exp_lemmasTheory pure_exp_relTheory pure_evalTheory
     pure_congruenceTheory pure_miscTheory;
(* from CakeML: *)
open mlmapTheory mlstringTheory;

val _ = new_theory "pure_letrecProof";

(*
  TODO: move the implementation to ../pure_letrecScript.sml once it's done.
*)

(*

  The motivation for these Letrec simplifications is that the parser
  will produce a giant Letrec holding all the top-level functions. It
  makes sense to split this up and clean it up as much as possible early.

  Plan for the Letrec simplifications:

    1. make a pass that ensures, for every Letrec xs y, that
       ALL_DISTINCT (MAP FST xs)

    2. split every Letrec according to top_sort_any, i.e. each Letrec becomes
       one or more nested Letrecs

    3. clean up pass:
        - remove any Letrec xs y that only bind variables that are not free in y
        - change any Letrec [(v,x)] y into Let v x y, when v not free in x

*)

Definition make_distinct_def:
  (* this could be written in a more efficient way, but perhaps this is good
     for the proofs, i.e. the implementation version might be different *)
  make_distinct [] = [] ∧
  make_distinct ((n:string,x)::xs) =
    if MEM n (MAP FST xs) then make_distinct xs else (n,x)::make_distinct xs
End

Definition distinct_def:
  distinct (Letrec xs y) =
    Letrec (make_distinct (MAP (λ(n,x). (n, distinct x)) xs)) y ∧
  distinct (Lam n x) = Lam n (distinct x) ∧
  distinct (Prim p xs) = Prim p (MAP distinct xs) ∧
  distinct (App x y) = App (distinct x) (distinct y) ∧
  distinct res = res
Termination
  WF_REL_TAC ‘measure exp_size’ >> rw [] >>
  Induct_on `xs` >> rw[] >> gvs[exp_size_def]
End

Theorem set_MAP_FST_make_distinct:
  ∀xs. set (MAP FST (make_distinct xs)) = set (MAP FST xs)
Proof
  Induct \\ fs [make_distinct_def,FORALL_PROD]
  \\ rw [] \\ fs [EXTENSION] \\ metis_tac []
QED

Triviality MEM_MAP_FST_make_distinct =
  set_MAP_FST_make_distinct |> SIMP_RULE std_ss [EXTENSION];

Theorem MEM_make_distinct:
  ∀x xs. MEM x (make_distinct xs) ⇒ MEM x xs
Proof
  strip_tac >> Induct >> rw[make_distinct_def] >>
  PairCases_on `h` >> gvs[make_distinct_def] >>
  EVERY_CASE_TAC >> gvs[]
QED

Theorem make_distinct_ALL_DISTINCT:
  ∀l. ALL_DISTINCT (make_distinct l)
Proof
  Induct >> rw[make_distinct_def] >>
  PairCases_on `h` >> rw[make_distinct_def, ALL_DISTINCT] >>
  gvs[Once (GSYM MEM_MAP_FST_make_distinct)] >>
  gvs[MEM_MAP, FORALL_PROD, PULL_EXISTS]
QED

Theorem freevars_distinct:
  ∀x. freevars (distinct x) ⊆ freevars x
Proof
  recInduct distinct_ind >> rw[distinct_def] >>
  gvs[set_MAP_FST_make_distinct, SUBSET_DEF] >> rw[] >> gvs[MEM_FILTER]
  >- (
    gvs[MEM_FLAT, MEM_MAP, FORALL_PROD] >>
    imp_res_tac MEM_make_distinct >> gvs[MEM_MAP, FORALL_PROD] >>
    simp[PULL_EXISTS, EXISTS_PROD] >>
    rename1 `MEM z _` >> PairCases_on `z` >> gvs[] >>
    DISJ2_TAC >> goal_assum (drule_at Any) >>
    last_x_assum irule >> simp[] >> goal_assum drule
    )
  >- gvs[MEM_MAP, FORALL_PROD]
  >- gvs[MEM_MAP, FORALL_PROD]
  >- (
    gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
    goal_assum (drule_at Any) >>
    last_x_assum irule >> simp[]
    )
QED

Theorem closed_distinct:
  ∀x. closed x ⇒ closed (distinct x)
Proof
  rw[closed_def, NIL_iff_NOT_MEM] >>
  CCONTR_TAC >> last_x_assum mp_tac >> gvs[] >> rename1 `MEM y _` >>
  drule (freevars_distinct |> SIMP_RULE std_ss [SUBSET_DEF]) >> strip_tac >>
  goal_assum drule
QED

Triviality ALOOKUP_REVERSE_make_distinct:
  ∀l x. ALOOKUP (REVERSE (make_distinct l)) x = ALOOKUP (REVERSE l) x
Proof
  Induct >> rw[make_distinct_def] >>
  PairCases_on `h` >> gvs[make_distinct_def] >>
  IF_CASES_TAC >> simp[ALOOKUP_APPEND] >>
  EVERY_CASE_TAC >> gvs[ALOOKUP_NONE, MEM_MAP, DISJ_EQ_IMP]
QED

Theorem make_distinct_FUPDATE_LIST:
  ∀f l.  f |++ (make_distinct l) = f |++ l
Proof
  rw[fmap_eq_flookup, flookup_fupdate_list] >>
  qspec_then `l` assume_tac ALOOKUP_REVERSE_make_distinct >> simp[]
QED

Triviality make_distinct_Letrec_exp_eq:
  ∀xs y.  Letrec xs y ≅ Letrec (make_distinct xs) y
Proof
  rw[] >> irule exp_eq_Letrec_cong2 >>
  simp[make_distinct_FUPDATE_LIST, exp_eq_refl]
QED

Theorem distinct_exp_eq:
  ∀x. x ≅ distinct x
Proof
  recInduct distinct_ind >> rw[distinct_def] >> gvs[]
  >- (
    irule exp_eq_Letrec_cong2 >>
    simp[exp_eq_refl, make_distinct_FUPDATE_LIST] >>
    irule fmap_rel_FUPDATE_LIST_same >> simp[] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[] >>
    rw[LIST_REL_EL_EQN, EL_MAP] >> last_x_assum irule >>
    qexists_tac `FST (EL n xs)` >> simp[EL_MEM]
    )
  >- (irule exp_eq_Lam_cong >> simp[])
  >- (
    irule exp_eq_Prim_cong >> simp[] >>
    rw[LIST_REL_EL_EQN, EL_MAP] >> last_x_assum irule >> simp[EL_MEM]
    )
  >- (irule exp_eq_App_cong >> simp[])
  >- simp[exp_eq_Var_cong]
QED

Theorem distinct_correct:
  closed x ⇒ x ≃ distinct x
Proof
  rw[app_bisimilarity_eq, distinct_exp_eq] >>
  irule closed_distinct >> simp[]
QED

(* some infrastructure for the proofs *)

Inductive letrec_rel:
  (∀n.
    letrec_rel c (Var n) (Var n))
  ∧
  (∀n x y.
    letrec_rel c x y ⇒
    letrec_rel c (Lam n x) (Lam n y))
  ∧
  (∀f g x y.
    letrec_rel c f g ∧ letrec_rel c x y ⇒
    letrec_rel c (App f x) (App g y))
  ∧
  (∀n xs ys.
    LIST_REL (letrec_rel c) xs ys ⇒
    letrec_rel c (Prim n xs) (Prim n ys))
  ∧
  (∀xs y xs1 y1 z.
    LIST_REL (letrec_rel c) (MAP SND xs) (MAP SND xs1) ∧
    MAP FST xs = MAP FST xs1 ∧ letrec_rel c y y1 ∧
    (c (Letrec xs1 y1) z ∨ Letrec xs1 y1 = z) ⇒
    letrec_rel c (Letrec xs y) z)
End

Theorem letrec_rel_refl:
  ∀x c. letrec_rel c x x
Proof
  recInduct freevars_ind >> rw[]
  >- simp[Once letrec_rel_cases]
  >- (
    simp[Once letrec_rel_cases, LIST_REL_EL_EQN] >> rw[] >>
    last_x_assum irule >> simp[EL_MEM]
    )
  >- simp[Once letrec_rel_cases]
  >- simp[Once letrec_rel_cases]
  >- (
    simp[Once letrec_rel_cases, LIST_REL_EL_EQN] >> rw[] >>
    irule_at Any EQ_REFL >> simp[] >> qexists_tac `e` >> simp[] >> rw[] >>
    last_x_assum irule >> simp[EL_MAP] >>
    qexists_tac `FST (EL n lcs)` >> simp[EL_MEM]
    )
QED

Theorem SND_THM:
  SND = λ(x,y). y
Proof
  irule EQ_EXT >> rw[] >>
  PairCases_on `x` >> rw[]
QED

Theorem letrec_rel_subst:
  ∀c x y. letrec_rel c x y ⇒
    (∀f a b. c a b ⇒ c (subst f a) (subst f b))
  ⇒ ∀f. letrec_rel c (subst f x) (subst f y)
Proof
  strip_tac >> ho_match_mp_tac letrec_rel_ind >> rw[subst_def]
  >- rw[letrec_rel_refl]
  >- simp[Once letrec_rel_cases]
  >- simp[Once letrec_rel_cases]
  >- (simp[Once letrec_rel_cases] >> gvs[LIST_REL_EL_EQN] >> rw[EL_MAP])
  >- (
    simp[Once letrec_rel_cases] >> gvs[] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    qpat_abbrev_tac `foo = λ(p1,p2). _ p2` >>
    qexists_tac `MAP (λ(x,y). (x,foo (x,y))) xs1` >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    simp[GSYM LAMBDA_PROD] >>
    first_x_assum (irule_at Any) >> gvs[LIST_REL_EL_EQN, EL_MAP] >>
    unabbrev_all_tac >> reverse (rw[])
    >- (disj1_tac >> first_x_assum drule >> simp[subst_def]) >>
    qmatch_goalsub_abbrev_tac `letrec_rel _ (_ a) (_ b)` >>
    PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
    last_x_assum drule >> strip_tac >> gvs[]
    )
  >- (
    simp[subst_def] >> gvs[] >>
    simp[Once letrec_rel_cases] >> gvs[] >>
    first_assum (irule_at Any) >> simp[] >>
    irule_at Any OR_INTRO_THM2 >>
    irule_at Any EQ_REFL >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    qmatch_goalsub_abbrev_tac `letrec_rel _ (_ a) (_ b)` >>
    PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
    last_x_assum drule >> gvs[]
    )
QED

Theorem letrec_rel_subst_single:
    letrec_rel c x y ∧
    (∀f a b. c a b ⇒ c (subst f a) (subst f b))
  ⇒ letrec_rel c (subst s e x) (subst s e y)
Proof
  rw[] >> irule letrec_rel_subst >> simp[]
QED

(* xs mappings can be split into xs1, xs2 such that things in xs1 do not
   depend on xs2 - i.e. xs1 mentions no vars defined in xs2 *)
Definition valid_split_def:
  valid_split xs xs1 xs2 ⇔
    ALL_DISTINCT (MAP FST xs) ∧ ALL_DISTINCT (MAP FST xs1 ++ MAP FST xs2) ∧
    set xs = set xs1 UNION set xs2 ∧
    DISJOINT (set (MAP FST xs2)) (BIGUNION (set (MAP (λ(_,e). freevars e) xs1)))
End

Definition Lets_def:
  Lets [] b = b ∧
  Lets ((v,x)::xs) b = Let v x (Lets xs b)
End

Inductive letrec_split:
  (∀xs xs1 xs2 x.
     valid_split xs xs1 xs2 ∧ closed (Letrec xs x) ⇒
     letrec_split
       (Letrec xs x)
       (subst (FEMPTY |++ (MAP (λ(a,A). (a, Letrec xs A)) xs1))
          (Letrec xs2 x)))
End

Theorem letrec_split_subst:
  ∀f g a b. letrec_split a b ⇒ letrec_split (subst f a) (subst g b)
Proof
  rw[Once letrec_split_cases] >> imp_res_tac valid_split_def >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[closed_subst] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[closed_subst] >> reverse (rw[])
  >- (rw[letrec_split_cases] >> irule_at Any EQ_REFL >> simp[]) >>
  simp[closed_def] >> once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
  simp[SUBSET_DIFF_EMPTY, FDOM_FUPDATE_LIST,
       MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  simp[GSYM FST_THM, DIFF_SUBSET] >> rw[]
  >- (
    drule (FRANGE_FUPDATE_LIST_SUBSET |> SIMP_RULE std_ss [SUBSET_DEF]) >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    gvs[MEM_MAP] >> rw[] >> PairCases_on `y` >> gvs[] >>
    gvs[EVERY_MEM] >> last_x_assum irule >> gvs[MEM_MAP, EXTENSION] >>
    irule_at Any OR_INTRO_THM1 >> goal_assum drule >> simp[]
    )
  >- (
    gvs[EXTENSION, SUBSET_DEF] >> rw[] >> last_x_assum drule >>
    gvs[MEM_MAP] >> metis_tac[]
    )
  >- (
    gvs[SUBSET_DEF, EVERY_MEM] >> rw[] >> rename1 `z ∈ s` >>
    qsuff_tac `MEM z (MAP FST xs)` >- (gvs[MEM_MAP] >> metis_tac[]) >>
    first_x_assum irule >> gvs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
    goal_assum (drule_at Any) >>
    irule_at Any OR_INTRO_THM2 >> goal_assum drule >> simp[]
    )
QED

Theorem letrec_rel_split_subst:
  letrec_rel letrec_split x y ⇒
  letrec_rel letrec_split (subst s e x) (subst s e y)
Proof
  rw[] >> irule letrec_rel_subst >> simp[letrec_split_subst]
QED

Theorem valid_split_FDIFF:
  valid_split ys ys1 ys2 ⇒
  FDIFF (FEMPTY |++ MAP (λ(g,x). (g,Letrec ys1 x)) ys1) (set (MAP FST ys2)) =
  FEMPTY |++ MAP (λ(g,x). (g,Letrec ys1 x)) ys1
Proof
  rw[valid_split_def, FDIFF_def] >> irule disjoint_drestrict >>
  simp[FDOM_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF,
       LAMBDA_PROD, FST_THM] >>
  gvs[PULL_EXISTS, GSYM FST_THM, MEM_MAP, DISJOINT_DEF, EXTENSION,
      ALL_DISTINCT_APPEND] >>
  metis_tac[]
QED

Theorem exp_eq_closed_Lets_subst:
  ∀l e.
    EVERY (closed o SND) l
  ⇒ subst (FEMPTY |++ l) e ≅ Lets l e
Proof
  recInduct Lets_ind >> rw[Lets_def, FUPDATE_LIST_THM, exp_eq_refl] >>
  simp[Once fupdate_list_funion] >>
  dep_rewrite.DEP_REWRITE_TAC[GSYM subst_subst_FUNION] >>
  rw[] >> gvs[]
  >- (
    drule (FRANGE_FUPDATE_LIST_SUBSET |> SIMP_RULE std_ss [SUBSET_DEF]) >>
    simp[MEM_MAP] >> strip_tac >> gvs[EVERY_MEM]
    ) >>
  drule beta_equality >> strip_tac >>
  irule exp_eq_trans >>
  qexists_tac `Let v x (subst (FEMPTY |++ xs) b)` >>
  simp[Once exp_eq_sym] >>
  irule exp_eq_App_cong >> simp[exp_eq_refl] >>
  irule exp_eq_Lam_cong >> simp[]
QED

Theorem letrec_split_correct:
  letrec_rel letrec_split x y ∧ closed x ∧ closed y ⇒ x ≃ y
Proof
  rw [] \\ irule eval_to_sim_thm \\ fs []
  \\ qexists_tac ‘letrec_rel letrec_split’ \\ fs []
  \\ simp [eval_to_sim_def]
  \\ rpt (pop_assum kall_tac)
  \\ qabbrev_tac ‘c = letrec_split’
  \\ gen_tac \\ gen_tac
  \\ qid_spec_tac ‘e1’
  \\ qid_spec_tac ‘k’
  \\ ho_match_mp_tac eval_wh_to_ind \\ rw []
  THEN1
   (rename [‘Lam s x’]
    \\ qpat_x_assum ‘letrec_rel c _ _’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ rw []
    \\ fs [eval_wh_to_def]
    \\ unabbrev_all_tac
    \\ fs [letrec_rel_split_subst])
  THEN1
   (rename [‘App x1 x2’]
    \\ qpat_x_assum ‘letrec_rel c _ _’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ rw [] \\ fs []
    \\ fs [eval_wh_to_def]
    \\ Cases_on ‘eval_wh_to k x1 = wh_Diverge’
    THEN1 (fs [] \\ res_tac \\ qexists_tac ‘ck’ \\ fs [])
    \\ fs []
    \\ first_x_assum drule \\ fs [] \\ rw []
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k x1)’ \\ fs []
    THEN1
     (fs [AllCaseEqs()] \\ qexists_tac ‘ck’ \\ fs []
      \\ Cases_on ‘eval_wh_to k x1’ \\ fs [])
    \\ Cases_on ‘eval_wh_to k x1’ \\ gvs []
    \\ rename [‘eval_wh_to (ck + k) g = wh_Closure _ e1’]
    \\ ‘letrec_rel c (bind s x2 e) (bind s y e1)’ by
        (
          fs [bind_single_def] \\ cheat (* TODO *)
        )
    \\ Cases_on ‘k’ \\ fs []
    THEN1 (qexists_tac ‘0’ \\ fs [] >>
      IF_CASES_TAC >> simp[] >>
      drule eval_wh_inc >> disch_then (qspec_then `ck` (assume_tac o GSYM)) >>
      gvs[])
    \\ fs [ADD1]
    \\ last_x_assum drule \\ fs []
    \\ impl_tac THEN1 (
        simp[bind_single_def] >>
        cheat (* TODO *)
        )
    \\ strip_tac
    \\ Cases_on ‘eval_wh_to n (bind s x2 e) = wh_Diverge’ \\ fs []
    THEN1
     (qexists_tac ‘ck'’ \\ fs [] \\ IF_CASES_TAC \\ fs [] >>
      drule eval_wh_to_agree >>
      disch_then (qspec_then `ck + (n + 1)` (assume_tac o GSYM)) >>
      gvs[])
    \\ qexists_tac ‘ck+ck'’
    \\ ‘eval_wh_to (ck + (n + 1) + ck') g = wh_Closure s e1’ by (
          qspecl_then [`ck + (n + 1) + ck'`,`g`,`ck + (n + 1)`]
            assume_tac eval_wh_inc >>
          gvs[])
    \\ fs [] \\ Cases_on ‘eval_wh_to n (bind s x2 e)’ \\ fs []
    \\ ‘eval_wh_to (ck + (ck' + n)) (bind s y e1) =
        eval_wh_to (ck' + n) (bind s y e1)’ by (
          irule eval_wh_inc >> simp[]) >>
        fs[])
  THEN1
   (rename [‘Letrec f y’]
    \\ qpat_x_assum ‘letrec_rel c _ _’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ reverse (rw []) \\ fs []
    THEN1
     (Cases_on ‘k’ \\ fs [eval_wh_to_def]
      THEN1 (qexists_tac ‘0’ \\ fs []) \\ fs [ADD1]
      \\ ‘letrec_rel c (subst_funs f y) (subst_funs xs1 y1)’ by cheat
      \\ first_x_assum drule \\ fs []
      \\ impl_tac THEN1 cheat (* closedness *)
      \\ rw [])
    \\ unabbrev_all_tac
    \\ pop_assum mp_tac
    THEN1
     (simp [Once letrec_split_cases] \\ rw []
      \\ cheat (* crucial part *))
    \\ all_tac (* more here in case letrec_split gets more cases *))
  \\ rename [‘Prim p xs’] >>
     qpat_x_assum `letrec_rel c _ _` mp_tac >>
     simp[Once letrec_rel_cases] >> rw[]
     \\ cheat
QED

Theorem valid_split_thm:
  valid_split xs xs1 xs2 ∧ closed (Letrec xs x) ⇒
  Letrec xs x ≃ Lets (MAP (λ(a,A). (a, Letrec xs A)) xs1) (Letrec xs2 x)
Proof
  rw [] \\ match_mp_tac app_bisimilarity_trans
  \\ qexists_tac ‘subst (FEMPTY |++ (MAP (λ(a,A). (a, Letrec xs A)) xs1)) (Letrec xs2 x)’
  \\ ‘closed (subst (FEMPTY |++ MAP (λ(a,A). (a,Letrec xs A)) xs1) (Letrec xs2 x))’ by (
        imp_res_tac valid_split_def >>
        simp[closed_def] >> once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
        dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >>
        simp[FDOM_FUPDATE_LIST, SUBSET_DIFF_EMPTY, DIFF_SUBSET] >> rw[]
        >- (
          drule (FRANGE_FUPDATE_LIST_SUBSET |> SIMP_RULE std_ss [SUBSET_DEF]) >>
          simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
          gvs[MEM_MAP] >> rw[] >> PairCases_on `y` >> gvs[] >>
          gvs[EVERY_MEM] >> last_x_assum irule >> gvs[MEM_MAP, EXTENSION] >>
          irule_at Any OR_INTRO_THM1 >> goal_assum drule >> simp[]
          )
        >- (
          gvs[EXTENSION, SUBSET_DEF] >> rw[] >> last_x_assum drule >>
          simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
          gvs[MEM_MAP] >> metis_tac[]
          )
        >- (
          gvs[SUBSET_DEF, EVERY_MEM] >> rw[] >> rename1 `z ∈ s` >>
          simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
          qsuff_tac `MEM z (MAP FST xs)` >- (gvs[MEM_MAP] >> metis_tac[]) >>
          first_x_assum irule >> gvs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
          goal_assum (drule_at Any) >>
          irule_at Any OR_INTRO_THM2 >> goal_assum drule >> simp[]
          ))
  \\ conj_tac
  THEN1
   (match_mp_tac letrec_split_correct \\ fs []
    \\ once_rewrite_tac [letrec_rel_cases] \\ fs []
    \\ qexists_tac ‘xs’ \\ qexists_tac ‘x’ \\ fs []
    \\ fs [letrec_split_cases]
    \\ rw []
    THEN1 rw[LIST_REL_EL_EQN, letrec_rel_refl]
    THEN1 rw[letrec_rel_refl]
    \\ disj1_tac \\ metis_tac [])
  \\ reverse (rw[app_bisimilarity_eq])
    >- (
      gvs[valid_split_def, MEM_MAP, PULL_EXISTS] >>
      cheat
      ) >>
     irule exp_eq_closed_Lets_subst >>
     gvs[EVERY_MEM, MEM_MAP, EXTENSION, valid_split_def, PULL_EXISTS] >>
     rw[] >> PairCases_on `y` >> gvs[] >>
     res_tac >> fs[] >>
     gvs[EVERY_MEM, MEM_MAP] >>
     metis_tac[]
QED

(* This lemma would allow us to verify a top_sort_any application anywhere
   in the program. See proof idea below. *)
Theorem Letrec_Letrec:
  valid_split xs xs1 xs2 ⇒
  Letrec xs y ≅ Letrec xs1 (Letrec xs2 y)
Proof
  cheat
QED

(*

Proof idea based on two examples:

Example 1:

Let's assume that A is an expression where only a is free
also assume that B is an expressions where a and b are free.

   Letrec [(a,A);(b,B)] r
 ≃ (* due to something like valid_split_thm *)
   subst a (Letrec [(a,A);(b,B)] A) (Letrec [(b,B)] r)
 ≃ (* easy *)
   Let a (Letrec [(a,A);(b,B)] A) (Letrec [(b,B)] r)
 ≃ (* because b is not reachable from A *)
   Let a (Letrec [(a,A)] A) (Letrec [(b,B)] r)
 ≃ (* easy *)
   Letrec [(a,A)] (Letrec [(b,B)] r)

Example 2:

Now let's consider a slightly more interesting case: below A1 and A2
both have a1 and a2 free, and B has a1, a2, b free.

   Letrec [(a1,A1);(a2,A2);(b,B)] r
 ≃ (* due to something like valid_split_thm *)
   subst (a1 -> (Letrec [(a1,A1);(a2,A2);(b,B)] A1);
          a2 -> (Letrec [(a1,A1);(a2,A2);(b,B)] A2))
     (Letrec [(b,B)] r)
 ≃ (* easy *)
   Let a1 (Letrec [(a1,A1);(a2,A2);(b,B)] A1)
   Let a2 (Letrec [(a1,A1);(a2,A2);(b,B)] A2)
     (Letrec [(b,B)] r)
 ≃ (* because b is not reachable from A1 and A2 *)
   Let a1 (Letrec [(a1,A1);(a2,A2)] A1)
   Let a2 (Letrec [(a1,A1);(a2,A2)] A2)
     (Letrec [(b,B)] r)
 ≃ (* easy *)
   Letrec [(a1,A1);(a2,A2)] (Letrec [(b,B)] r)

*)

val _ = export_theory();
