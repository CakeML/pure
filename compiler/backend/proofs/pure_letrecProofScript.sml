(*
   Verification of pure_letrec, i.e. simplification of Letrec.
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_exp_lemmasTheory pure_exp_relTheory pure_evalTheory
     pure_congruenceTheory pure_miscTheory pure_eval_lemmasTheory;
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

(* xs mappings can be split into xs1, xs2 such that things in xs1 do not
   depend on xs2 - i.e. xs1 mentions no vars defined in xs2 *)
Definition valid_split_def:
  valid_split xs xs1 xs2 ⇔
    ALL_DISTINCT (MAP FST xs) ∧ ALL_DISTINCT (MAP FST xs1 ++ MAP FST xs2) ∧
    set xs = set xs1 UNION set xs2 ∧
    DISJOINT (set (MAP FST xs2)) (BIGUNION (set (MAP (λ(_,e). freevars e) xs1)))
End

Theorem trivial_valid_split:
  ∀l. ALL_DISTINCT (MAP FST l)
  ⇒ valid_split l l [] ∧
    valid_split l [] l
Proof
  rw[valid_split_def] >> simp[]
QED

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
          (Letrec xs2 x))) ∧
  (∀xs xs1 xs2 x.
     valid_split xs xs1 xs2 ∧ closed (Letrec xs x) ∧
     freevars x ⊆ set (MAP FST xs1) ⇒
     letrec_split
       (Letrec xs x)
       (Letrec xs1 x))
End

Theorem letrec_split_subst:
  ∀f g a b. letrec_split a b ⇒ letrec_split (subst f a) (subst g b)
Proof
  rw[Once letrec_split_cases] >> imp_res_tac valid_split_def
  THEN1
   (dep_rewrite.DEP_ONCE_REWRITE_TAC[closed_subst] >>
    dep_rewrite.DEP_ONCE_REWRITE_TAC[closed_subst] >> reverse (rw[])
    >- (rw[letrec_split_cases] >> disj1_tac >> irule_at Any EQ_REFL >> simp[]) >>
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
     ))
  >- (
    dep_rewrite.DEP_ONCE_REWRITE_TAC[closed_subst] >>
    dep_rewrite.DEP_ONCE_REWRITE_TAC[closed_subst] >> reverse (rw[])
    >- (simp[Once letrec_split_cases] >> DISJ2_TAC >> goal_assum drule) >>
    gvs[EVERY_MEM, SUBSET_DEF, EXTENSION] >> rw[] >> rename1 `MEM z _` >>
    `MEM e (MAP SND xs)` by metis_tac[MEM_MAP] >>
    last_x_assum drule >> disch_then drule >>
    simp[MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >> rw[]
    >- goal_assum drule >>
    qpat_x_assum `MEM _ (MAP _ xs1)` mp_tac >>
    qpat_x_assum `∀s._` mp_tac >> simp[MEM_MAP, PULL_EXISTS] >> rw[] >>
    first_x_assum drule >> simp[DISJOINT_DEF, EXTENSION] >> pairarg_tac >>
    gvs[] >> simp[MEM_MAP, PULL_EXISTS, DISJ_EQ_IMP] >>
    disch_then drule >> simp[]
    )
QED

Theorem letrec_rel_split_subst:
  ∀x y. letrec_rel letrec_split x y ⇒
    ∀f g. fmap_rel (letrec_rel letrec_split) f g
  ⇒ letrec_rel letrec_split (subst f x) (subst g y)
Proof
  ho_match_mp_tac letrec_rel_ind >> rw[subst_def] >>
  qabbrev_tac `spl = letrec_split`
  >- (
    gvs[fmap_rel_OPTREL_FLOOKUP] >>
    last_x_assum (qspec_then `n` assume_tac) >>
    EVERY_CASE_TAC >> gvs[letrec_rel_refl]
    )
  >- (
    simp[Once letrec_rel_cases] >>
    last_x_assum irule >>
    gvs[fmap_rel_OPTREL_FLOOKUP, DOMSUB_FLOOKUP_THM] >>
    rw[] >> EVERY_CASE_TAC >> gvs[]
    )
  >- simp[Once letrec_rel_cases]
  >- (simp[Once letrec_rel_cases] >> gvs[LIST_REL_EL_EQN] >> rw[EL_MAP])
  >- (
    simp[Once letrec_rel_cases] >> gvs[] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    qexists_tac
      `(MAP (λ(p1,p2). (p1,subst (FDIFF f (set (MAP FST xs1))) p2)) xs1)` >>
    qexists_tac `subst (FDIFF f (set (MAP FST xs1))) y` >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    gvs[LIST_REL_EL_EQN] >> rw[]
    >- (
      rw[] >> gvs[EL_MAP] >> last_x_assum drule >>
      qabbrev_tac `a = EL n xs` >> qabbrev_tac `b = EL n xs1` >>
      PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
      disch_then irule >>
      gvs[fmap_rel_OPTREL_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >> rw[] >>
      Cases_on `FLOOKUP f k` >> gvs[letrec_rel_refl]
      )
    >- (
      first_x_assum irule >>
      gvs[fmap_rel_OPTREL_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >> rw[] >>
      Cases_on `FLOOKUP f k` >> gvs[letrec_rel_refl]
      )
    >- (
      disj1_tac >> unabbrev_all_tac >>
      drule letrec_split_subst >>
      disch_then (qspecl_then [`f`,`g`] assume_tac) >>
      gvs[subst_def]
      )
    )
  >- (
    simp[subst_def] >> gvs[] >>
    simp[Once letrec_rel_cases] >> gvs[] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    qexists_tac
      `MAP (λ(f',e). (f',subst (FDIFF g (set (MAP FST xs1))) e)) xs1` >>
    qexists_tac `subst (FDIFF g (set (MAP FST xs1))) y` >> simp[] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    first_assum (irule_at Any) >>
    gvs[LIST_REL_EL_EQN] >> rw[]
    >- (gvs[fmap_rel_OPTREL_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >> rw[]) >>
    last_x_assum drule >> gvs[EL_MAP] >>
    qabbrev_tac `a = EL n xs` >> qabbrev_tac `b = EL n xs1` >>
    PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
    disch_then irule >>
    gvs[fmap_rel_OPTREL_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >> rw[]
    )
QED

Triviality letrec_rel_split_subst_single:
  letrec_rel letrec_split x y ∧
  letrec_rel letrec_split a b ⇒
  letrec_rel letrec_split (subst s a x) (subst s b y)
Proof
  rw[] >> irule letrec_rel_split_subst >> simp[] >>
  simp[fmap_rel_OPTREL_FLOOKUP, FLOOKUP_UPDATE] >> rw[]
QED


(*
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
*)


Theorem valid_split_FDIFF:
  valid_split ys ys1 ys2 ⇒
  FDIFF (FEMPTY |++ MAP (λ(g,x). (g,Letrec ys x)) ys1) (set (MAP FST ys2)) =
  FEMPTY |++ MAP (λ(g,x). (g,Letrec ys x)) ys1
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

Theorem Lets_APPEND:
  ∀l1 e l2. Lets (l1 ++ l2) e = Lets l1 (Lets l2 e)
Proof
  recInduct Lets_ind >> rw[Lets_def]
QED

Theorem freevars_Lets:
  ∀l e.
    EVERY closed (MAP SND l)
  ⇒ freevars (Lets l e) = freevars e DIFF set (MAP FST l)
Proof
  recInduct Lets_ind >> rw[Lets_def] >> gvs[] >>
  simp[LIST_TO_SET_FILTER] >> gvs[closed_def] >>
  gvs[EXTENSION] >> rw[] >> metis_tac[]
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

Theorem letrec_split_closed:
  ∀x y. letrec_split x y ⇒ closed x ∧ closed y
Proof
  reverse (rw[letrec_split_cases]) >> gvs[freevars_set_def, closed_simps]
  >- (
    gvs[valid_split_def, EVERY_MEM, SUBSET_DEF, DISJOINT_DEF, EXTENSION] >>
    gvs[MEM_MAP, PULL_EXISTS, FORALL_PROD, PULL_FORALL, EXISTS_PROD] >> rw[] >>
    last_x_assum drule >>
    once_rewrite_tac[DISJ_COMM] >> simp[DISJ_EQ_IMP] >> disch_then drule >>
    rw[] >> first_x_assum (drule_at Any) >> simp[] >> disch_then irule >>
    irule_at Any OR_INTRO_THM1 >> goal_assum drule
    ) >>
  simp[closed_def] >> once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
  dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >>
  simp[FDOM_FUPDATE_LIST] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
  conj_tac
  >- (
    ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> simp[] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[MEM_MAP, PULL_EXISTS] >> rw[] >>
    PairCases_on `y` >> simp[closed_simps] >>
    gvs[EVERY_MEM] >> first_x_assum irule >>
    simp[MEM_MAP, EXISTS_PROD] >>
    gvs[valid_split_def] >> metis_tac[]
    ) >>
  simp[SUBSET_DIFF_EMPTY, DIFF_SUBSET] >>
  `set (MAP FST xs) = set (MAP FST xs2) ∪ set (MAP FST xs1)` by (
    gvs[valid_split_def, MEM_MAP, EXTENSION] >> metis_tac[]) >>
  gvs[] >> pop_assum (SUBST_ALL_TAC o GSYM) >>
  gvs[EVERY_MEM, SUBSET_DEF, MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
  rw[] >> first_x_assum irule >>
  goal_assum drule >> gvs[valid_split_def, EXTENSION] >>
  metis_tac[]
QED

Theorem letrec_rel_freevars:
  ∀x y. letrec_rel letrec_split x y ⇒ freevars x = freevars y
Proof
  ho_match_mp_tac letrec_rel_ind >> rw[] >> gvs[freevars_set_def]
  >- (
    rw[EXTENSION] >> gvs[LIST_REL_EL_EQN, MEM_MAP, PULL_EXISTS] >>
    metis_tac[EL_MEM, MEM_EL]
    )
  >- (
    drule letrec_split_closed >> gvs[closed_simps] >> rw[] >>
    gvs[closed_def, SUBSET_DIFF_EMPTY] >>
    gvs[EVERY_MEM, SUBSET_DEF, MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
    rw[] >> first_x_assum irule >>
    pop_assum mp_tac >> simp[Once MEM_EL] >> rw[] >>
    qexistsl_tac [`SND (EL n xs1)`, `p_1`] >> gvs[LIST_REL_EL_EQN] >>
    last_x_assum drule >> gvs[EL_MAP] >> strip_tac >> gvs[] >>
    Cases_on `EL n xs` >> Cases_on `EL n xs1` >> gvs[] >>
    qpat_x_assum `MAP _ _ = MAP _ _` mp_tac >>
    simp[Once LIST_EQ_REWRITE] >>
    disch_then drule >> rw[EL_MAP] >>
    metis_tac[EL_MEM]
    )
  >- (
    qsuff_tac `MAP (λ(fn,e). freevars e) xs = MAP (λ(fn,e). freevars e) xs1`
    >- gvs[] >>
    gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2] >> rw[] >>
    ntac 2 (last_x_assum drule) >> gvs[UNCURRY, EL_MAP]
    )
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
    \\ unabbrev_all_tac \\ rw[]
    \\ irule letrec_rel_split_subst_single
    \\ simp[letrec_rel_refl])
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
    \\ ‘letrec_rel c (bind s x2 e) (bind s y e1)’ by (
      rw[bind_single_def] >> unabbrev_all_tac >>
      irule letrec_rel_split_subst >> simp[] >>
      simp[fmap_rel_OPTREL_FLOOKUP, FLOOKUP_UPDATE] >> rw[])
    \\ Cases_on ‘k’ \\ fs []
    THEN1 (qexists_tac ‘0’ \\ fs [] >>
           IF_CASES_TAC >> simp[] >>
           drule eval_wh_inc >> disch_then (qspec_then `ck` (assume_tac o GSYM)) >>
           gvs[])
    \\ fs [ADD1]
    \\ last_x_assum drule \\ fs []
    \\ impl_tac THEN1 (
         simp[bind_single_def] >>
         imp_res_tac eval_wh_to_Closure_freevars_SUBSET >> simp[closed_def] >>
         once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
         dep_rewrite.DEP_REWRITE_TAC[freevars_subst_single] >> simp[] >>
         rw[EXTENSION, DISJ_EQ_IMP] >>
         first_x_assum drule >> rw[] >> gvs[closed_def])
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
      \\ ‘letrec_rel c (subst_funs f y) (subst_funs xs1 y1)’ by (
        dep_rewrite.DEP_REWRITE_TAC[subst_funs_eq_subst] >> gvs[] >>
        unabbrev_all_tac >>
        irule letrec_rel_split_subst >> simp[] >>
        irule fmap_rel_FUPDATE_LIST_same >>
        simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        simp[GSYM FST_THM] >>
        gvs[LIST_REL_EL_EQN] >> rw[] >> gvs[EL_MAP] >>
        last_assum drule >> rename1 `EL foo f` >>
        qabbrev_tac `a = EL foo f` >> qabbrev_tac `b = EL foo xs1` >>
        PairCases_on `a` >> PairCases_on `b` >> gvs[] >> rw[] >>
        simp[Once letrec_rel_cases] >>
        goal_assum (drule_at Any) >> qexists_tac `xs1` >> simp[] >>
        gvs[LIST_REL_EL_EQN, EL_MAP])
      \\ first_x_assum drule \\ fs []
      \\ reverse impl_tac >- rw[] >>
         rw[subst_funs_def, bind_def] >> simp[closed_def] >>
         once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
         dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >>
         simp[IN_FRANGE_FLOOKUP, PULL_EXISTS, FDOM_FUPDATE_LIST] >>
         simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
         simp[GSYM FST_THM] >> gvs[SUBSET_DEF, EXTENSION] >>
         metis_tac[])
    \\ unabbrev_all_tac
    \\ pop_assum mp_tac
    \\ simp [Once letrec_split_cases] \\ reverse (rw [])
      >- (
        fs [eval_wh_to_def] \\ rw [] THEN1 (qexists_tac ‘0’ \\ fs [])
        \\ fs [] \\ last_x_assum irule \\ reverse (rw[])
        >- (
          rename1 `_ (subst_funs ys1 _)` >>
          dep_rewrite.DEP_REWRITE_TAC[subst_funs_eq_subst] >> gvs[] >>
          imp_res_tac letrec_rel_freevars >>
          once_rewrite_tac[subst_FDIFF] >>
          irule letrec_rel_split_subst >> simp[] >>
          simp[fmap_rel_OPTREL_FLOOKUP, FLOOKUP_DRESTRICT, flookup_fupdate_list] >>
          rw[] >> rename1 `MEM k1 _` >>
          gvs[valid_split_def, ALL_DISTINCT_APPEND] >>
          simp[GSYM MAP_REVERSE, ALOOKUP_MAP, alookup_distinct_reverse] >>
          CASE_TAC >> gvs[]
          >- (
            gvs[ALOOKUP_NONE] >>
            qsuff_tac `¬ MEM k1 (MAP FST ys1)` >- gvs[GSYM ALOOKUP_NONE] >>
            gvs[EXTENSION, MEM_MAP] >> metis_tac[]
            ) >>
          drule_all ALOOKUP_SOME_EL_2 >> strip_tac >> gvs[] >>
          rename1 `EL _ f = (k1, ef)` >> rename1 `EL _ xs1 = (_, ex1)` >>
          `MEM (k1,ex1) xs1` by (gvs[MEM_EL, LIST_REL_EL_EQN] >> metis_tac[]) >>
          qpat_assum `_ = _ ∪ _` mp_tac >> once_rewrite_tac[EXTENSION] >>
          disch_then imp_res_tac >> reverse (gvs[])
          >- (gvs[SUBSET_DEF, MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD]) >>
          drule_all ALOOKUP_ALL_DISTINCT_MEM >> rw[] >>
          simp[Once letrec_rel_cases] >> goal_assum drule >> simp[] >>
          qexists_tac `ex1` >> simp[] >>
          gvs[LIST_REL_EL_EQN, EL_MAP] >> last_x_assum drule >> rw[] >>
          disj1_tac >> simp[letrec_split_cases] >> disj2_tac >>
          qexists_tac `xs2` >> gvs[valid_split_def, ALL_DISTINCT_APPEND] >> rw[]
          >- (
            gvs[EVERY_MEM, SUBSET_DEF] >> rw[] >>
            first_x_assum irule >> once_rewrite_tac[MEM_MAP] >>
            goal_assum (drule_at Any) >> qexists_tac `EL n xs1` >>
            once_rewrite_tac[MEM_EL] >> simp[] >> metis_tac[]
            ) >>
          gvs[EVERY_MEM] >>
          last_x_assum irule >> simp[MEM_MAP, EXISTS_PROD] >>
          goal_assum drule
          ) >>
       rw[subst_funs_def, bind_def] >> simp[closed_def] >>
       once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
       dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >>
       simp[IN_FRANGE_FLOOKUP, PULL_EXISTS, FDOM_FUPDATE_LIST] >>
       simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
       simp[GSYM FST_THM] >> gvs[SUBSET_DEF, EXTENSION] >>
       metis_tac[]
       )
  \\ simp [subst_def]
  \\ drule valid_split_FDIFF \\ fs []
  \\ disch_then kall_tac
  \\ qabbrev_tac ‘ss = (FEMPTY |++ MAP (λ(a,A). (a,Letrec xs1 A)) xs1')’
  \\ qabbrev_tac ‘new_xs = (MAP (λ(f',e). (f',subst ss e)) xs2)’
  \\ fs [eval_wh_to_def] \\ rw []
  THEN1 (qexists_tac ‘0’ \\ fs [])
  \\ fs [] \\ last_x_assum irule
  \\ reverse (rw[])
    >- (
      dep_rewrite.DEP_REWRITE_TAC[subst_funs_eq_subst] >> gvs[] >> rw[]
      >- (
        unabbrev_all_tac >> gvs[] >>
        simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, EVERY_MAP] >>
        simp[GSYM FST_THM] >> rw[EVERY_MEM] >>
        PairCases_on `e` >> gvs[] >>
        dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >> conj_tac
        >- (
          ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> simp[] >>
          simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
          gvs[EVERY_MEM, MEM_MAP] >> rw[] >> pairarg_tac >> gvs[] >>
          simp[EVERY_MEM, MEM_MAP] >>
          gvs[valid_split_def] >> first_x_assum irule >>
          simp[EXISTS_PROD] >> metis_tac[]
          ) >>
        simp[FDOM_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        simp[GSYM FST_THM] >> gvs[valid_split_def] >>
        qsuff_tac `freevars e1 ⊆ set (MAP FST xs1)`
        >- (gvs[SUBSET_DEF, MEM_MAP] >> metis_tac[]) >>
        gvs[EVERY_MEM] >> first_x_assum irule >>
        gvs[MEM_MAP, EXTENSION, EXISTS_PROD] >> metis_tac[]
        ) >>
      dep_rewrite.DEP_REWRITE_TAC[subst_subst_FUNION] >> conj_tac
      >- (
        unabbrev_all_tac >>
        ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> simp[] >>
        simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        simp[MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
        gvs[EVERY_MEM, SUBSET_DEF] >>
        first_x_assum ho_match_mp_tac >>
        simp[MEM_MAP, EXISTS_PROD] >> gvs[valid_split_def, EXTENSION] >>
        metis_tac[]
        ) >>
      irule letrec_rel_split_subst >> simp[Abbr `ss`] >>
      rename1 `valid_split _ ys1 _` >>
      simp[GSYM fupdate_list_funion, GSYM FUPDATE_LIST_APPEND] >>
      simp[fmap_rel_OPTREL_FLOOKUP, flookup_fupdate_list] >> rw[] >>
      rename1 `ALOOKUP _ k1` >>
      simp[REVERSE_APPEND, ALOOKUP_APPEND] >>
      imp_res_tac valid_split_def >> gvs[ALL_DISTINCT_APPEND] >>
      `MAP FST new_xs = MAP FST xs2` by (
        unabbrev_all_tac >>
        gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]) >>
      simp[GSYM MAP_REVERSE, ALOOKUP_MAP, alookup_distinct_reverse] >>
      CASE_TAC >> gvs[]
      >- (
        gvs[ALOOKUP_NONE] >>
        qsuff_tac `¬ MEM k1 (MAP FST ys1) ∧ ¬ MEM k1 (MAP FST new_xs)`
        >- gvs[GSYM ALOOKUP_NONE] >>
        gvs[] >> gvs[EXTENSION, MEM_MAP] >> metis_tac[]
        ) >>
      drule_all ALOOKUP_SOME_EL_2 >> strip_tac >> gvs[] >>
      rename1 `EL _ f = (k1, ef)` >> rename1 `EL _ xs1 = (_, ex1)` >>
      `MEM (k1,ex1) xs1` by (gvs[MEM_EL, LIST_REL_EL_EQN] >> metis_tac[]) >>
      qpat_assum `_ = _ ∪ _` mp_tac >> once_rewrite_tac[EXTENSION] >>
      disch_then imp_res_tac >> gvs[]
      >- (
        drule_all ALOOKUP_ALL_DISTINCT_MEM >> rw[] >>
        simp[Once letrec_rel_cases] >>
        goal_assum drule >> simp[] >>
        qexists_tac `ex1` >> simp[] >>
        gvs[LIST_REL_EL_EQN, EL_MAP] >> last_x_assum drule >> simp[]
        )
      >- (
        `¬ MEM k1 (MAP FST ys1)` by (
          gvs[MEM_MAP, PULL_EXISTS, FORALL_PROD] >> metis_tac[]) >>
        gvs[GSYM ALOOKUP_NONE] >>
        qmatch_asmsub_abbrev_tac `MAP (λ(f,e).(f, g e)) xs2` >>
        drule (MEM_MAP_f |> INST_TYPE [beta |-> ``:string # exp``]) >>
        disch_then (qspec_then `λ(f,e). (f, g e)` assume_tac) >> gvs[] >>
        `ALL_DISTINCT (MAP FST new_xs)` by gvs[] >>
        drule_all ALOOKUP_ALL_DISTINCT_MEM >> rw[] >>
        simp[Once letrec_rel_cases] >>
        goal_assum drule >> simp[] >>
        qexists_tac `ex1` >> simp[] >>
        gvs[LIST_REL_EL_EQN, EL_MAP] >> last_x_assum drule >> simp[] >> rw[] >>
        disj1_tac >> unabbrev_all_tac >>
        simp[letrec_split_cases] >> disj1_tac >>
        qexistsl_tac [`ys1`,`xs2`] >> simp[] >>
        simp[subst_def, MAP_EQ_f, FORALL_PROD] >>
        drule valid_split_FDIFF >> simp[] >> strip_tac >>
        gvs[EVERY_MEM] >>
        first_x_assum irule >>
        simp[MEM_MAP, EXISTS_PROD] >>
        metis_tac[]
        )
      )
    >- (
      rw[subst_funs_def, bind_def] >> simp[closed_def] >>
      once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
      dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >>
      simp[IN_FRANGE_FLOOKUP, PULL_EXISTS, FDOM_FUPDATE_LIST] >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      simp[GSYM FST_THM] >> gvs[SUBSET_DEF, EXTENSION] >>
      metis_tac[]
      )
    >- (
      rw[subst_funs_def, bind_def] >> simp[closed_def] >>
      rename1 `valid_split A B C` >> gvs[valid_split_def] >>
      once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
      simp[IN_FRANGE_FLOOKUP, PULL_EXISTS, FDOM_FUPDATE_LIST] >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      simp[GSYM FST_THM] >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
      conj_tac
      >- (
        unabbrev_all_tac >>
        gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        simp[IN_FRANGE_FLOOKUP, flookup_fupdate_list] >> rw[] >>
        EVERY_CASE_TAC >> gvs[] >> imp_res_tac ALOOKUP_MEM >> gvs[] >>
        pop_assum mp_tac >> simp[MEM_MAP, EXISTS_PROD] >> rw[] >>
        rename1 `MEM (key, value) _` >>
        simp[closed_def] >> gvs[EVERY_MEM] >>
        first_x_assum irule >> simp[MEM_MAP, EXISTS_PROD] >>
        irule_at Any OR_INTRO_THM1 >> goal_assum drule
        ) >>
       unabbrev_all_tac >> simp[FDOM_FUPDATE_LIST] >>
       simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
       simp[GSYM FST_THM] >>
       gvs[EXTENSION, SUBSET_DEF] >> metis_tac[MEM_MAP]
       )
    )
  >- (
    rename [‘Prim p xs’] >>
    qpat_x_assum `letrec_rel c _ _` mp_tac >>
    simp[Once letrec_rel_cases] >> rw[] >>
    Cases_on `p` >> gvs[eval_wh_to_def]
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> gvs[]) >>
      IF_CASES_TAC >> gvs[LIST_REL_EL_EQN] >>
      `∃x1 x2 x3. xs = [x1;x2;x3]` by (
        Cases_on `xs` >> gvs[] >> Cases_on `t` >> gvs[] >>
        Cases_on `t'` >> gvs[] >> Cases_on `t` >> gvs[]
        ) >>
      `∃y1 y2 y3. ys = [y1;y2;y3]` by (
        Cases_on `ys` >> gvs[] >> Cases_on `t` >> gvs[] >>
        Cases_on `t'` >> gvs[] >> Cases_on `t` >> gvs[]
        ) >>
      gvs[] >>
      first_assum (qspec_then `0` assume_tac) >>
      first_assum (qspec_then `1` assume_tac) >>
      first_x_assum (qspec_then `2` assume_tac) >> gvs[] >>
      gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      reverse (Cases_on `eval_wh_to (k - 1) x1`) >> gvs[]
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[]) >>
      reverse (IF_CASES_TAC) >> gvs[]
      >- (
        reverse (IF_CASES_TAC) >> gvs[]
        >- (qexists_tac `ck` >> gvs[])
        >- (
          qexists_tac `ck` >> gvs[] >>
          Cases_on `l` >> gvs[] >> Cases_on `ys'` >> gvs[]
          ) >>
        last_x_assum drule_all >> strip_tac >> gvs[] >>
        reverse (Cases_on `eval_wh_to (k - 1) x3`) >> gvs[]
        >- (
          qexists_tac `ck'` >>
          Cases_on `eval_wh_to (ck' + k - 1) y1 = wh_Diverge` >> gvs[] >>
          drule eval_wh_to_agree >>
          disch_then (qspec_then `ck + k - 1` assume_tac) >> gvs[]
          ) >>
        qspecl_then [`ck + ck' + k - 1`,`y1`,`ck + k - 1`] mp_tac eval_wh_inc >>
        gvs[] >> strip_tac >>
        qspecl_then [`ck + ck' + k - 1`,`y3`,`ck' + k - 1`] mp_tac eval_wh_inc >>
        gvs[] >> strip_tac >>
        qexists_tac `ck + ck'` >> gvs[]
        )
      >- (
        qexists_tac `ck` >> gvs[] >>
        Cases_on `l` >> gvs[] >> Cases_on `ys'` >> gvs[]
        )
      >- (
        first_x_assum drule_all >> strip_tac >> gvs[] >>
        reverse (Cases_on `eval_wh_to (k - 1) x2`) >> gvs[]
        >- (
          qexists_tac `ck'` >>
          Cases_on `eval_wh_to (ck' + k - 1) y1 = wh_Diverge` >> gvs[] >>
          drule eval_wh_to_agree >>
          disch_then (qspec_then `ck + k - 1` assume_tac) >> gvs[]
          ) >>
        qspecl_then [`ck + ck' + k - 1`,`y1`,`ck + k - 1`] mp_tac eval_wh_inc >>
        gvs[] >> strip_tac >>
        qspecl_then [`ck + ck' + k - 1`,`y2`,`ck' + k - 1`] mp_tac eval_wh_inc >>
        gvs[] >> strip_tac >>
        qexists_tac `ck + ck'` >> gvs[]
        )
      )
    >- (
      IF_CASES_TAC >> gvs[] >> qexists_tac `0` >> simp[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> simp[]) >>
      IF_CASES_TAC >> gvs[] >> gvs[LIST_REL_EL_EQN] >>
      `∃x. xs = [x]` by (
        Cases_on `xs` >> gvs[] >> Cases_on `t` >> gvs[]) >>
      `∃y. ys = [y]` by (
        Cases_on `ys` >> gvs[] >> Cases_on `t` >> gvs[]) >>
      gvs[] >>
      first_x_assum drule_all >> rw[] >>
      Cases_on `eval_wh_to (k - 1) x` >> gvs[] >>
      qexists_tac `ck` >> gvs[] >>
      IF_CASES_TAC >> gvs[] >>
      IF_CASES_TAC >> gvs[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> simp[]) >>
      IF_CASES_TAC >> gvs[] >> gvs[LIST_REL_EL_EQN] >>
      `∃x. xs = [x]` by (
        Cases_on `xs` >> gvs[] >> Cases_on `t` >> gvs[]) >>
      `∃y. ys = [y]` by (
        Cases_on `ys` >> gvs[] >> Cases_on `t` >> gvs[]) >>
      gvs[] >>
      first_x_assum drule_all >> rw[] >>
      reverse (Cases_on `eval_wh_to (k - 1) x`) >> gvs[]
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[]) >>
      reverse IF_CASES_TAC >> gvs[]
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[]) >>
      first_x_assum drule >> rw[] >>
      last_x_assum drule >> impl_tac
      >- (
        gvs[closed_def, NIL_iff_NOT_MEM] >>
        CCONTR_TAC >> gvs[] >>
        imp_res_tac eval_wh_to_freevars_SUBSET >> gvs[MEM_MAP]
        >- (
          pop_assum kall_tac >> pop_assum mp_tac >> simp[PULL_EXISTS] >>
          goal_assum drule >> simp[EL_MEM]
          )
        >- (
          pop_assum mp_tac >> simp[PULL_EXISTS] >>
          goal_assum drule >> simp[EL_MEM]
          )
        ) >>
      rw[] >>
      reverse (Cases_on `eval_wh_to (k - 1) (EL n l)`) >> gvs[]
      >- (
        qexists_tac `ck'` >>
        Cases_on `eval_wh_to (ck' + k - 1) y = wh_Diverge` >> gvs[] >>
        drule eval_wh_to_agree >>
        disch_then (qspec_then `ck + k - 1` (assume_tac o GSYM)) >> gvs[]
        ) >>
      qspecl_then [`ck + ck' + k - 1`,`y`,`ck + k - 1`] mp_tac eval_wh_inc >>
      gvs[] >> strip_tac >>
      qspecl_then [`ck + ck' + k - 1`,`EL n ys'`,`ck' + k - 1`]
        mp_tac eval_wh_inc >>
      gvs[] >> strip_tac >>
      qexists_tac `ck + ck'` >> gvs[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> gvs[]) >>
      CASE_TAC >> gvs[]
      >- (
        qsuff_tac `get_atoms (MAP (λa. eval_wh_to (k − 1) a) ys) = NONE`
        >- (rw[] >> qexists_tac `0` >> simp[]) >>
        gvs[get_atoms_NONE_eq] >> imp_res_tac LIST_REL_LENGTH >> gvs[] >>
        csimp[EL_MAP] >> gvs[EL_MAP] >>
        map_every (fn pat => qpat_x_assum pat mp_tac)
          [`∀e1. MEM e1 _ ⇒ _`, `n < _`,`eval_wh_to _ _ = _`, `∀m. m < _ ⇒ _`,
           `EVERY _ _`, `EVERY _ _`, `LENGTH _ = _`] >>
        qid_spec_tac `n` >>
        qpat_x_assum `LIST_REL _ _ _` mp_tac >>
        map_every qid_spec_tac [`ys`,`xs`] >>
        ho_match_mp_tac LIST_REL_ind >> rw[] >>
        Cases_on `n` >> gvs[]
        >- (
          qexists_tac `0` >> gvs[] >>
          first_x_assum (qspec_then `h1` mp_tac) >> simp[] >>
          disch_then drule_all >> rw[] >>
          CCONTR_TAC >> drule eval_wh_inc >>
          disch_then (qspec_then `ck + k - 1` mp_tac) >> simp[]
          ) >>
        rename1 `n < _` >>
        Cases_on `eval_wh_to (k - 1) h2 = wh_Diverge`
        >- (qexists_tac `0` >> simp[]) >>
        last_x_assum (qspec_then `n` mp_tac) >> simp[IMP_CONJ_THM] >>
        impl_tac
        >- (rw[] >> last_x_assum (qspec_then `SUC m` mp_tac) >> simp[]) >>
        strip_tac >> rename1 `l < _` >>
        qexists_tac `SUC l` >> simp[] >> rw[] >>
        Cases_on `m` >> gvs[] >>
        last_x_assum (qspec_then `0` assume_tac) >> gvs[] >>
        first_x_assum (qspec_then `h1` mp_tac) >> simp[] >>
        disch_then drule_all >> strip_tac >>
        drule eval_wh_to_agree >>
        disch_then (qspec_then `ck + k - 1` mp_tac) >> rw[] >>
        metis_tac[]
        ) >>
      Cases_on `x` >> gvs[]
      >- (
        gvs[get_atoms_SOME_NONE_eq, EL_MAP] >>
        qsuff_tac
          `∃ck. get_atoms (MAP (λa. eval_wh_to (ck + k − 1) a) ys) = SOME NONE`
        >- (rw[] >> qexists_tac `ck` >> simp[]) >>
        simp[get_atoms_SOME_NONE_eq] >> csimp[EL_MAP] >>
        imp_res_tac LIST_REL_LENGTH >> gvs[] >> goal_assum drule >>
        map_every (fn pat => qpat_x_assum pat mp_tac)
          [`∀e1. MEM e1 _ ⇒ _`, `n < _`,` ∀a. eval_wh_to _ _ ≠ _`,
           `∀m. m ≤ _ ⇒ _`, `EVERY _ _`, `EVERY _ _`, `LENGTH _ = _`] >>
        qid_spec_tac `n` >>
        qpat_x_assum `LIST_REL _ _ _` mp_tac >>
        map_every qid_spec_tac [`ys`,`xs`] >>
        ho_match_mp_tac LIST_REL_ind >> rw[] >>
        Cases_on `n` >> gvs[]
        >- (
          pop_assum (qspec_then `h1` mp_tac) >> simp[] >>
          disch_then drule_all >> strip_tac >>
          qexists_tac `ck` >>
          Cases_on `eval_wh_to (k - 1) h1` >> gvs[]
          ) >>
        rename1 `SUC n` >>
        last_x_assum (qspec_then `n` mp_tac) >> simp[] >> impl_tac
        >- (rw[] >> last_x_assum (qspec_then `SUC m` mp_tac) >> simp[]) >>
        strip_tac >>
        first_x_assum (qspec_then `h1` mp_tac) >> simp[] >>
        disch_then drule_all >> strip_tac >>
        qexists_tac `ck + ck'` >> rw[]
        >- (
          qpat_x_assum `∀a. _ ≠ wh_Atom a` (qspec_then `a` mp_tac) >>
          first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
          drule eval_wh_inc >>
          disch_then (qspec_then `ck + (ck' + k) - 1` assume_tac) >> gvs[]
          ) >>
        Cases_on `m` >> gvs[]
        >- (
          qspecl_then [`ck + (ck' + k) - 1`,`h2`,`ck' + k - 1`]
            assume_tac eval_wh_inc >>
          gvs[] >>
          full_case_tac >> gvs[] >>
          last_x_assum (qspec_then `0` assume_tac) >> gvs[]
          )
        >- (
          rename1 `m ≤ _` >>
          first_x_assum drule >> strip_tac >>
          drule eval_wh_inc >>
          disch_then (qspec_then `ck + (ck' + k) - 1` assume_tac) >> gvs[]
          )
        ) >>
      rename1 `SOME (SOME as)` >>
      qsuff_tac
        `∃ck. get_atoms (MAP (λa. eval_wh_to (ck + k − 1) a) ys) = SOME (SOME as)`
      >- (rw[] >> qexists_tac `ck` >> simp[] >> CASE_TAC >> gvs[]) >>
      gvs[get_atoms_SOME_SOME_eq, EVERY2_MAP] >>
      map_every (fn pat => qpat_x_assum pat mp_tac)
        [`∀e1. MEM e1 _ ⇒ _`, `LIST_REL _ _ _`, `EVERY _ _`, `EVERY _ _`] >>
      qid_spec_tac `as` >>
      qpat_x_assum `LIST_REL _ _ _` mp_tac >>
      map_every qid_spec_tac [`ys`,`xs`] >>
      ho_match_mp_tac LIST_REL_strongind >> rw[] >>
      rename1 `LIST_REL _ _ as` >>
      qsuff_tac
        `∃ck. LIST_REL (λa a'. eval_wh_to (ck + k − 1) a = wh_Atom a') ys as`
      >- (
        pop_assum (qspec_then `h1` mp_tac) >> simp[] >>
        disch_then drule_all >> rw[] >>
        qexists_tac `ck + ck'` >>
        qspecl_then [`ck + ck' + k - 1`,`h2`,`ck + k - 1`]
          assume_tac eval_wh_inc >>
        gvs[LIST_REL_EL_EQN] >> rw[] >>
        qspecl_then [`ck + ck' + k - 1`,`EL n ys`,`ck' + k - 1`]
          assume_tac eval_wh_inc >>
        gvs[]
        ) >>
      last_x_assum irule >> simp[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> gvs[]) >>
      IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[]
      )
    )
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
      gvs[valid_split_def, MEM_MAP, PULL_EXISTS, closed_def] >>
      once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
      dep_rewrite.DEP_REWRITE_TAC[freevars_Lets] >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
      rw[]
      >- (
        gvs[EVERY_MEM, MEM_MAP, EXISTS_PROD] >> rw[closed_def] >>
        gvs[PULL_EXISTS] >>
        `freevars p_2 ⊆ set (MAP FST xs)` by res_tac >>
        gvs[SUBSET_DEF] >>
        simp[FILTER_EQ_NIL, MEM_MAP, EXISTS_PROD, EVERY_MEM] >> rw[] >>
        pop_assum mp_tac >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        simp[FORALL_PROD] >> gvs[MEM_MAP, EXISTS_PROD] >>
        rw[] >> metis_tac[]
        ) >>
      simp[SUBSET_DIFF_EMPTY, DIFF_SUBSET] >>
      `set (MAP FST xs2) ∪ set (MAP FST xs1) = set (MAP FST xs)` by (
        gvs[EXTENSION, MEM_MAP] >> metis_tac[]) >>
      gvs[] >>
      gvs[SUBSET_DEF, MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
      gvs[EVERY_MEM] >> rw[] >>
      first_x_assum irule >> simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >>
      metis_tac[]
      ) >>
     irule exp_eq_closed_Lets_subst >>
     gvs[EVERY_MEM, MEM_MAP, EXTENSION, valid_split_def, PULL_EXISTS] >>
     rw[] >> PairCases_on `y` >> gvs[] >>
     res_tac >> fs[] >>
     gvs[EVERY_MEM, MEM_MAP] >>
     metis_tac[]
QED

Theorem valid_split_thm_alt:
  valid_split xs xs1 xs2 ∧ closed (Letrec xs x) ⇒
  Letrec xs x ≃
  subst (FEMPTY |++ MAP (λ(a,A). (a, Letrec xs A)) xs1) (Letrec xs2 x)
Proof
  rw[] >> irule app_bisimilarity_trans >>
  irule_at Any valid_split_thm >> goal_assum drule >> simp[] >>
  simp[app_bisimilarity_eq] >>
  irule_at Any (iffLR exp_eq_sym) >>
  irule_at Any exp_eq_closed_Lets_subst >>
  `freevars (Letrec xs2 x) ⊆ set (MAP FST xs1)` by (
    simp[DIFF_SUBSET] >> rw[]
    >- (gvs[valid_split_def, EXTENSION, MEM_MAP, SUBSET_DEF] >> metis_tac[]) >>
    gvs[EVERY_MEM, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
    gvs[valid_split_def, EXTENSION, MEM_MAP, SUBSET_DEF] >> metis_tac[]
    ) >>
  conj_asm1_tac
  >- (
    gvs[EVERY_MAP, LAMBDA_PROD] >>
    gvs[valid_split_def, EXTENSION, EVERY_MEM]
    ) >>
  rw[]
  >- (
    simp[closed_def] >> once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
    dep_rewrite.DEP_REWRITE_TAC[freevars_Lets] >>
    gvs[SUBSET_DIFF_EMPTY, DIFF_SUBSET] >>
    conj_tac >- gvs[EVERY_MAP] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM]
    )
  >- (
    simp[closed_def] >> once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
    dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >>
    gvs[FDOM_FUPDATE_LIST, SUBSET_DIFF_EMPTY, DIFF_SUBSET] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> simp[] >>
    gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS]
    )
QED

Theorem valid_split_shrink:
  valid_split xs xs1 xs2 ∧ closed (Letrec xs x) ∧
  freevars x ⊆ set (MAP FST xs1) ⇒
  Letrec xs x ≃ Letrec xs1 x
Proof
  rw []
  \\ match_mp_tac letrec_split_correct \\ fs []
  \\ reverse (rw [])
  THEN1 (
    gvs[EVERY_MEM, valid_split_def] >> rw[] >> gvs[EXTENSION] >>
    `MEM e (MAP SND xs)` by metis_tac[MEM_MAP] >>
    first_x_assum drule >> rw[] >>
    qpat_x_assum `MEM _ (_ xs1)` mp_tac >>
    last_x_assum mp_tac >> simp[MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
    first_x_assum drule >> simp[DISJOINT_DEF, EXTENSION, DISJ_EQ_IMP] >>
    strip_tac >> gvs[SUBSET_DEF] >>
    metis_tac[MEM_MAP]
    )
  \\ once_rewrite_tac [letrec_rel_cases] \\ fs []
  \\ qexists_tac ‘xs’ \\ qexists_tac ‘x’ \\ fs []
  \\ irule_at Any EVERY2_refl \\ simp[letrec_rel_refl]
  \\ fs [letrec_split_cases]
  \\ metis_tac []
QED


Theorem FDIFF_FDIFF:
  ∀fm s1 s2. FDIFF (FDIFF fm s1) s2 = FDIFF fm (s1 ∪ s2)
Proof
  rw[FDIFF_def, DRESTRICT_DRESTRICT, fmap_eq_flookup, FLOOKUP_DRESTRICT]
QED

Theorem closed_subst_all_freevars:
  ∀m e.
    (∀v. v ∈ FRANGE m ⇒ closed v) ∧
    closed (subst m e)
  ⇒ freevars e ⊆ FDOM m
Proof
  rw[] >> imp_res_tac freevars_subst >>
  gvs[closed_def, EXTENSION, NIL_iff_NOT_MEM, SUBSET_DEF, DISJ_EQ_IMP]
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

Triviality app_bisimilarity_subst:
  ∀fm1 e fm2.
    fmap_rel ($≃) fm1 fm2 ∧
    freevars e ⊆ FDOM fm1
  ⇒ subst fm1 e ≃ subst fm2 e
Proof
  rw[app_bisimilarity_eq]
  >- (
    gvs[exp_eq_open_bisimilarity_freevars] >>
    irule Sub_lift >> gvs[fmap_rel_def, Exps_def, closed_def] >> rw[]
    >- (last_x_assum (qspec_then `k` assume_tac) >> gvs[])
    >- (
      assume_tac Sub_Howe_open_similarity >> gvs[Howe_open_similarity] >>
      gvs[open_bisimilarity_eq, Sub_def]
      )
    >- gvs[SUBSET_DEF]
    >- (
      assume_tac Ref_open_bisimilarity >> gvs[Ref_def] >>
      pop_assum irule >> simp[Exps_def] >> gvs[SUBSET_DEF]
      )
    ) >>
  gvs[closed_def] >> once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
  dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >> simp[SUBSET_DIFF_EMPTY] >>
  gvs[fmap_rel_def, IN_FRANGE] >> rw[closed_def] >>
  metis_tac[]
QED

Triviality beta_equality_Letrec_app_bisimilarity:
  closed (Letrec fns e) ⇒ Letrec fns e ≃ subst_funs fns e
Proof
  rw[app_bisimilarity_eq]
  >- (irule beta_equality_Letrec >> simp[]) >>
  rw[subst_funs_def, bind_def, closed_def] >>
  once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
  dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >>
  simp[IN_FRANGE_FLOOKUP, closed_def, SUBSET_DIFF_EMPTY, FDOM_FUPDATE_LIST] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM]
QED

(* This lemma would allow us to verify a top_sort_any application anywhere
   in the program. See proof idea below. *)
Theorem Letrec_Letrec:
  valid_split xs ys zs ⇒
  Letrec xs e ≅ Letrec ys (Letrec zs e)
Proof
  rw[] >>
  once_rewrite_tac[exp_eq_open_bisimilarity_freevars] >>
  irule open_bisimilarity_suff >> rw[] >>
  `FDOM f = freevars e ∪
    BIGUNION (set (MAP (λ(fn,e). freevars e) xs)) DIFF set (MAP FST xs)` by (
    gvs[valid_split_def, EXTENSION, SUBSET_DEF, MEM_MAP,
        PULL_EXISTS, EXISTS_PROD, FORALL_PROD, DISJOINT_DEF] >>
    rw[] >> metis_tac[]) >>
  gvs[] >> pop_assum kall_tac >> rw[bind_def] >>
  simp[subst_def, FDIFF_FDIFF] >>
  `set (MAP FST ys) ∪ set (MAP FST zs) = set (MAP FST xs)` by (
    gvs[valid_split_def, EXTENSION, MEM_MAP] >> metis_tac[]) >>
  simp[] >>
  `DISJOINT (set (MAP FST xs)) (FDOM f)` by (
    gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  drule disjoint_drestrict >> simp[GSYM FDIFF_def] >> disch_then kall_tac >>
  qpat_x_assum `_ = _` (SUBST_ALL_TAC o GSYM) >>
  pop_assum mp_tac >> once_rewrite_tac[DISJOINT_UNION] >> strip_tac >>
  imp_res_tac disjoint_drestrict >> gvs[GSYM FDIFF_def] >>
  ntac 4 (pop_assum kall_tac) >>
  `set (MAP FST ys) ∪ set (MAP FST zs) = set (MAP FST xs)` by (
    gvs[valid_split_def, EXTENSION, MEM_MAP] >> metis_tac[]) >>
  irule app_bisimilarity_trans >>
  irule_at Any valid_split_thm_alt >> simp[GSYM CONJ_ASSOC] >>
  qexists_tac `MAP (λ(f',e). (f',subst f e)) zs` >>
  qexists_tac `MAP (λ(f',e). (f',subst f e)) ys` >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
  conj_asm1_tac
  >- (
    gvs[valid_split_def] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    gvs[LIST_TO_SET_MAP, EXISTS_PROD, PULL_EXISTS] >> rw[] >>
    last_x_assum drule >> rw[] >>
    qsuff_tac `freevars (subst f p_2) ⊆ freevars p_2`
    >- (rw[] >> irule DISJOINT_SUBSET >> goal_assum drule >> simp[]) >>
    dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >> simp[FDIFF_def] >>
    simp[IN_FRANGE_FLOOKUP]
    ) >>
  conj_asm1_tac
  >- (
    dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >>
    simp[DIFF_SUBSET, IN_FRANGE_FLOOKUP] >>
    gvs[SUBSET_DEF, valid_split_def, EXTENSION]
    ) >>
  conj_asm1_tac
  >- (
    gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> rw[] >>
    dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >>
    simp[DIFF_SUBSET, IN_FRANGE_FLOOKUP] >>
    gvs[valid_split_def, SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    rw[GSYM DISJ_ASSOC] >>
    disj2_tac >> disj1_tac >> goal_assum drule >> metis_tac[]
    ) >>
  qmatch_goalsub_abbrev_tac `Letrec zs1 e1` >>
  qpat_abbrev_tac `xs1 = MAP _ xs` >>
  `MAP (λ(p1,p2). (p1,Letrec xs1 (subst f p2))) ys =
   MAP (λ(p1,p2). (p1, Letrec xs1 p2)) (MAP (λ(p1,p2). (p1, subst f p2)) ys)` by
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  simp[] >> pop_assum kall_tac >>
  qpat_abbrev_tac `ys1 = MAP _ ys` >>
  irule app_bisimilarity_trans >>
  irule_at Any app_bisimilarity_subst >>
  simp[FDOM_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  simp[GSYM FST_THM, DIFF_SUBSET] >>
  qexists_tac `FEMPTY |++ MAP (λ(p1,p2). (p1,Letrec ys1 p2)) ys1` >> rw[]
  >- (
    irule fmap_rel_FUPDATE_LIST_same >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    gvs[LIST_REL_EL_EQN] >> rw[EL_MAP] >> Cases_on `EL n ys1` >> simp[] >>
    irule valid_split_shrink >>
    simp[PULL_EXISTS] >> goal_assum (drule_at Any) >>
    gvs[valid_split_def] >>
    unabbrev_all_tac >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> gvs[GSYM FST_THM] >>
    gvs[EL_MAP, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
    Cases_on `EL n ys` >> gvs[] >> rename1 `(q,r)` >>
    conj_asm2_tac
    >- (gvs[SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
    first_x_assum (qspecl_then [`q`,`r`] mp_tac) >>
    impl_tac >- metis_tac[EL_MEM] >> rw[] >>
    gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
    first_x_assum (qspecl_then [`q`,`r`] mp_tac) >>
    impl_tac >- metis_tac[EL_MEM] >> rw[] >>
    gvs[SUBSET_DEF, DISJOINT_DEF, EXTENSION] >> metis_tac[]
    )
  >- (
    unabbrev_all_tac >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    simp[Once UNION_COMM]
    )
  >- (
    unabbrev_all_tac >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    simp[Once UNION_COMM] >>
    simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
    gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
    first_x_assum irule >> gvs[valid_split_def, EXTENSION] >> metis_tac[]
    ) >>
  dep_rewrite.DEP_REWRITE_TAC[GSYM subst_funs_eq_subst] >> conj_asm1_tac
  >- (
    gvs[valid_split_def, EVERY_MAP, EVERY_MEM, FORALL_PROD] >> rw[] >>
    unabbrev_all_tac >> gvs[MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
    PairCases_on `y` >> gvs[] >>
    first_x_assum drule >> strip_tac >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> gvs[GSYM FST_THM] >>
    qsuff_tac `freevars (subst f y1) ⊆ set (MAP FST xs)`
    >- (gvs[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
    metis_tac[]
    ) >>
  irule (symmetric_app_bisimilarity |> SIMP_RULE std_ss [symmetric_def] |> iffLR) >>
  irule beta_equality_Letrec_app_bisimilarity >> simp[DIFF_SUBSET] >>
  unabbrev_all_tac >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> gvs[GSYM FST_THM] >>
  simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
  rw[] >> simp[Once UNION_COMM] >>
  gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
  last_x_assum irule >> gvs[valid_split_def, EXTENSION] >>
  metis_tac[]
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
 ≃ (* from valid_split_shrink *)
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
 ≃ (* from valid_split_shrink *)
   Let a1 (Letrec [(a1,A1);(a2,A2)] A1)
   Let a2 (Letrec [(a1,A1);(a2,A2)] A2)
     (Letrec [(b,B)] r)
 ≃ (* easy *)
   Letrec [(a1,A1);(a2,A2)] (Letrec [(b,B)] r)

*)

val _ = export_theory();
