
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open arithmeticTheory listTheory rich_listTheory alistTheory stringTheory
     optionTheory pairTheory pred_setTheory finite_mapTheory;
open pure_miscTheory pure_expTheory pure_exp_lemmasTheory
     pure_evalTheory pure_eval_lemmasTheory pure_semanticsTheory
     pure_exp_relTheory pure_congruenceTheory
     itreeTheory pure_obs_sem_equalTheory;

val _ = new_theory "pure_ctxt_equiv";


(******************** Basic definitions ********************)

Datatype:
  ctxt = Hole
       | Prim op (exp list) ctxt (exp list)
       | AppL ctxt exp
       | AppR exp ctxt
       | Lam vname ctxt
       | LetrecL ((vname # exp) list)
                  (vname # ctxt)
                 ((vname # exp) list) exp
       | LetrecR ((vname # exp) list) ctxt
End

Definition plug_def:
  plug Hole n = n ∧
  plug (Prim op xs1 h xs2) n = Prim op (xs1 ++ [plug h n] ++ xs2) ∧
  plug (AppL h y) n = App (plug h n) y ∧
  plug (AppR x h) n = App x (plug h n) ∧
  plug (Lam v h) n = Lam v (plug h n) ∧
  plug (LetrecL xs1 (f,h) xs2 x) n = Letrec (xs1 ++ [(f,plug h n)] ++ xs2) x ∧
  plug (LetrecR xs h) n = Letrec xs (plug h n)
End

Definition plug_ctxt_def:
  plug_ctxt Hole n = n ∧
  plug_ctxt (Prim op xs1 h xs2) n = Prim op xs1 (plug_ctxt h n) xs2 ∧
  plug_ctxt (AppL h y) n = AppL (plug_ctxt h n) y ∧
  plug_ctxt (AppR x h) n = AppR x (plug_ctxt h n) ∧
  plug_ctxt (Lam v h) n = Lam v (plug_ctxt h n) ∧
  plug_ctxt (LetrecL xs1 (f,h) xs2 x) n = LetrecL xs1 (f, plug_ctxt h n) xs2 x ∧
  plug_ctxt (LetrecR xs h) n = LetrecR xs (plug_ctxt h n)
End

Definition AppLs_def:
  AppLs c [] = c ∧
  AppLs c (e::es) = AppLs (AppL c e) es
End

Definition LamsC_def:
  LamsC [] c = c :ctxt ∧
  LamsC (v::vs) c = Lam v (LamsC vs c)
End


(******************** Lemmas ********************)

Theorem plug_AppLs:
  ∀l c e. plug (AppLs c l) e = Apps (plug c e) l
Proof
  Induct >> rw[AppLs_def, Apps_def, plug_def]
QED

Theorem plug_LamsC:
  ∀l c e. plug (LamsC l c) e = Lams l (plug c e)
Proof
  Induct >> rw[LamsC_def, Lams_def, plug_def]
QED

Theorem plug_plug_ctxt:
  ∀c1 c2 e. plug (plug_ctxt c1 c2) e = plug c1 (plug c2 e)
Proof
  recInduct plug_ctxt_ind >> rw[plug_def, plug_ctxt_def]
QED

Theorem exp_equiv_plug:
  ∀h x y. x ≅ y ⇒ plug h x ≅ plug h y
Proof
  recInduct plug_ind >> rw[plug_def]
  >- ( (* Prim *)
    irule exp_eq_Prim_cong >>
    irule LIST_REL_APPEND_suff >> simp[] >>
    rw[LIST_REL_EL_EQN, exp_eq_refl]
    )
  >- ( (* AppL *)
    irule exp_eq_App_cong >> simp[exp_eq_refl]
    )
  >- ( (* AppR *)
    irule exp_eq_App_cong >> simp[exp_eq_refl]
    )
  >- ( (* Lam *)
    irule exp_eq_Lam_cong >> simp[exp_eq_refl]
    )
  >- ( (* LetrecL *)
    irule exp_eq_Letrec_cong >> simp[exp_eq_refl] >>
    irule LIST_REL_APPEND_suff >> simp[] >>
    rw[LIST_REL_EL_EQN, exp_eq_refl]
    )
  >- ( (* LetrecR *)
    irule exp_eq_Letrec_cong >> simp[exp_eq_refl] >>
    rw[LIST_REL_EL_EQN, exp_eq_refl]
    )
QED

Theorem freevars_plug_eq:
  ∀ctxt e1 e2.
    freevars e1 = freevars e2
  ⇒ freevars (plug ctxt e1) = freevars (plug ctxt e2)
Proof
  recInduct plug_ind >> rw[plug_def]
  >- (AP_THM_TAC >> ntac 2 AP_TERM_TAC >> first_x_assum irule >> simp[])
  >- (AP_THM_TAC >> AP_TERM_TAC >> first_x_assum irule >> simp[])
  >- (AP_TERM_TAC >> first_x_assum irule >> simp[])
  >- (AP_THM_TAC >> AP_TERM_TAC >> first_x_assum irule >> simp[])
  >- (
    AP_THM_TAC >> ntac 2 AP_TERM_TAC >> AP_THM_TAC >>
    ntac 2 AP_TERM_TAC >> first_x_assum irule >> simp[]
    )
  >- (
    AP_THM_TAC >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
    first_x_assum irule >> simp[]
    )
QED

Triviality app_bisimilarity_plug:
  ∀c x y. (x ≃ y) T ∧ closed (plug c x) ⇒ (plug c x ≃ plug c y) T
Proof
  rw[app_bisimilarity_eq]
  >- (irule exp_equiv_plug >> simp[])
  >- (
    gvs[closed_def] >>
    qspecl_then [`c`,`x`,`y`] assume_tac freevars_plug_eq >> gvs[]
    )
QED

Theorem semantics_Length_alt:
  semantics (Length e) k st =
    case eval_wh e of
      wh_Diverge => Div
    | wh_Atom (Loc n) =>
        if LENGTH st ≤ n then Ret Error else
        semantics (Ret (Lit (Int (&LENGTH (EL n st))))) k st
    | _ => Ret Error
Proof
  reverse $ Cases_on `∃a. eval_wh e = wh_Atom a` >> gvs[]
  >- (
    rw[semantics_def, eval_wh_thm] >>
    simp[Once interp_def, next_action_def] >>
    simp[Once next_def, with_atom_def, with_atoms_def] >>
    Cases_on `eval_wh e` >> gvs[get_atoms_def] >>
    DEEP_INTRO_TAC some_intro >> rw[] >>
    simp[Once next_def, with_atom_def, with_atoms_def, get_atoms_def]
    ) >>
  reverse $ Cases_on `∃n. a = Loc n` >> gvs[]
  >- (
    rw[semantics_def, eval_wh_thm] >>
    simp[Once interp_def, next_action_def] >>
    simp[Once next_def, with_atom_def, with_atoms_def, get_atoms_def] >>
    Cases_on `a` >> gvs[] >>
    DEEP_INTRO_TAC some_intro >> rw[] >>
    simp[Once next_def, with_atom_def, with_atoms_def, get_atoms_def]
    ) >>
  reverse $ IF_CASES_TAC >> gvs[]
  >- (DEP_REWRITE_TAC[semantics_Length] >> simp[]) >>
  rw[semantics_def, eval_wh_thm] >>
  simp[Once interp_def, next_action_def] >>
  simp[Once next_def, with_atom_def, with_atoms_def, get_atoms_def] >>
  DEEP_INTRO_TAC some_intro >> rw[] >>
  simp[Once next_def, with_atom_def, with_atoms_def, get_atoms_def]
QED


(******************** Contextual equivalence ********************)

Definition ctxt_equiv_def:
  ctxt_equiv e1 e2 ⇔
    ∀ctxt. closed (plug ctxt e1) ∧ closed (plug ctxt e2)
      ⇒ itree_of (plug ctxt e1) = itree_of (plug ctxt e2)
End

val _ = set_fixity "∽" (Infixl 480);
Overload "∽" = “ctxt_equiv”;

(******************** Proof apparatus ********************)

Datatype:
  wh_cons = wh_At lit
          | wh_Cons string
          | wh_Clos
          | wh_Div
          | wh_Err
End

Definition wh_to_cons_def:
  wh_to_cons (wh_Atom a) = wh_At a ∧
  wh_to_cons (wh_Constructor s es) = wh_Cons s ∧
  wh_to_cons (wh_Closure x e) = wh_Clos ∧
  wh_to_cons  wh_Diverge = wh_Div ∧
  wh_to_cons  wh_Error = wh_Err
End

Triviality app_bisimilarity_wh_to_cons:
  ∀x y. (x ≃ y) T ⇒ wh_to_cons (eval_wh x) = wh_to_cons (eval_wh y)
Proof
  rw[Once app_bisimilarity_iff_alt2] >>
  Cases_on `eval_wh x` >> gvs[wh_to_cons_def]
QED

Definition step_eval_wh_def:
  step_eval_wh [] e = SOME (wh_to_cons $ eval_wh e) ∧
  step_eval_wh (INL (s,n) :: rest) e =
    (case eval_wh e of
      wh_Constructor s' es =>
        if s = s' then OPTION_BIND (oEL n es) (step_eval_wh rest) else NONE
    | _ => NONE) ∧
  step_eval_wh (INR arg :: rest) e =
    case dest_wh_Closure (eval_wh e) of
      SOME (x, body) =>
        if closed arg then step_eval_wh rest (subst1 x arg body) else NONE
    | NONE => NONE
End

Triviality step_eval_wh_eq:
  ∀l e1 e2. eval_wh e1 = eval_wh e2 ⇒ step_eval_wh l e1 = step_eval_wh l e2
Proof
  Cases >> rw[step_eval_wh_def] >>
  Cases_on `h` >> rw[step_eval_wh_def] >>
  PairCases_on `x` >> rw[step_eval_wh_def]
QED

(* Creating a context to distinguish `Loc`s: *)
Definition BindAllocs_def:
  BindAllocs 0 e = Length e ∧
  BindAllocs (SUC n) e = Bind (Alloc (Lit (Int 0)) Fail) (Lam "" $ BindAllocs n e)
End

Definition BindAllocsC_def:
  BindAllocsC 0 = Prim (Cons "Length") [] Hole [] ∧
  BindAllocsC (SUC n) =
    Prim (Cons "Bind") [Alloc (Lit (Int 0)) Fail] (Lam "" $ BindAllocsC n) []
End

Theorem plug_BindAllocsC:
  ∀n. plug (BindAllocsC n) e = BindAllocs n e
Proof
  Induct >> rw[BindAllocsC_def, BindAllocs_def, plug_def]
QED

Triviality freevars_BindAllocs:
  ∀n e. freevars (BindAllocs n e) ⊆ freevars e
Proof
  Induct >> rw[BindAllocs_def] >>
  simp[DELETE_SUBSET_INSERT] >> gvs[SUBSET_DEF]
QED

Theorem semantics_BindAllocs:
  ∀n e k st.
  closed e ⇒
  semantics (BindAllocs n e) k st =
    semantics (Length e) k (st ++ REPLICATE n [])
Proof
  Induct >> rw[BindAllocs_def] >>
  simp[semantics_Bind] >>
  `eval_wh (Lit (Int 0)) = wh_Atom (Int &0)` by
    simp[eval_wh_Prim, pure_evalTheory.get_atoms_def] >>
  drule semantics_Alloc >> rw[] >>
  simp[semantics_Ret_BC] >>
  qmatch_goalsub_abbrev_tac `semantics foo _ st' = _` >>
  `semantics foo k st' = semantics (BindAllocs n e) k st'` by (
    unabbrev_all_tac >>
    simp[semantics_def, eval_wh_thm, bind1_def] >>
    DEP_REWRITE_TAC[subst1_ignore] >>
    simp[GSYM semantics_def] >> simp[semantics_def, eval_wh_thm] >>
    CCONTR_TAC >> gvs[closed_def] >>
    drule (freevars_BindAllocs |> SIMP_RULE std_ss [SUBSET_DEF]) >> gvs[]) >>
  simp[Abbr `st'`] >> AP_TERM_TAC >> simp[GSYM APPEND_ASSOC]
QED


(******************** Main lemmas ********************)

Theorem step_eval_wh_IMP_app_similarity[local]:
  ∀e1 e2.
    (closed e1 ∧ closed e2 ∧ ∀l. step_eval_wh l e1 = step_eval_wh l e2)
  ⇒ (e1 ≲ e2) T
Proof
  ho_match_mp_tac app_similarity_companion_coind >>
  rw[FF_def, EXISTS_PROD, unfold_rel_def] >>
  first_assum (qspec_then `[]` mp_tac) >> simp[step_eval_wh_def] >>
  Cases_on `eval_wh e2` >> simp[wh_to_cons_def] >> rw[]
  >- (
    irule companion_rel >> simp[] >>
    rpt $ irule_at Any IMP_closed_subst >>
    simp[IN_FRANGE_FLOOKUP, FLOOKUP_UPDATE] >>
    imp_res_tac eval_wh_Closure_closed >> simp[] >> rw[] >>
    rename1 `closed arg` >>
    first_x_assum $ qspec_then `INR arg :: l` mp_tac >>
    simp[step_eval_wh_def]
    ) >>
  simp[LIST_REL_EL_EQN] >> conj_asm1_tac >> rw[]
  >- (
    first_assum $ qspec_then `[INL (s, LENGTH l)]` mp_tac >>
    first_x_assum $ qspec_then `[INL (s, LENGTH e1s)]` mp_tac >>
    simp[step_eval_wh_def, oEL_THM]
    ) >>
  irule companion_rel >> simp[] >>
  imp_res_tac eval_wh_freevars_SUBSET >>
  gvs[closed_def, DISJ_EQ_IMP, MEM_MAP, PULL_FORALL] >>
  rw[EMPTY_iff_NOTIN] >- metis_tac[EL_MEM] >- metis_tac[EL_MEM] >>
  rename1 `step_eval_wh ll` >>
  last_x_assum $ qspec_then `INL (s,n) :: ll` mp_tac >>
  simp[step_eval_wh_def, oEL_THM]
QED

Theorem step_eval_wh_eq_app_bisimilarity:
  ∀e1 e2.
    closed e1 ∧ closed e2 ∧ (∀l. step_eval_wh l e1 = step_eval_wh l e2) ⇔
    (e1 ≃ e2) T
Proof
  rw[] >> eq_tac
  >- (
    rw[app_bisimilarity_similarity] >>
    irule step_eval_wh_IMP_app_similarity >> simp[]
    ) >>
  rw[]
  >- gvs[Once app_bisimilarity_iff_alt2]
  >- gvs[Once app_bisimilarity_iff_alt2] >>
  pop_assum mp_tac >>
  map_every qid_spec_tac [`e2`,`e1`,`l`] >>
  Induct >> rw[step_eval_wh_def] >>
  pop_assum mp_tac >> once_rewrite_tac[app_bisimilarity_iff_alt2] >> strip_tac
  >- (Cases_on `eval_wh e1` >> gvs[wh_to_cons_def]) >>
  Cases_on `h` >> gvs[]
  >- (
    PairCases_on `x` >> gvs[step_eval_wh_def] >>
    Cases_on `eval_wh e1` >> gvs[] >> IF_CASES_TAC >> gvs[] >>
    gvs[oEL_THM, LIST_REL_EL_EQN] >> IF_CASES_TAC >> gvs[]
    )
  >- (
    gvs[step_eval_wh_def] >> Cases_on `eval_wh e1` >> gvs[] >>
    IF_CASES_TAC >> gvs[]
    )
QED

Triviality not_app_bisimilarity_IMP_not_step_eval_wh:
  ∀e1 e2.
    ¬ (e1 ≃ e2) T ∧ closed e1 ∧ closed e2
  ⇒ ∃l. step_eval_wh l e1 ≠ step_eval_wh l e2
Proof
  rw[] >> CCONTR_TAC >> gvs[] >>
  drule_all $ iffLR step_eval_wh_eq_app_bisimilarity >> simp[]
QED

Theorem not_exp_eq_IMP_not_step_eval_wh:
  ∀e1 e2.
    ¬ (e1 ≅ e2) ⇒
    ∃vs es.
      ALL_DISTINCT vs ∧ EVERY closed es ∧
      freevars e1 ∪ freevars e2 ⊆ set vs ∧
      ∃l. step_eval_wh l (Apps (Lams vs e1) es) ≠
          step_eval_wh l (Apps (Lams vs e2) es)
Proof
  rw[exp_eq_def] >> gvs[bind_def] >> EVERY_CASE_TAC >> gvs[] >>
  qspec_then `f` assume_tac fmap_to_list >> gvs[FDOM_FUPDATE_LIST] >>
  goal_assum drule >> qexists_tac `MAP SND l` >> simp[] >>
  conj_asm1_tac
  >- (
    gvs[EVERY_MAP, EVERY_MEM, flookup_fupdate_list, alookup_distinct_reverse] >>
    rw[] >> PairCases_on `x` >> gvs[] >>
    first_x_assum (qspec_then `x0` assume_tac) >>
    EVERY_CASE_TAC >> gvs[ALOOKUP_NONE, MEM_MAP] >>
    drule_all ALOOKUP_ALL_DISTINCT_MEM >> rw[] >> simp[]
    ) >>
  drule not_app_bisimilarity_IMP_not_step_eval_wh >> impl_tac
  >- (
    rpt $ irule_at Any IMP_closed_subst >> simp[FDOM_FUPDATE_LIST] >>
    ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> gvs[EVERY_MEM]
    ) >>
  strip_tac >> rename1 `step_eval_wh ll` >> qexists_tac `ll` >>
  Cases_on `ll` >> gvs[step_eval_wh_def]
  >- (DEP_REWRITE_TAC[eval_Apps_Lams] >> gvs[EVERY_MAP, combinTheory.o_DEF]) >>
  reverse $ Cases_on `h` >> gvs[step_eval_wh_def]
  >- (DEP_REWRITE_TAC[eval_Apps_Lams] >> gvs[EVERY_MAP, combinTheory.o_DEF]) >>
  reverse $ Cases_on `x` >> gvs[step_eval_wh_def] >>
  DEP_REWRITE_TAC[eval_Apps_Lams] >> gvs[EVERY_MAP, combinTheory.o_DEF]
QED

Theorem exists_closed_step_eval_wh:
  ∀l e1 e2.
    step_eval_wh l e1 ≠ step_eval_wh l e2
  ⇒ ∃l'. EVERY (λs. sum_CASE s (K T) closed) l' ∧
         step_eval_wh l' e1 ≠ step_eval_wh l' e2
Proof
  Induct >> rw[step_eval_wh_def]
  >- (qexists_tac `[]` >> simp[step_eval_wh_def]) >>
  reverse $ Cases_on `h` >> gvs[step_eval_wh_def]
  >- (
    reverse $ EVERY_CASE_TAC >> gvs[]
    >- (
      last_x_assum drule >> rw[] >> rename1 `step_eval_wh ll` >>
      qexists_tac `INR y :: ll` >> simp[step_eval_wh_def]
      ) >>
    qexists_tac `[]` >> simp[step_eval_wh_def] >>
    Cases_on `eval_wh e1` >> gvs[] >>
    Cases_on `eval_wh e2` >> gvs[wh_to_cons_def]
    ) >>
  PairCases_on `x` >>
  reverse $ Cases_on `step_eval_wh (INL (x0,x1) :: l) e1` >>
  gvs[step_eval_wh_def]
  >- (
    Cases_on `eval_wh e1` >> gvs[oEL_THM] >> rename1 `eval_wh e1 = _ e1s` >>
    reverse $ Cases_on `∃e2s. eval_wh e2 = wh_Constructor s e2s` >> gvs[]
    >- (
      qexists_tac `[]` >> gvs[step_eval_wh_def] >>
      Cases_on `eval_wh e2` >> gvs[wh_to_cons_def]
      ) >>
    last_x_assum (qspecl_then [`EL x1 e1s`,`EL x1 e2s`] assume_tac) >> gvs[] >>
    Cases_on `x1 < LENGTH e2s` >> gvs[]
    >- (
      rename1 `step_eval_wh ll` >>
      qexists_tac `INL (s,x1) :: ll` >> gvs[step_eval_wh_def, oEL_THM]
      )
    >- (qexists_tac `[INL (s,x1)]` >> gvs[step_eval_wh_def, oEL_THM])
    ) >>
  Cases_on `eval_wh e2` >> gvs[oEL_THM] >>
  Cases_on `∃e1s. eval_wh e1 = wh_Constructor s e1s` >> gvs[]
  >- (qexists_tac `[INL (s,x1)]` >> gvs[step_eval_wh_def, oEL_THM])
  >- (
    rename1 `eval_wh e2 = _ e2s` >>
    last_x_assum $ qspecl_then [`EL x1 e1s`,`EL x1 e2s`] mp_tac >> rw[] >>
    rename1 `step_eval_wh ll` >>
    qexists_tac `INL (s,x1) :: ll` >> simp[step_eval_wh_def, oEL_THM]
    )
  >- (
    qexists_tac `[INL (s,x1)]` >> gvs[step_eval_wh_def, oEL_THM] >>
    Cases_on `eval_wh e1` >> gvs[]
    )
QED

Theorem neq_step_eval_IMP_exists_ctxt:
  ∀l e1 e2.
    EVERY (λs. sum_CASE s (K T) closed) l ∧
    closed e1 ∧ closed e2 ∧
    step_eval_wh l e1 ≠ step_eval_wh l e2
  ⇒ ∃ctxt.
      closed (plug ctxt e1) ∧ closed (plug ctxt e2) ∧
      wh_to_cons (eval_wh $ plug ctxt e1) ≠ wh_to_cons (eval_wh $ plug ctxt e2)
Proof
  Induct >> rw[step_eval_wh_def]
  >- (qexists_tac `Hole` >> simp[plug_def]) >>
  reverse $ Cases_on `h` >> gvs[step_eval_wh_def]
  >- (
    EVERY_CASE_TAC >> gvs[]
    >- (
      qexists_tac `Hole` >> simp[plug_def] >>
      Cases_on `eval_wh e2` >> gvs[] >>
      Cases_on `eval_wh e1` >> gvs[wh_to_cons_def]
      )
    >- (
      qexists_tac `Hole` >> simp[plug_def] >>
      Cases_on `eval_wh e1` >> gvs[] >>
      Cases_on `eval_wh e2` >> gvs[wh_to_cons_def]
      ) >>
    last_x_assum $ drule_at $ Pos last >>
    Cases_on `eval_wh e1` >> gvs[] >> rename1 `eval_wh _ = _ v1 ce1` >>
    Cases_on `eval_wh e2` >> gvs[] >> rename1 `eval_wh _ = _ v2 ce2` >>
    impl_keep_tac
    >- (
      rpt $ irule_at Any IMP_closed_subst >> simp[FRANGE_FUPDATE] >>
      imp_res_tac eval_wh_Closure_closed >> gvs[]
      ) >>
    rw[] >> qexists_tac `plug_ctxt ctxt (AppL Hole y)` >>
    simp[plug_plug_ctxt, plug_def] >> simp[CONJ_ASSOC] >> conj_asm1_tac
    >- (
      gvs[closed_def] >>
      qspecl_then [`ctxt`,`App e1 y`,`subst1 v1 y ce1`]
        assume_tac freevars_plug_eq >> gvs[] >>
      qspecl_then [`ctxt`,`App e2 y`,`subst1 v2 y ce2`]
        assume_tac freevars_plug_eq >> gvs[]
      ) >>
    `(plug ctxt (subst1 v1 y ce1) ≃ plug ctxt (App e1 y)) T ∧
     (plug ctxt (subst1 v2 y ce2) ≃ plug ctxt (App e2 y)) T` by (
      rw[] >> irule app_bisimilarity_plug >> simp[] >> rw[app_bisimilarity_eq] >>
      irule eval_wh_IMP_exp_eq >> rw[eval_wh_thm, bind1_def]) >>
    imp_res_tac app_bisimilarity_wh_to_cons >> gvs[]
    ) >>
  PairCases_on `x` >>
  reverse $ Cases_on `step_eval_wh (INL (x0,x1) :: l) e1` >>
  gvs[step_eval_wh_def]
  >- (
    Cases_on `eval_wh e1` >> gvs[oEL_THM] >> rename1 `eval_wh e1 = _ e1s` >>
    reverse $ Cases_on `∃e2s. eval_wh e2 = wh_Constructor s e2s` >> gvs[]
    >- (
      qexists_tac `Hole` >> gvs[plug_def] >>
      Cases_on `eval_wh e2` >> gvs[wh_to_cons_def]
      ) >>
    reverse $ Cases_on `x1 < LENGTH e2s` >> gvs[]
    >- (
      rw[] >> qexists_tac `Prim (IsEq s (LENGTH e1s) F) [] Hole []` >>
      simp[plug_def, closed_simps, eval_wh_thm, wh_to_cons_def]
      ) >>
    last_x_assum $ qspecl_then [`EL x1 e1s`,`EL x1 e2s`] mp_tac >> gvs[] >>
    impl_keep_tac
    >- (
      imp_res_tac eval_wh_freevars_SUBSET >> gvs[PULL_EXISTS, MEM_MAP] >>
      gvs[closed_def, EMPTY_iff_NOTIN] >> metis_tac[EL_MEM]
      ) >>
    rw[] >> qexists_tac `plug_ctxt ctxt (Prim (Proj s x1) [] Hole [])` >>
    simp[plug_plug_ctxt, plug_def] >> simp[CONJ_ASSOC] >> conj_asm1_tac
    >- (
      gvs[closed_def] >>
      qspecl_then [`ctxt`,`Proj s x1 e1`,`EL x1 e1s`]
        assume_tac freevars_plug_eq >> gvs[] >>
      qspecl_then [`ctxt`,`Proj s x1 e2`,`EL x1 e2s`]
        assume_tac freevars_plug_eq >> gvs[]
      ) >>
    `(plug ctxt (EL x1 e1s) ≃ plug ctxt (Proj s x1 e1)) T ∧
     (plug ctxt (EL x1 e2s) ≃ plug ctxt (Proj s x1 e2)) T` by (
      rw[] >> irule app_bisimilarity_plug >> simp[] >> rw[app_bisimilarity_eq] >>
      irule eval_wh_IMP_exp_eq >> rw[eval_wh_thm]) >>
    imp_res_tac app_bisimilarity_wh_to_cons >> gvs[]
    ) >>
  Cases_on `eval_wh e2` >> gvs[oEL_THM] >> rename1 `eval_wh _ = _ e2s` >>
  reverse $ Cases_on `∃e1s. eval_wh e1 = wh_Constructor s e1s` >> gvs[]
  >- (
    qexists_tac `Prim (IsEq s (LENGTH e2s) F) [] Hole []` >>
    simp[plug_def, eval_wh_thm] >>
    Cases_on `eval_wh e1` >> gvs[wh_to_cons_def]
    )
  >- (
    qexists_tac `Prim (IsEq s (LENGTH e2s) F) [] Hole []` >>
    simp[plug_def, eval_wh_thm] >>
    Cases_on `eval_wh e1` >> gvs[wh_to_cons_def]
    ) >>
  last_x_assum $ qspecl_then [`EL x1 e1s`,`EL x1 e2s`] mp_tac >> gvs[] >>
  impl_keep_tac
  >- (
    imp_res_tac eval_wh_freevars_SUBSET >> gvs[PULL_EXISTS, MEM_MAP] >>
    gvs[closed_def, EMPTY_iff_NOTIN] >> metis_tac[EL_MEM]
    ) >>
  rw[] >> qexists_tac `plug_ctxt ctxt (Prim (Proj s x1) [] Hole [])` >>
  simp[plug_plug_ctxt, plug_def] >> simp[CONJ_ASSOC] >> conj_asm1_tac
  >- (
    gvs[closed_def] >>
    qspecl_then [`ctxt`,`Proj s x1 e1`,`EL x1 e1s`]
      assume_tac freevars_plug_eq >> gvs[] >>
    qspecl_then [`ctxt`,`Proj s x1 e2`,`EL x1 e2s`]
      assume_tac freevars_plug_eq >> gvs[]
    ) >>
  `(plug ctxt (EL x1 e1s) ≃ plug ctxt (Proj s x1 e1)) T ∧
   (plug ctxt (EL x1 e2s) ≃ plug ctxt (Proj s x1 e2)) T` by (
    rw[] >> irule app_bisimilarity_plug >> simp[] >> rw[app_bisimilarity_eq] >>
    irule eval_wh_IMP_exp_eq >> rw[eval_wh_thm]) >>
  imp_res_tac app_bisimilarity_wh_to_cons >> gvs[]
QED


(******************** Main theorems ********************)

Theorem exp_eq_eq_ctxt_equiv_lemma:
  ∀e1 e2.
    ¬ (e1 ≅ e2)
  ⇒ ∃ctxt.
      closed (plug ctxt e1) ∧ closed (plug ctxt e2) ∧
      wh_to_cons (eval_wh $ plug ctxt e1) ≠ wh_to_cons (eval_wh $ plug ctxt e2)
Proof
  rw[] >>
  imp_res_tac not_exp_eq_IMP_not_step_eval_wh >>
  imp_res_tac exists_closed_step_eval_wh >>
  Q.REFINE_EXISTS_TAC `plug_ctxt c (AppLs (LamsC vs Hole) es)` >>
  simp[plug_plug_ctxt, plug_AppLs, plug_LamsC] >>
  irule neq_step_eval_IMP_exists_ctxt >> simp[plug_def] >> gvs[UNION_SUBSET] >>
  goal_assum drule >> simp[]
QED

Triviality interp_simps[simp]:
  (∀k st. interp wh_Diverge k st = Div) ∧
  (∀x. interp (wh_Constructor "Ret" [x]) Done [] = Ret Termination) ∧
  (∀k st. interp wh_Error k st = Ret Error)
Proof
  once_rewrite_tac[interp_def] >> simp[next_action_def] >> rw[] >>
  simp[Once next_def] >> DEEP_INTRO_TAC some_intro >> rw[Once next_def]
QED

Theorem exp_eq_eq_ctxt_equiv:
  ∀e1 e2. e1 ≅ e2 ⇔ e1 ∽ e2
Proof
  rw[] >> eq_tac >> rw[ctxt_equiv_def]
  >- (
    rw[itree_of_def] >>
    irule bisimilarity_IMP_all_semantics_eq >> simp[] >>
    rw[app_bisimilarity_eq] >> irule exp_equiv_plug >> simp[]
    ) >>
  CCONTR_TAC >> last_x_assum mp_tac >> simp[] >>
  drule exp_eq_eq_ctxt_equiv_lemma >> rw[] >>
  Q.REFINE_EXISTS_TAC `plug_ctxt c ctxt` >> simp[plug_plug_ctxt] >>
  map_every qpat_abbrev_tac [`e1' = plug ctxt e1`, `e2' = plug ctxt e2`] >>
  Cases_on `eval_wh e1' = wh_Diverge` >> gvs[wh_to_cons_def]
  >- (
    `eval_wh e2' ≠ wh_Diverge` by (CCONTR_TAC >> gvs[wh_to_cons_def]) >>
    qexists_tac `Prim Seq [] Hole [Ret Fail]` >> simp[plug_def] >>
    simp[itree_of_def, semantics_def, eval_wh_thm] >> IF_CASES_TAC >> gvs[]
    ) >>
  Cases_on `eval_wh e2' = wh_Diverge` >> gvs[wh_to_cons_def]
  >- (
    qexists_tac `Prim Seq [] Hole [Ret Fail]` >> simp[plug_def] >>
    simp[itree_of_def, semantics_def, eval_wh_thm] >> IF_CASES_TAC >> gvs[]
    ) >>
  Cases_on `eval_wh e1' = wh_Error` >> gvs[wh_to_cons_def]
  >- (
    `eval_wh e2' ≠ wh_Error` by (CCONTR_TAC >> gvs[wh_to_cons_def]) >>
    qexists_tac `Prim Seq [] Hole [Ret Fail]` >> simp[plug_def] >>
    simp[itree_of_def, semantics_def, eval_wh_thm]
    ) >>
  Cases_on `eval_wh e2' = wh_Error` >> gvs[wh_to_cons_def]
  >- (
    qexists_tac `Prim Seq [] Hole [Ret Fail]` >> simp[plug_def] >>
    simp[itree_of_def, semantics_def, eval_wh_thm]
    ) >>
  Cases_on `∃s e1s. eval_wh e1' = wh_Constructor s e1s` >> gvs[wh_to_cons_def]
  >- (
    qexists_tac
      `Prim If [] (Prim (IsEq s (LENGTH e1s) F) [] Hole []) [Ret Fail; Fail]` >>
    simp[plug_def, itree_of_def, semantics_def, eval_wh_thm] >>
    Cases_on `eval_wh e2'` >> gvs[wh_to_cons_def]
    ) >>
  Cases_on `∃s e2s. eval_wh e2' = wh_Constructor s e2s` >> gvs[wh_to_cons_def]
  >- (
    qexists_tac
      `Prim If [] (Prim (IsEq s (LENGTH e2s) F) [] Hole []) [Ret Fail; Fail]` >>
    simp[plug_def, itree_of_def, semantics_def, eval_wh_thm] >>
    Cases_on `eval_wh e1'` >> gvs[wh_to_cons_def]
    ) >>
  Cases_on `∃a. eval_wh e1' = wh_Atom a` >> gvs[wh_to_cons_def]
  >- (
    Cases_on `a` >> gvs[]
    >- ( (* Int *)
      qexists_tac
        `Prim If [] (Prim (AtomOp Eq) [Lit (Int i)] Hole []) [Ret Fail; Fail]` >>
      simp[plug_def] >>
      simp[itree_of_def, semantics_def, eval_wh_thm] >>
      simp[eval_wh_Prim, pure_evalTheory.get_atoms_def] >>
      Cases_on `eval_wh e2'` >> gvs[wh_to_cons_def, dest_Atom_def] >>
      every_case_tac >> gvs[pure_configTheory.eval_op_SOME]
      )
    >- ( (* Str *)
      qexists_tac
        `Prim If [] (Prim (AtomOp StrEq) [Lit (Str s)] Hole []) [Ret Fail; Fail]` >>
      simp[plug_def] >>
      simp[itree_of_def, semantics_def, eval_wh_thm] >>
      simp[eval_wh_Prim, pure_evalTheory.get_atoms_def] >>
      Cases_on `eval_wh e2'` >> gvs[wh_to_cons_def, dest_Atom_def] >>
      every_case_tac >> gvs[pure_configTheory.eval_op_SOME]
      )
    >- ( (* Loc *)
      reverse $ Cases_on `∃m. eval_wh e2' = wh_Atom (Loc m)` >> gvs[]
      >- (
        qexists_tac `BindAllocsC (SUC n)` >>
        simp[plug_BindAllocsC, closed_def, EMPTY_iff_NOTIN] >> conj_tac
        >- (
          CCONTR_TAC >> gvs[closed_def] >>
          drule (freevars_BindAllocs |> SIMP_RULE std_ss [SUBSET_DEF]) >> gvs[]
          ) >>
        simp[itree_of_def, semantics_BindAllocs] >>
        simp[semantics_Length_alt, semantics_Ret] >>
        EVERY_CASE_TAC >> gvs[]
        ) >>
      Cases_on `n < m` >> gvs[]
      >- (
        qexists_tac `BindAllocsC (SUC n)` >>
        simp[plug_BindAllocsC, closed_def, EMPTY_iff_NOTIN] >> conj_tac
        >- (
          CCONTR_TAC >> gvs[closed_def] >>
          drule (freevars_BindAllocs |> SIMP_RULE std_ss [SUBSET_DEF]) >> gvs[]
          ) >>
        simp[itree_of_def, semantics_BindAllocs] >>
        simp[semantics_Length_alt, semantics_Ret]
        )
      >- (
        qexists_tac `BindAllocsC (SUC m)` >>
        simp[plug_BindAllocsC, closed_def, EMPTY_iff_NOTIN] >> conj_tac
        >- (
          CCONTR_TAC >> gvs[closed_def] >>
          drule (freevars_BindAllocs |> SIMP_RULE std_ss [SUBSET_DEF]) >> gvs[]
          ) >>
        simp[itree_of_def, semantics_BindAllocs] >>
        simp[semantics_Length_alt, semantics_Ret] >>
        IF_CASES_TAC >> gvs[NOT_LESS, wh_to_cons_def]
        )
      )
    >- ( (* Msg *)
      qexists_tac `Prim (Cons "Act") [] Hole []` >> simp[plug_def] >>
      simp[itree_of_def] >> drule semantics_Act >> strip_tac >> simp[] >>
      simp[semantics_def, eval_wh_thm] >>
      once_rewrite_tac[interp_def] >>
      simp[next_action_def, Once next_def] >>
      simp[with_atom_def, with_atoms_def] >>
      Cases_on `eval_wh e2'` >> gvs[get_atoms_def]
      >- (
        DEEP_INTRO_TAC some_intro >> rw[Once next_def] >>
        simp[with_atom_def, with_atoms_def, get_atoms_def, GSYM itree_distinct]
        )
      >- (
        simp[AllCaseEqs(), GSYM itree_distinct] >> rw[Once next_def] >>
        simp[with_atom_def, with_atoms_def, get_atoms_def] >>
        Cases_on `l` >> gvs[wh_to_cons_def]
        )
      )
    ) >>
  Cases_on `∃a. eval_wh e2' = wh_Atom a` >> gvs[wh_to_cons_def]
  >- (
    Cases_on `a` >> gvs[]
    >- ( (* Int *)
      qexists_tac
        `Prim If [] (Prim (AtomOp Eq) [Lit (Int i)] Hole []) [Ret Fail; Fail]` >>
      simp[plug_def] >>
      simp[itree_of_def, semantics_def, eval_wh_thm] >>
      simp[eval_wh_Prim, pure_evalTheory.get_atoms_def] >>
      Cases_on `eval_wh e1'` >> gvs[wh_to_cons_def, dest_Atom_def]
      )
    >- ( (* Str *)
      qexists_tac
        `Prim If [] (Prim (AtomOp StrEq) [Lit (Str s)] Hole []) [Ret Fail; Fail]` >>
      simp[plug_def] >>
      simp[itree_of_def, semantics_def, eval_wh_thm] >>
      simp[eval_wh_Prim, pure_evalTheory.get_atoms_def] >>
      Cases_on `eval_wh e1'` >> gvs[wh_to_cons_def, dest_Atom_def]
      )
    >- ( (* Loc *)
      qexists_tac `BindAllocsC (SUC n)` >>
      simp[plug_BindAllocsC, closed_def, EMPTY_iff_NOTIN] >> conj_tac
      >- (
        CCONTR_TAC >> gvs[closed_def] >>
        drule (freevars_BindAllocs |> SIMP_RULE std_ss [SUBSET_DEF]) >> gvs[]
        ) >>
      simp[itree_of_def, semantics_BindAllocs] >>
      simp[semantics_Length_alt, semantics_Ret] >>
      EVERY_CASE_TAC >> gvs[]
      )
    >- ( (* Msg *)
      qexists_tac `Prim (Cons "Act") [] Hole []` >> simp[plug_def] >>
      simp[itree_of_def] >> drule semantics_Act >> strip_tac >> simp[] >>
      simp[semantics_def, eval_wh_thm] >>
      once_rewrite_tac[interp_def] >>
      simp[next_action_def, Once next_def] >>
      simp[with_atom_def, with_atoms_def] >>
      Cases_on `eval_wh e1'` >> gvs[get_atoms_def] >>
      DEEP_INTRO_TAC some_intro >> rw[Once next_def] >>
      simp[with_atom_def, with_atoms_def, get_atoms_def, GSYM itree_distinct]
      )
    ) >>
  Cases_on `eval_wh e1'` >> gvs[] >>
  Cases_on `eval_wh e2'` >> gvs[wh_to_cons_def]
QED


(****************************************)

val _ = export_theory();
