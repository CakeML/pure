(*
   Alpha equivalence and permutations for PureCake expressions
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_exp_relTheory;

val _ = new_theory "pure_alpha_equiv";

val no_IN = SIMP_RULE std_ss [IN_DEF];

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

Definition perm_wh_def:
  (perm_wh x y (wh_Constructor s xs) = wh_Constructor s (MAP (perm_exp x y) xs)) ∧
  (perm_wh x y (wh_Closure s xs) = wh_Closure (perm1 x y s) (perm_exp x y xs)) ∧
  (perm_wh x y wh = wh)
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
  >- (
    rw[LIST_EQ_REWRITE] >>
    gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
    )
  >- (
    rw[LIST_EQ_REWRITE] >>
    gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS] >>
    first_x_assum drule >>
    Cases_on `EL x l'` >> Cases_on `EL x l` >> rw[] >>
    first_x_assum irule >> simp[] >>
    goal_assum drule >> simp[Once EQ_SYM]
    )
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

Theorem perm_wh_inj:
  ∀wh wh' v1 v2. (perm_wh v1 v2 wh = perm_wh v1 v2 wh') ⇔ wh = wh'
Proof
  Cases >> Cases >> rw[perm_wh_def] >> eq_tac >> rw[]
  >- (
    gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, LIST_EQ_REWRITE] >> rw[] >>
    irule (iffLR perm_exp_inj) >>
    first_x_assum drule >> rw[] >>
    goal_assum drule
    )
  >- (
    irule (iffLR perm_exp_inj) >>
    goal_assum drule
    )
QED

Definition perm_subst_def:
  perm_subst v1 v2 s =
  FUN_FMAP
    (λz. perm_exp v1 v2 (THE(FLOOKUP s (perm1 v1 v2 z))))
    {z | perm1 v1 v2 z ∈ FDOM s}
End

Theorem perm_subst_sym:
  perm_subst v1 v2 s = perm_subst v2 v1 s
Proof
  rw[perm_subst_def,perm_exp_sym,perm1_sym]
QED

Theorem perm1_sym':
  perm1 v1 v2 = perm1 v2 v1
Proof
  rw[FUN_EQ_THM,perm1_sym]
QED

Theorem perm_subst_flookup:
  FLOOKUP(perm_subst v1 v2 s) x =
  OPTION_MAP (perm_exp v1 v2) (FLOOKUP s (perm1 v1 v2 x))
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

Theorem subst_eqvt_alt:
  subst f (perm_exp x y e) =
  perm_exp x y (subst (perm_subst x y f) e)
Proof
  rw[subst_eqvt, perm_subst_cancel]
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

Theorem subst_single_eqvt_alt:
  subst s e' (perm_exp x y e) =
  perm_exp x y (subst (perm1 x y s) (perm_exp x y e') e)
Proof
  rw[subst_single_eqvt, perm_subst_cancel]
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

Triviality get_atoms_perm_cancel:
  ∀v1 v2 l.
    get_atoms (MAP (perm_wh v1 v2) l) =
    get_atoms l
Proof
  gen_tac >> gen_tac >>
  Induct >> rw[get_atoms_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[perm_wh_def]
QED

Theorem eval_wh_to_eqvt:
  ∀v1 v2 k e.
    perm_wh v1 v2 (eval_wh_to k e) =
    eval_wh_to k (perm_exp v1 v2 e)
Proof
  gen_tac >> gen_tac >>
  recInduct eval_wh_to_ind >> rw[] >>
  gvs[perm_wh_def, eval_wh_to_def, perm_exp_def]
  >- (
    IF_CASES_TAC >> gvs[perm_wh_def] >>
    TOP_CASE_TAC >> gvs[perm_wh_def]
    >- (
      Cases_on `eval_wh_to k x` >> gvs[dest_wh_Closure_def, perm_wh_def] >>
      EVERY_CASE_TAC >> gvs[] >>
      last_x_assum (assume_tac o GSYM) >> gvs[]
      ) >>
    Cases_on `eval_wh_to k x` >> gvs[dest_wh_Closure_def, perm_wh_def] >>
    last_x_assum (assume_tac o GSYM) >> gvs[] >>
    IF_CASES_TAC >> gvs[perm_wh_def] >>
    gvs[bind_single_eqvt]
    )
  >- (
    IF_CASES_TAC >> gvs[perm_wh_def] >>
    gvs[subst_funs_eqvt, pure_miscTheory.PAIR_MAP_ALT]
    ) >>
  IF_CASES_TAC >> gvs[perm_wh_def] >>
  TOP_CASE_TAC >> gvs[perm_wh_def]
  >- (
    IF_CASES_TAC >> gvs[perm_wh_def] >>
    `∃x1 x2 x3. xs = [x1;x2;x3]` by (
      Cases_on `xs` >> gvs[] >>
      Cases_on `t` >> gvs[] >>
      Cases_on `t'` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    last_x_assum (assume_tac o GSYM) >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
    TOP_CASE_TAC >> gvs[perm_wh_def] >>
    ntac 2 (IF_CASES_TAC >> gvs[perm_wh_def])
    )
  >- rw[MAP_EQ_f]
  >- (
    last_x_assum (assume_tac o GSYM) >>
    IF_CASES_TAC >> gvs[perm_wh_def] >>
    Cases_on `xs` >> gvs[] >>
    TOP_CASE_TAC >> gvs[perm_wh_def] >>
    rpt (IF_CASES_TAC >> gvs[perm_wh_def, EL_MAP])
    )
  >- (
    last_x_assum (assume_tac o GSYM) >>
    IF_CASES_TAC >> gvs[perm_wh_def] >>
    Cases_on `xs` >> gvs[] >>
    TOP_CASE_TAC >> gvs[perm_wh_def] >>
    rpt (IF_CASES_TAC >> gvs[perm_wh_def]) >>
    simp[EL_MAP]
    )
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF] >>
    qmatch_goalsub_abbrev_tac `MAP f xs` >>
    qpat_abbrev_tac `g = λa. eval_wh_to _ (_ a)` >>
    `MAP g xs = MAP (λa. perm_wh v1 v2 (f a)) xs` by (
      rw[LIST_EQ_REWRITE, EL_MAP] >>
      unabbrev_all_tac >> fs[] >>
      first_x_assum (irule o GSYM) >> gvs[EL_MEM]) >>
    unabbrev_all_tac >> gvs[] >>
    simp[GSYM combinTheory.o_DEF, GSYM MAP_MAP_o] >>
    simp[get_atoms_perm_cancel] >>
    TOP_CASE_TAC >> gvs[perm_wh_def] >>
    rename1 `option_CASE x` >> Cases_on `x` >> gvs[perm_wh_def] >>
    rename1 `option_CASE x` >> Cases_on `x` >> gvs[perm_wh_def]
    )
  >- (IF_CASES_TAC >> gvs[perm_wh_def])
QED

Theorem eval_wh_eqvt:
  ∀v1 v2 e.
    perm_wh v1 v2 (eval_wh e) =
    eval_wh (perm_exp v1 v2 e)
Proof
  rw[eval_wh_def] >>
  DEEP_INTRO_TAC some_intro >> rw[]
  >- (
    rename1 `eval_wh_to k` >>
    qspecl_then [`v1`,`v2`,`k`,`e`] assume_tac eval_wh_to_eqvt >>
    simp[] >>
    DEEP_INTRO_TAC some_intro >> rw[] >> gvs[] >>
    rename1 `_ = eval_wh_to k' _` >>
    irule eval_wh_to_agree >> simp[] >>
    once_rewrite_tac[GSYM eval_wh_to_eqvt] >>
    pop_assum kall_tac >> pop_assum kall_tac >>
    Cases_on `eval_wh_to k e` >> gvs[perm_wh_def]
    )
  >- (
    DEEP_INTRO_TAC some_intro >> rw[] >> gvs[perm_wh_def] >>
    pop_assum mp_tac >> simp[] >>
    rename1 `eval_wh_to k` >>
    qspecl_then [`v1`,`v2`,`k`,`e`] assume_tac (GSYM eval_wh_to_eqvt) >>
    simp[perm_wh_def]
    )
QED

Theorem follow_path_eval_wh_eqvt:
  ∀v1 v2 l f e.
    (perm_v_prefix v1 v2 ## I) (follow_path eval_wh e l) =
    follow_path eval_wh (perm_exp v1 v2 e) l
Proof
  gen_tac >> gen_tac >>
  Induct >> rw[follow_path_def] >>
  simp[GSYM eval_wh_eqvt] >>
  Cases_on `eval_wh e` >> gvs[perm_wh_def, perm_v_prefix_def] >>
  gvs[oEL_THM] >>
  IF_CASES_TAC >> gvs[EL_MAP, perm_v_prefix_def]
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
  rw[eval_def, v_unfold_def] >>
  rw[gen_v_eqvt] >>
  AP_TERM_TAC >> irule EQ_EXT >> rw[] >>
  simp[follow_path_eval_wh_eqvt]
QED

Theorem eval_wh_perm_closure:
  eval_wh (perm_exp v1 v2 e) = wh_Closure x e'
    ⇔ eval_wh e = wh_Closure (perm1 v1 v2 x) (perm_exp v1 v2 e')
Proof
  assume_tac (Q.SPECL [‘w1’,‘w2’,‘v1’,‘v2’] perm_wh_inj |> Q.GENL [‘w1’,‘w2’])
  \\ pop_assum (fn th => simp [Once (GSYM th)])
  \\ fs [eval_wh_eqvt,perm_wh_def]
QED

Theorem eval_wh_perm_cons:
  eval_wh (perm_exp v1 v2 e) = wh_Constructor s e'
    ⇔ eval_wh e = wh_Constructor s (MAP (perm_exp v1 v2) e')
Proof
  assume_tac (Q.SPECL [‘w1’,‘w2’,‘v1’,‘v2’] perm_wh_inj |> Q.GENL [‘w1’,‘w2’])
  \\ pop_assum (fn th => simp [Once (GSYM th)])
  \\ fs [eval_wh_eqvt,perm_wh_def]
QED

Theorem eval_wh_perm_atom:
  eval_wh (perm_exp v1 v2 e) = wh_Atom a ⇔ eval_wh e = wh_Atom a
Proof
  assume_tac (Q.SPECL [‘w1’,‘w2’,‘v1’,‘v2’] perm_wh_inj |> Q.GENL [‘w1’,‘w2’])
  \\ pop_assum (fn th => simp [Once (GSYM th)])
  \\ fs [eval_wh_eqvt,perm_wh_def]
QED

Theorem eval_wh_perm_diverge:
  eval_wh (perm_exp v1 v2 e) = wh_Diverge ⇔ eval_wh e = wh_Diverge
Proof
  assume_tac (Q.SPECL [‘w1’,‘w2’,‘v1’,‘v2’] perm_wh_inj |> Q.GENL [‘w1’,‘w2’])
  \\ pop_assum (fn th => simp [Once (GSYM th)])
  \\ fs [eval_wh_eqvt,perm_wh_def]
QED

Theorem eval_wh_perm_error:
  eval_wh (perm_exp v1 v2 e) = wh_Error ⇔ eval_wh e = wh_Error
Proof
  assume_tac (Q.SPECL [‘w1’,‘w2’,‘v1’,‘v2’] perm_wh_inj |> Q.GENL [‘w1’,‘w2’])
  \\ pop_assum (fn th => simp [Once (GSYM th)])
  \\ fs [eval_wh_eqvt,perm_wh_def]
QED

Theorem compatible_perm:
  compatible (λR. {(e1,e2) | ∃v1 v2 e3 e4. e1 = perm_exp v1 v2 e3  ∧
                                           e2 = perm_exp v1 v2 e4 ∧ R(e3,e4)})
Proof
  rw[compatible_def] >> simp[SUBSET_DEF] >>
  Cases >> rw[FF_def,unfold_rel_def,ELIM_UNCURRY,eval_wh_perm_closure] >>
  simp[closed_perm] >> gvs[eval_wh_perm_closure,eval_wh_perm_cons] >>
  gvs[eval_wh_perm_atom,eval_wh_perm_diverge,eval_wh_perm_error]
  >- (irule_at (Pos hd) (GSYM perm1_cancel) >>
      irule_at (Pos hd) (GSYM perm_exp_cancel) >>
      rw[] >>
      irule_at (Pos hd) (GSYM perm_exp_cancel) >>
      simp[subst_single_eqvt] >>
      PRED_ASSUM is_forall (irule_at (Pos last)) >>
      simp[subst_single_eqvt,closed_perm]) >>
  qexists_tac ‘MAP (perm_exp v1 v2) e2s’ >>
  gvs[eval_thm] >>
  fs [MAP_MAP_o,combinTheory.o_DEF,perm_exp_cancel] >>
  fs[EVERY2_MAP] >>
  drule_at_then (Pos last) match_mp_tac EVERY2_mono >>
  rw[] >>
  goal_assum (first_assum o mp_then (Pos last) mp_tac) >>
  irule_at (Pos hd) (GSYM perm_exp_cancel) >> fs []
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
  (∀e x y. x ≠ y ∧ y ∉ set(freevars e) ⇒
    exp_alpha (Lam x e) (Lam y (perm_exp x y e))) ∧
[~Prim:]
  (∀op es es'. LIST_REL exp_alpha es es' ⇒ exp_alpha (Prim op es) (Prim op es')) ∧
[~App:]
  (∀e1 e1' e2 e2'. exp_alpha e1 e1' ∧ exp_alpha e2 e2' ⇒
    exp_alpha (App e1 e2) (App e1' e2')) ∧
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
               (Letrec
                  (MAP (perm1 x y ## perm_exp x y) funs1 ++
                       (y,perm_exp x y e)::MAP (perm1 x y ## perm_exp x y) funs2)
                  (perm_exp x y e1))) ∧
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

Triviality MAP_PAIR_MAP':
  MAP (λ(x,y). h x) (MAP (f ## g) l) = MAP h (MAP f (MAP FST l)) ∧
  MAP (λ(x,y). h y) (MAP (f ## g) l) = MAP h (MAP g (MAP SND l))
Proof
  rw[MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f,ELIM_UNCURRY]
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

Theorem EVERY2_refl_EQ:
  LIST_REL R ls ls ⇔ (∀x. MEM x ls ⇒ R x x)
Proof
  simp[EQ_IMP_THM,EVERY2_refl] >>
  Induct_on ‘ls’ >> rw[] >>
  metis_tac[]
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
    exp_alpha e e' ⇒ pure_exp$freevars e = pure_exp$freevars e'
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
          qspec_then ‘λx. freevars(SND x)’
            (simp o single o SIMP_RULE std_ss []) MAP_MAP_perm_lemma >>
          simp[GSYM MAP_FLAT] >>
          simp[FILTER_MAP,combinTheory.o_DEF,perm1_right,perm1_simps] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MAP_ID_ON] >>
          rw[MEM_FILTER,MEM_FLAT,MEM_MAP] >>
          rw[perm1_def] >>
          gvs[MEM_MAP,PULL_EXISTS] >>
          metis_tac[FST,SND,PAIR])
      >- (simp[MAP_PAIR_MAP,MEM_PERM_EQ_GEN,FILTER_MAP,combinTheory.o_DEF,
               perm1_right,perm1_simps] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MAP_ID_ON] >>
          rw[MEM_FILTER,MEM_FLAT,MEM_MAP] >>
          rw[perm1_def] >>
          gvs[MEM_MAP,PULL_EXISTS] >>
          metis_tac[FST,SND,PAIR])
      >- (simp[MAP_PAIR_MAP,MEM_PERM_EQ_GEN] >>
          simp[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY,GSYM perm_exp_eqvt] >>
          qspec_then ‘λx. freevars(SND x)’
            (simp o single o SIMP_RULE std_ss []) MAP_MAP_perm_lemma >>
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
          qspec_then ‘λx. freevars(SND x)’
            (simp o single o SIMP_RULE std_ss []) MAP_MAP_perm_lemma >>
          simp[GSYM MAP_FLAT] >>
          simp[FILTER_MAP,combinTheory.o_DEF,perm1_right,perm1_simps] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MAP_ID_ON] >>
          rw[MEM_FILTER,MEM_FLAT,MEM_MAP] >>
          rw[perm1_def] >>
          gvs[MEM_MAP,PULL_EXISTS] >>
          metis_tac[FST,SND,PAIR])
      >- (simp[MAP_PAIR_MAP,MEM_PERM_EQ_GEN,FILTER_MAP,combinTheory.o_DEF,
               perm1_right,perm1_simps] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MAP_ID_ON] >>
          rw[MEM_FILTER,MEM_FLAT,MEM_MAP] >>
          rw[perm1_def] >>
          gvs[MEM_MAP,PULL_EXISTS] >>
          metis_tac[FST,SND,PAIR])
      >- (simp[MAP_PAIR_MAP,MEM_PERM_EQ_GEN] >>
          simp[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY,GSYM perm_exp_eqvt] >>
          qspec_then ‘λx. freevars(SND x)’
            (simp o single o SIMP_RULE std_ss []) MAP_MAP_perm_lemma >>
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

Theorem exp_alpha_bind_all_closed':
  ∀s s' e.
    fmap_rel exp_alpha s s' ⇒
    exp_alpha (bind s e) (bind s' e)
Proof
  rpt strip_tac >>
  rw[bind_def,exp_alpha_refl]
  >- (match_mp_tac exp_alpha_subst_closed' >> gvs[IN_FRANGE_FLOOKUP]) >>
  gvs[fmap_rel_OPTREL_FLOOKUP] >>
  rename1 ‘FLOOKUP _ z’ >>
  last_x_assum (qspec_then ‘z’ mp_tac) >>
  rw[OPTREL_SOME] >>
  imp_res_tac exp_alpha_freevars >>
  metis_tac[closed_def]
QED

Theorem exp_alpha_bind_all_closed'_alt:
  ∀s e s'.
    fmap_rel exp_alpha (DRESTRICT s (freevars e)) (DRESTRICT s' (freevars e)) ∧
    ((∀z. z ∈ FRANGE s ⇒ closed z) ⇔ (∀z. z ∈ FRANGE s' ⇒ closed z))
    ⇒
    exp_alpha (bind s e) (bind s' e)
Proof
  rpt strip_tac >>
  rw[bind_def,exp_alpha_refl]
  >- (match_mp_tac exp_alpha_subst_closed'_strong >> gvs[IN_FRANGE_FLOOKUP]) >>
  gvs[IN_FRANGE_FLOOKUP] >> metis_tac[]
QED

Theorem exp_alpha_subst_funs_closed':
  ∀s s' e.
    MAP FST f = MAP FST f' ∧
    LIST_REL exp_alpha (MAP SND f) (MAP SND f')
    ⇒
    exp_alpha (subst_funs f e) (subst_funs f' e)
Proof
  rpt strip_tac >>
  rw[subst_funs_def] >>
  match_mp_tac exp_alpha_bind_all_closed' >>
  simp[fmap_rel_OPTREL_FLOOKUP] >>
  simp[flookup_fupdate_list,GSYM MAP_REVERSE,ALOOKUP_MAP_2] >>
  rw[ALOOKUP_LEAST_EL] >>
  TRY(gvs[MAP_REVERSE] >> NO_TAC) >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- (gvs[MEM_EL] >> metis_tac[]) >>
  rw[] >>
  ‘n < LENGTH f’
    by(qpat_x_assum ‘MAP _ _ = MAP _ _’
        (strip_assume_tac o ONCE_REWRITE_RULE[LIST_EQ_REWRITE]) >>
       gvs[MEM_MAP,MEM_REVERSE] >>
       gvs[MEM_EL] >>
       spose_not_then strip_assume_tac >>
       gvs[NOT_LESS] >>
       last_x_assum (qspec_then ‘PRE (LENGTH f - n'')’ mp_tac) >>
       impl_tac >- DECIDE_TAC >>
       simp[EL_MAP,EL_REVERSE] >>
       rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >>
       DECIDE_TAC) >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- (gvs[MEM_EL] >> metis_tac[]) >>
  rw[] >>
  ‘n' = n’
    by(‘MAP FST(REVERSE f) = MAP FST(REVERSE f')’
         by(gvs[MAP_REVERSE,REVERSE_11]) >>
       match_mp_tac LESS_EQUAL_ANTISYM >>
       conj_tac >> spose_not_then strip_assume_tac >>
       gvs[NOT_LESS_EQUAL] >>
       first_x_assum drule >>
       simp[]) >>
  match_mp_tac exp_alpha_Letrec >>
  simp[] >>
  gvs[LIST_REL_EL_EQN] >>
  last_x_assum(qspec_then ‘PRE(LENGTH f - n)’ mp_tac) >>
  impl_tac >- DECIDE_TAC >>
  simp[EL_MAP,EL_REVERSE]
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

Theorem fresh_list:
  ∀s. FINITE s ⇒ ∃x. x ∉ s:('a list set)
Proof
  metis_tac[GSYM INFINITE_LIST_UNIV,NOT_IN_FINITE]
QED

Theorem exp_alpha_sym:
  ∀e e'.
    exp_alpha e e' ⇒ exp_alpha e' e
Proof
  Induct_on ‘exp_alpha’ >>
  rw[exp_alpha_Refl,exp_alpha_Lam,exp_alpha_Prim,exp_alpha_App]
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
          gvs[MEM_MAP,MEM_FILTER,GSYM perm_exp_eqvt,
              PAIR_MAP,ELIM_UNCURRY,PULL_EXISTS] >>
          metis_tac[perm1_def,PAIR,FST,SND]) >>
      simp[perm_exp_sym,perm1_sym,exp_alpha_Refl,
           MAP_MAP_o,combinTheory.o_DEF,PAIR_MAP])
  >- (gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
      gvs[MEM_MAP,ELIM_UNCURRY,PULL_EXISTS] >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Alpha >>
      qexists_tac ‘x’ >>
      conj_tac >- simp[] >>
      conj_tac
      >- (spose_not_then strip_assume_tac >>
          gvs[MEM_MAP,MEM_FILTER,GSYM perm_exp_eqvt,PAIR_MAP,
              ELIM_UNCURRY,PULL_EXISTS] >>
          metis_tac[perm1_def,PAIR,FST,SND]) >>
      simp[perm_exp_sym,perm1_sym,exp_alpha_Refl,
           MAP_MAP_o,combinTheory.o_DEF,PAIR_MAP])
  >- (gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
      gvs[MEM_MAP,ELIM_UNCURRY,PULL_EXISTS] >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Alpha >>
      qexists_tac ‘x’ >>
      conj_tac >- simp[] >>
      conj_tac
      >- (spose_not_then strip_assume_tac >>
          gvs[MEM_MAP,MEM_FILTER,GSYM perm_exp_eqvt,PAIR_MAP,
              ELIM_UNCURRY,PULL_EXISTS] >>
          metis_tac[perm1_def,PAIR,FST,SND]) >>
      simp[perm_exp_sym,perm1_sym,exp_alpha_Refl,MAP_MAP_o,
           combinTheory.o_DEF,PAIR_MAP])
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
  >- (Cases_on ‘x = y’
      >- (simp[perm_exp_id,perm1_simps,exp_alpha_Refl,ELIM_UNCURRY]) >>
      Cases_on ‘MEM x (MAP FST l)’
      >- (qpat_x_assum ‘MEM _ (MAP FST l)’
            (strip_assume_tac o REWRITE_RULE[MEM_MAP]) >>
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
      >- (qpat_x_assum ‘MEM _ (MAP FST l)’
            (strip_assume_tac o REWRITE_RULE[MEM_MAP]) >>
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
    perm_exp x y (perm_exp z å e) =
    perm_exp (perm1 x y z) (perm1 x y å) (perm_exp x y e)
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
          gvs[DISJ_EQ_IMP |> PURE_ONCE_REWRITE_RULE[DISJ_SYM],
              MEM_MAP,ELIM_UNCURRY,PULL_EXISTS,
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
      PURE_REWRITE_TAC[GSYM PAIR_MAP_THM,GSYM LAMBDA_PROD] >>
      CONV_TAC(DEPTH_CONV ETA_CONV) >>
      simp[MAP_PAIR_MAP] >>
      simp[MEM_PERM_EQ_GEN] >>
      gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
      gvs[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY,GSYM perm_exp_eqvt,
          MEM_MAP,PULL_EXISTS] >>
      match_mp_tac exp_alpha_refl >>
      simp[] >>
      simp[SimpR“$=”,Once perm_exp_compose])
  >- (simp[] >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Vacuous2 >>
      qexists_tac ‘perm1 x y y'’ >>
      simp[perm1_eq_cancel,GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
      PURE_REWRITE_TAC[GSYM PAIR_MAP_THM,GSYM LAMBDA_PROD] >>
      CONV_TAC(DEPTH_CONV ETA_CONV) >>
      simp[MAP_PAIR_MAP] >>
      simp[MEM_PERM_EQ_GEN] >>
      gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
      gvs[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY,GSYM perm_exp_eqvt,
          MEM_MAP,PULL_EXISTS] >>
      match_mp_tac exp_alpha_refl >>
      simp[] >>
      simp[SimpR“$=”,Once perm_exp_compose])
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

Theorem FUPDATE_perm_keys:
  MAP_KEYS (perm1 x y) (fm |+ (k,v)) = MAP_KEYS (perm1 x y) fm |+ (perm1 x y k,v)
Proof
  dep_rewrite.DEP_ONCE_REWRITE_TAC[MAP_KEYS_FUPDATE] >>
  rw[INJ_DEF]
QED

Theorem FDOM_perm_keys:
  z ∈ FDOM (MAP_KEYS (perm1 x y) s) ⇔
  perm1 x y z ∈ FDOM s
Proof
  rw[MAP_KEYS_def,EQ_IMP_THM] >> rw[] >>
  metis_tac[perm1_cancel]
QED

Theorem FRANGE_perm_keys:
  z ∈ FRANGE (MAP_KEYS (perm1 x y) s) ⇔
  z ∈ FRANGE s
Proof
  rw[FRANGE_DEF,EQ_IMP_THM,FDOM_perm_keys]
  >- (goal_assum drule >>
      qspecl_then [‘perm1 x y’] (drule_at (Pos last))
        (cj 2 MAP_KEYS_def |> SIMP_RULE std_ss [AND_IMP_INTRO,PULL_FORALL]) >>
      disch_then(qspecl_then[‘y’,‘x’] mp_tac) >>
      simp[perm1_simps] >>
      impl_tac >- (rw[INJ_DEF]) >>
      rw[]) >>
  rename1 ‘z ∈ FDOM s’ >>
  qexists_tac ‘perm1 x y z’ >>
  simp[] >>
  qspecl_then [‘perm1 x y’] (drule_at (Pos last))
              (cj 2 MAP_KEYS_def |> SIMP_RULE std_ss [AND_IMP_INTRO,PULL_FORALL]) >>
  disch_then(qspecl_then[‘y’,‘x’] mp_tac) >>
  simp[perm1_simps] >>
  impl_tac >- (rw[INJ_DEF]) >>
  rw[]
QED

Theorem FRANGE_MEM_eqvt:
  e ∈ FRANGE (perm_subst x y s) ⇔ perm_exp x y e ∈ FRANGE (MAP_KEYS (perm1 x y) s)
Proof
  rw[IN_FRANGE_FLOOKUP,perm_subst_flookup] >>
  rw[EQ_IMP_THM] >> metis_tac[perm_exp_cancel]
QED

Theorem exp_alpha_Letrec_Alpha_MEM:
  ∀x y f e1.
  MEM x (MAP FST f) ∧
  ¬MEM y (freevars (Letrec f e1)) ⇒
  exp_alpha (Letrec f e1)
            (Letrec (MAP (perm1 x y ## perm_exp x y) f) (perm_exp x y e1))
Proof
  rpt strip_tac >>
  reverse(Cases_on ‘x = y’)
  >- (qpat_x_assum ‘MEM _ _’
        (strip_assume_tac o
         ONCE_REWRITE_RULE[MEM_SPLIT] o ONCE_REWRITE_RULE[MEM_MAP]) >>
      rpt VAR_EQ_TAC >>
      rename1 ‘xx::_’ >>
      PairCases_on ‘xx’ >>
      simp[perm1_simps] >>
      match_mp_tac exp_alpha_Letrec_Alpha >>
      gvs[]) >>
  gvs[perm_exp_id] >>
  match_mp_tac exp_alpha_refl >>
  simp[] >>
  CONV_TAC SYM_CONV >>
  match_mp_tac MAP_ID_ON >>
  simp[FORALL_PROD,perm1_simps,perm_exp_id]
QED

Theorem FDIFF_MAP_KEYS_BIJ:
  BIJ f 𝕌(:α) 𝕌(:β) ⇒
  FDIFF (MAP_KEYS f fm) (IMAGE f s) = MAP_KEYS f (FDIFF fm s)
Proof
  rpt strip_tac >>
  simp[FDIFF_def] >>
  ‘COMPL(IMAGE f s) = IMAGE f (COMPL s)’
    by(rw[COMPL_DEF,IMAGE_DEF,SET_EQ_SUBSET,SUBSET_DEF] >>
       gvs[BIJ_DEF,INJ_DEF,SURJ_DEF] >> metis_tac[]) >>
  pop_assum SUBST_ALL_TAC >>
  gvs[BIJ_DEF] >>
  simp[DRESTRICT_MAP_KEYS_IMAGE]
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
          rw[fmap_rel_OPTREL_FLOOKUP,DOMSUB_FLOOKUP_THM,
             fdomsub_eqvt,perm1_simps] >>
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
          rw[fmap_rel_OPTREL_FLOOKUP,DOMSUB_FLOOKUP_THM,
             fdomsub_eqvt,perm1_simps] >>
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
      Cases_on ‘MEM x (MAP FST f)’
      >- (gvs[] >>
          match_mp_tac exp_alpha_Trans >>
          irule_at (Pos hd) exp_alpha_Letrec_Alpha_MEM >>
          qexists_tac ‘y’ >>
          qexists_tac ‘x’ >>
          conj_tac
          >- (rw[MAP_MAP_o,combinTheory.o_DEF] >> metis_tac[]) >>
          conj_tac
          >- (gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
              gvs[MAP_MAP_o,combinTheory.o_DEF] >>
              rw[MEM_MAP] >>
              (dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
               conj_tac
               >- (simp[FDIFF_def] >> metis_tac[IN_FRANGE_DRESTRICT_suff])) >>
              gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY]) >>
          simp[MAP_MAP_o,combinTheory.o_DEF] >>
          match_mp_tac exp_alpha_Letrec >>
          simp[subst_eqvt,MAP_MAP_o,combinTheory.o_DEF,FDIFF_eqvt] >>
          conj_tac
          >- (match_mp_tac exp_alpha_subst_closed' >>
              conj_tac
              >- (simp[FDIFF_def] >>
                  match_mp_tac IN_FRANGE_DRESTRICT_suff >>
                  simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
                  metis_tac[closed_perm]) >>
              conj_tac
              >- (simp[FDIFF_def] >>
                  match_mp_tac IN_FRANGE_DRESTRICT_suff >>
                  simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
                  metis_tac[closed_perm]) >>
              rw[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
              rw[fmap_rel_OPTREL_FLOOKUP,FDIFF_def,FLOOKUP_DRESTRICT] >>
              rw[] >>
              gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM],perm_subst_flookup] >>
              Cases_on ‘FLOOKUP s (perm1 x y k)’ >> gvs[] >>
              match_mp_tac exp_alpha_sym >>
              match_mp_tac exp_alpha_perm_irrel >>
              gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS,closed_def] >>
              res_tac >> gvs[]) >>
          simp[EVERY2_MAP] >>
          match_mp_tac EVERY2_refl >>
          PairCases >>
          rw[] >>
          match_mp_tac exp_alpha_subst_closed' >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          rw[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
          rw[fmap_rel_OPTREL_FLOOKUP,FDIFF_def,FLOOKUP_DRESTRICT] >>
          rw[] >>
          gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM],perm_subst_flookup] >>
          Cases_on ‘FLOOKUP s (perm1 x y k)’ >> gvs[] >>
          match_mp_tac exp_alpha_sym >>
          match_mp_tac exp_alpha_perm_irrel >>
          gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS,closed_def] >>
          res_tac >> gvs[]) >>
      gvs[] >>
      Cases_on ‘MEM y (MAP FST f)’
      >- (gvs[] >>
          match_mp_tac exp_alpha_Trans >>
          irule_at (Pos hd) exp_alpha_Letrec_Alpha_MEM >>
          qexists_tac ‘x’ >>
          qexists_tac ‘y’ >>
          conj_tac
          >- (rw[MAP_MAP_o,combinTheory.o_DEF] >> metis_tac[]) >>
          conj_tac
          >- (gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
              gvs[MAP_MAP_o,combinTheory.o_DEF] >>
              rw[MEM_MAP] >>
              (dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
               conj_tac
               >- (simp[FDIFF_def] >> metis_tac[IN_FRANGE_DRESTRICT_suff])) >>
              gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY]) >>
          simp[MAP_MAP_o,combinTheory.o_DEF] >>
          match_mp_tac exp_alpha_Letrec >>
          simp[subst_eqvt,MAP_MAP_o,combinTheory.o_DEF,FDIFF_eqvt] >>
          conj_tac
          >- (simp[perm1_sym',perm_subst_sym,perm_exp_sym] >>
              match_mp_tac exp_alpha_subst_closed' >>
              conj_tac
              >- (simp[FDIFF_def] >>
                  match_mp_tac IN_FRANGE_DRESTRICT_suff >>
                  simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
                  metis_tac[closed_perm]) >>
              conj_tac
              >- (simp[FDIFF_def] >>
                  match_mp_tac IN_FRANGE_DRESTRICT_suff >>
                  simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
                  metis_tac[closed_perm]) >>
              rw[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
              rw[fmap_rel_OPTREL_FLOOKUP,FDIFF_def,FLOOKUP_DRESTRICT] >>
              rw[] >>
              gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM],perm_subst_flookup] >>
              Cases_on ‘FLOOKUP s (perm1 x y k)’ >> gvs[] >>
              match_mp_tac exp_alpha_sym >>
              match_mp_tac exp_alpha_perm_irrel >>
              gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS,closed_def] >>
              res_tac >> gvs[]) >>
          simp[perm1_sym] >>
          simp[EVERY2_MAP] >>
          match_mp_tac EVERY2_refl >>
          PairCases >>
          rw[] >>
          simp[perm_exp_sym] >>
          match_mp_tac exp_alpha_subst_closed' >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          rw[perm_subst_sym,perm1_sym'] >>
          rw[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
          rw[fmap_rel_OPTREL_FLOOKUP,FDIFF_def,FLOOKUP_DRESTRICT] >>
          rw[] >>
          gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM],perm_subst_flookup] >>
          Cases_on ‘FLOOKUP s (perm1 x y k)’ >> gvs[] >>
          match_mp_tac exp_alpha_sym >>
          match_mp_tac exp_alpha_perm_irrel >>
          gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS,closed_def] >>
          res_tac >> gvs[]) >>
      ‘∀g: string # exp -> exp. MAP (λx'. (perm1 x y (FST x'), g x')) f =
                                MAP (λx'. (FST x'), g x') f’
        by(rw[MAP_EQ_f] >> gvs[MEM_MAP] >> metis_tac[perm1_def]) >>
      pop_assum(Ho_Rewrite.ONCE_REWRITE_TAC o single) >>
      match_mp_tac exp_alpha_Letrec >>
      simp[MAP_MAP_o,combinTheory.o_DEF] >>
      conj_tac
      >- (match_mp_tac exp_alpha_Trans >>
          first_x_assum(irule_at (Pos hd)) >>
          conj_tac
          >- (simp[FDIFF_def] >> metis_tac[IN_FRANGE_DRESTRICT_suff]) >>
          simp[LIST_TO_SET_MAP] >>
          ‘IMAGE (λx'. perm1 x y (FST x')) (set f) =
           IMAGE (perm1 x y) (IMAGE FST (set f))’
            by(rw[IMAGE_IMAGE,combinTheory.o_DEF]) >>
          pop_assum SUBST_ALL_TAC >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[FDIFF_MAP_KEYS_BIJ] >>
          conj_tac >- (rw[perm1_def,BIJ_DEF,INJ_DEF,SURJ_DEF] >> metis_tac[]) >>
          simp[exp_alpha_refl]) >>
      simp[EVERY2_MAP] >>
      match_mp_tac EVERY2_refl >>
      PairCases >> rw[] >>
      match_mp_tac exp_alpha_Trans >>
      first_x_assum(irule_at (Pos hd)) >>
      goal_assum drule >>
      conj_tac >- (gvs[MEM_MAP,ELIM_UNCURRY,PULL_EXISTS] >>
      metis_tac[FST,SND,PAIR]) >>
      conj_tac
      >- (simp[FDIFF_def] >> metis_tac[IN_FRANGE_DRESTRICT_suff]) >>
      simp[LIST_TO_SET_MAP] >>
      ‘IMAGE (λx'. perm1 x y (FST x')) (set f) =
       IMAGE (perm1 x y) (IMAGE FST (set f))’
        by(rw[IMAGE_IMAGE,combinTheory.o_DEF]) >>
      pop_assum SUBST_ALL_TAC >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC[FDIFF_MAP_KEYS_BIJ] >>
      conj_tac >- (rw[perm1_def,BIJ_DEF,INJ_DEF,SURJ_DEF] >> metis_tac[]) >>
      simp[exp_alpha_refl])
  >- (gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
      simp[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
      gvs[] >>
      match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Alpha_MEM >>
      qexists_tac ‘x’ >>
      qexists_tac ‘y’ >>
      conj_tac
      >- (rw[MAP_MAP_o,combinTheory.o_DEF] >> metis_tac[]) >>
      conj_tac
      >- (gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          gvs[MAP_MAP_o,combinTheory.o_DEF] >>
          rw[MEM_MAP] >>
          (dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
           conj_tac >- (simp[FDIFF_def] >> metis_tac[IN_FRANGE_DRESTRICT_suff])) >>
          gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY]) >>
      simp[MAP_MAP_o,combinTheory.o_DEF] >>
      match_mp_tac exp_alpha_Letrec >>
      simp[subst_eqvt,MAP_MAP_o,combinTheory.o_DEF,FDIFF_eqvt] >>
      conj_tac
      >- (simp[perm1_sym',perm_subst_sym,perm_exp_sym] >>
          match_mp_tac exp_alpha_subst_closed' >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          rw[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
          rw[fmap_rel_OPTREL_FLOOKUP,FDIFF_def,FLOOKUP_DRESTRICT] >>
          rw[] >>
          gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM],perm_subst_flookup] >>
          Cases_on ‘FLOOKUP s (perm1 x y k)’ >> gvs[] >>
          match_mp_tac exp_alpha_sym >>
          match_mp_tac exp_alpha_perm_irrel >>
          gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS,closed_def] >>
          res_tac >> gvs[]) >>
      simp[perm1_sym] >>
      simp[EVERY2_MAP] >>
      match_mp_tac EVERY2_refl >>
      PairCases >>
      rw[] >>
      simp[perm_exp_sym] >>
      match_mp_tac exp_alpha_subst_closed' >>
      conj_tac
      >- (simp[FDIFF_def] >>
          match_mp_tac IN_FRANGE_DRESTRICT_suff >>
          simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
          metis_tac[closed_perm]) >>
      conj_tac
      >- (simp[FDIFF_def] >>
          match_mp_tac IN_FRANGE_DRESTRICT_suff >>
          simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
          metis_tac[closed_perm]) >>
      rw[perm_subst_sym,perm1_sym'] >>
      rw[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
      rw[fmap_rel_OPTREL_FLOOKUP,FDIFF_def,FLOOKUP_DRESTRICT] >>
      rw[] >>
      gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM],perm_subst_flookup] >>
      Cases_on ‘FLOOKUP s (perm1 x y k)’ >> gvs[] >>
      match_mp_tac exp_alpha_sym >>
      match_mp_tac exp_alpha_perm_irrel >>
      gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS,closed_def] >>
      res_tac >> gvs[])
QED

Theorem exp_alpha_subst_closed_both:
  ∀x y s e.
    x ≠ y ∧
    x ∈ FDOM s ∧
    y ∈ FDOM s ∧
    (∀e. e ∈ FRANGE s ⇒ closed e) ⇒
    exp_alpha (subst s e) (subst (MAP_KEYS (perm1 x y) s) (perm_exp x y e))
Proof
  rpt strip_tac >>
  match_mp_tac exp_alpha_Trans >>
  irule_at (Pos hd) exp_alpha_perm_irrel >>
  qexists_tac ‘y’ >> qexists_tac ‘x’ >>
  simp[freevars_subst] >>
  simp[subst_eqvt] >>
  match_mp_tac exp_alpha_subst_closed' >>
  simp[FRANGE_perm_keys,FRANGE_MEM_eqvt] >>
  conj_tac >- metis_tac[closed_perm] >>
  simp[fmap_rel_OPTREL_FLOOKUP,perm_subst_flookup] >>
  strip_tac >>
  Cases_on ‘FLOOKUP s (perm1 x y k)’ >>
  gvs[] >>
  match_mp_tac exp_alpha_sym >>
  match_mp_tac exp_alpha_perm_irrel >>
  gvs[IN_FRANGE_FLOOKUP] >>
  res_tac >>
  gvs[closed_def]
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

Theorem ALOOKUP_MAP_perm:
  ALOOKUP (MAP (perm1 x y ## g) l) z =
  OPTION_MAP g (ALOOKUP l (perm1 x y z))
Proof
  Induct_on ‘l’ >> simp[FORALL_PROD] >>
  rw[] >> gvs[]
QED

Theorem ALOOKUP_MAP_perm':
  ALOOKUP (MAP (λz. (perm1 x y (FST z), g (SND z))) l) z =
  OPTION_MAP g (ALOOKUP l (perm1 x y z))
Proof
  Induct_on ‘l’ >> simp[FORALL_PROD] >>
  rw[] >> gvs[]
QED

Theorem perm_keys_update_list:
  MAP_KEYS (perm1 x y) (fm |++ l) =
  (MAP_KEYS (perm1 x y) fm) |++ (MAP (perm1 x y ## I) l)
Proof
  rw[fmap_eq_flookup,flookup_fupdate_list,GSYM MAP_REVERSE,ALOOKUP_MAP_perm] >>
  TOP_CASE_TAC >> gvs[]
QED

Theorem exp_alpha_subst_all_closed''_lemma:
  ∀f e e'.
    (∀n v. v ∈ FRANGE f ⇒ closed v) ∧ exp_alpha e e' ∧ (FDOM f ⊆ freevars e) ⇒
    exp_alpha (subst f e) (subst f e')
Proof
  Induct_on ‘exp_alpha’ >>
  rw[subst_def,exp_alpha_Refl]
  >- (metis_tac[exp_alpha_Trans,exp_alpha_freevars])
  >- (rw[] >> match_mp_tac exp_alpha_Lam >> simp[] >>
      first_x_assum match_mp_tac >>
      conj_tac >- metis_tac[IN_FRANGE_DOMSUB_suff] >>
      gvs[FDOM_DOMSUB,SUBSET_DEF])
  >- (match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Alpha >>
      goal_assum drule >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
      conj_tac >- metis_tac[IN_FRANGE_DOMSUB_suff] >>
      simp[subst_eqvt,fdomsub_eqvt,perm1_simps] >>
      match_mp_tac exp_alpha_Lam >>
      irule_at (Pos hd) exp_alpha_subst_closed'_strong >>
      conj_tac
      >- (match_mp_tac IN_FRANGE_DOMSUB_suff >>
      simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >> metis_tac[closed_perm]) >>
      conj_tac
      >- (metis_tac[IN_FRANGE_DOMSUB_suff]) >>
      rw[fmap_rel_OPTREL_FLOOKUP] >>
      rw[FLOOKUP_DRESTRICT,GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
      rw[DOMSUB_FLOOKUP_THM] >>
      Cases_on ‘x = k’ >- gvs[perm1_def] >>
      gvs[perm1_def] >>
      simp[perm_subst_flookup,perm1_def] >>
      Cases_on ‘FLOOKUP f k’ >>
      gvs[] >>
      match_mp_tac exp_alpha_sym >>
      match_mp_tac exp_alpha_perm_irrel >>
      gvs[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
      res_tac >> gvs[closed_def])
  >- (match_mp_tac exp_alpha_Prim >>
      simp[EVERY2_MAP] >>
      drule_at_then Any match_mp_tac EVERY2_mono >>
      rw[] >>
      PURE_ONCE_REWRITE_TAC[subst_FDIFF] >>
      drule_then (SUBST_ALL_TAC o GSYM) exp_alpha_freevars >>
      first_x_assum match_mp_tac >>
      conj_tac >- (metis_tac[IN_FRANGE_DRESTRICT_suff]) >>
      rw[FDOM_DRESTRICT])
  >- (match_mp_tac exp_alpha_App >> simp[] >>
      conj_tac >>
      (PURE_ONCE_REWRITE_TAC[subst_FDIFF] >>
       imp_res_tac exp_alpha_freevars >>
       simp[] >>
       first_x_assum match_mp_tac >>
       conj_tac >- (metis_tac[IN_FRANGE_DRESTRICT_suff]) >>
       rw[FDOM_DRESTRICT]))
  >- (match_mp_tac exp_alpha_Letrec >>
      simp[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
      CONV_TAC(DEPTH_CONV ETA_CONV) >> gvs[] >>
      conj_tac
      >- (PURE_ONCE_REWRITE_TAC[subst_FDIFF] >>
          drule_then (SUBST_ALL_TAC o GSYM) exp_alpha_freevars >>
          first_x_assum match_mp_tac >>
          simp[FDIFF_def] >>
          conj_tac >- metis_tac[IN_FRANGE_DRESTRICT_suff] >>
          rw[FDOM_DRESTRICT,SUBSET_DEF]) >>
      gvs[EVERY2_MAP] >>
      drule_at_then Any match_mp_tac EVERY2_mono >> rw[] >>
      PURE_ONCE_REWRITE_TAC[subst_FDIFF] >>
      drule_then (SUBST_ALL_TAC o GSYM) exp_alpha_freevars >>
      first_x_assum match_mp_tac >>
      simp[FDIFF_def] >>
      conj_tac >- metis_tac[IN_FRANGE_DRESTRICT_suff] >>
      rw[FDOM_DRESTRICT,SUBSET_DEF])
  >- (match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Alpha_MEM >>
      qexists_tac ‘y’ >> qexists_tac ‘x’ >>
      conj_tac >- simp[] >>
      conj_tac
      >- (spose_not_then strip_assume_tac >>
          gvs[MEM_MAP,ELIM_UNCURRY,DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM],
              PULL_EXISTS,FORALL_AND_THM] >>
          pop_assum mp_tac >>
          impl_tac
          >- (rw[] >>
              (dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
               conj_tac >- (simp[FDIFF_def] >>
               metis_tac[IN_FRANGE_DRESTRICT_suff]) >>
               gvs[])) >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
          conj_tac >- (simp[FDIFF_def] >>
          metis_tac[IN_FRANGE_DRESTRICT_suff]) >>
          gvs[]) >>
      match_mp_tac exp_alpha_Letrec >>
      simp[MAP_MAP_o,combinTheory.o_DEF,perm1_simps,subst_eqvt,FDIFF_eqvt] >>
      conj_tac
      >- (match_mp_tac exp_alpha_subst_closed'_strong >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
          rw[] >>
          gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
          Cases_on ‘x = k’ >- gvs[perm1_def] >>
          simp[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
          simp[FDIFF_def,FLOOKUP_DRESTRICT] >>
          simp[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          rw[] >>
          gvs[perm_subst_flookup] >>
          simp[perm1_def] >>
          Cases_on ‘FLOOKUP f k’ >> simp[] >>
          match_mp_tac exp_alpha_sym >>
          match_mp_tac exp_alpha_perm_irrel >>
          gvs[IN_FRANGE_FLOOKUP] >>
          res_tac >> gvs[closed_def]) >>
      conj_tac
      >- (rpt(match_mp_tac APPEND_EQ_IMP >> conj_tac) >>
          rw[MAP_EQ_f] >>
          pairarg_tac >> rw[]) >>
      rw[EVERY2_MAP,LIST_REL_APPEND_EQ,ELIM_UNCURRY,subst_eqvt,FDIFF_eqvt,
         LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF,perm1_simps,
         EVERY2_refl_EQ] >>
      (match_mp_tac exp_alpha_subst_closed'_strong >>
       conj_tac
       >- (simp[FDIFF_def] >>
           match_mp_tac IN_FRANGE_DRESTRICT_suff >>
           simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
           metis_tac[closed_perm]) >>
       conj_tac
       >- (simp[FDIFF_def] >>
           match_mp_tac IN_FRANGE_DRESTRICT_suff >>
           simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
           metis_tac[closed_perm]) >>
       simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
       rw[] >>
       gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
       gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
       gvs[MEM_MAP,ELIM_UNCURRY,PULL_EXISTS] >>
       Cases_on ‘x = k’ >- gvs[perm1_def] >>
       simp[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
       simp[FDIFF_def,FLOOKUP_DRESTRICT] >>
       simp[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
       rw[] >>
       gvs[perm_subst_flookup] >>
       simp[perm1_def] >>
       Cases_on ‘FLOOKUP f k’ >> simp[] >>
       match_mp_tac exp_alpha_sym >>
       match_mp_tac exp_alpha_perm_irrel >>
       gvs[IN_FRANGE_FLOOKUP] >>
       res_tac >> gvs[closed_def]))
  >- (match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Alpha_MEM >>
      qexists_tac ‘y’ >> qexists_tac ‘x’ >>
      conj_tac >- simp[] >>
      conj_tac
      >- (spose_not_then strip_assume_tac >>
          gvs[MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR]) >>
      match_mp_tac exp_alpha_Letrec >>
      simp[MAP_MAP_o,combinTheory.o_DEF,perm1_simps,subst_eqvt,FDIFF_eqvt] >>
      conj_tac
      >- (match_mp_tac exp_alpha_subst_closed'_strong >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
          rw[] >>
          gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
          simp[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
          simp[FDIFF_def,FLOOKUP_DRESTRICT] >>
          simp[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          rw[] >>
          gvs[perm_subst_flookup] >>
          Cases_on ‘x = k’
          >- (gvs[perm1_simps] >> gvs[MEM_MAP,PULL_EXISTS] >>
              metis_tac[FST,SND,PAIR,perm1_simps]) >>
          simp[perm1_def] >>
          Cases_on ‘FLOOKUP f k’ >> simp[] >>
          match_mp_tac exp_alpha_sym >>
          match_mp_tac exp_alpha_perm_irrel >>
          gvs[IN_FRANGE_FLOOKUP] >>
          res_tac >> gvs[closed_def]) >>
      conj_tac
      >- (rpt(match_mp_tac APPEND_EQ_IMP >> conj_tac) >>
          rw[MAP_EQ_f] >>
          pairarg_tac >> rw[]) >>
      rw[EVERY2_MAP,LIST_REL_APPEND_EQ,ELIM_UNCURRY,subst_eqvt,FDIFF_eqvt,
        LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF,perm1_simps,
        EVERY2_refl_EQ] >>
      (match_mp_tac exp_alpha_subst_closed'_strong >>
       conj_tac
       >- (simp[FDIFF_def] >>
           match_mp_tac IN_FRANGE_DRESTRICT_suff >>
           simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
           metis_tac[closed_perm]) >>
       conj_tac
       >- (simp[FDIFF_def] >>
           match_mp_tac IN_FRANGE_DRESTRICT_suff >>
           simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
           metis_tac[closed_perm]) >>
       simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
       rw[] >>
       gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
       simp[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
       simp[FDIFF_def,FLOOKUP_DRESTRICT] >>
       simp[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
       rw[] >>
       gvs[perm_subst_flookup] >>
       Cases_on ‘x = k’
       >- (gvs[perm1_simps] >> gvs[MEM_MAP,PULL_EXISTS] >>
           metis_tac[FST,SND,PAIR,perm1_simps]) >>
       simp[perm1_def] >>
       Cases_on ‘FLOOKUP f k’ >> simp[] >>
       match_mp_tac exp_alpha_sym >>
       match_mp_tac exp_alpha_perm_irrel >>
       gvs[IN_FRANGE_FLOOKUP] >>
       res_tac >> gvs[closed_def]))
  >- (match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Alpha_MEM >>
      qexists_tac ‘y’ >> qexists_tac ‘x’ >>
      conj_tac >- simp[] >>
      conj_tac
      >- (spose_not_then strip_assume_tac >>
          gvs[MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR]) >>
      match_mp_tac exp_alpha_Letrec >>
      simp[MAP_MAP_o,combinTheory.o_DEF,perm1_simps,subst_eqvt,FDIFF_eqvt] >>
      conj_tac
      >- (match_mp_tac exp_alpha_subst_closed'_strong >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
          rw[] >>
          gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
          simp[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
          simp[FDIFF_def,FLOOKUP_DRESTRICT] >>
          simp[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          rw[] >>
          gvs[perm_subst_flookup] >>
          Cases_on ‘x = k’
          >- (gvs[perm1_simps] >> gvs[MEM_MAP,PULL_EXISTS] >>
              metis_tac[FST,SND,PAIR,perm1_simps]) >>
          simp[perm1_def] >>
          Cases_on ‘FLOOKUP f k’ >> simp[] >>
          match_mp_tac exp_alpha_sym >>
          match_mp_tac exp_alpha_perm_irrel >>
          gvs[IN_FRANGE_FLOOKUP] >>
          res_tac >> gvs[closed_def]) >>
      conj_tac
      >- (rpt(match_mp_tac APPEND_EQ_IMP >> conj_tac) >>
          rw[MAP_EQ_f] >>
          pairarg_tac >> rw[]) >>
      rw[EVERY2_MAP,LIST_REL_APPEND_EQ,ELIM_UNCURRY,subst_eqvt,FDIFF_eqvt,
        LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF,perm1_simps,
        EVERY2_refl_EQ] >>
      (match_mp_tac exp_alpha_subst_closed'_strong >>
       conj_tac
       >- (simp[FDIFF_def] >>
           match_mp_tac IN_FRANGE_DRESTRICT_suff >>
           simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
           metis_tac[closed_perm]) >>
       conj_tac
       >- (simp[FDIFF_def] >>
           match_mp_tac IN_FRANGE_DRESTRICT_suff >>
           simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
           metis_tac[closed_perm]) >>
       simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
       rw[] >>
       gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
       simp[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
       simp[FDIFF_def,FLOOKUP_DRESTRICT] >>
       simp[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
       rw[] >>
       gvs[perm_subst_flookup] >>
       Cases_on ‘x = k’
       >- (gvs[perm1_simps] >> gvs[MEM_MAP,PULL_EXISTS] >>
           metis_tac[FST,SND,PAIR,perm1_simps]) >>
       simp[perm1_def] >>
       Cases_on ‘FLOOKUP f k’ >> simp[] >>
       match_mp_tac exp_alpha_sym >>
       match_mp_tac exp_alpha_perm_irrel >>
       gvs[IN_FRANGE_FLOOKUP] >>
       res_tac >> gvs[closed_def]))
  >- (match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Vacuous1 >>
      goal_assum drule >>
      conj_tac
      >- (gvs[MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR]) >>
      conj_tac
      >- (rw[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
          CONV_TAC(DEPTH_CONV ETA_CONV) >> simp[] >>
          gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          rpt conj_tac >> rpt gen_tac >>
          (dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
           conj_tac
           >- (simp[FDIFF_def] >> metis_tac[IN_FRANGE_DRESTRICT_suff])) >>
          simp[] >>
          rw[MEM_MAP] >>
          (dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
           conj_tac >- (simp[FDIFF_def] >>
           metis_tac[IN_FRANGE_DRESTRICT_suff])) >>
          gvs[MEM_MAP,ELIM_UNCURRY,PULL_EXISTS]) >>
      conj_tac
      >- (gvs[MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR]) >>
      conj_tac
      >- (gvs[MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR]) >>
      simp[subst_eqvt,FDIFF_eqvt,perm1_simps] >>
      match_mp_tac exp_alpha_Letrec >>
      simp[] >>
      conj_tac
      >- (match_mp_tac exp_alpha_subst_closed'_strong >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
          rw[] >>
          gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
          ‘k ≠ y’ by metis_tac[] >>
          simp[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
          simp[FDIFF_def,FLOOKUP_DRESTRICT] >>
          simp[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          Cases_on ‘k = x’
          >- (gvs[] >>
              Cases_on ‘FLOOKUP f k’ >> gvs[] >>
              gvs[flookup_thm] >>
              drule_all SUBSET_THM >>
              rw[]) >>
          rw[] >>
          Cases_on ‘FLOOKUP f k’ >> simp[exp_alpha_refl]) >>
      conj_tac
      >- (rpt(match_mp_tac APPEND_EQ_IMP >> conj_tac) >>
          rw[MAP_MAP_o,MAP_EQ_f,ELIM_UNCURRY]) >>
      rw[EVERY2_MAP,LIST_REL_APPEND_EQ,ELIM_UNCURRY,subst_eqvt,FDIFF_eqvt,
         LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF,perm1_simps,
         EVERY2_refl_EQ]
      >- (match_mp_tac exp_alpha_subst_closed'_strong >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
          rw[] >>
          gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
          gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY] >>
          ‘k ≠ y’ by(metis_tac[]) >>
          simp[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
          simp[FDIFF_def,FLOOKUP_DRESTRICT] >>
          simp[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          Cases_on ‘k = FST y'’
          >- (gvs[] >>
              Cases_on ‘FLOOKUP f (FST y')’ >> gvs[] >>
              gvs[flookup_thm] >>
              drule_all SUBSET_THM >>
              rw[]) >>
          rw[] >>
          Cases_on ‘FLOOKUP f k’ >> simp[exp_alpha_refl])
      >- (match_mp_tac exp_alpha_subst_closed'_strong >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
          rw[] >>
          gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
          gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY] >>
          simp[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
          simp[FDIFF_def,FLOOKUP_DRESTRICT] >>
          simp[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          Cases_on ‘FST y' = k’
          >- (gvs[perm1_simps]) >>
          Cases_on ‘k = y’
          >- gvs[] >>
          simp[] >>
          gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          simp[perm_subst_flookup,perm1_def] >>
          Cases_on ‘FLOOKUP f k’ >- gvs[] >>
          gvs[] >>
          ‘(∀x'. MEM x' funs1 ⇒ k ≠ if FST x' = FST y' then y else FST x') =
           (∀x'. MEM x' funs1 ⇒ k ≠ FST x')’
            by(rw[EQ_IMP_THM] >> gvs[flookup_thm] >>
               first_x_assum drule >> rw[]) >>
          pop_assum SUBST_ALL_TAC >>
          ‘(∀x'. MEM x' funs2 ⇒ k ≠ if FST x' = FST y' then y else FST x') =
           (∀x'. MEM x' funs2 ⇒ k ≠ FST x')’
            by(rw[EQ_IMP_THM] >> gvs[flookup_thm] >>
               first_x_assum drule >> rw[]) >>
          pop_assum SUBST_ALL_TAC >>
          rw[] >>
          match_mp_tac exp_alpha_sym >>
          match_mp_tac exp_alpha_perm_irrel >>
          gvs[IN_FRANGE_FLOOKUP] >>
          res_tac >>
          gvs[closed_def])
      >- (match_mp_tac exp_alpha_subst_closed'_strong >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
          rw[] >>
          gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
          gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY] >>
          ‘k ≠ y’ by(metis_tac[]) >>
          simp[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
          simp[FDIFF_def,FLOOKUP_DRESTRICT] >>
          simp[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          Cases_on ‘k = FST y'’
          >- (gvs[] >>
              Cases_on ‘FLOOKUP f (FST y')’ >> gvs[] >>
              gvs[flookup_thm] >>
              drule_all SUBSET_THM >>
              rw[]) >>
          rw[] >>
          Cases_on ‘FLOOKUP f k’ >> simp[exp_alpha_refl]))
  >- (match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_Letrec_Vacuous2 >>
      goal_assum drule >>
      conj_tac
      >- (rw[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
          CONV_TAC(DEPTH_CONV ETA_CONV) >> simp[] >>
          gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          rpt conj_tac >> rpt gen_tac >>
          (dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
           conj_tac >- (simp[FDIFF_def] >>
           metis_tac[IN_FRANGE_DRESTRICT_suff])) >>
          simp[] >>
          rw[MEM_MAP] >>
          (dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
           conj_tac >- (simp[FDIFF_def] >>
           metis_tac[IN_FRANGE_DRESTRICT_suff])) >>
          gvs[MEM_MAP,ELIM_UNCURRY,PULL_EXISTS]) >>
      conj_tac
      >- (gvs[MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR]) >>
      conj_tac
      >- (gvs[MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR]) >>
      conj_tac
      >- (gvs[MEM_MAP,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR]) >>
      conj_tac
      >- (dep_rewrite.DEP_ONCE_REWRITE_TAC[freevars_subst] >>
          conj_tac >- (simp[FDIFF_def] >>
          metis_tac[IN_FRANGE_DRESTRICT_suff]) >>
          simp[]) >>
      simp[subst_eqvt,FDIFF_eqvt,perm1_simps] >>
      match_mp_tac exp_alpha_Letrec >>
      simp[] >>
      conj_tac
      >- (match_mp_tac exp_alpha_subst_closed'_strong >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
          rw[] >>
          gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
          ‘k ≠ x’ by metis_tac[] >>
          simp[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
          simp[FDIFF_def,FLOOKUP_DRESTRICT] >>
          simp[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          Cases_on ‘k = y’
          >- (gvs[] >>
              Cases_on ‘FLOOKUP f k’ >> gvs[] >>
              gvs[flookup_thm] >>
              drule_all SUBSET_THM >>
              rw[]) >>
          rw[] >>
          Cases_on ‘FLOOKUP f k’ >> simp[exp_alpha_refl]) >>
      conj_tac
      >- (rpt(match_mp_tac APPEND_EQ_IMP >> conj_tac) >>
          rw[MAP_MAP_o,MAP_EQ_f,ELIM_UNCURRY]) >>
      rw[EVERY2_MAP,LIST_REL_APPEND_EQ,ELIM_UNCURRY,subst_eqvt,FDIFF_eqvt,
         LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF,perm1_simps,
         EVERY2_refl_EQ]
      >- (match_mp_tac exp_alpha_subst_closed'_strong >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
          rw[] >>
          gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
          gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY] >>
          ‘k ≠ x’ by(metis_tac[]) >>
          simp[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
          simp[FDIFF_def,FLOOKUP_DRESTRICT] >>
          simp[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          Cases_on ‘k = FST y'’
          >- (gvs[] >>
              Cases_on ‘FLOOKUP f (FST y')’ >> gvs[] >>
              gvs[flookup_thm] >>
              drule_all SUBSET_THM >>
              rw[] >>
              rw[MEM_MAP] >> metis_tac[]) >>
          rw[] >>
          Cases_on ‘FLOOKUP f k’ >> simp[exp_alpha_refl])
      >- (match_mp_tac exp_alpha_subst_closed'_strong >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
          rw[] >>
          gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
          gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY] >>
          simp[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
          simp[FDIFF_def,FLOOKUP_DRESTRICT] >>
          simp[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          Cases_on ‘FST y' = k’
          >- (gvs[perm1_simps]) >>
          Cases_on ‘k = x’
          >- (gvs[perm1_def]) >>
          simp[] >>
          gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          simp[perm_subst_flookup,perm1_def] >>
          Cases_on ‘FLOOKUP f k’ >- gvs[] >>
          gvs[] >>
          ‘(∀x'. MEM x' funs1 ⇒ k ≠ if FST x' = FST y' then x else FST x') =
           (∀x'. MEM x' funs1 ⇒ k ≠ FST x')’
            by(rw[EQ_IMP_THM] >> gvs[flookup_thm] >>
               first_x_assum drule >> rw[]) >>
          pop_assum SUBST_ALL_TAC >>
          ‘(∀x'. MEM x' funs2 ⇒ k ≠ if FST x' = FST y' then x else FST x') =
           (∀x'. MEM x' funs2 ⇒ k ≠ FST x')’
            by(rw[EQ_IMP_THM] >> gvs[flookup_thm] >>
               first_x_assum drule >> rw[]) >>
          pop_assum SUBST_ALL_TAC >>
          rw[] >>
          match_mp_tac exp_alpha_sym >>
          match_mp_tac exp_alpha_perm_irrel >>
          gvs[IN_FRANGE_FLOOKUP] >>
          res_tac >>
          gvs[closed_def])
      >- (match_mp_tac exp_alpha_subst_closed'_strong >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          conj_tac
          >- (simp[FDIFF_def] >>
              match_mp_tac IN_FRANGE_DRESTRICT_suff >>
              simp[FRANGE_MEM_eqvt,FRANGE_perm_keys] >>
              metis_tac[closed_perm]) >>
          simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
          rw[] >>
          gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
          gvs[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY] >>
          ‘k ≠ x’ by(metis_tac[]) >>
          simp[LIST_TO_SET_MAP,IMAGE_IMAGE,combinTheory.o_DEF] >>
          simp[FDIFF_def,FLOOKUP_DRESTRICT] >>
          simp[DISJ_EQ_IMP |> ONCE_REWRITE_RULE[DISJ_SYM]] >>
          Cases_on ‘k = FST y'’
          >- (gvs[] >>
              Cases_on ‘FLOOKUP f (FST y')’ >> gvs[] >>
              gvs[flookup_thm] >>
              drule_all SUBSET_THM >>
              rw[MEM_MAP] >> metis_tac[]) >>
          rw[] >>
          Cases_on ‘FLOOKUP f k’ >> simp[exp_alpha_refl]))
QED

Theorem exp_alpha_subst_all_closed'':
  ∀f e e'.
    (∀n v. v ∈ FRANGE f ⇒ closed v) ∧ exp_alpha e e' ⇒
    exp_alpha (subst f e) (subst f e')
Proof
  rw[] >>
  PURE_ONCE_REWRITE_TAC[subst_FDIFF] >>
  drule_then (SUBST_ALL_TAC o GSYM) exp_alpha_freevars >>
  match_mp_tac exp_alpha_subst_all_closed''_lemma >>
  conj_tac >- (metis_tac[IN_FRANGE_DRESTRICT_suff]) >>
  rw[FDOM_DRESTRICT]
QED

Theorem exp_alpha_subst_closed_strong:
  ∀x y s e.
    x ≠ y ∧ y ∉ freevars e ∧
    x ∈ FDOM s ∧
    (∀e. e ∈ FRANGE s ⇒ closed e) ⇒
    exp_alpha (subst s e) (subst (MAP_KEYS (perm1 x y) s) (perm_exp x y e))
Proof
  rw[] >>
  PURE_ONCE_REWRITE_TAC[subst_FDIFF] >>
  Cases_on ‘x ∈ freevars e’
  >- (match_mp_tac exp_alpha_Trans >>
      irule_at (Pos hd) exp_alpha_subst_closed >>
      goal_assum drule >>
      simp[FDOM_DRESTRICT] >>
      conj_tac >- metis_tac[IN_FRANGE_DRESTRICT_suff] >>
      simp[GSYM perm_exp_eqvt,LIST_TO_SET_MAP] >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC[DRESTRICT_MAP_KEYS_IMAGE] >>
      conj_tac >- rw[INJ_DEF] >>
      simp[exp_alpha_refl]) >>
  simp[GSYM perm_exp_eqvt,LIST_TO_SET_MAP] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[DRESTRICT_MAP_KEYS_IMAGE] >>
  conj_tac >- rw[INJ_DEF] >>
  match_mp_tac exp_alpha_sym >>
  match_mp_tac exp_alpha_Trans >>
  irule_at (Pos hd) exp_alpha_subst_all_closed'' >>
  simp[GSYM PULL_EXISTS] >>
  conj_tac >- (simp[FRANGE_perm_keys] >> metis_tac[IN_FRANGE_DRESTRICT_suff]) >>
  irule_at (Pos hd) exp_alpha_sym >>
  irule_at (Pos hd) exp_alpha_perm_irrel >>
  simp[] >>
  irule_at (Pos hd) exp_alpha_subst_closed' >>
  conj_tac >- (simp[FRANGE_perm_keys] >> metis_tac[IN_FRANGE_DRESTRICT_suff]) >>
  conj_tac >- (simp[FRANGE_perm_keys] >> metis_tac[IN_FRANGE_DRESTRICT_suff]) >>
  simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
  rw[]
  >- (gvs[perm1_def] >> rw[] >> gvs[] >> Cases_on ‘FLOOKUP s k’ >>
      gvs[exp_alpha_refl]) >>
  gvs[perm1_def] >> metis_tac[]
QED

Theorem exp_alpha_bind_closed:
  ∀x y s e.
    x ≠ y ∧ (y ∉ freevars e ∨ y ∈ FDOM s) ∧
    x ∈ FDOM s ⇒
    exp_alpha (bind s e) (bind (MAP_KEYS (perm1 x y) s) (perm_exp x y e))
Proof
  rpt strip_tac >>
  simp[bind_def] >>
  rw[exp_alpha_refl] >> gvs[]
  >- (match_mp_tac exp_alpha_subst_closed_strong >>
      rw[] >>
      gvs[IN_FRANGE_FLOOKUP] >>
      metis_tac[])
  >- (‘perm1 x y n ≠ n’ by metis_tac[] >>
      gvs[perm1_def,AllCaseEqs()] >>
      metis_tac[])
  >- (‘perm1 x y n ≠ n’ by metis_tac[] >>
      gvs[perm1_def,AllCaseEqs()] >>
      metis_tac[])
  >- (match_mp_tac exp_alpha_subst_closed_both >>
      rw[] >>
      gvs[IN_FRANGE_FLOOKUP] >>
      metis_tac[]
     ) >>
  ‘perm1 x y n ≠ n’ by metis_tac[] >>
  gvs[perm1_def,AllCaseEqs()] >>
  metis_tac[]
QED

Theorem exp_alpha_subst_funs_closed:
    x ≠ y ∧ MEM x (MAP FST f) ∧ ¬MEM y (freevars(Letrec f e))
    ⇒
    exp_alpha (subst_funs f e)
              (subst_funs (MAP (perm1 x y ## perm_exp x y) f) (perm_exp x y e))
Proof
  rpt strip_tac >>
  rw[subst_funs_def] >>
  match_mp_tac exp_alpha_Trans >>
  irule_at (Pos hd) exp_alpha_bind_closed >>
  goal_assum drule >>
  simp[FDOM_FUPDATE_LIST] >>
  conj_tac >- (gvs[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >> metis_tac[]) >>
  conj_tac >- (gvs[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >> metis_tac[]) >>
  qpat_x_assum ‘¬MEM y (freevars(Letrec f e))’ assume_tac >>
  qmatch_asmsub_abbrev_tac ‘¬MEM y a1’ >>
  gvs[perm_keys_update_list,MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
  match_mp_tac exp_alpha_bind_all_closed' >>
  Ho_Rewrite.PURE_ONCE_REWRITE_TAC[GSYM PAIR_MAP_THM] >>
  PURE_REWRITE_TAC[PAIR] >>
  CONV_TAC(DEPTH_CONV ETA_CONV) >>
  PURE_REWRITE_TAC[
    fmap_rel_OPTREL_FLOOKUP,flookup_fupdate_list,GSYM MAP_REVERSE] >>
  rw[ALOOKUP_MAP_perm',ALOOKUP_MAP_perm] >>
  Cases_on ‘ALOOKUP (REVERSE f) (perm1 x y k)’ >> gvs[] >>
  match_mp_tac exp_alpha_Letrec_Alpha_MEM >>
  simp[] >>
  imp_res_tac ALOOKUP_MEM >>
  gvs[MEM_REVERSE,MEM_MAP] >>
  unabbrev_all_tac >>
  gvs[MEM_FILTER,MEM_FLAT,MEM_MAP,ELIM_UNCURRY] >>
  metis_tac[perm1_def,FST,SND,PAIR]
QED

Theorem exp_alpha_subst_closed'':
  ∀x e' e e''.
    closed e' ∧ exp_alpha e e'' ⇒
    exp_alpha (subst x e' e) (subst x e' e'')
Proof
  rpt strip_tac >>
  match_mp_tac exp_alpha_subst_all_closed'' >>
  rw[]
QED

Theorem exp_alpha_bind_all_closed:
  ∀x e e'.
    exp_alpha e e' ⇒
    exp_alpha (bind x e) (bind x e')
Proof
  rw[bind_def,exp_alpha_Refl] >>
  match_mp_tac exp_alpha_subst_all_closed'' >>
  gvs[IN_FRANGE_FLOOKUP]
QED

Inductive wh_alpha:
  (wh_alpha (wh_Error) (wh_Error)) ∧
  (wh_alpha (wh_Diverge) (wh_Diverge)) ∧
  (∀a. wh_alpha (wh_Atom a) (wh_Atom a)) ∧
  (∀s x y.
     exp_alpha x y ⇒
     wh_alpha (wh_Closure s x) (wh_Closure s y)) ∧
  (∀x y e1 e2.
     x ∉ freevars e2 ∧ y ∉ freevars e1 ∧ exp_alpha e1 (perm_exp x y e2) ⇒
     wh_alpha (wh_Closure x e1) (wh_Closure y e2)) ∧
  (∀s xs ys.
     LIST_REL exp_alpha xs ys ⇒
     wh_alpha (wh_Constructor s xs) (wh_Constructor s ys))
End

CoInductive v_alpha:
[~refl:]
  (∀v. v_alpha v v) ∧
[~cons:]
   (∀s vs vs'. LIST_REL v_alpha vs vs'
      ⇒ v_alpha (Constructor s vs) (Constructor s vs')) ∧
[~closure:]
   (∀s e1 e2. exp_alpha e1 e2 ⇒ v_alpha (Closure s e1) (Closure s e2)) ∧
[~alpha:]
   (∀x y e1 e2.
      x ∉ freevars e2 ∧ y ∉ freevars e1 ∧ exp_alpha e1 (perm_exp x y e2)
    ⇒ v_alpha (Closure x e1) (Closure y e2))
End

Inductive v_prefix_alpha:
[~Refl:]
  (∀v1. v_prefix_alpha v1 v1) ∧
[~Closure:]
  (∀e1 e2 x. exp_alpha e1 e2 ⇒ v_prefix_alpha (Closure' x e1) (Closure' x e2)) ∧
[~Alpha:]
  (∀x y e1 e2.
      x ∉ freevars e2 ∧ y ∉ freevars e1 ∧ exp_alpha e1 (perm_exp x y e2)
    ⇒ v_prefix_alpha (Closure' x e1) (Closure' y e2))
End

Theorem v_alpha_trans:
  ∀v1 v2 v3. v_alpha v1 v2 ∧ v_alpha v2 v3 ⇒ v_alpha v1 v3
Proof
  CONV_TAC(QUANT_CONV(SWAP_FORALL_CONV)) >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
  ho_match_mp_tac v_alpha_coind >>
  rw[Once v_alpha_cases] >>
  qhdtm_x_assum ‘v_alpha’ (strip_assume_tac o REWRITE_RULE [v_alpha_cases]) >>
  gvs[]
  >- (disj2_tac >>
      drule_at_then Any match_mp_tac EVERY2_mono >>
      metis_tac[v_alpha_refl])
  >- (disj2_tac >>
      drule_at_then Any match_mp_tac EVERY2_mono >>
      metis_tac[v_alpha_refl])
  >- (disj2_tac >>
      gvs[LIST_REL_EL_EQN] >>
      metis_tac[])
  >- (metis_tac[exp_alpha_Trans])
  >- (metis_tac[exp_alpha_freevars,exp_alpha_Trans])
  >- (metis_tac[exp_alpha_perm_closed,perm_exp_sym,exp_alpha_Trans,
                exp_alpha_freevars])
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

Triviality closed_Letrec_perm_lemma:
  x ≠ y ∧
  y ∉ freevars(Letrec (funs1 ++ (x,e)::funs2) e1) ∧
  MEM x (MAP FST funs2) ∧
  ¬MEM y (MAP FST funs1) ∧
  ¬MEM y (MAP FST funs2) ⇒
  (closed (Letrec (funs1 ++ (y,perm_exp x y e)::funs2) e1) ⇔
   closed (Letrec (funs1 ++ (x,e)::funs2) e1))
Proof
  strip_tac >>
  ‘pure_exp$freevars (Letrec (funs1 ++ (y,perm_exp x y e)::funs2) e1) =
    freevars (Letrec (funs1 ++ (x,e)::funs2) e1)’
    suffices_by metis_tac[closed_def] >>
  match_mp_tac exp_alpha_freevars >>
  match_mp_tac exp_alpha_sym >>
  match_mp_tac exp_alpha_Letrec_Vacuous1 >>
  gvs[]
QED

Triviality closed_Letrec_perm_lemma':
  MEM x (MAP FST f) ∧
  MEM y (MAP FST f)
  ⇒
  (closed (Letrec f (perm_exp x y e1)) ⇔
   closed (Letrec f e1))
Proof
  PURE_REWRITE_TAC[closed_def] >>
  rw[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,MEM_FLAT] >>
  rw[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN] >>
  rw[PULL_EXISTS,ELIM_UNCURRY] >>
  metis_tac[perm1_def,FST,SND,PAIR]
QED

Triviality closed_Letrec_perm_lemma'':
  MEM e1 (MAP SND f) ∧
  MEM e2 (MAP SND f) ∧
  closed (Letrec f e1) ⇒
  closed (Letrec f e2)
Proof
  rw[closed_def,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,MEM_FLAT,ELIM_UNCURRY,PULL_EXISTS] >>
  metis_tac[FST,SND,PAIR]
QED

Triviality closed_Letrec_perm_lemma''':
  x ≠ y ∧
  ¬MEM x (freevars (Letrec (funs1 ++ funs2) e1)) ∧
  ¬MEM x (MAP FST funs1) ∧ ¬MEM x (MAP FST funs2) ∧
  MEM y (MAP FST funs2) ∧ ¬MEM y (freevars e) ⇒
  (closed (Letrec (funs1 ++ (y,perm_exp x y e)::funs2) e1) ⇔
   closed (Letrec (funs1 ++ (x,e)::funs2) e1))
Proof
  strip_tac >>
  ‘pure_exp$freevars (Letrec (funs1 ++ (y,perm_exp x y e)::funs2) e1) =
    freevars (Letrec (funs1 ++ (x,e)::funs2) e1)’
    suffices_by metis_tac[closed_def] >>
  match_mp_tac exp_alpha_freevars >>
  match_mp_tac exp_alpha_sym >>
  match_mp_tac exp_alpha_Letrec_Vacuous2 >>
  gvs[]
QED

Theorem exp_alpha_subst_funs_vacuous1:
  x ≠ y ∧
  MEM x (MAP FST funs2) ∧
  y ∉ freevars(Letrec (funs1 ++ (x,e)::funs2) e1) ∧
  ¬MEM y (MAP FST funs1) ∧
  ¬MEM y (MAP FST funs2)
  ⇒
  exp_alpha (subst_funs (funs1 ++ (x,e)::funs2) e1)
            (subst_funs (funs1 ++ (y,perm_exp x y e)::funs2) e1)
Proof
  rpt strip_tac >>
  simp[subst_funs_def] >>
  match_mp_tac exp_alpha_bind_all_closed'_alt >>
  simp[IN_FRANGE_FLOOKUP,flookup_fupdate_list,GSYM MAP_REVERSE,REVERSE_APPEND,
       ALOOKUP_MAP_2,ALOOKUP_APPEND] >>
  reverse conj_tac
  >- (
      rw[EQ_IMP_THM] >>
      gvs[PULL_EXISTS] >>
      pop_assum mp_tac >>
      simp[AllCaseEqs()] >>
      strip_tac >> rpt (VAR_EQ_TAC)
      >- (
          first_assum(qspec_then ‘k’ mp_tac o CONV_RULE(SWAP_FORALL_CONV)) >>
          full_simp_tac std_ss [] >> strip_tac >>
          Cases_on `x = k` >>
          full_simp_tac std_ss [ALOOKUP_NONE,MAP_REVERSE,MEM_REVERSE] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[GEN_ALL closed_Letrec_perm_lemma] >>
          full_simp_tac std_ss [] >>
          imp_res_tac ALOOKUP_MEM >>
          full_simp_tac std_ss [MEM_REVERSE,MEM_MAP,ELIM_UNCURRY, closed_def] >>
          simp[]
          )
      >- (
          dep_rewrite.DEP_ONCE_REWRITE_TAC[GEN_ALL closed_Letrec_perm_lemma'] >>
          conj_tac >- simp[] >>
          full_simp_tac std_ss [
            AllCaseEqs(),FORALL_AND_THM,DISJ_IMP_THM,PULL_EXISTS] >>
          Cases_on ‘ALOOKUP (REVERSE funs2) x’ >>
          full_simp_tac std_ss [ALOOKUP_NONE,MAP_REVERSE,MEM_REVERSE] >>
          res_tac >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[GEN_ALL closed_Letrec_perm_lemma] >>
          conj_tac >- gvs[] >>
          drule_at_then (Pos last) match_mp_tac closed_Letrec_perm_lemma'' >>
          imp_res_tac ALOOKUP_MEM >>
          simp[] >>
          gvs[MEM_MAP,EXISTS_PROD] >>
          metis_tac[]
          )
      >- (
          first_assum(qspec_then ‘k’ mp_tac o CONV_RULE(SWAP_FORALL_CONV)) >>
          full_simp_tac std_ss [] >> strip_tac >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[GEN_ALL closed_Letrec_perm_lemma] >>
          gvs[] >>
          imp_res_tac ALOOKUP_MEM >>
          gvs[MEM_REVERSE,MEM_MAP,ELIM_UNCURRY] >>
          metis_tac[FST,SND,PAIR]
          )
      >- (
          full_simp_tac std_ss [AllCaseEqs(),FORALL_AND_THM,DISJ_IMP_THM,PULL_EXISTS] >>
          full_simp_tac std_ss [ALOOKUP_NONE,MAP_REVERSE,MEM_REVERSE] >>
          rev_full_simp_tac std_ss [] >>
          qhdtm_x_assum ‘closed’ mp_tac >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[GEN_ALL closed_Letrec_perm_lemma'] >>
          conj_tac >- gvs[] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[GEN_ALL closed_Letrec_perm_lemma] >>
          conj_tac >- gvs[] >>
          strip_tac >>
          drule_at_then (Pos last) match_mp_tac closed_Letrec_perm_lemma'' >>
          simp[] >>
          imp_res_tac ALOOKUP_MEM >>
          gvs[MEM_REVERSE,MEM_MAP,ELIM_UNCURRY] >>
          metis_tac[FST,SND,PAIR]
          )
      >- (gvs[ALOOKUP_NONE,MAP_REVERSE,MEM_REVERSE])
      >- (
          full_simp_tac std_ss [AllCaseEqs(),FORALL_AND_THM,DISJ_IMP_THM,PULL_EXISTS] >>
          full_simp_tac std_ss [ALOOKUP_NONE,MAP_REVERSE,MEM_REVERSE] >>
          rev_full_simp_tac std_ss [] >>
          qhdtm_x_assum ‘closed’ mp_tac >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[GEN_ALL closed_Letrec_perm_lemma'] >>
          conj_tac >- gvs[] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[GEN_ALL closed_Letrec_perm_lemma] >>
          conj_tac >- gvs[] >>
          strip_tac >>
          drule_at_then (Pos last) match_mp_tac closed_Letrec_perm_lemma'' >>
          simp[] >>
          imp_res_tac ALOOKUP_MEM >>
          gvs[MEM_REVERSE,MEM_MAP,ELIM_UNCURRY] >>
          metis_tac[FST,SND,PAIR]
          )
      ) >>
  simp[fmap_rel_OPTREL_FLOOKUP,FLOOKUP_DRESTRICT] >>
  rw[] >>
  rw[flookup_fupdate_list,GSYM MAP_REVERSE,REVERSE_APPEND,
     ALOOKUP_APPEND,ALOOKUP_MAP_2]
  >- (Cases_on ‘ALOOKUP (REVERSE funs2) k’ >>
      gvs[ALOOKUP_NONE,OPTREL_SOME,AllCaseEqs(),PULL_EXISTS] >>
      gvs[MAP_REVERSE] >>
      match_mp_tac exp_alpha_Letrec_Vacuous1 >> gvs[] >>
      imp_res_tac ALOOKUP_MEM >>
      gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR])
  >- (Cases_on ‘ALOOKUP (REVERSE funs2) k’ >>
      gvs[ALOOKUP_NONE,OPTREL_SOME,AllCaseEqs(),PULL_EXISTS] >>
      gvs[MAP_REVERSE] >>
      match_mp_tac exp_alpha_Letrec_Vacuous1 >> gvs[] >>
      imp_res_tac ALOOKUP_MEM >>
      gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR])
  >- (Cases_on ‘ALOOKUP (REVERSE funs2) k’ >>
      gvs[ALOOKUP_NONE,OPTREL_SOME,AllCaseEqs(),PULL_EXISTS] >>
      gvs[MAP_REVERSE]
      >- (Cases_on ‘ALOOKUP (REVERSE funs1) k’ >>
          gvs[ALOOKUP_NONE,OPTREL_SOME,AllCaseEqs(),PULL_EXISTS] >>
          gvs[MAP_REVERSE] >>
          match_mp_tac exp_alpha_Letrec_Vacuous1 >> gvs[] >>
          imp_res_tac ALOOKUP_MEM >>
          gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR]) >>
      match_mp_tac exp_alpha_Letrec_Vacuous1 >> gvs[] >>
      imp_res_tac ALOOKUP_MEM >>
      gvs[MEM_MAP,PULL_EXISTS,ELIM_UNCURRY] >> metis_tac[FST,SND,PAIR])
QED

Theorem exp_alpha_subst_funs_vacuous2:
  x ≠ y ∧
  ¬MEM x (freevars (Letrec (funs1 ++ funs2) e1)) ∧
  ¬MEM x (MAP FST funs1) ∧ ¬MEM x (MAP FST funs2) ∧
  MEM y (MAP FST funs2) ∧ ¬MEM y (freevars e)
  ⇒
  exp_alpha (subst_funs (funs1 ++ (x,e)::funs2) e1)
            (subst_funs (funs1 ++ (y,perm_exp x y e)::funs2) e1)
Proof
  rpt strip_tac >>
  match_mp_tac exp_alpha_sym >>
  match_mp_tac exp_alpha_Trans >>
  qexists_tac
    ‘subst_funs (funs1 ++ (x, perm_exp y x (perm_exp x y e))::funs2) e1’ >>
  conj_tac
  >- (match_mp_tac exp_alpha_subst_funs_vacuous1 >>
      gvs[GSYM perm_exp_eqvt,MEM_PERM_EQ_GEN,perm1_simps]) >>
  simp[perm_exp_sym,exp_alpha_refl]
QED

Inductive wh_alpha:
[~refl:]
  (wh_alpha v v) ∧
[~cons:]
  (LIST_REL exp_alpha e1s e2s
    ⇒ wh_alpha (wh_Constructor s e1s) (wh_Constructor s e2s)) ∧
[~closure:]
   (exp_alpha e1 e2 ⇒ wh_alpha (wh_Closure s e1) (wh_Closure s e2)) ∧
[~alpha:]
   (x ∉ freevars e2 ∧ y ∉ freevars e1 ∧ exp_alpha e1 (perm_exp x y e2)
    ⇒ wh_alpha (wh_Closure x e1) (wh_Closure y e2))
End

Triviality wh_alpha_sym_imp:
  ∀wh1 wh2.
    wh_alpha wh1 wh2
  ⇒ wh_alpha wh2 wh1
Proof
  Induct_on `wh_alpha` >> rw[]
  >- simp[wh_alpha_refl]
  >- (
    irule wh_alpha_cons >>
    fs[LIST_REL_EL_EQN] >> rw[] >>
    irule exp_alpha_sym >> fs[]
    )
  >- (
    irule wh_alpha_closure >>
    irule exp_alpha_sym >> fs[]
    )
  >- (
    irule wh_alpha_alpha >> fs[] >>
    irule exp_alpha_perm_closed_sym >>
    qexists_tac `y` >> qexists_tac `x` >>
    simp[perm_exp_cancel] >>
    simp[Once perm_exp_sym] >>
    irule exp_alpha_sym >> fs[]
    )
QED

Theorem wh_alpha_sym:
  ∀wh1 wh2. wh_alpha wh1 wh2 ⇔ wh_alpha wh2 wh1
Proof
  rw[] >> eq_tac >> rw[wh_alpha_sym_imp]
QED

Triviality perm_exp_eqvt_alt:
  ∀ v1 v2 e.
    IMAGE (perm1 v1 v2) (freevars e) = freevars (perm_exp v1 v2 e)
Proof
  rw[EXTENSION] >>
  simp[GSYM perm_exp_eqvt, MEM_MAP]
QED

Triviality perm1_MAP_unchanged:
  ∀x y e.
    ¬ MEM x (freevars e) ∧ ¬ MEM y (freevars e)
  ⇒ MAP (perm1 x y) (freevars e) = freevars e
Proof
  rw[LIST_EQ_REWRITE, EL_MAP] >> gvs[MEM_EL, GSYM IMP_DISJ_THM, perm1_def]
QED

Triviality perm1_swap:
  ∀x y z a.
    x ≠ z ∧ x ≠ y ⇒
  perm1 x y (perm1 y z a) =
  perm1 y z (perm1 x z a)
Proof
  rw[perm1_def]
  >- (Cases_on `a = x` >> gvs[] >> Cases_on `a = z` >> gvs[])
  >- (Cases_on `y = a` >> gvs[])
  >- (Cases_on `a = x` >> gvs[] >> Cases_on `a = z` >> gvs[])
  >- (Cases_on `a = x` >> gvs[] >> Cases_on `a = z` >> gvs[])
  >- (Cases_on `a = x` >> gvs[])
  >- (Cases_on `a = z` >> gvs[])
  >- (Cases_on `a = z` >> gvs[])
  >- (Cases_on `a = z` >> gvs[])
  >- (Cases_on `a = z` >> gvs[])
QED

Triviality perm_exp_swap:
  ∀x y e z.
    x ≠ z ∧ x ≠ y ⇒
  perm_exp x y (perm_exp y z e) =
  perm_exp y z (perm_exp x z e)
Proof
  recInduct perm_exp_ind >> rw[perm_exp_def]
  >- metis_tac[perm1_swap]
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >>
    rw[] >> first_x_assum irule >> simp[]
    )
  >- (first_x_assum irule >> simp[])
  >- (first_x_assum irule >> simp[])
  >- metis_tac[perm1_swap]
  >- (first_x_assum irule >> simp[])
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >> rw[] >>
    Cases_on `x` >> gvs[] >>
    rw[] >- metis_tac[perm1_swap] >>
    first_x_assum irule >> simp[] >> goal_assum drule
    )
  >- (first_x_assum irule >> simp[])
QED

Theorem wh_alpha_trans:
  ∀wh1 wh2 wh3.
    wh_alpha wh1 wh2 ∧
    wh_alpha wh2 wh3
  ⇒ wh_alpha wh1 wh3
Proof
  Induct_on `wh_alpha` >> rw[]
  >- (
    gvs[Once wh_alpha_cases] >>
    irule wh_alpha_cons >> fs[] >>
    gvs[LIST_REL_EL_EQN] >> rw[] >>
    irule exp_alpha_Trans >>
    res_tac >> goal_assum drule >> fs[]
    )
  >- (
    reverse (gvs[Once wh_alpha_cases])
    >- (
      simp[Once wh_alpha_sym] >>
      irule wh_alpha_alpha >> fs[] >>
      imp_res_tac exp_alpha_freevars >> gvs[] >>
      irule exp_alpha_perm_closed_sym >>
      qexists_tac `y` >> qexists_tac `s` >> simp[perm_exp_cancel] >>
      irule exp_alpha_sym >> fs[] >>
      irule exp_alpha_Trans >>
      goal_assum drule >>
      simp[Once perm_exp_sym]
      ) >>
    irule wh_alpha_closure >> fs[] >>
    irule exp_alpha_Trans >>
    goal_assum drule >> fs[]
    )
  >- (
    imp_res_tac exp_alpha_freevars >>
    gvs[GSYM perm_exp_eqvt, MEM_MAP, GSYM IMP_DISJ_THM] >>
    reverse (gvs[Once wh_alpha_cases])
    >- (
      rename1 `wh_alpha _ (wh_Closure z _)` >>
      Cases_on `x = z` >> gvs[]
      >- (
        irule wh_alpha_closure >>
        irule exp_alpha_perm_closed_sym >>
        irule_at Any exp_alpha_Trans >>
        goal_assum (drule_at Any) >>
        irule exp_alpha_perm_closed_sym >>
        qexists_tac `y` >> qexists_tac `x` >>
        simp[perm_exp_cancel, Once perm_exp_sym]
        ) >>
      irule wh_alpha_alpha >> rw[]
      >- (
        imp_res_tac exp_alpha_freevars >>
        gvs[GSYM perm_exp_eqvt, MEM_MAP, GSYM IMP_DISJ_THM] >>
        first_x_assum (qspec_then `x` mp_tac) >> simp[perm1_def] >>
        last_x_assum (qspec_then `x` mp_tac) >>
        rewrite_tac[perm1_def] >> simp[] >>
        IF_CASES_TAC >> simp[]
        )
      >- (
        simp[MEM_PERM_EQ_GEN] >>
        rw[perm1_def]
        ) >>
      imp_res_tac exp_alpha_freevars >>
      gvs[GSYM perm_exp_eqvt] >>
      gvs[MEM_PERM_EQ_GEN, perm1_simps] >>
      last_assum (qspec_then `x` mp_tac) >>
      rewrite_tac[perm1_def] >> simp[] >>
      IF_CASES_TAC >> gvs[perm1_simps]
      >- (
        `∀x:string. perm1 x x = I ∧ perm_exp x x = I` by (
          rw[] >> irule EQ_EXT >> rw[perm1_simps, perm_exp_id]) >> gvs[] >>
        irule exp_alpha_Trans >>
        goal_assum drule >> fs[]
        ) >>
      rw[] >>
      irule exp_alpha_Trans >> goal_assum drule >>
      Cases_on `y = z` >> gvs[perm1_simps, perm_exp_id]
      >- (irule exp_alpha_perm_closed >> simp[]) >>
      irule exp_alpha_perm_closed_sym >>
      qexists_tac `x` >> qexists_tac `y` >>
      simp[perm_exp_cancel] >>
      simp[Once perm_exp_sym] >>
      qspecl_then [`y`,`x`,`e2'`,`z`] assume_tac perm_exp_swap >> gvs[] >>
      pop_assum kall_tac >>
      `perm_exp y z e2' = perm_exp z y e2'` by simp[Once perm_exp_sym] >>
      pop_assum SUBST_ALL_TAC >>
      qspecl_then [`x`,`z`,`e2'`,`y`] assume_tac perm_exp_swap >> gvs[] >>
      pop_assum SUBST_ALL_TAC >>
      irule exp_alpha_Trans >>
      goal_assum drule >>
      irule exp_alpha_perm_closed >>
      irule exp_alpha_perm_irrel >> gvs[]
      )
    >- (
      Cases_on `x = y` >> gvs[perm1_simps, perm_exp_id]
      >- (
        irule wh_alpha_closure >>
        irule exp_alpha_Trans >> goal_assum drule >> gvs[]
        ) >>
      irule wh_alpha_alpha >>
      last_x_assum (qspec_then `x` mp_tac) >> simp[perm1_def] >> strip_tac >>
      simp[MEM_PERM_EQ] >>
      imp_res_tac exp_alpha_freevars >> gvs[] >>
      irule exp_alpha_Trans >>
      goal_assum drule >>
      irule exp_alpha_perm_closed >> simp[]
      )
    >- (
      Cases_on `x = y` >> gvs[perm1_simps, perm_exp_id]
      >- (irule wh_alpha_closure >> simp[]) >>
      irule wh_alpha_alpha >>
      last_x_assum (qspec_then `x` mp_tac) >> simp[perm1_def] >> strip_tac >>
      simp[MEM_PERM_EQ]
      )
    )
QED

Theorem exp_alpha_eval_wh_to:
  ∀k e1 e2. exp_alpha e1 e2 ⇒ wh_alpha (eval_wh_to k e1) (eval_wh_to k e2)
Proof
  completeInduct_on `k` >>
  Induct_on `exp_alpha` >> rw[]
  >- simp[wh_alpha_refl]
  >- metis_tac[wh_alpha_trans]
  >- (
    simp[eval_wh_to_def] >>
    irule wh_alpha_closure >> fs[]
    )
  >- (
    simp[eval_wh_to_def] >>
    irule wh_alpha_alpha >>
    simp[perm_exp_cancel, exp_alpha_refl, GSYM perm_exp_eqvt, MEM_PERM_EQ]
    )
  >- (
    simp[eval_wh_to_def] >>
    IF_CASES_TAC >> gvs[]
    >- simp[wh_alpha_refl] >>
    TOP_CASE_TAC >> gvs[]
    >- (
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      IF_CASES_TAC >- simp[wh_alpha_cases] >>
      Cases_on `es` >> gvs[] >>
      Cases_on `t` >> gvs[] >>
      Cases_on `t'` >> gvs[] >>
      Cases_on `t` >> gvs[] >>
      first_x_assum (qspec_then `k - 1` mp_tac) >> gvs[] >>
      disch_then imp_res_tac >>
      qpat_x_assum `wh_alpha (_ h) _` mp_tac >>
      simp[Once wh_alpha_cases] >>
      TOP_CASE_TAC >> gvs[] >> rw[] >>
      simp[wh_alpha_cases] >>
      IF_CASES_TAC >> gvs[] >>
      IF_CASES_TAC >> gvs[]
      )
    >- (
      irule wh_alpha_cons >>
      gvs[LIST_REL_EL_EQN] >> rw[]
      )
    >- (
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      IF_CASES_TAC >- simp[wh_alpha_cases] >>
      Cases_on `es` >> gvs[] >>
      last_x_assum (qspec_then `k - 1` mp_tac) >> gvs[] >>
      disch_then drule >>
      simp[Once wh_alpha_cases] >>
      TOP_CASE_TAC >> gvs[] >> rw[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      simp[wh_alpha_cases]
      )
    >- (
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      IF_CASES_TAC >- simp[wh_alpha_cases] >>
      Cases_on `es` >> gvs[] >>
      last_x_assum (qspec_then `k - 1` mp_tac) >> impl_tac >- fs[] >>
      strip_tac >> first_assum drule >>
      SIMP_TAC bool_ss [Once wh_alpha_cases] >>
      TOP_CASE_TAC >> rw[] >> gvs[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      simp[wh_alpha_cases] >>
      simp[GSYM wh_alpha_cases] >>
      first_x_assum irule >> gvs[LIST_REL_EL_EQN]
      )
    >- (
      rename1 `LIST_REL _ e1s e2s` >>
      qmatch_goalsub_abbrev_tac `MAP f e1s` >>
      qsuff_tac `get_atoms (MAP f e1s) = get_atoms (MAP f e2s)`
      >- (rw[] >> TOP_CASE_TAC >> simp[wh_alpha_cases]) >>
      unabbrev_all_tac >>
      qpat_x_assum `LIST_REL _ _ _` mp_tac >>
      qid_spec_tac `e2s` >> qid_spec_tac `e1s` >>
      ho_match_mp_tac LIST_REL_ind >> simp[] >> rw[get_atoms_def] >>
      last_x_assum (qspec_then `k - 1` mp_tac) >> gvs[] >>
      disch_then drule >>
      simp[Once wh_alpha_cases] >>
      TOP_CASE_TAC >> gvs[] >> rw[] >>
      first_assum SUBST_ALL_TAC >> simp[]
      )
    >- (
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      Cases_on `es` >> gvs[wh_alpha_cases]
      )
    )
  >- (
    simp[eval_wh_to_def] >>
    IF_CASES_TAC >- gvs[wh_alpha_cases] >>
    IF_CASES_TAC >- gvs[wh_alpha_cases] >>
    TOP_CASE_TAC >- gvs[wh_alpha_cases, dest_wh_Closure_def] >>
    Cases_on `dest_wh_Closure (eval_wh_to k e2)`
    >- gvs[wh_alpha_cases, dest_wh_Closure_def] >>
    Cases_on `eval_wh_to k e1` >> gvs[dest_wh_Closure_def] >>
    Cases_on `eval_wh_to k e2` >> gvs[dest_wh_Closure_def] >>
    IF_CASES_TAC >- gvs[wh_alpha_cases] >> simp[] >>
    first_x_assum irule >> simp[] >>
    qpat_x_assum `wh_alpha (wh_Closure _ _) _` mp_tac >>
    simp[Once wh_alpha_cases] >> rw[]
    >- (irule exp_alpha_bind_all_closed' >> simp[fmap_rel_def])
    >- (
      irule exp_alpha_Trans >> qexists_tac `bind s e2' e` >> rw[]
      >- (irule exp_alpha_bind_all_closed' >> simp[fmap_rel_def])
      >- (irule exp_alpha_bind_all_closed >> simp[])
      )
    >- (
      irule exp_alpha_Trans >> qexists_tac `bind s e2' e` >> rw[]
      >- (irule exp_alpha_bind_all_closed' >> simp[fmap_rel_def]) >>
      Cases_on `s = s'` >> gvs[perm_exp_id]
      >- (irule exp_alpha_bind_all_closed >> simp[exp_alpha_refl]) >>
      drule exp_alpha_bind_closed >>
      disch_then (qspecl_then [`FEMPTY |+ (s,e2')`,`e`] assume_tac) >> gvs[] >>
      gvs[FUPDATE_perm_keys, perm1_def] >>
      irule exp_alpha_Trans >>
      goal_assum drule >>
      irule exp_alpha_bind_all_closed >>
      irule exp_alpha_perm_closed_sym >>
      qexists_tac `s` >> qexists_tac `s'` >>
      simp[perm_exp_cancel]
      )
    )
  >- (
    simp[eval_wh_to_def] >>
    IF_CASES_TAC >- gvs[wh_alpha_cases] >> simp[] >>
    first_x_assum irule >> gvs[] >>
    irule exp_alpha_Trans >> qexists_tac `subst_funs funs' e1` >> rw[]
    >- (irule exp_alpha_subst_funs_closed' >> gvs[LIST_REL_EL_EQN]) >>
    simp[subst_funs_def] >>
    irule exp_alpha_bind_all_closed >> simp[]
    )
  >- (
    simp[eval_wh_to_def] >>
    IF_CASES_TAC >- gvs[wh_alpha_cases] >> simp[] >>
    first_x_assum irule >> gvs[] >>
    drule exp_alpha_subst_funs_closed >>
    disch_then (qspec_then `funs1 ++ (x,e)::funs2` assume_tac) >>
    gvs[perm1_simps]
    )
  >- (
    simp[eval_wh_to_def] >>
    IF_CASES_TAC >- gvs[wh_alpha_cases] >> simp[] >>
    first_x_assum irule >> gvs[] >>
    drule exp_alpha_subst_funs_closed >>
    disch_then (qspec_then `funs1 ++ (x,e)::funs2` assume_tac) >>
    gvs[perm1_simps]
    )
  >- (
    simp[eval_wh_to_def] >>
    IF_CASES_TAC >- gvs[wh_alpha_cases] >> simp[] >>
    first_x_assum irule >> gvs[] >>
    drule exp_alpha_subst_funs_closed >>
    disch_then (qspec_then `funs1 ++ (x,e)::funs2` assume_tac) >>
    gvs[perm1_simps]
    )
  >- (
    simp[eval_wh_to_def] >>
    IF_CASES_TAC >- gvs[wh_alpha_cases] >> simp[] >>
    first_x_assum irule >> gvs[] >>
    irule exp_alpha_subst_funs_vacuous1 >> simp[]
    )
  >- (
    simp[eval_wh_to_def] >>
    IF_CASES_TAC >- gvs[wh_alpha_cases] >> simp[] >>
    first_x_assum irule >> gvs[] >>
    irule exp_alpha_subst_funs_vacuous2 >> simp[]
    )
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
  gvs[Once v_alpha_cases,v_prefix_alpha_cases] >>
  imp_res_tac LIST_REL_LENGTH >>
  gvs[oEL_THM]
  >- (rename1 ‘EL z vs’ >>
      ‘v_alpha (EL z vs') (EL z vs)’
        by(gvs[LIST_REL_EL_EQN]) >>
      first_x_assum drule_all >>
      strip_tac >> simp[])
  >- metis_tac[LIST_REL_EL_EQN]
QED

Theorem gen_v_alpha_pres: (* not used *)
  ∀v1 v2 f g.
  (∀path vp1 vp2 n1 n2.
    f path = (vp1,n1) ∧ g path = (vp2,n2)
  ⇒ v_prefix_alpha vp1 vp2 ∧ n1 = n2) ∧
  v1 = gen_v f ∧ v2 = gen_v g
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

Theorem exp_alpha_eval_wh:
  ∀e1 e2. exp_alpha e1 e2 ⇒ wh_alpha (eval_wh e1) (eval_wh e2)
Proof
  rw[eval_wh_def] >> drule exp_alpha_eval_wh_to >> rw[] >>
  DEEP_INTRO_TAC some_intro >> reverse (rw[])
  >- (
    DEEP_INTRO_TAC some_intro >> rw[wh_alpha_cases] >>
    rpt (first_x_assum (qspec_then `x` assume_tac)) >> gvs[wh_alpha_cases]
    ) >>
  DEEP_INTRO_TAC some_intro >> reverse (rw[])
  >- (rpt (first_x_assum (qspec_then `x` assume_tac)) >> gvs[wh_alpha_cases]) >>
  Cases_on `x ≤ x'`
  >- (drule_all eval_wh_inc >> rw[] >> metis_tac[]) >>
  `x' ≤ x` by gvs[] >>
  drule_all eval_wh_inc >> rw[] >> metis_tac[]
QED

Theorem follow_path_v_prefix_alpha:
  ∀path e1 e2 vp1 vp2 n1 n2.
    exp_alpha e1 e2 ∧
    follow_path eval_wh e1 path = (vp1,n1) ∧
    follow_path eval_wh e2 path = (vp2,n2)
  ⇒ v_prefix_alpha vp1 vp2 ∧ n1 = n2
Proof
  Induct >> gvs[follow_path_def]
  >- (
    rpt (gen_tac) >> strip_tac >>
    drule exp_alpha_eval_wh >>
    Cases_on `eval_wh e1` >> simp[Once wh_alpha_cases] >> rw[] >> gvs[] >>
    simp[v_prefix_alpha_Refl] >> gvs[LIST_REL_EL_EQN]
    >- (irule v_prefix_alpha_Closure >> simp[])
    >- (irule v_prefix_alpha_Alpha >> simp[])
    ) >>
  rpt (gen_tac) >> strip_tac >>
  drule exp_alpha_eval_wh >>
  Cases_on `eval_wh e1` >> simp[Once wh_alpha_cases] >> rw[] >> gvs[] >>
  simp[v_prefix_alpha_Refl] >> gvs[LIST_REL_EL_EQN, oEL_THM] >>
  Cases_on `h < LENGTH e2s` >> gvs[v_prefix_alpha_Refl] >>
  first_x_assum drule >> rw[] >>
  last_x_assum drule_all >> simp[]
QED

Theorem exp_alpha_eval: (* not used *)
  ∀e1 e2. exp_alpha e1 e2 ⇒ v_alpha (eval e1) (eval e2)
Proof
  rw[eval_def, v_unfold_def] >>
  match_mp_tac gen_v_alpha_pres >>
  ntac 2 (irule_at (Pos last) EQ_REFL) >>
  rpt GEN_TAC >> disch_then strip_assume_tac >>
  irule follow_path_v_prefix_alpha >>
  goal_assum drule >> fs[] >> goal_assum drule >> fs[]
QED

Triviality LIST_REL_mono:
  (∀x y. R x y ∧ MEM x xs ∧ MEM y ys ⇒ R1 x y) ==>
  LIST_REL R xs ys ⇒ LIST_REL R1 xs ys
Proof
  qid_spec_tac ‘ys’ \\ Induct_on ‘xs’ \\ fs [] \\ rw []
QED

Theorem eval_wh_Closure_closed:
  eval_wh e = wh_Closure v body ∧ closed e ⇒ freevars body SUBSET {v}
Proof
  rw [] \\ imp_res_tac eval_wh_freevars_SUBSET
  \\ fs [] \\ fs [SUBSET_DEF]
  \\ gvs [closed_def] \\ rw[] \\ res_tac \\ fs [] \\ metis_tac []
QED

Theorem compatible_exp_alpha:
  compatible (λR (x,y). exp_alpha x y ∧ closed x ∧ closed y)
Proof
  simp[compatible_def,SUBSET_DEF] >>
  PairCases >>
  rw[ELIM_UNCURRY] >>
  gvs[FF_def,unfold_rel_def] >>
  rpt strip_tac >>
  drule exp_alpha_eval_wh >>
  rpt strip_tac >>
  gvs[Once wh_alpha_cases]
  >- (
    rw[exp_alpha_refl] >>
    imp_res_tac eval_wh_Closure_closed >>
    imp_res_tac eval_wh_freevars_SUBSET >> fs [] >>
    match_mp_tac closed_freevars_subst >> fs []
    )
  >- (
    rw[exp_alpha_refl]
    >- (irule exp_alpha_subst_closed'' >> simp[]) >>
    imp_res_tac eval_wh_Closure_closed >>
    imp_res_tac eval_wh_freevars_SUBSET >> fs [] >>
    match_mp_tac closed_freevars_subst >> fs []
    )
  >- (
    rw[exp_alpha_refl]
    >- (
      Cases_on `x = y` >> gvs[perm_exp_id]
      >- (irule exp_alpha_subst_closed'' >> simp[]) >>
      irule exp_alpha_Trans >> qexists_tac `subst x e (perm_exp x y e2)` >>
      rw[]
      >- (irule exp_alpha_subst_closed'' >> simp[]) >>
      irule exp_alpha_sym >>
      once_rewrite_tac[perm_exp_sym] >>
      irule exp_alpha_subst_closed_single >> simp[]
      ) >>
    imp_res_tac eval_wh_Closure_closed >>
    imp_res_tac eval_wh_freevars_SUBSET >> fs [] >>
    match_mp_tac closed_freevars_subst >> fs []
    )
  >- (
    rw[LIST_REL_EL_EQN, exp_alpha_refl] >>
    drule eval_wh_freevars_SUBSET >>
    gvs[closed_def, MEM_MAP, PULL_FORALL, GSYM IMP_DISJ_THM] >> rw[] >>
    fs[Once MONO_NOT_EQ] >>
    simp[pure_miscTheory.NIL_iff_NOT_MEM] >> rw[] >>
    first_x_assum irule >> simp[EL_MEM]
    )
  >- (
    gvs[LIST_REL_EL_EQN] >> rw[] >>
    imp_res_tac eval_wh_freevars_SUBSET >>
    gvs[closed_def, MEM_MAP, PULL_FORALL, GSYM IMP_DISJ_THM] >> rw[] >>
    fs[Once MONO_NOT_EQ] >>
    simp[pure_miscTheory.NIL_iff_NOT_MEM] >> rw[]
    >- (first_x_assum irule >> simp[EL_MEM])
    >- (last_x_assum irule >> simp[EL_MEM])
    )
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
  conj_tac
  >- (
    match_mp_tac(GEN_ALL exp_alpha_Alpha) >>
    full_simp_tac std_ss [closed_def] >>
    gvs[FILTER_EQ_NIL,EVERY_MEM] >> metis_tac[]
    ) >>
  full_simp_tac std_ss [closed_def] >>
  gvs[FILTER_EQ_NIL,GSYM perm_exp_eqvt,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  metis_tac[perm1_def]
QED

Theorem app_similarity_Lam_Alpha_alt:
  closed(Lam y e1) ⇒
  Lam x (perm_exp x y e1) ≲ Lam y e1
Proof
  Cases_on ‘x = y’ >- (simp[perm_exp_id,reflexive_app_similarity']) >>
  strip_tac >>
  match_mp_tac companion_app_similarity  >>
  match_mp_tac(companion_exp_alpha |> SIMP_RULE std_ss [IN_DEF] |> GEN_ALL) >>
  conj_tac
  >- (
    match_mp_tac exp_alpha_sym >> simp [Once perm_exp_sym] >>
    match_mp_tac(GEN_ALL exp_alpha_Alpha) >>
    full_simp_tac std_ss [closed_def] >>
    gvs[FILTER_EQ_NIL,EVERY_MEM] >> metis_tac[]
    ) >>
  full_simp_tac std_ss [closed_def] >>
  gvs[FILTER_EQ_NIL,GSYM perm_exp_eqvt,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  metis_tac[perm1_def]
QED

Theorem app_similarity_perm_exp:
  ∀e x y.  closed e ⇒ perm_exp x y e ≲ e
Proof
  rw[] >>
  irule companion_app_similarity  >>
  irule (companion_exp_alpha |> SIMP_RULE std_ss [IN_DEF]) >>
  simp[closed_perm] >>
  irule exp_alpha_sym >> irule exp_alpha_perm_irrel >>
  gvs[closed_def]
QED

Theorem app_similarity_perm_exp_left:
  ∀e1 e2 x y.  e1 ≲ e2 ⇒ perm_exp x y e1 ≲ e2
Proof
  rw[] >>
  assume_tac transitive_app_similarity >> gvs[transitive_def] >>
  first_assum irule >> goal_assum (drule_at Any) >>
  irule app_similarity_perm_exp >>
  imp_res_tac app_similarity_closed
QED

Theorem app_similarity_perm_exp_alt:
  ∀e x y.  closed e ⇒ e ≲ perm_exp x y e
Proof
  rw[] >>
  irule companion_app_similarity  >>
  irule (companion_exp_alpha |> SIMP_RULE std_ss [IN_DEF]) >>
  simp[closed_perm] >>
  irule exp_alpha_perm_irrel >>
  gvs[closed_def]
QED

Theorem app_similarity_perm_exp_right:
  ∀e1 e2 x y.  e1 ≲ e2 ⇒ e1 ≲ perm_exp x y e2
Proof
  rw[] >>
  assume_tac transitive_app_similarity >> gvs[transitive_def] >>
  first_assum irule >> goal_assum (drule_at Any) >>
  irule app_similarity_perm_exp_alt >>
  imp_res_tac app_similarity_closed
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

Theorem exp_alpha_app_similarity:
  ∀x y. exp_alpha x y ∧ closed x ∧ closed y ⇒ x ≲ y
Proof
  rw [] \\ match_mp_tac companion_app_similarity
  \\ match_mp_tac(no_IN companion_exp_alpha) \\ fs []
QED

Theorem exp_alpha_app_bisimilarity:
  ∀x y. exp_alpha x y ∧ closed x ∧ closed y ⇒ x ≃ y
Proof
  rw [app_bisimilarity_similarity]
  \\ match_mp_tac exp_alpha_app_similarity \\ fs []
  \\ match_mp_tac exp_alpha_sym \\ fs []
QED

Theorem exp_alpha_exp_eq:
  ∀x y. exp_alpha x y ⇒ x ≅ y
Proof
  fs [exp_eq_def] \\ rw []
  \\ match_mp_tac exp_alpha_app_bisimilarity
  \\ conj_tac THEN1 (match_mp_tac exp_alpha_bind_all_closed \\ fs [])
  \\ rw [bind_def] \\ TRY (fs [closed_def] \\ NO_TAC)
  \\ match_mp_tac IMP_closed_subst
  \\ fs [FLOOKUP_DEF,FRANGE_DEF,PULL_EXISTS]
QED

val _ = export_theory();
