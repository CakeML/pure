(*
   Relation describing inlining and proof that it fits bidir from pure_pres
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory listTheory pred_setTheory mlstringTheory;
open pure_cexpTheory pure_cexp_lemmasTheory pureLangTheory pure_exp_lemmasTheory
     pure_barendregtTheory pure_presTheory;

val _ = new_theory "pure_inline_rel_alt";

val _ = set_grammar_ancestry ["pure_barendregt", "pure_cexp", "pure_pres"]

Overload Letrec1 = ``λd f e1 e2. Letrec d [(f,e1)] e2``

(*---------------------------------------------------------------------------*
   Definition of what inliner can remember
 *---------------------------------------------------------------------------*)

Datatype:
  inline_mem = Simple 'a mlstring ('a cexp) | Rec 'a ((mlstring # 'a cexp) list)
End

Definition lhs_names_def[simp]:
  lhs_names (Simple d v e) = {v} ∧
  lhs_names (Rec d fns) = set (MAP FST fns)
End

Definition lhs_vars_def[simp]:
  lhs_vars (Simple d v e) = freevars_cexp e ∧
  lhs_vars (Rec d fns) = BIGUNION (set $ MAP (freevars_cexp o SND) fns)
End

(*---------------------------------------------------------------------------*
   Definition of precondition pre
 *---------------------------------------------------------------------------*)

Definition vars_of_def:
  vars_of [] = {} ∧
  vars_of (h::t) = lhs_names h ∪ lhs_vars h ∪ vars_of t
End

Definition pre_def:
  pre l (x:'a cexp) ⇔ barendregt (exp_of x) ∧
                      DISJOINT (boundvars (exp_of x)) (IMAGE explode $ vars_of l)
End

(*---------------------------------------------------------------------------*
   Definition of lets_ok
 *---------------------------------------------------------------------------*)

Definition lets_ok_def:
  (lets_ok [] ⇔ T) ∧
  (lets_ok ((Simple d v x)::rest) ⇔
    v ∉ freevars_cexp x ∧
    DISJOINT ({v} ∪ freevars_cexp x) (BIGUNION (set $ MAP lhs_names rest)) ∧
    lets_ok rest) ∧
  (lets_ok ((Rec d fns)::rest) ⇔
    DISJOINT
      (set (MAP FST fns) ∪ BIGUNION (set $ MAP (freevars_cexp o SND) fns))
      (BIGUNION (set $ MAP lhs_names rest)) ∧
    ALL_DISTINCT (MAP FST fns) ∧
    lets_ok rest)
End

(*---------------------------------------------------------------------------*
   Lemmas about lets_ok etc.
 *---------------------------------------------------------------------------*)

Theorem vars_of_eq_MAP:
  vars_of l = BIGUNION $ set $ MAP (λx. lhs_names x ∪ lhs_vars x) l
Proof
  Induct_on `l` >> rw[vars_of_def]
QED

Theorem vars_of_APPEND:
  ∀xs ys. vars_of (xs ++ ys) = vars_of xs ∪ vars_of ys
Proof
  simp[vars_of_eq_MAP]
QED

Theorem lhs_names_SUBSET_vars_of:
  ∀xs. EVERY (λx. lhs_names x ⊆ vars_of xs) xs
Proof
  Induct >> rw[lhs_names_def, vars_of_def] >> gvs[SUBSET_DEF] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem lhs_exp_SUBSET_vars_of:
  ∀xs. BIGUNION $ set (MAP lhs_vars xs) ⊆ pure_inline_rel_alt$vars_of xs
Proof
  rw[vars_of_eq_MAP, SUBSET_DEF, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem lets_ok_APPEND:
  lets_ok (l1 ++ l2) ⇔
    lets_ok l1 ∧ lets_ok l2 ∧
    DISJOINT
      (BIGUNION $ set (MAP (λx. lhs_names x ∪ lhs_vars x) l1))
      (BIGUNION $ set (MAP lhs_names l2))
Proof
  Induct_on `l1` >> rw[lets_ok_def] >>
  Cases_on `h` >> gvs[lets_ok_def] >> pop_assum kall_tac >>
  eq_tac >> rw[] >> gvs[SF DNF_ss, MEM_MAP] >> metis_tac[]
QED

Theorem lets_ok_SNOC_Simple_lemma[local]:
  lets_ok xs ∧ v ∉ freevars_cexp x1 ∧ v ∉ vars_of xs
  ⇒ lets_ok (SNOC (Simple d v x1) xs)
Proof
  simp[SNOC_APPEND] >> Induct_on `xs` >> rw[] >> gvs[lets_ok_def] >>
  Cases_on `h` >> gvs[lets_ok_def, vars_of_def, SF DNF_ss] >>
  gvs[vars_of_eq_MAP, MEM_MAP, PULL_FORALL] >> metis_tac[]
QED

Theorem lets_ok_SNOC_Simple:
  lets_ok xs ∧ pre xs (Let d v x y) ⇒ lets_ok (SNOC (Simple d' v x) xs)
Proof
  rw[] >> irule lets_ok_SNOC_Simple_lemma >>
  gvs[pre_def, exp_of_def, barendregt_alt_def, allvars_thm, freevars_exp_of]
QED

Theorem lets_ok_SNOC_Rec_lemma[local]:
  lets_ok xs ∧ DISJOINT (set $ MAP FST fns) (vars_of xs) ∧ ALL_DISTINCT (MAP FST fns)
  ⇒ lets_ok (SNOC (Rec d fns) xs)
Proof
  simp[SNOC_APPEND] >> Induct_on `xs` >> rw[] >> gvs[lets_ok_def] >>
  Cases_on `h` >> gvs[lets_ok_def, vars_of_def, DISJOINT_SYM, SF DNF_ss]
QED

Theorem lets_ok_SNOC_Rec:
  lets_ok xs ∧ pre xs (Letrec d fns y) ⇒
  lets_ok (SNOC (Rec d' fns) xs)
Proof
  rw[] >> irule lets_ok_SNOC_Rec_lemma >> gvs[pre_def, exp_of_def] >> conj_tac
  >- (
    gvs[barendregt_alt_def, MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY] >>
    qpat_x_assum `ALL_DISTINCT _` mp_tac >>
    simp[GSYM combinTheory.o_DEF, GSYM MAP_MAP_o]
    ) >>
  gvs[DISJOINT_ALT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  gvs[MEM_MAP, PULL_EXISTS, FORALL_PROD] >> metis_tac[]
QED

Theorem lets_ok_Simple_MEM:
  lets_ok xs ∧ MEM (Simple d x e) xs ⇒ x ∉ freevars_cexp e
Proof
  Induct_on `xs` >> rw[] >> gvs[lets_ok_def] >>
  Cases_on `h` >> gvs[lets_ok_def]
QED

Theorem lets_ok_Rec_MEM:
  lets_ok xs ∧ MEM (Rec d fns) xs ⇒ ALL_DISTINCT (MAP FST fns)
Proof
  Induct_on `xs` >> rw[] >> gvs[lets_ok_def] >>
  Cases_on `h` >> gvs[lets_ok_def]
QED

(*---------------------------------------------------------------------------*
   Lemmas and precondition pre
 *---------------------------------------------------------------------------*)

Theorem pre_Let:
  pre xs (Let d v x y) ⇒
  pre xs x ∧ pre (xs ++ [Simple d' v x]) y ∧ v ∉ vars_of xs
Proof
  rw[pre_def, exp_of_def, barendregt_alt_def, vars_of_APPEND, vars_of_def]
  >- simp[DISJOINT_SYM]
  >- gvs[GSYM freevars_exp_of, allvars_thm]
QED

Theorem pre_App:
  pre xs (App d x y) ⇒ pre xs x ∧ EVERY (pre xs) y
Proof
  rw[pre_def] >> gvs[exp_of_def, barendregt_Apps, boundvars_Apps] >>
  gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, pre_def]
QED

Theorem pre_Prim:
  pre xs (Prim d x ys) ⇒ EVERY (pre xs) ys
Proof
  gvs[pre_def, exp_of_def, barendregt_alt_def, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem pre_Lam:
  pre xs (Lam d ws x) ⇒ EVERY (λw. w ∉ vars_of xs) ws ∧ pre xs x
Proof
  rw[pre_def] >> gvs[exp_of_def, barendregt_Lams, boundvars_Lams] >>
  simp[EVERY_MEM] >> gen_tac >> strip_tac >>
  gvs[DISJOINT_ALT, MEM_MAP, PULL_EXISTS, PULL_FORALL] >> metis_tac[]
QED

Triviality barendregt_exp_of_Case_imp:
  barendregt (exp_of (Case d k v css usopt)) ⇒
    barendregt (exp_of k) ∧
    EVERY (λ(cn,pvs,e). barendregt (exp_of e)) css ∧
    OPTION_ALL (λ(cn_ars,e). barendregt (exp_of e)) usopt
Proof
  simp[exp_of_def] >>
  simp[Once COND_RAND] >> simp[Once barendregt_alt_def] >>
  simp[APPEND_EQ_CONS, PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM,
       RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR] >>
  simp[barendregt_alt_def, barendregt_rows_of] >> strip_tac >>
  gvs[EVERY_MEM, FORALL_PROD, MEM_MAP, PULL_EXISTS] >> rw[]
  >- res_tac >>
  Cases_on `usopt` >> gvs[] >> pairarg_tac >> gvs[barendregt_IfDisj]
QED

Theorem pre_Case:
  pre xs (Case d x v css usopt) ⇒
    pre xs x ∧ EVERY (λ(cn,pvs,e). pre xs e) css ∧
    OPTION_ALL (λ(cn_ars,e). pre xs e) usopt ∧
    v ∉ vars_of xs ∧
    EVERY (λ(cn,pvs,e). DISJOINT (set pvs) (vars_of xs)) css
Proof
  simp[pre_def] >> strip_tac >>
  imp_res_tac barendregt_exp_of_Case_imp >> gvs[] >>
  gvs[boundvars_exp_of_Case] >> rw[]
  >- (
    gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
    rpt $ first_x_assum drule >> rw[]
    )
  >- (Cases_on `usopt` >> gvs[] >> pairarg_tac >> gvs[])
  >- (
    gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
    last_x_assum drule >> rw[] >> gvs[DISJOINT_ALT]
    )
QED

Theorem pre_Annot:
  pre xs (Annot d annot e) ⇒ pre xs e
Proof
  rw[pre_def, exp_of_def]
QED

Theorem pre_SNOC_Simple:
  pre xs x ∧
  v ∉ freevars_cexp x1 ∧ explode v ∉ boundvars (exp_of x) ∧
  DISJOINT (boundvars (exp_of x)) (boundvars (exp_of x1)) ∧
  DISJOINT (boundvars (exp_of x)) (freevars (exp_of x1))
  ⇒ pre (xs ++ [Simple d v x1]) x
Proof
  gvs[pre_def, vars_of_APPEND, vars_of_def, GSYM freevars_exp_of] >>
  simp[DISJOINT_SYM]
QED

Theorem pre_SNOC_Rec:
  pre xs x ∧
  DISJOINT (set $ MAP (explode o FST) fns) (boundvars (exp_of x)) ∧
  DISJOINT (BIGUNION $ set $ MAP (freevars o exp_of o SND) fns) (boundvars (exp_of x))
  ⇒ pre (xs ++ [Rec d fns]) x
Proof
  gvs[pre_def, vars_of_APPEND, vars_of_def] >> rw[DISJOINT_SYM]
  >- gvs[GSYM LIST_TO_SET_MAP, MAP_MAP_o] >>
  simp[Once DISJOINT_SYM] >>
  gvs[DISJOINT_ALT, MEM_MAP, freevars_exp_of, PULL_EXISTS, PULL_FORALL] >>
  metis_tac[]
QED

Theorem pre_Letrec:
  pre xs (Letrec d ys x) ⇒
  pre xs x ∧ EVERY (pre xs) (MAP SND ys) ∧
  DISJOINT (set (MAP (explode o FST) ys)) (boundvars (exp_of x)) ∧
  DISJOINT (BIGUNION $ set $ MAP (freevars o exp_of o SND) ys) (boundvars (exp_of x)) ∧
  EVERY (λ(v,e). v ∉ vars_of xs) ys
Proof
  rw[]
  >- gvs[pre_def, exp_of_def, barendregt_alt_def]
  >- (
    gvs[pre_def, exp_of_def, barendregt_alt_def,
        EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
    rw[] >> gvs[] >> res_tac
    )
  >- (
    gvs[pre_def, exp_of_def, barendregt_alt_def,
        MEM_MAP, PULL_EXISTS, FORALL_PROD, DISJOINT_ALT] >>
    metis_tac[]
    )
  >- (
    gvs[pre_def, exp_of_def, barendregt_alt_def] >>
    gvs[MEM_MAP, PULL_EXISTS] >>
    last_x_assum drule >> pairarg_tac >> gvs[] >> simp[allvars_thm]
    )
  >- (
    rw[EVERY_MEM, FORALL_PROD] >> gvs[pre_def, exp_of_def] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY] >>
    gvs[DISJOINT_ALT, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> res_tac
    )
QED

Theorem pre_Letrec1:
  pre xs (Letrec1 d v x y) ⇒
  pre xs x ∧ pre (xs ++ [Rec d' [(v,x)]]) y ∧ v ∉ vars_of xs
Proof
  strip_tac >> imp_res_tac pre_Letrec >> gvs[] >> irule pre_SNOC_Rec >> gvs[]
QED

Theorem pre_Letrec_alt:
  pre xs (Letrec d fns e) ⇒
  pre xs e ∧ pre (xs ++ [Rec d' fns]) e ∧
  EVERY (λ(v,e). v ∉ vars_of xs) fns
Proof
  rw[] >> imp_res_tac pre_Letrec >> irule pre_SNOC_Rec >> gvs[]
QED

(*---------------------------------------------------------------------------*
   Theorems about pushing and pulling let-expressions
 *---------------------------------------------------------------------------*)

Definition Binds_def:
  Binds [] y = y ∧
  Binds ((Simple d v x)::xs) y = Let d v x (Binds xs y) ∧
  Binds ((Rec d fns)::xs) y = Letrec d fns (Binds xs y)
End

Theorem Binds_APPEND:
  Binds (l1 ++ l2) e = Binds l1 (Binds l2 e)
Proof
  Induct_on `l1` >> rw[Binds_def] >> Cases_on `h` >> gvs[Binds_def]
QED

Theorem Binds_SNOC:
  Binds [] y = y ∧
  Binds (SNOC (Simple d x e) xs) y = Binds xs (Let d x e y) ∧
  Binds (SNOC (Rec d fns) xs) y = Binds xs (Letrec d fns y)
Proof
  simp[Binds_def] >> Induct_on `xs` >> rw[Binds_def] >>
  Cases_on `h` >> gvs[Binds_def]
QED

Definition mem_rel[simp]:
  mem_rel R (Simple d x e) h = (∃d' e'. h = Simple d' x e' ∧ R e e') ∧
  mem_rel R (Rec d fns) h =
    ∃d' fns'. h = Rec d' fns' ∧
              LIST_REL (λ(f,e) (f',e'). f = f' ∧ R e e') fns fns'
End

Theorem mem_rel_refl:
  (∀e. R e e) ⇒ mem_rel R x x
Proof
  Cases_on `x` >> rw[] >> gvs[LIST_REL_EL_EQN, ELIM_UNCURRY]
QED

Triviality LIST_REL_mem_rel_refl[simp]:
  LIST_REL (mem_rel bidir) xs xs
Proof
  rw[LIST_REL_EL_EQN] >> irule mem_rel_refl >> simp[]
QED

Theorem bidir_Binds:
  LIST_REL (mem_rel bidir) xs ys ∧ bidir e1 e2
    ⇒ Binds xs e1 <--> Binds ys e2
Proof
  Induct_on `LIST_REL` >> rw[Binds_def] >>
  Cases_on `h1` >> gvs[Binds_def]
  >- (irule bidir_Let >> simp[])
  >- (
    irule bidir_Letrec >> simp[] >>
    gvs[LIST_REL_EL_EQN, ELIM_UNCURRY]
    )
QED

Triviality LIST_REL_mem_rel_refl_pres[simp]:
  LIST_REL (mem_rel pres) xs xs
Proof
  rw[LIST_REL_EL_EQN] >> irule mem_rel_refl >> simp[]
QED

Theorem pres_Binds:
  LIST_REL (mem_rel pres) xs ys ∧ e1 ~~> e2
    ⇒ Binds xs e1 ~~> Binds ys e2
Proof
  Induct_on `LIST_REL` >> rw[Binds_def] >>
  Cases_on `h1` >> gvs[Binds_def]
  >- (irule pres_Let >> simp[])
  >- (
    irule pres_Letrec >> simp[] >>
    gvs[LIST_REL_EL_EQN, ELIM_UNCURRY]
    )
QED

Theorem Binds_MEM:
  ∀xs e x.
    MEM e xs ∧ lets_ok xs ⇒ Binds xs x <--> Binds (xs ++ [e]) x
Proof
  Induct using SNOC_INDUCT >> rw[] >> gvs[]
  >- (
    last_x_assum kall_tac >>
    Cases_on `e` >> gvs[Binds_APPEND, Binds_def, Binds_SNOC]
    >- (
      irule bidir_Binds >> rw[] >> irule bidir_Let_dup >>
      gvs[SNOC_APPEND, lets_ok_APPEND, lets_ok_def, freevars_exp_of]
      )
    >- (irule bidir_Binds >> rw[] >> simp[bidir_Letrec_dup])
    ) >>
  gvs[Binds_APPEND, SNOC_APPEND] >>
  irule bidir_trans >> last_assum $ irule_at Any >>
  goal_assum drule >> conj_asm1_tac >- gvs[lets_ok_APPEND] >>
  irule bidir_trans >> last_assum $ irule_at Any >> goal_assum drule >> rw[] >>
  irule $ iffLR bidir_sym >>
  irule bidir_trans >> last_x_assum $ irule_at Any >> goal_assum drule >> rw[] >>
  irule bidir_Binds >> rw[] >> irule $ iffLR bidir_sym >>
  Cases_on `e` >> Cases_on `x` >> gvs[Binds_def]
  >- (
    irule bidir_Let_Let_Let >> gvs[lets_ok_APPEND, lets_ok_def] >>
    gvs[MEM_MAP, PULL_EXISTS] >> first_x_assum drule >> gvs[freevars_exp_of] >>
    imp_res_tac lets_ok_Simple_MEM >> gvs[]
    )
  >- (
    irule bidir_Let_Let_Letrec >> gvs[lets_ok_APPEND, lets_ok_def] >>
    gvs[MEM_MAP, PULL_EXISTS, freevars_exp_of] >>
    first_x_assum drule >> gvs[MEM_MAP, DISJOINT_SYM] >>
    imp_res_tac lets_ok_Simple_MEM >> gvs[]
    )
  >- (
    irule bidir_Letrec_Letrec_Let >> gvs[lets_ok_APPEND, lets_ok_def] >>
    gvs[MEM_MAP, PULL_EXISTS, freevars_exp_of] >>
    first_x_assum drule >> gvs[MEM_MAP, EVERY_MEM, PULL_EXISTS] >> metis_tac[]
    )
  >- (
    irule bidir_Letrec_Letrec_Letrec >> gvs[lets_ok_APPEND, lets_ok_def] >>
    gvs[MEM_MAP, PULL_EXISTS] >>
    first_x_assum drule >> gvs[EVERY_MAP, EVERY_MEM, MEM_MAP, PULL_EXISTS, DISJOINT_SYM]
    )
QED

Theorem bidir_Binds_push_Let:
  ∀xs d v x y.
  v ∉ vars_of xs
  ⇒ Binds xs (Let d v x y) <--> Let d v (Binds xs x) (Binds xs y)
Proof
  Induct using SNOC_INDUCT >> rw[Binds_SNOC] >>
  Cases_on `x` >> rw[Binds_SNOC] >>
  irule bidir_trans >> irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl >>
  last_x_assum $ irule_at Any >> gvs[SNOC_APPEND, vars_of_APPEND] >>
  irule bidir_push_pull >> simp[Once push_pull_cases] >> gvs[vars_of_def] >>
  gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem bidir_Binds_push_Prim:
  ∀xs d p es.
    es ≠ [] ⇒
    Binds xs (Prim d p es) <--> Prim d p (MAP (λe. Binds xs e) es)
Proof
  Induct using SNOC_INDUCT >> rw[Binds_SNOC] >>
  Cases_on `x` >> rw[Binds_SNOC] >>
  irule bidir_trans >> irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl >>
  irule_at Any bidir_push_pull >> simp[Once push_pull_cases, PULL_EXISTS] >>
  irule_at Any bidir_trans >> first_x_assum $ irule_at Any >> simp[] >>
  irule_at Any bidir_Prim >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
  qexists `a` >> rw[LIST_REL_EL_EQN]
QED

Theorem bidir_Binds_push_App:
  ∀xs d e es.
    Binds xs (App d e es) <--> App d (Binds xs e) (MAP (λe. Binds xs e) es)
Proof
  Induct using SNOC_INDUCT >> rw[Binds_SNOC] >>
  Cases_on `x` >> rw[Binds_SNOC] >>
  irule bidir_trans >> irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl >>
  irule_at Any bidir_push_pull >> simp[Once push_pull_cases, PULL_EXISTS] >>
  irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
  irule_at Any bidir_App >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
  qexistsl [`a`,`a`] >> rw[LIST_REL_EL_EQN]
QED

Theorem bidir_Binds_push_Lam:
  ∀xs d ys e.
    DISJOINT (set ys) (vars_of xs)
  ⇒ Binds xs (Lam d ys e) <--> Lam d ys (Binds xs e)
Proof
  Induct using SNOC_INDUCT >> rw[Binds_SNOC] >>
  Cases_on `x` >> rw[Binds_SNOC] >>
  irule bidir_trans >> irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl >>
  irule_at Any bidir_push_pull >> simp[Once push_pull_cases, PULL_EXISTS] >>
  irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
  irule_at Any bidir_Lam >> irule_at Any bidir_refl >>
  gvs[SNOC_APPEND, vars_of_APPEND, vars_of_def, DISJOINT_SYM] >>
  conj_tac >- (gvs[EVERY_MEM, DISJOINT_ALT] >> metis_tac[]) >>
  gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, DISJOINT_SYM]
QED

Theorem bidir_Binds_push_Letrec:
  ∀xs d fns e.
    DISJOINT (set $ MAP FST fns) (vars_of xs)
  ⇒ Binds xs (Letrec d fns e) <-->
    Letrec d (MAP (λ(f,e). (f,Binds xs e)) fns) (Binds xs e)
Proof
  Induct using SNOC_INDUCT >> rw[Binds_SNOC]
  >- simp[ELIM_UNCURRY] >>
  Cases_on `x` >> rw[Binds_SNOC] >>
  irule bidir_trans >> irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl >>
  irule_at Any bidir_push_pull >> simp[Once push_pull_cases, PULL_EXISTS] >>
  irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
  irule_at Any bidir_Letrec >> irule_at Any bidir_refl >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  simp[GSYM pure_miscTheory.FST_THM] >>
  gvs[SNOC_APPEND, vars_of_APPEND, vars_of_def, DISJOINT_SYM] >>
  rw[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY] >>
  gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Triviality bidir_Binds_push_Letrec1:
  ∀xs d v x y.
    v ∉ vars_of xs
  ⇒ Binds xs (Letrec1 d v x y) <--> Letrec1 d v (Binds xs x) (Binds xs y)
Proof
  rw[] >> irule bidir_trans >> irule_at Any bidir_Binds_push_Letrec >> simp[]
QED

Theorem bidir_Binds_push_Case:
  ∀xs d e v css usopt.
    v ∉ vars_of xs ∧
    EVERY (λ(cn,pvs,e). DISJOINT (set pvs) (vars_of xs)) css
  ⇒ Binds xs (Case d e v css usopt) <-->
    Case d (Binds xs e) v
      (MAP (λ(cn,pvs,e). (cn,pvs,Binds xs e)) css)
      (OPTION_MAP (λ(cn_ars,e). (cn_ars,Binds xs e)) usopt)
Proof
  Induct using SNOC_INDUCT >> rw[Binds_SNOC]
  >- simp[ELIM_UNCURRY] >>
  Cases_on `x` >> rw[Binds_SNOC] >>
  irule bidir_trans >> irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl>>
  irule_at Any bidir_push_pull >> simp[Once push_pull_cases, PULL_EXISTS]
  >- (
    irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
    irule_at Any bidir_Case >> irule_at Any bidir_refl >> rw[] >>
    gvs[SNOC_APPEND, vars_of_APPEND, vars_of_def, DISJOINT_SYM]
    >- rw[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
    >- (Cases_on `usopt` >> gvs[] >> rpt (pairarg_tac >> gvs[])) >>
    gvs[EVERY_MAP, FORALL_PROD, EVERY_MEM] >> metis_tac[]
    )
  >- (
    irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
    irule_at Any bidir_Case >> irule_at Any bidir_refl >> rw[] >>
    gvs[SNOC_APPEND, vars_of_APPEND, vars_of_def, DISJOINT_SYM]
    >- rw[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
    >- (Cases_on `usopt` >> gvs[] >> rpt (pairarg_tac >> gvs[])) >>
    gvs[DISJOINT_ALT, EVERY_MAP, MEM_FLAT, MEM_MAP, PULL_FORALL,
        PULL_EXISTS, ELIM_UNCURRY, EVERY_MEM] >>
    metis_tac[]
    )
QED

Theorem bidir_Binds_push_Annot:
  ∀xs d annot e. Binds xs (Annot d annot e) <--> Annot d annot (Binds xs e)
Proof
  Induct using SNOC_INDUCT >> rw[Binds_SNOC] >>
  Cases_on `x` >> rw[Binds_SNOC] >>
  irule bidir_trans >> irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl >>
  irule_at Any bidir_push_pull >> simp[Once push_pull_cases, PULL_EXISTS] >>
  irule_at Any bidir_trans >> first_x_assum $ irule_at Any >> irule_at Any bidir_refl
QED

(*---------------------------------------------------------------------------*
   Definition of inline_rev_rel - reversible inlinings
 *---------------------------------------------------------------------------*)

Inductive inline_rev_rel:
[~Var:]
  MEM (Simple d x e) l
    ⇒ inline_rev_rel l (Var d x) e
[~Var_Rec:]
  MEM (Rec d fns) l ∧ MEM (x,e) fns
    ⇒ inline_rev_rel l (Var d x) e
[~Let:]
  inline_rev_rel l e1 e1' ∧
  inline_rev_rel (l ++ [Simple d x e1]) e2 e2'
    ⇒ inline_rev_rel l (Let d x e1 e2) (Let d x e1' e2')
[~Prim:]
  LIST_REL (inline_rev_rel l) e1s e2s
    ⇒ inline_rev_rel l (Prim d p e1s) (Prim d p e2s)
[~App:]
  inline_rev_rel l e1 e1' ∧
  LIST_REL (inline_rev_rel l) e2s e2s'
    ⇒ inline_rev_rel l (App d e1 e2s) (App d e1' e2s')
[~Lam:]
  inline_rev_rel l e1 e2
    ⇒ inline_rev_rel l (Lam d xs e1) (Lam d xs e2)
[~Letrec:]
  LIST_REL (λ(f1,e1) (f2,e2). f2 = f1 ∧ inline_rev_rel l e1 e2) fns1 fns2 ∧
  inline_rev_rel l e1 e2
    ⇒ inline_rev_rel l (Letrec d fns1 e1) (Letrec d fns2 e2)
[~Letrec_Rec:]
  LIST_REL (λ(f1,e1) (f2,e2). f2 = f1 ∧ inline_rev_rel l e1 e2) fns1 fns2 ∧
  inline_rev_rel (l ++ [Rec d fns1]) e1 e2
    ⇒ inline_rev_rel l (Letrec d fns1 e1) (Letrec d fns2 e2)
[~spec:]
  inline_rev_rel l e1 e2 ∧
  (∀e d. Letrec1 d x e1 e <--> Let d x e1' e) ∧
  x ∉ freevars_cexp e1' ∧
  DISJOINT (boundvars (exp_of e3)) (boundvars (exp_of e1')) ∧
  DISJOINT (boundvars (exp_of e3)) (freevars (exp_of e1')) ∧
  inline_rev_rel (l ++ [Simple d x e1']) e3 e4
    ⇒ inline_rev_rel l (Letrec1 d x e1 e3) (Letrec1 d x e2 e4)
[~Case:]
  inline_rev_rel l e1 e2 ∧
  LIST_REL
    (λ(cn1,pvs1,k1) (cn2,pvs2,k2). cn2 = cn1 ∧ pvs2 = pvs1 ∧ inline_rev_rel l k1 k2)
    css1 css2 ∧
  OPTREL (λ(cn_ars1,k1) (cn_ars2,k2). cn_ars2 = cn_ars1 ∧ inline_rev_rel l k1 k2)
    usopt1 usopt2
    ⇒ inline_rev_rel l (Case d e1 v css1 usopt1) (Case d e2 v css2 usopt2)
[~Annot:]
  inline_rev_rel l e1 e2
    ⇒ inline_rev_rel l (Annot d a e1) (Annot d' a e2)
[~refl:]
  inline_rev_rel l e e
[~trans:]
  inline_rev_rel l e1 e2 ∧ inline_rev_rel l e2 e3 ∧ pre l e2
    ⇒ inline_rev_rel l e1 e3
[~simp:]
  inline_rev_rel l e1 e2 ∧ e2 <--> e2'
    ⇒ inline_rev_rel l e1 e2'
End

(*---------------------------------------------------------------------------*
   inline_rev_rel ⇒ bidir
 *---------------------------------------------------------------------------*)

Theorem inline_rev_rel_IMP_bidir_lemma:
  ∀xs x y.
    inline_rev_rel xs x y ∧ lets_ok xs ∧ pre xs x ⇒
    Binds xs x <--> Binds xs y
Proof
  Induct_on `inline_rev_rel` >> rw[]
  >~ [`Var`,`Simple`]
  >- (
    irule bidir_trans >>
    irule_at Any Binds_MEM >> goal_assum drule >> simp[] >>
    simp[Binds_APPEND, Binds_def] >>
    irule bidir_Binds >> rw[] >> simp[bidir_Let_unroll]
    )
  >~ [`Var`,`Rec`]
  >- (
    irule bidir_trans >>
    irule_at Any Binds_MEM >> goal_assum drule >> simp[] >>
    irule $ iffLR bidir_sym >> irule bidir_trans >>
    irule_at Any Binds_MEM >> goal_assum drule >> simp[] >>
    simp[Binds_APPEND, Binds_def] >>
    irule bidir_Binds >> rw[] >>
    irule $ iffLR bidir_sym >> irule bidir_Letrec_unroll >> simp[] >>
    imp_res_tac lets_ok_Rec_MEM
    )
  >~ [`Let`]
  >- (
    rename1 `Binds xs (Let _ v e1 e2) <--> Binds xs (Let _ v e1' e2')` >>
    imp_res_tac pre_Let >> gvs[SRULE [SNOC_APPEND] Binds_SNOC] >>
    irule bidir_trans >> first_x_assum $ irule_at Any >> rw[]
    >- (simp[GSYM SNOC_APPEND] >> irule lets_ok_SNOC_Simple >> simp[SF SFY_ss]) >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Let >> simp[] >>
    irule $ iffLR bidir_sym >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Let >> simp[] >>
    irule $ iffLR bidir_sym >> irule bidir_Let >> simp[]
    )
  >~ [`Prim`]
  >- (
    Cases_on `e1s = []` >> gvs[] >>
    imp_res_tac pre_Prim >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Prim >> simp[] >>
    irule $ iffLR bidir_sym >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Prim >>
    Cases_on `e2s = []` >> gvs[] >>
    irule $ iffLR bidir_sym >>
    irule bidir_Prim >> gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    first_x_assum drule >> strip_tac >> first_x_assum irule >> gvs[EVERY_EL]
    )
  >~ [`App`]
  >- (
    imp_res_tac pre_App >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_App >>
    irule $ iffLR bidir_sym >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_App >>
    irule $ iffLR bidir_sym >>
    irule bidir_App >> rpt $ first_assum $ irule_at Any >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    first_x_assum drule >> strip_tac >> first_x_assum irule >> gvs[EVERY_EL]
    )
  >~ [`Lam`]
  >- (
    imp_res_tac pre_Lam >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Lam >> conj_asm1_tac
    >- gvs[DISJOINT_ALT, EVERY_MEM] >>
    irule $ iffLR bidir_sym >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Lam >> simp[] >>
    irule $ iffLR bidir_sym >> irule bidir_Lam >> simp[]
    )
  >~ [`Letrec`]
  >- (
    imp_res_tac pre_Letrec >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Letrec >> conj_asm1_tac
    >- (
      gvs[DISJOINT_ALT, EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw[] >>
      first_x_assum drule >> pairarg_tac >> gvs[]
      ) >>
    irule $ iffLR bidir_sym >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Letrec >> simp[] >>
    irule_at Any $ iffLR bidir_sym >> irule_at Any bidir_Letrec >> simp[] >>
    `MAP FST fns2 = MAP FST fns1` by
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, ELIM_UNCURRY] >> simp[] >>
    gvs[LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, EVERY_EL]
    )
  >~ [`Rec`]
  >- (
    rename1 `Binds xs (Letrec _ fns1 e1) <--> Binds xs (Letrec _ fns2 e2)` >>
    imp_res_tac pre_Letrec >> gvs[SRULE [SNOC_APPEND] Binds_SNOC] >>
    irule bidir_trans >> first_x_assum $ irule_at Any >> rw[]
    >- (simp[GSYM SNOC_APPEND] >> irule lets_ok_SNOC_Rec >> simp[SF SFY_ss])
    >- (irule pre_SNOC_Rec >> simp[]) >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Letrec >> simp[] >>
    conj_asm1_tac
    >- (gvs[EVERY_MEM, DISJOINT_ALT, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> metis_tac[]) >>
    irule $ iffLR bidir_sym >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Letrec >> simp[] >>
    `MAP FST fns2 = MAP FST fns1` by
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, ELIM_UNCURRY] >> simp[] >>
    irule $ iffLR bidir_sym >> irule bidir_Letrec >> simp[] >>
    gvs[LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP] >> rw[] >>
    first_x_assum drule >> strip_tac >> first_x_assum irule >> gvs[EVERY_EL, EL_MAP]
    )
  >~ [`Simple`] (* spec *)
  >- (
    rename1 `Binds xs (Letrec1 _ v eA eB) <--> Binds xs (Letrec1 _ v eA' eB')` >>
    irule $ iffLR bidir_sym >> irule bidir_trans >>
    irule_at Any bidir_Binds_push_Letrec1 >> simp[] >> conj_asm1_tac
    >- (imp_res_tac pre_Letrec >> gvs[]) >>
    irule bidir_trans >>
    irule_at Any bidir_Letrec >> simp[PULL_EXISTS, EXISTS_PROD] >>
    irule_at Any $ iffLR bidir_sym >>
    last_x_assum $ irule_at Any >> imp_res_tac pre_Letrec1 >> simp[] >>
    irule_at Any bidir_refl >> irule_at Any bidir_trans >>
    irule_at Any $ SRULE [Once bidir_sym] bidir_Binds_push_Letrec1 >> simp[] >>
    irule_at Any bidir_trans >>
    irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl >>
    last_assum $ irule_at Any >>
    irule_at Any $ iffLR bidir_sym >> irule_at Any bidir_trans >>
    irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl >>
    last_assum $ irule_at Any >> gvs[GSYM Binds_SNOC, SNOC_APPEND] >>
    first_x_assum $ irule_at Any >> reverse $ rw[]
    >- (irule pre_SNOC_Simple >> simp[] >> imp_res_tac pre_Letrec >> gvs[]) >>
    gvs[lets_ok_APPEND, lets_ok_def] >>
    gvs[pre_def, exp_of_def, barendregt_alt_def, allvars_thm, freevars_exp_of] >>
    gvs[MEM_MAP, PULL_EXISTS] >> gen_tac >> strip_tac >> rw[] >>
    gvs[vars_of_eq_MAP, MEM_MAP, DISJ_EQ_IMP, PULL_FORALL] >> metis_tac[]
    )
  >~ [`Case`]
  >- (
    imp_res_tac pre_Case >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Case >> simp[] >>
    irule_at Any $ iffLR bidir_sym >>
    irule_at Any bidir_trans >> irule_at Any bidir_Binds_push_Case >> simp[] >>
    conj_asm1_tac >- gvs[EVERY_EL, LIST_REL_EL_EQN, ELIM_UNCURRY] >>
    irule $ iffLR bidir_sym >>
    irule bidir_Case >> rpt $ first_assum $ irule_at Any >>
    gvs[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY] >> rw[]
    >- (first_x_assum drule >> strip_tac >> first_x_assum irule >> gvs[EVERY_EL])
    >- (Cases_on `usopt1` >> gvs[] >> Cases_on `usopt2` >> gvs[])
    )
  >~ [`Annot`]
  >- (
    imp_res_tac pre_Annot >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Annot >>
    irule_at Any $ iffLR bidir_sym >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Annot >>
    irule $ iffLR bidir_sym >> irule bidir_Annot >> gvs[]
    )
  >- metis_tac[bidir_trans]
  >- (
    irule bidir_trans >>
    first_x_assum $ irule_at Any >> simp[] >>
    irule bidir_Binds >> rw[]
    )
QED

(*---------------------------------------------------------------------------*
   Definition of inline_rel - non-reversible inlinings
 *---------------------------------------------------------------------------*)

Inductive inline_rel:
[~Var:]
  MEM (Simple d x e) l
    ⇒ inline_rel l (Var d x) e
[~Var_Rec:]
  MEM (Rec d fns) l ∧ MEM (x,e) fns
    ⇒ inline_rel l (Var d x) e
[~Let:]
  inline_rel l e1 e1' ∧
  inline_rel (l ++ [Simple d x e1]) e2 e2'
    ⇒ inline_rel l (Let d x e1 e2) (Let d x e1' e2')
[~Prim:]
  LIST_REL (inline_rel l) e1s e2s
    ⇒ inline_rel l (Prim d p e1s) (Prim d p e2s)
[~App:]
  inline_rel l e1 e1' ∧
  LIST_REL (inline_rel l) e2s e2s'
    ⇒ inline_rel l (App d e1 e2s) (App d e1' e2s')
[~Lam:]
  inline_rel l e1 e2
    ⇒ inline_rel l (Lam d xs e1) (Lam d xs e2)
[~Letrec:]
  LIST_REL (λ(f1,e1) (f2,e2). f2 = f1 ∧ inline_rel l e1 e2) fns1 fns2 ∧
  inline_rel l e1 e2
    ⇒ inline_rel l (Letrec d fns1 e1) (Letrec d fns2 e2)
[~Letrec_Rec:]
  LIST_REL (λ(f1,e1) (f2,e2). f2 = f1 ∧ inline_rel l e1 e2) fns1 fns2 ∧
  inline_rel (l ++ [Rec d fns1]) e1 e2
    ⇒ inline_rel l (Letrec d fns1 e1) (Letrec d fns2 e2)
[~spec:]
  inline_rel l e1 e2 ∧
  (∀e d. Letrec1 d x e1 e <--> Let d x e1' e) ∧
  x ∉ freevars_cexp e1' ∧
  DISJOINT (boundvars (exp_of e3)) (boundvars (exp_of e1')) ∧
  DISJOINT (boundvars (exp_of e3)) (freevars (exp_of e1')) ∧
  inline_rel (l ++ [Simple d x e1']) e3 e4
    ⇒ inline_rel l (Letrec1 d x e1 e3) (Letrec1 d x e2 e4)
[~Case:]
  inline_rel l e1 e2 ∧
  LIST_REL
    (λ(cn1,pvs1,k1) (cn2,pvs2,k2). cn2 = cn1 ∧ pvs2 = pvs1 ∧ inline_rel l k1 k2)
    css1 css2 ∧
  OPTREL (λ(cn_ars1,k1) (cn_ars2,k2). cn_ars2 = cn_ars1 ∧ inline_rel l k1 k2)
    usopt1 usopt2
    ⇒ inline_rel l (Case d e1 v css1 usopt1) (Case d e2 v css2 usopt2)
[~Annot:]
  inline_rel l e1 e2
    ⇒ inline_rel l (Annot d a e1) (Annot d' a e2)
[~refl:]
  inline_rel l e e
[~trans:]
  inline_rel l e1 e2 ∧ inline_rel l e2 e3 ∧ pre l e2
    ⇒ inline_rel l e1 e3
[~simp:]
  inline_rel l e1 e2 ∧ e2 <--> e2'
    ⇒ inline_rel l e1 e2'

(* non-reversible cases *)
[~freshen:]
  freshen_cexp e1 avoid1 = (e2,avoid2) ∧
  avoid_set_ok avoid1 e1 ∧ IMAGE explode (vars_of l) ⊆ set_of avoid1
  ⇒ inline_rel l e1 e2

[~Case_simp:]
  ALOOKUP css cn = SOME (pvs,e) ∧
  LENGTH es = LENGTH pvs ∧
  explode cn ∉ monad_cns
    ⇒ inline_rel l (Case d (pure_cexp$Prim d' (Cons cn) es) x css usopt)
                   (Let d x (Prim d' (Cons cn) es) $ Lets d (ZIP (pvs,es)) e)
End

(*---------------------------------------------------------------------------*
   inline_rel ⇒ pure_pres
 *---------------------------------------------------------------------------*)

Theorem inline_rel_IMP_pure_pres_lemma:
  ∀xs x y.
    inline_rel xs x y ∧ lets_ok xs ∧ pre xs x ⇒
    Binds xs x ~~> Binds xs y
Proof
  Induct_on `inline_rel` >> rw[]
  >~ [`Var`,`Simple`]
  >- (
    irule pres_bidir >> irule bidir_trans >>
    irule_at Any Binds_MEM >> goal_assum drule >> simp[] >>
    simp[Binds_APPEND, Binds_def] >>
    irule bidir_Binds >> rw[] >> simp[bidir_Let_unroll]
    )
  >~ [`Var`,`Rec`]
  >- (
    irule pres_bidir >> irule bidir_trans >>
    irule_at Any Binds_MEM >> goal_assum drule >> simp[] >>
    irule $ iffLR bidir_sym >> irule bidir_trans >>
    irule_at Any Binds_MEM >> goal_assum drule >> simp[] >>
    simp[Binds_APPEND, Binds_def] >>
    irule bidir_Binds >> rw[] >>
    irule $ iffLR bidir_sym >> irule bidir_Letrec_unroll >> simp[] >>
    imp_res_tac lets_ok_Rec_MEM
    )
  >~ [`Let`]
  >- (
    rename1 `Binds xs (Let _ v e1 e2) ~~> Binds xs (Let _ v e1' e2')` >>
    imp_res_tac pre_Let >> gvs[SRULE [SNOC_APPEND] Binds_SNOC] >>
    irule pres_trans >> first_x_assum $ irule_at Any >> rw[]
    >- (simp[GSYM SNOC_APPEND] >> irule lets_ok_SNOC_Simple >> simp[SF SFY_ss]) >>
    irule pres_trans >> irule_at Any pres_bidir >>
    irule_at Any bidir_Binds_push_Let >> simp[] >>
    irule pres_trans >> irule_at (Pos last) pres_bidir >>
    irule_at Any $ iffLR bidir_sym >> irule_at Any bidir_Binds_push_Let >> simp[] >>
    irule pres_Let >> simp[]
    )
  >~ [`Prim`]
  >- (
    Cases_on `e1s = []` >> gvs[] >> imp_res_tac pre_Prim >>
    irule pres_trans >> irule_at Any pres_bidir >>
    irule_at Any bidir_Binds_push_Prim >> simp[] >>
    irule pres_trans >> irule_at (Pos last) pres_bidir >>
    irule_at Any $ iffLR bidir_sym >> irule_at Any bidir_Binds_push_Prim >> simp[] >>
    Cases_on `e2s = []` >> gvs[] >>
    irule pres_Prim >> gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    first_x_assum drule >> strip_tac >> first_x_assum irule >> gvs[EVERY_EL]
    )
  >~ [`App`]
  >- (
    imp_res_tac pre_App >>
    irule pres_trans >> irule_at Any pres_bidir >>
    irule_at Any bidir_Binds_push_App >>
    irule pres_trans >> irule_at (Pos last) pres_bidir >>
    irule_at Any $ iffLR bidir_sym >> irule_at Any bidir_Binds_push_App >> simp[] >>
    irule pres_App >> simp[] >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    first_x_assum drule >> strip_tac >> first_x_assum irule >> gvs[EVERY_EL]
    )
  >~ [`Lam`]
  >- (
    imp_res_tac pre_Lam >>
    irule pres_trans >> irule_at Any pres_bidir >>
    irule_at Any bidir_Binds_push_Lam >> conj_asm1_tac
    >- gvs[DISJOINT_ALT, EVERY_MEM] >>
    irule pres_trans >> irule_at (Pos last) pres_bidir >>
    irule_at Any $ iffLR bidir_sym >> irule_at Any bidir_Binds_push_Lam >>
    simp[] >> irule pres_Lam >> gvs[]
    )
  >~ [`Letrec`]
  >- (
    imp_res_tac pre_Letrec >>
    irule pres_trans >> irule_at Any pres_bidir >>
    irule_at Any bidir_Binds_push_Letrec >> conj_asm1_tac
    >- (
      gvs[DISJOINT_ALT, EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw[]>>
      first_x_assum drule >> pairarg_tac >> gvs[]
      ) >>
    irule pres_trans >> irule_at (Pos last) pres_bidir >>
    irule_at Any $ iffLR bidir_sym >> irule_at Any bidir_Binds_push_Letrec >>
    `MAP FST fns2 = MAP FST fns1` by
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, ELIM_UNCURRY] >> simp[] >>
    irule pres_Letrec >> gvs[LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, EVERY_EL]
    )
  >~ [`Rec`]
  >- (
    rename1 `Binds xs (Letrec _ fns1 e1) ~~> Binds xs (Letrec _ fns2 e2)` >>
    imp_res_tac pre_Letrec >> gvs[SRULE [SNOC_APPEND] Binds_SNOC] >>
    irule pres_trans >> first_x_assum $ irule_at Any >> rw[]
    >- (simp[GSYM SNOC_APPEND] >> irule lets_ok_SNOC_Rec >> simp[SF SFY_ss])
    >- (irule pre_SNOC_Rec >> simp[]) >>
    irule pres_trans >> irule_at Any pres_bidir >>
    irule_at Any bidir_Binds_push_Letrec >> simp[] >>
    conj_asm1_tac
    >- (gvs[EVERY_MEM, DISJOINT_ALT, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> metis_tac[]) >>
    irule pres_trans >> irule_at (Pos last) pres_bidir >>
    irule_at Any $ iffLR bidir_sym >> irule_at Any bidir_Binds_push_Letrec >>
    `MAP FST fns2 = MAP FST fns1` by
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, ELIM_UNCURRY] >> simp[] >>
    irule pres_Letrec >> simp[] >>
    gvs[LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP] >> rw[] >>
    first_x_assum drule >> strip_tac >> first_x_assum irule >> gvs[EVERY_EL, EL_MAP]
    )
  >~ [`Simple`] (* spec *)
  >- (
    rename1 `Binds xs (Letrec1 _ v eA eB) ~~> Binds xs (Letrec1 _ v eA' eB')` >>
    (* push Binds in *)
    irule pres_trans >> irule_at Any pres_bidir >>
    irule_at Any bidir_Binds_push_Letrec1 >> conj_asm1_tac
    >- (imp_res_tac pre_Letrec >> gvs[]) >>
    irule pres_trans >> irule_at (Pos last) pres_bidir >>
    irule_at Any $ iffLR bidir_sym  >>
    irule_at Any bidir_Binds_push_Letrec1 >> simp[] >>
    (* turn eA' --> eA *)
    imp_res_tac pre_Letrec1 >> irule pres_trans >>
    irule_at (Pos last) pres_Letrec >> simp[PULL_EXISTS, EXISTS_PROD] >>
    last_x_assum $ irule_at Any >> simp[] >>
    irule_at Any pres_bidir >> irule_at Any bidir_Binds >>
    irule_at Any LIST_REL_mem_rel_refl >> irule_at Any bidir_refl >>
    (* pull Binds out *)
    irule_at Any pres_trans >> irule_at Any pres_bidir >>
    irule_at Any $ iffLR bidir_sym >> irule_at Any bidir_Binds_push_Letrec1 >> simp[] >>
    irule_at Any pres_trans >> irule_at (Pos last) pres_bidir >>
    irule_at Any bidir_Binds_push_Letrec1 >> simp[] >>
    (* turn `Letrec1 _ v eA _` --> `Let _ v e1' _` *)
    irule_at Any pres_trans >> irule_at Any pres_bidir >>
    irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl >>
    last_assum $ irule_at Any >>
    irule_at Any pres_trans >> irule_at (Pos last) pres_bidir >>
    irule_at Any $ iffLR bidir_sym >> irule_at Any bidir_Binds >>
    irule_at Any LIST_REL_mem_rel_refl >> last_assum $ irule_at Any >>
    (* push `Let _ v e1' _` into Binds, irule, preconditions *)
    simp[GSYM Binds_SNOC, SNOC_APPEND] >>
    first_x_assum $ irule_at Any >> reverse $ rw[]
    >- (irule pre_SNOC_Simple >> simp[] >> imp_res_tac pre_Letrec >> gvs[]) >>
    gvs[lets_ok_APPEND, lets_ok_def] >>
    gvs[pre_def, exp_of_def, barendregt_alt_def, allvars_thm, freevars_exp_of] >>
    gvs[MEM_MAP, PULL_EXISTS] >> gen_tac >> strip_tac >> rw[] >>
    gvs[vars_of_eq_MAP, MEM_MAP, DISJ_EQ_IMP, PULL_FORALL] >> metis_tac[]
    )
  >~ [`Case`]
  >- (
    imp_res_tac pre_Case >>
    irule pres_trans >> irule_at Any pres_bidir >>
    irule_at Any bidir_Binds_push_Case >> simp[] >>
    irule pres_trans >> irule_at (Pos last) pres_bidir >>
    irule_at Any $ iffLR bidir_sym >>
    irule_at Any bidir_Binds_push_Case >> simp[] >>
    conj_asm1_tac >- gvs[EVERY_EL, LIST_REL_EL_EQN, ELIM_UNCURRY] >>
    irule pres_Case >> first_x_assum $ irule_at Any >>
    gvs[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY] >> rw[]
    >- (first_x_assum drule >> strip_tac >> first_x_assum irule >> gvs[EVERY_EL])
    >- (Cases_on `usopt1` >> gvs[] >> Cases_on `usopt2` >> gvs[])
    )
  >~ [`Annot`]
  >- (
    imp_res_tac pre_Annot >>
    irule pres_trans >> irule_at Any pres_bidir >>
    irule_at Any bidir_Binds_push_Annot >>
    irule pres_trans >>
    irule_at (Pos last) pres_bidir >>
    irule_at Any $ iffLR bidir_sym >>
    irule_at Any bidir_Binds_push_Annot >>
    irule pres_Annot >> simp[]
    )
  >- metis_tac[pres_trans]
  >- (
    irule pres_trans >> first_x_assum $ irule_at Any >> simp[] >>
    irule pres_bidir >> irule bidir_Binds >> rw[]
    )
  >~ [`freshen_cexp`]
  >- (
    irule pres_Binds >> simp[] >>
    irule pres_unidir >> drule_all unidir_freshen >> simp[]
    )
  >- (
    irule pres_Binds >> simp[] >>
    irule pres_unidir >> irule unidir_Case_simp >> simp[] >>
    `css ≠ []` by (CCONTR_TAC >> gvs[]) >> pop_assum mp_tac >>
    dxrule $ cj 1 $ iffLR pre_def >> qpat_x_assum `ALOOKUP _ _ = _` mp_tac >>
    rpt $ pop_assum kall_tac >> ntac 3 strip_tac >>
    gvs[MEM_MAP, DISJ_EQ_IMP, PULL_FORALL, AND_IMP_INTRO, SF CONJ_ss] >>
    rpt gen_tac >> gvs[exp_of_def, COND_RAND] >>
    qmatch_asmsub_abbrev_tac `COND _ _ (barendregt foo)` >>
    gvs[barendregt_alt_def] >>
    gvs[APPEND_EQ_CONS, PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM,
        RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR] >>
    unabbrev_all_tac >> conj_tac
    >- (
      simp[Once MONO_NOT_EQ] >> rw[] >> gvs[Once barendregt_alt_def, SF DNF_ss] >>
      gvs[DECIDE ``A ∨ B ⇔ ¬B ⇒ A``, MEM_MAP, PULL_EXISTS] >>
      gvs[allvars_thm, freevars_exp_of]
      )
    >- (
      simp[Once MONO_NOT_EQ] >> rw[EVERY_MEM] >>
      qmatch_asmsub_abbrev_tac `rows_of _ us css'` >>
      `explode y ∈ boundvars (rows_of (explode x) us css')` by (
        unabbrev_all_tac >> gvs[boundvars_rows_of, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
        disj2_tac >> imp_res_tac alistTheory.ALOOKUP_MEM >>
        goal_assum $ drule_at Any >> simp[]) >>
      gvs[op_of_def, SF ETA_ss, barendregt_alt_def, allvars_thm, SF DNF_ss] >>
      qpat_x_assum `∀s. MEM _ (MAP allvars _) ⇒ DISJOINT (boundvars _) _` mp_tac >>
      simp[MEM_MAP, allvars_thm, PULL_EXISTS] >> disch_then drule >>
      simp[freevars_exp_of, DISJOINT_ALT] >> metis_tac[]
      )
    )
QED

(*--------------------*)

val _ = export_theory();
