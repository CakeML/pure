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
   TODO rules to add to pure_pres
 *---------------------------------------------------------------------------*)

Theorem bidir_Let_unroll:
  Let d x y (Var d' x) <--> y
Proof
  cheat
QED

Theorem bidir_Letrec_dup:
  Letrec1 d1 f x y <--> Letrec1 d2 f x (Letrec1 d3 f x y)
Proof
  cheat
QED

Theorem bidir_Let_Let_swap:
  v ≠ w ∧ v ∉ freevars_cexp y ∧ w ∉ freevars_cexp x
  ⇒ Let d v x (Let d' w y z) <--> Let d w y (Let d' v x z)
Proof
  cheat
QED

Theorem bidir_Let_Let_Letrec:
  v ≠ w ∧
  explode w ∉ freevars (exp_of x) ∧
  explode v ∉ freevars (exp_of x)
  ⇒
  bidir (Let a1 v x (Let a2 v x (Letrec1 a3 w y e)))
        (Let b1 v x (Letrec1 b2 w y (Let b3 v x e)))
Proof
  cheat
QED

Theorem bidir_Letrec_Letrec_Let:
  v ≠ w ∧
  explode w ∉ freevars (exp_of x)
  ⇒
  bidir (Letrec1 a1 v x (Letrec1 a2 v x (Let a3 w y e)))
        (Letrec1 b1 v x (Let b2 w y (Letrec1 b3 v x e)))
Proof
  cheat
QED

Theorem bidir_Letrec_Letrec_Letrec:
  v ≠ w ∧
  explode w ∉ freevars (exp_of x)
  ⇒
  bidir (Letrec1 a1 v x (Letrec1 a2 v x (Letrec1 a3 w y e)))
        (Letrec1 b1 v x (Letrec1 b2 w y (Letrec1 b3 v x e)))
Proof
  cheat
QED

Theorem bidir_Annot:
  e1 <--> e2
  ⇒ Annot d1 annot e1 <--> Annot d2 annot e2
Proof
  cheat
QED

(*---------- push cases ----------*)

Theorem bidir_Let_push_Let:
  x ≠ y ⇒
  Let d1 x e1 (Let d2 y e2 e3) <--> Let d3 y (Let d4 x e1 e2) (Let d5 x e1 e3)
Proof
  cheat
QED

Theorem bidir_Letrec_push_Let:
  x ≠ y ⇒
  Letrec1 d1 x e1 (Let d2 y e2 e3) <--> Let d3 y (Letrec1 d4 x e1 e2) (Letrec1 d5 x e1 e3)
Proof
  cheat
QED

Theorem bidir_Let_push_Prim:
  Let d1 x e1 (Prim d2 p es) <--> Prim d3 p (MAP (Let d4 x e1) es)
Proof
  cheat
QED

Theorem bidir_Letrec_push_Prim:
  Letrec1 d1 x e1 (Prim d2 p es) <--> Prim d3 p (MAP (Letrec1 d4 x e1) es)
Proof
  cheat
QED

Theorem bidir_Let_push_App:
  Let d1 x e1 (App d2 e es) <--> App d3 (Let d4 x e1 e) (MAP (Let d5 x e1) es)
Proof
  cheat
QED

Theorem bidir_Letrec_push_App:
  Letrec1 d1 x e1 (App d2 e es) <--> App d3 (Letrec1 d4 x e1 e) (MAP (Letrec1 d5 x e1) es)
Proof
  cheat
QED

Theorem bidir_Let_push_Lam:
  ¬MEM x xs ⇒
  Let d1 x e1 (Lam d2 xs e2) <--> Lam d3 xs (Let d4 x e1 e2)
Proof
  cheat
QED

Theorem bidir_Letrec_push_Lam:
  ¬MEM x xs ⇒
  Letrec1 d1 x e1 (Lam d2 xs e2) <--> Lam d3 xs (Letrec1 d4 x e1 e2)
Proof
  cheat
QED

Theorem bidir_Let_push_Letrec:
  ¬MEM x (MAP FST fns) ⇒
  Let d1 x e1 (Letrec d2 fns e2) <-->
  Letrec d3 (MAP (λ(f,e). (f, Let d4 x e1 e)) fns) (Let d4 x e1 e2)
Proof
  cheat
QED

Theorem bidir_Letrec_push_Letrec:
  ¬MEM x (MAP FST fns) ⇒
  Letrec1 d1 x e1 (Letrec d2 fns e2) <-->
  Letrec d3 (MAP (λ(f,e). (f, Letrec1 d4 x e1 e)) fns) (Letrec1 d4 x e1 e2)
Proof
  cheat
QED

Theorem bidir_Let_push_Case:
  x ≠ y ∧ EVERY (λ(cn,pvs,e). ¬ MEM x pvs) css ⇒
  Let d1 x e1 (Case d2 e2 y css usopt) <-->
  Case d3 (Let d4 x e1 e2) y
    (MAP (λ(cn,pvs,e). (cn,pvs,Let d4 x e1 e)) css)
    (OPTION_MAP (λ(cn_ars,e). (cn_ars, Let d4 x e1 e)) usopt)
Proof
  cheat
QED

Theorem bidir_Letrec_push_Case:
  x ≠ y ∧ EVERY (λ(cn,pvs,e). ¬ MEM x pvs) css ⇒
  Letrec1 d1 x e1 (Case d2 e2 y css usopt) <-->
  Case d3 (Letrec1 d4 x e1 e2) y
    (MAP (λ(cn,pvs,e). (cn,pvs,Letrec1 d4 x e1 e)) css)
    (OPTION_MAP (λ(cn_ars,e). (cn_ars, Letrec1 d4 x e1 e)) usopt)
Proof
  cheat
QED

Theorem bidir_Let_push_Annot:
  Let d1 x e1 (Annot d2 annot e2) <--> Annot d3 annot (Let d4 x e1 e2)
Proof
  cheat
QED

Theorem bidir_Letrec_push_Annot:
  Letrec1 d1 x e1 (Annot d2 annot e2) <--> Annot d3 annot (Letrec1 d4 x e1 e2)
Proof
  cheat
QED

(*---------------------------------------------------------------------------*
   Definition of what inliner can remember
 *---------------------------------------------------------------------------*)

Datatype:
  inline_mem = Simple 'a mlstring ('a cexp) | Rec 'a mlstring ('a cexp)
End

Definition lhs_name_def[simp]:
  lhs_name (Simple d v e) = v ∧
  lhs_name (Rec d v e) = v
End

Definition lhs_exp_def[simp]:
  lhs_exp (Simple d v e) = e ∧
  lhs_exp (Rec d v e) = e
End

(*---------------------------------------------------------------------------*
   Definition of precondition pre
 *---------------------------------------------------------------------------*)

Definition vars_of_def:
  vars_of [] = {} ∧
  vars_of (h::t) = lhs_name h INSERT freevars_cexp (lhs_exp h) ∪ vars_of t
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
    DISJOINT ({v} ∪ freevars_cexp x) (set (MAP lhs_name rest)) ∧
    lets_ok rest) ∧
  (lets_ok ((Rec d v x)::rest) ⇔
    DISJOINT ({v} ∪ freevars_cexp x) (set (MAP lhs_name rest)) ∧
    lets_ok rest)
End

(*---------------------------------------------------------------------------*
   Lemmas about lets_ok etc.
 *---------------------------------------------------------------------------*)

Theorem vars_of_eq_MAP:
  vars_of l = BIGUNION $ set $
    MAP (λx. lhs_name x INSERT freevars_cexp (lhs_exp x)) l
Proof
  Induct_on `l` >> rw[vars_of_def, INSERT_UNION_EQ]
QED

Theorem vars_of_APPEND:
  ∀xs ys. vars_of (xs ++ ys) = vars_of xs ∪ vars_of ys
Proof
  simp[vars_of_eq_MAP]
QED

Theorem lhs_name_SUBSET_vars_of:
  ∀xs. set (MAP lhs_name xs) ⊆ vars_of xs
Proof
  Induct >> rw[lhs_name_def, vars_of_def] >> gvs[SUBSET_DEF]
QED

Theorem lhs_exp_SUBSET_vars_of:
  ∀xs. BIGUNION $ set (MAP (λx. freevars_cexp (lhs_exp x)) xs) ⊆ pure_inline_rel_alt$vars_of xs
Proof
  Induct >> rw[lhs_exp_def, vars_of_def] >> gvs[SUBSET_DEF]
QED

Theorem lets_ok_APPEND:
  lets_ok (l1 ++ l2) ⇔
    lets_ok l1 ∧ lets_ok l2 ∧
    DISJOINT
      (BIGUNION $ set (MAP (λx. lhs_name x INSERT freevars_cexp (lhs_exp x)) l1))
      (set (MAP lhs_name l2))
Proof
  Induct_on `l1` >> rw[lets_ok_def] >>
  Cases_on `h` >> gvs[lets_ok_def] >> pop_assum kall_tac >>
  eq_tac >> rw[] >> gvs[DISJOINT_SYM] >> gvs[SF DNF_ss]
QED

Theorem lets_ok_SNOC_Simple_lemma[local]:
  lets_ok xs ∧ v ∉ freevars_cexp x1 ∧ ¬MEM v (MAP lhs_name xs) ∧ v ∉ vars_of xs
  ⇒ lets_ok (SNOC (Simple d v x1) xs)
Proof
  simp[SNOC_APPEND] >> Induct_on `xs` >> rw[] >> gvs[lets_ok_def] >>
  Cases_on `h` >> gvs[lets_ok_def, vars_of_def, DISJOINT_SYM]
QED

Theorem lets_ok_SNOC_Simple:
  lets_ok xs ∧ pre xs (Let d v x y) ⇒ lets_ok (SNOC (Simple d' v x) xs)
Proof
  rw[] >> irule lets_ok_SNOC_Simple_lemma >>
  gvs[pre_def, exp_of_def, barendregt_alt_def, allvars_thm, freevars_exp_of] >>
  metis_tac[SRULE [SUBSET_DEF] lhs_name_SUBSET_vars_of, DISJOINT_ALT]
QED

Theorem lets_ok_SNOC_Rec_lemma[local]:
  lets_ok xs ∧ ¬MEM v (MAP lhs_name xs) ∧ v ∉ vars_of xs
  ⇒ lets_ok (SNOC (Rec d v x1) xs)
Proof
  simp[SNOC_APPEND] >> Induct_on `xs` >> rw[] >> gvs[lets_ok_def] >>
  Cases_on `h` >> gvs[lets_ok_def, vars_of_def, DISJOINT_SYM]
QED

Theorem lets_ok_SNOC_Rec:
  lets_ok xs ∧ pre xs (Letrec1 d v x y) ⇒
  lets_ok (SNOC (Rec d' v x) xs)
Proof
  rw[] >> irule lets_ok_SNOC_Rec_lemma >> gvs[pre_def, exp_of_def] >>
  metis_tac[SRULE [SUBSET_DEF] lhs_name_SUBSET_vars_of, DISJOINT_ALT]
QED

Theorem lets_ok_Simple_MEM:
  lets_ok xs ∧ MEM (Simple d x e) xs ⇒ x ∉ freevars_cexp e
Proof
  Induct_on `xs` >> rw[] >> gvs[lets_ok_def] >>
  Cases_on `h` >> gvs[lets_ok_def]
QED

(*---------------------------------------------------------------------------*
   Lemmas and precondition pre
 *---------------------------------------------------------------------------*)

Theorem pre_Let:
  pre xs (Let d v x y) ⇒
  pre xs x ∧ pre (xs ++ [Simple d' v x]) y ∧
  ¬MEM v (MAP lhs_name xs) ∧ v ∉ vars_of xs
Proof
  rw[pre_def, exp_of_def, barendregt_alt_def, vars_of_APPEND, vars_of_def]
  >- simp[DISJOINT_SYM]
  >- gvs[GSYM freevars_exp_of, allvars_thm] >>
  metis_tac[SUBSET_DEF, lhs_name_SUBSET_vars_of]
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
  pre xs (Lam d ws x) ⇒
    EVERY (λw. ¬MEM w (MAP lhs_name xs) ∧ w ∉ vars_of xs) ws ∧ pre xs x
Proof
  rw[pre_def] >> gvs[exp_of_def, barendregt_Lams, boundvars_Lams] >>
  simp[EVERY_MEM] >> gen_tac >> strip_tac >>
  qspec_then `xs` assume_tac lhs_name_SUBSET_vars_of >> gvs[SUBSET_DEF] >>
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
  explode v ∉ boundvars (exp_of x) ∧
  DISJOINT (boundvars (exp_of x)) (boundvars (exp_of x1)) ∧
  DISJOINT (boundvars (exp_of x)) (freevars (exp_of x1))
  ⇒ pre (xs ++ [Rec d v x1]) x
Proof
  gvs[pre_def, vars_of_APPEND, vars_of_def, GSYM freevars_exp_of] >>
  simp[DISJOINT_SYM]
QED

Theorem pre_Letrec:
  pre xs (Letrec d ys x) ⇒
  pre xs x ∧ EVERY (pre xs) (MAP SND ys) ∧
  DISJOINT (set (MAP (explode o FST) ys)) (boundvars (exp_of x)) ∧
  EVERY (λ(v,e). ¬MEM v (MAP lhs_name xs) ∧ v ∉ vars_of xs) ys
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
    simp[EVERY_MEM, FORALL_PROD] >> rpt gen_tac >> strip_tac >>
    qspec_then `xs` assume_tac lhs_name_SUBSET_vars_of >> gvs[SUBSET_DEF] >>
    pop_assum $ qspec_then `p_1` assume_tac >> gvs[] >>
    gvs[pre_def, exp_of_def] >> gvs[MEM_MAP, PULL_EXISTS, FORALL_PROD, DISJOINT_ALT] >>
    metis_tac[]
    )
QED

Theorem pre_Letrec1:
  pre xs (Letrec1 d v x y) ⇒
  pre xs x ∧ pre (xs ++ [Rec d' v x]) y ∧
  ¬ MEM v (MAP lhs_name xs) ∧ v ∉ vars_of xs
Proof
  rw[pre_def, exp_of_def, barendregt_alt_def, vars_of_APPEND, vars_of_def]
  >- simp[DISJOINT_SYM]
  >- gvs[GSYM freevars_exp_of, allvars_thm] >>
  metis_tac[SUBSET_DEF, lhs_name_SUBSET_vars_of]
QED

(*---------------------------------------------------------------------------*
   Theorems about pushing and pulling let-expressions
 *---------------------------------------------------------------------------*)

Definition Binds_def:
  Binds [] y = y ∧
  Binds ((Simple d v x)::xs) y = Let d v x (Binds xs y) ∧
  Binds ((Rec d v x)::xs) y = Letrec1 d v x (Binds xs y)
End

Theorem Binds_APPEND:
  Binds (l1 ++ l2) e = Binds l1 (Binds l2 e)
Proof
  Induct_on `l1` >> rw[Binds_def] >> Cases_on `h` >> gvs[Binds_def]
QED

Theorem Binds_SNOC:
  Binds [] y = y ∧
  Binds (SNOC (Simple d x e) xs) y = Binds xs (Let d x e y) ∧
  Binds (SNOC (Rec d x e) xs) y = Binds xs (Letrec1 d x e y)
Proof
  simp[Binds_def] >> Induct_on `xs` >> rw[Binds_def] >>
  Cases_on `h` >> gvs[Binds_def]
QED

Definition mem_rel[simp]:
  mem_rel R (Simple d x e) h = (∃d' e'. h = Simple d' x e' ∧ R e e') ∧
  mem_rel R (Rec d x e) h = (∃d' e'. h = Rec d' x e' ∧ R e e')
End

Theorem mem_rel_refl:
  (∀e. R e e) ⇒ mem_rel R x x
Proof
  Cases_on `x` >> rw[]
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
  >- (irule bidir_Letrec >> simp[])
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
    gvs[MEM_MAP, PULL_EXISTS] >> first_x_assum drule >> gvs[freevars_exp_of] >>
    imp_res_tac lets_ok_Simple_MEM >> gvs[]
    )
  >- (
    irule bidir_Letrec_Letrec_Let >> gvs[lets_ok_APPEND, lets_ok_def] >>
    gvs[MEM_MAP, PULL_EXISTS] >> first_x_assum drule >> gvs[freevars_exp_of]
    )
  >- (
    irule bidir_Letrec_Letrec_Letrec >> gvs[lets_ok_APPEND, lets_ok_def] >>
    gvs[MEM_MAP, PULL_EXISTS] >> first_x_assum drule >> gvs[freevars_exp_of]
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
  last_x_assum $ irule_at Any >> gvs[SNOC_APPEND, vars_of_APPEND]
  >- (irule bidir_Let_push_Let >> gvs[vars_of_def])
  >- (irule bidir_Letrec_push_Let >> gvs[vars_of_def])
QED

Theorem bidir_Binds_push_Prim:
  ∀xs d p es.
    Binds xs (Prim d p es) <--> Prim d p (MAP (λe. Binds xs e) es)
Proof
  Induct using SNOC_INDUCT >> rw[Binds_SNOC] >>
  Cases_on `x` >> rw[Binds_SNOC] >>
  irule bidir_trans >> irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl
  >- (
    irule_at Any bidir_Let_push_Prim >>
    irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
    irule_at Any bidir_Prim >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
    qexists `a` >> rw[LIST_REL_EL_EQN]
    )
  >- (
    irule_at Any bidir_Letrec_push_Prim >>
    irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
    irule_at Any bidir_Prim >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
    qexists `a` >> rw[LIST_REL_EL_EQN]
    )
QED

Theorem bidir_Binds_push_App:
  ∀xs d e es.
    Binds xs (App d e es) <--> App d (Binds xs e) (MAP (λe. Binds xs e) es)
Proof
  Induct using SNOC_INDUCT >> rw[Binds_SNOC] >>
  Cases_on `x` >> rw[Binds_SNOC] >>
  irule bidir_trans >> irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl
  >- (
    irule_at Any bidir_Let_push_App >>
    irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
    irule_at Any bidir_App >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
    qexistsl [`a`,`a`] >> rw[LIST_REL_EL_EQN]
    )
  >- (
    irule_at Any bidir_Letrec_push_App >>
    irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
    irule_at Any bidir_App >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
    qexistsl [`a`,`a`] >> rw[LIST_REL_EL_EQN]
    )
QED

Theorem bidir_Binds_push_Lam:
  ∀xs d ys e.
    DISJOINT (set ys) (vars_of xs)
  ⇒ Binds xs (Lam d ys e) <--> Lam d ys (Binds xs e)
Proof
  Induct using SNOC_INDUCT >> rw[Binds_SNOC] >>
  Cases_on `x` >> rw[Binds_SNOC] >>
  irule bidir_trans >> irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl
  >- (
    irule_at Any bidir_Let_push_Lam >>
    irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
    irule_at Any bidir_Lam >> irule_at Any bidir_refl >>
    gvs[SNOC_APPEND, vars_of_APPEND, vars_of_def, DISJOINT_SYM]
    )
  >- (
    irule_at Any bidir_Letrec_push_Lam >>
    irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
    irule_at Any bidir_Lam >> irule_at Any bidir_refl >>
    gvs[SNOC_APPEND, vars_of_APPEND, vars_of_def, DISJOINT_SYM]
    )
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
  irule bidir_trans >> irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl
  >- (
    irule_at Any bidir_Let_push_Letrec >>
    irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
    irule_at Any bidir_Letrec >> irule_at Any bidir_refl >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[GSYM pure_miscTheory.FST_THM] >>
    gvs[SNOC_APPEND, vars_of_APPEND, vars_of_def, DISJOINT_SYM] >>
    rw[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
    )
  >- (
    irule_at Any bidir_Letrec_push_Letrec >>
    irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
    irule_at Any bidir_Letrec >> irule_at Any bidir_refl >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[GSYM pure_miscTheory.FST_THM] >>
    gvs[SNOC_APPEND, vars_of_APPEND, vars_of_def, DISJOINT_SYM] >>
    rw[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
    )
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
  irule bidir_trans >> irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl
  >- (
    irule_at Any bidir_Let_push_Case >>
    irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
    irule_at Any bidir_Case >> irule_at Any bidir_refl >> rw[] >>
    gvs[SNOC_APPEND, vars_of_APPEND, vars_of_def, DISJOINT_SYM]
    >- rw[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
    >- (Cases_on `usopt` >> gvs[] >> rpt (pairarg_tac >> gvs[])) >>
    gvs[EVERY_MAP, FORALL_PROD, EVERY_MEM] >> metis_tac[]
    )
  >- (
    irule_at Any bidir_Letrec_push_Case >>
    irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
    irule_at Any bidir_Case >> irule_at Any bidir_refl >> rw[] >>
    gvs[SNOC_APPEND, vars_of_APPEND, vars_of_def, DISJOINT_SYM]
    >- rw[LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
    >- (Cases_on `usopt` >> gvs[] >> rpt (pairarg_tac >> gvs[])) >>
    gvs[EVERY_MAP, FORALL_PROD, EVERY_MEM] >> metis_tac[]
    )
QED

Theorem bidir_Binds_push_Annot:
  ∀xs d annot e. Binds xs (Annot d annot e) <--> Annot d annot (Binds xs e)
Proof
  Induct using SNOC_INDUCT >> rw[Binds_SNOC] >>
  Cases_on `x` >> rw[Binds_SNOC] >>
  irule bidir_trans >> irule_at Any bidir_Binds >> irule_at Any LIST_REL_mem_rel_refl
  >- (
    irule_at Any bidir_Let_push_Annot >>
    irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
    irule_at Any bidir_refl
    )
  >- (
    irule_at Any bidir_Letrec_push_Annot >>
    irule_at Any bidir_trans >> first_x_assum $ irule_at Any >>
    irule_at Any bidir_refl
    )
QED

(*---------------------------------------------------------------------------*
   Definition of inline_rev_rel - reversible inlinings
 *---------------------------------------------------------------------------*)

Inductive inline_rev_rel:
[~Var:]
  MEM (Simple d x e) l
    ⇒ inline_rev_rel l (Var d x) e
[~Var_Rec:]
  MEM (Rec d x e) l
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
  inline_rev_rel l e1 e1' ∧
  inline_rev_rel (l ++ [Rec d x e1]) e2 e2'
    ⇒ inline_rev_rel l (Letrec1 d x e1 e2) (Letrec1 d x e1' e2')
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

Theorem inline_rev_rel_IMP_pure_pres_lemma:
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
    irule $ iffLR bidir_sym >> irule bidir_Letrec_unroll >> simp[]
    )
  >~ [`Let`]
  >- (
    rename1 `Binds xs (Let _ v e1 e2) <--> Binds xs (Let _ v e1' e2')` >>
    imp_res_tac pre_Let >> gvs[SRULE [SNOC_APPEND] Binds_SNOC] >>
    irule bidir_trans >> first_x_assum $ irule_at Any >> rw[]
    >- (
      gvs[lets_ok_APPEND, lets_ok_def] >>
      gvs[pre_def, exp_of_def, barendregt_alt_def, allvars_thm, freevars_exp_of] >>
      gvs[MEM_MAP, PULL_EXISTS] >> gen_tac >> strip_tac >> rw[]
      >- metis_tac[SRULE [SUBSET_DEF] lhs_name_SUBSET_vars_of] >>
      drule_at Concl $ SRULE [BIGUNION_SUBSET, SUBSET_DEF] lhs_exp_SUBSET_vars_of >>
      simp[MEM_MAP] >> metis_tac[]
      ) >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Let >> simp[] >>
    irule $ iffLR bidir_sym >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Let >> simp[] >>
    irule $ iffLR bidir_sym >> irule bidir_Let >> simp[]
    )
  >~ [`Prim`]
  >- (
    imp_res_tac pre_Prim >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Prim >>
    irule $ iffLR bidir_sym >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Prim >>
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
      gvs[DISJOINT_ALT, EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw[]>>
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
    rename1 `Binds xs (Letrec1 _ v e1 e2) <--> Binds xs (Letrec1 _ v e1' e2')` >>
    imp_res_tac pre_Letrec1 >> gvs[SRULE [SNOC_APPEND] Binds_SNOC] >>
    irule bidir_trans >> first_x_assum $ irule_at Any >> rw[]
    >- (
      gvs[lets_ok_APPEND, lets_ok_def] >>
      gvs[pre_def, exp_of_def, barendregt_alt_def, allvars_thm, freevars_exp_of] >>
      gvs[MEM_MAP, PULL_EXISTS] >> gen_tac >> strip_tac >> rw[]
      >- metis_tac[SRULE [SUBSET_DEF] lhs_name_SUBSET_vars_of] >>
      drule_at Concl $ SRULE [BIGUNION_SUBSET, SUBSET_DEF] lhs_exp_SUBSET_vars_of >>
      simp[MEM_MAP] >> metis_tac[]
      ) >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Letrec >> simp[] >>
    irule $ iffLR bidir_sym >>
    irule bidir_trans >> irule_at Any bidir_Binds_push_Letrec >> simp[] >>
    irule $ iffLR bidir_sym >> irule bidir_Letrec >> simp[]
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
    gvs[MEM_MAP, PULL_EXISTS] >> gen_tac >> strip_tac >> rw[]
    >- metis_tac[SRULE [SUBSET_DEF] lhs_name_SUBSET_vars_of] >>
    drule_at Concl $ SRULE [BIGUNION_SUBSET, SUBSET_DEF] lhs_exp_SUBSET_vars_of >>
    simp[MEM_MAP] >> metis_tac[]
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

val _ = export_theory();
