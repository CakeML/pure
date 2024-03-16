(*
   This theory defines a syntactic relation that preserves semantics and wf.
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     combinTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_exp_relTheory
     pure_alpha_equivTheory pure_miscTheory pure_congruenceTheory
     pure_letrecProofTheory pure_demandTheory pure_letrec_delargTheory
     pure_cexpTheory pure_cexp_lemmasTheory pureLangTheory
     pure_freshenTheory pure_freshenProofTheory;

val exp_of_def = pureLangTheory.exp_of_def;
val rows_of_def = pureLangTheory.rows_of_def;
val lets_for_def = pureLangTheory.lets_for_def;
val freevars_exp_of = pure_cexp_lemmasTheory.freevars_exp_of

val _ = new_theory "pure_pres";

Overload Letrec1 = ``λd f e1 e2. Letrec d [(f,e1)] e2``

(*----------------------------------------------------------------------------*
   Definition of syntactic relation
 *----------------------------------------------------------------------------*)

Inductive unidir:
[~Let:]
  (∀(x:'a cexp) y v a.
    explode v ∉ freevars (exp_of y) ⇒
    unidir (Let a v x y) y)

[~freshen:]
  (∀e1 e2 avoid1 avoid2.
    freshen_cexp e1 avoid1 = (e2,avoid2) ∧ avoid_set_ok avoid1 e1
    ⇒ unidir e1 e2)
End

Overload "-->" = “unidir”

(* used by specialise rule in bidir below *)
Inductive spec_arg:
[~Apps_Var:]
  (∀f vs v ws xs1 xs2 ys1 ys2 c d.
    LENGTH xs1 = LENGTH vs ∧
    LENGTH ys1 = LENGTH ws ∧
    LIST_REL (spec_arg f vs v ws) xs1 xs2 ∧
    LIST_REL (spec_arg f vs v ws) ys1 ys2 ⇒
    spec_arg f vs v ws (App c (Var a f) (xs1 ++ [Var b v] ++ ys1))
                       (App d (Var a f) (xs2 ++ ys2)))
[~Var:]
  (∀f vs v ws n a b.
    n ≠ f ⇒
    spec_arg f vs v ws (Var a n) (Var b n :'a cexp))
[~Lam:]
  (∀f vs v ws ns x y a b.
    spec_arg f vs v ws x y ∧
    ~MEM v ns ∧ ~MEM f ns ⇒
    spec_arg f vs v ws (Lam a ns x) (Lam b ns y))
[~Let:]
  (∀f vs v ws x1 x2 y1 y2 n.
    spec_arg f vs v ws x1 x2 ∧
    spec_arg f vs v ws y1 y2 ∧
    n ≠ v ∧ n ≠ f ⇒
    spec_arg f vs v ws (Let a n x1 y1) (Let b n x2 y2))
[~App:]
  (∀f vs v ws f1 g1 xs ys a b.
    spec_arg f vs v ws f1 g1 ∧
    LIST_REL (spec_arg f vs v ws) xs ys ⇒
    spec_arg f vs v ws (App a f1 xs) (App b g1 ys))
[~Prim:]
  (∀f vs v ws n xs ys a b.
    LIST_REL (spec_arg f vs v ws) xs ys ⇒
    spec_arg f vs v ws (Prim a n xs) (Prim b n ys))
[~Letrec:]
  (∀f vs v ws x y xs ys a b.
    LIST_REL (spec_arg f vs v ws) (MAP SND xs) (MAP SND ys) ∧
    DISJOINT {v; f} (set (MAP FST xs)) ∧
    MAP FST xs = MAP FST ys ∧
    spec_arg f vs v ws x y ⇒
    spec_arg f vs v ws (Letrec a xs x) (Letrec b ys y))
[~Case:]
  (∀f vs v ws x y xs ys a b d e.
    LIST_REL (spec_arg f vs v ws) (MAP (SND o SND) xs) (MAP (SND o SND) ys) ∧
    MAP FST xs = MAP FST ys ∧
    MAP (FST o SND) xs = MAP (FST o SND) ys ∧
    spec_arg f vs v ws x y ∧ z ≠ v ∧ z ≠ f ∧
    EVERY (λ(c,ns,e). ~MEM v ns ∧ ~MEM f ns) xs ∧
    OPTREL (λ(x,e1) (y,e2). x = y ∧ spec_arg f vs v ws e1 e2) d e ⇒
    spec_arg f vs v ws (Case a x z xs d) (Case b y z ys e))
End

Inductive push_pull:
[~Let_Let:]
  x ≠ y ∧ y ∉ freevars_cexp e1 ⇒
  push_pull (Let d1 x e1 (Let d2 y e2 e3))
            (Let d3 y (Let d4 x e1 e2) (Let d5 x e1 e3))
[~Letrec_Let:]
  x ≠ y ∧ y ∉ freevars_cexp e1 ⇒
  push_pull (Letrec1 d1 x e1 (Let d2 y e2 e3))
            (Let d3 y (Letrec1 d4 x e1 e2) (Letrec1 d5 x e1 e3))
[~Let_Prim:]
  es ≠ [] ⇒
  push_pull (Let d1 x e1 (Prim d2 p es)) (Prim d3 p (MAP (Let d4 x e1) es))
[~Letrec_Prim:]
  es ≠ [] ⇒
  push_pull (Letrec1 d1 x e1 (Prim d2 p es))
            (Prim d3 p (MAP (Letrec1 d4 x e1) es))
[~Let_App:]
  push_pull (Let d1 x e1 (App d2 e es))
            (App d3 (Let d4 x e1 e) (MAP (Let d5 x e1) es))
[~Letrec_App:]
  push_pull (Letrec1 d1 x e1 (App d2 e es))
            (App d3 (Letrec1 d4 x e1 e) (MAP (Letrec1 d5 x e1) es))
[~Let_Lam:]
  ¬MEM x xs ∧ DISJOINT (set xs) (freevars_cexp e1) ⇒
  push_pull (Let d1 x e1 (Lam d2 xs e2))
            (Lam d3 xs (Let d4 x e1 e2))
[~Letrec_Lam:]
  ¬MEM x xs ∧ DISJOINT (set xs) (freevars_cexp e1) ⇒
  push_pull (Letrec1 d1 x e1 (Lam d2 xs e2))
            (Lam d3 xs (Letrec1 d4 x e1 e2))
[~Let_Letrec:]
  ¬MEM x (MAP FST fns) ∧ DISJOINT (set $ MAP FST fns) (freevars_cexp e1) ⇒
  push_pull (Let d1 x e1 (Letrec d2 fns e2))
            (Letrec d3 (MAP (λ(f,e). (f, Let d4 x e1 e)) fns) (Let d4 x e1 e2))
[~Letrec_Letrec:]
  ¬MEM x (MAP FST fns) ∧ DISJOINT (set $ MAP FST fns) (freevars_cexp e1) ⇒
  push_pull (Letrec1 d1 x e1 (Letrec d2 fns e2))
            (Letrec d3 (MAP (λ(f,e). (f, Letrec1 d4 x e1 e)) fns) (Letrec1 d4 x e1 e2))
[~Let_Case:]
  x ≠ y ∧ EVERY (λ(cn,pvs,e). ¬ MEM x pvs) css ∧ y ∉ freevars_cexp e1 ⇒
  push_pull (Let d1 x e1 (Case d2 e2 y css usopt))
            (Case d3 (Let d4 x e1 e2) y
              (MAP (λ(cn,pvs,e). (cn,pvs,Let d4 x e1 e)) css)
              (OPTION_MAP (λ(cn_ars,e). (cn_ars, Let d4 x e1 e)) usopt))
[~Letrec_Case:]
  x ≠ y ∧ EVERY (λ(cn,pvs,e). ¬ MEM x pvs) css ∧ y ∉ freevars_cexp e1 ⇒
  push_pull (Letrec1 d1 x e1 (Case d2 e2 y css usopt))
            (Case d3 (Letrec1 d4 x e1 e2) y
              (MAP (λ(cn,pvs,e). (cn,pvs,Letrec1 d4 x e1 e)) css)
              (OPTION_MAP (λ(cn_ars,e). (cn_ars, Letrec1 d4 x e1 e)) usopt))
[~Let_Annot:]
  push_pull (Let d1 x e1 (Annot d2 annot e2)) (Annot d3 annot (Let d4 x e1 e2))
[~Letrec_Annot:]
  push_pull (Letrec1 d1 x e1 (Annot d2 annot e2)) (Annot d3 annot (Letrec1 d4 x e1 e2))
End

Inductive bidir:
(* --- standard rules --- *)
[~refl:]
  (∀x.
     bidir x x)
[~sym:]
  (∀x y.
     bidir x y
     ⇒
     bidir y x)
[~trans:]
  (∀x y.
     bidir x y ∧
     bidir y z
     ⇒
     bidir x z)
[~Lam:]
  (∀a b vs x y.
     bidir x y
     ⇒
     bidir (Lam a vs x) (Lam b vs y))
[~Prim:]
  (∀a b p xs ys.
     LIST_REL bidir xs ys
     ⇒
     bidir (Prim a p xs) (Prim b p ys))
[~App:]
  (∀a b x xs y ys.
     bidir x y ∧
     LIST_REL bidir xs ys
     ⇒
     bidir (App a x xs) (App b y ys))
[~Let:]
  (∀a b v x x1 y y1.
     bidir x y ∧
     bidir x1 y1
     ⇒
     bidir (Let a v x x1) (Let b v y y1))
[~Letrec:]
  (∀a b xs x ys y.
     LIST_REL (λx y. FST x = FST y ∧ bidir (SND x) (SND y)) xs ys ∧
     bidir x y
     ⇒
     bidir (Letrec a xs x) (Letrec b ys y))
[~Case:]
  (∀a b x y v xs ys d e.
     bidir x y ∧
     LIST_REL (λ(c1,vs1,x) (c2,vs2,y).
                c1 = c2 ∧ vs1 = vs2 ∧ bidir x y) xs ys ∧
     OPTREL (λ(r1,x) (r2,y). r1 = r2 ∧ bidir x y) d e
     ⇒
     bidir (Case a x v xs d) (Case b y v ys e))
[~Annot:]
  (∀e1 e2 d1 d2.
    bidir e1 e2
    ⇒ bidir (Annot d1 annot e1) (Annot d2 annot e2))

(* --- interesting rules --- *)
[~Letrec_eq_Let_Letrec:]
  (∀a b v x y.
    bidir (Letrec a [(v,x)] y)
          (Let b v (Letrec c [(v,x)] (Var d v)) y))
[~App_Lam:]
  (∀a b c vs x ws.
    set vs ⊆ set ws ∧ vs ≠ []
    ⇒
    bidir (Lam a ws (App b (Lam c vs x) (MAP (Var d) vs)))
          (Lam a ws x))
[~Letrec_Lam:]
  (∀a b c d vs l e.
    EVERY (λ(v,e). DISJOINT (IMAGE explode (set vs)) (freevars (exp_of e)) ∧
                   ~MEM v vs) l
    ⇒
    bidir (Letrec a l (Lam b vs e))
          (Lam c vs (Letrec d l e)))
[~Lam_append:]
  (∀a xs ys x.
    xs ≠ [] ∧ ys ≠ []
    ⇒
    bidir (Lam a (xs ++ ys) x)
          (Lam a xs (Lam a ys x)))
[~App_append:]
  (∀a xs ys x.
    xs ≠ [] ∧ ys ≠ []
    ⇒
    bidir (App a x (xs ++ ys))
          (App a (App a x xs) ys))
[~Letrec_App:]
  (∀a l b e es.
    bidir (Letrec a l (App b e es))
          (App b (Letrec a l e) (MAP (Letrec a l) es)))
[~Letrec_App_forget:]
  (∀a b l e es.
    EVERY (λe. DISJOINT (freevars (exp_of e))
                        (IMAGE explode (set (MAP FST l)))) es
    ⇒
    bidir (Letrec a l (App b e es))
          (App b (Letrec a l e) es))
[~Let_unroll:]
  (∀d x y d'. bidir (Let d x y (Var d' x)) y)
[~Letrec_unroll:]
  (∀a b v x l.
    MEM (v,x) l ∧ ALL_DISTINCT (MAP FST l)
    ⇒
    bidir (Letrec a l (Var b v))
          (Letrec a l x))
[~specialise:]
  (∀f vs v ws rhs1 rhs2 a b c d e h rs.
     spec_arg f vs v ws rhs1 rhs2 ∧
     (vs = [] ⇒ ws ≠ []) ∧ ALL_DISTINCT (f::v::vs ++ ws) ∧
     set vs ∪ {v} ∪ set ws ⊆ set rs
     ⇒
     bidir (Lam h rs $ Letrec a [(f,Lam e (vs ++ [v] ++ ws) rhs1)]
                         (App b (Var c f) (MAP (Var d) (vs ++ [v] ++ ws))))
           (Lam h rs $ Letrec a [(f,Lam e (vs ++ ws) rhs2)]
                         (App b (Var c f) (MAP (Var d) (vs ++ ws)))))
[~Let_Let_Let:]
  (∀v w x y e a1 a2 a3 b1 b2 b3.
     v ≠ w ∧
     explode w ∉ freevars (exp_of x) ∧
     explode v ∉ freevars (exp_of x)
     ⇒
     bidir (Let a1 v x (Let a2 v x (Let a3 w y e)))
           (Let b1 v x (Let b2 w y (Let b3 v x e))))
[~Let_Let_Letrec:]
  (∀a1 v x a2 a3 w y e b1 b2 b3.
    v ≠ w ∧
    explode w ∉ freevars (exp_of x) ∧
    explode v ∉ freevars (exp_of x)
    ⇒
    bidir (Let a1 v x (Let a2 v x (Letrec1 a3 w y e)))
          (Let b1 v x (Letrec1 b2 w y (Let b3 v x e))))
[~Letrec_Letrec_Let:]
  (∀a1 v x a2 w y e b1 b2 b3.
    v ≠ w ∧
    explode w ∉ freevars (exp_of x)
    ⇒
    bidir (Letrec1 a1 v x (Letrec1 a2 v x (Let a3 w y e)))
          (Letrec1 b1 v x (Let b2 w y (Letrec1 b3 v x e))))
[~Letrec_Letrec_Letrec:]
  (∀a1 v x a2 w y e b1 b2 b3.
    v ≠ w ∧
    explode w ∉ freevars (exp_of x)
    ⇒
    bidir (Letrec1 a1 v x (Letrec1 a2 v x (Letrec1 a3 w y e)))
          (Letrec1 b1 v x (Letrec1 b2 w y (Letrec1 b3 v x e))))
[~Let_dup:]
  (∀v x e a.
     explode v ∉ freevars (exp_of x)
     ⇒
     bidir (Let a v x e)
           (Let a v x (Let a v x e)))
[~Letrec_dup:]
  (∀d1 f x y d2. bidir (Letrec1 d1 f x y) (Letrec1 d2 f x (Letrec1 d3 f x y)))
[~push_pull:]
  (∀e1 e2. push_pull e1 e2 ⇒ bidir e1 e2)
End

Overload "<-->" = “bidir”
val _ = set_fixity "<-->" (Infixl 480);

Theorem bidir_refl[allow_rebind,simp] = bidir_refl;

Theorem bidir_sym[allow_rebind]:
  ∀x y. (x <--> y) ⇔ (y <--> x)
Proof
  metis_tac [bidir_sym]
QED

Inductive pres:
[~refl:]
  (∀x.
     pres x x)
[~trans:]
  (∀x y.
     pres x y ∧
     pres y z
     ⇒
     pres x z)
[~unidir:]
  (∀x y.
     (x --> y)
     ⇒
     pres x y)
[~bidir:]
  (∀x y.
     (x <--> y)
     ⇒
     pres x y)
[~Lam:]
  (∀a b vs x y.
     pres x y
     ⇒
     pres (Lam a vs x) (Lam b vs y))
[~Prim:]
  (∀a b p xs ys.
     LIST_REL pres xs ys
     ⇒
     pres (Prim a p xs) (Prim b p ys))
[~App:]
  (∀a b x xs y ys.
     pres x y ∧
     LIST_REL pres xs ys
     ⇒
     pres (App a x xs) (App b y ys))
[~Let:]
  (∀a b v x x1 y y1.
     pres x y ∧
     pres x1 y1
     ⇒
     pres (Let a v x x1) (Let b v y y1))
[~Letrec:]
  (∀a b xs x ys y.
     LIST_REL (λx y. FST x = FST y ∧ pres (SND x) (SND y)) xs ys ∧
     pres x y
     ⇒
     pres (Letrec a xs x) (Letrec b ys y))
[~Case:]
  (∀a b x y v xs ys d e.
     pres x y ∧
     LIST_REL (λ(c1,vs1,x) (c2,vs2,y).
                c1 = c2 ∧ vs1 = vs2 ∧ pres x y) xs ys ∧
     OPTREL (λ(r1,x) (r2,y). r1 = r2 ∧ pres x y) d e
     ⇒
     pres (Case a x v xs d) (Case b y v ys e))
[~Annot:]
  (∀a b annot x y.
     pres x y
     ⇒
     pres (Annot a annot x) (Annot b annot y))
End

Overload "~~>" = “pres”
val _ = set_fixity "~~>" (Infixl 480);

Theorem pres_refl[simp,allow_rebind] = pres_refl;

(*----------------------------------------------------------------------------*
   Proof of preservation of well-formedness
 *----------------------------------------------------------------------------*)

Theorem unidir_imp_wf_preserved:
  ∀x y. (x --> y) ⇒
    (NestedCase_free x ⇒ NestedCase_free y) ∧
    (letrecs_distinct (exp_of x) ⇒ letrecs_distinct (exp_of y)) ∧
    (cexp_wf x ⇒ cexp_wf y)
Proof
  Induct_on `unidir` >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  gvs[exp_of_def, NestedCase_free_def, letrecs_distinct_def, cexp_wf_def]
  >- (drule freshen_cexp_preserves_wf >> rw[])
QED

Theorem push_pull_imp_wf_preserved:
  ∀x y. push_pull x y ⇒
    (NestedCase_free x ⇔ NestedCase_free y) ∧
    (letrecs_distinct (exp_of x) ⇔ letrecs_distinct (exp_of y)) ∧
    (cexp_wf x ⇔ cexp_wf y)
Proof
  Induct_on `push_pull` >> rpt conj_tac >> rpt gen_tac >> simp[] >> strip_tac >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY] >>
  gvs[NestedCase_free_def, cexp_wf_def, exp_of_def, letrecs_distinct_def,
      letrecs_distinct_Apps, letrecs_distinct_Lams, EVERY_MAP] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss]
  >>~- (
    [`OPTION_ALL`],
    once_rewrite_tac[COND_RAND] >> simp[letrecs_distinct_rows_of] >>
    gvs[exp_of_def, EVERY_MAP] >>
    Cases_on `usopt` >> gvs[] >- (rw[] >> eq_tac >> rw[] >> gvs[]) >>
    EVERY_CASE_TAC >> gvs[exp_of_def, cexp_wf_def] >>
    rw[] >> eq_tac >> rw[] >> gvs[EVERY_MEM]
    ) >>
  rw[] >> eq_tac >> rw[] >> gvs[EVERY_MEM, FORALL_PROD] >> res_tac >> gvs[] >>
  Cases_on `es` >> gvs[]
QED

Theorem bidir_imp_wf_preserved:
  ∀x y. (x <--> y) ⇒
    (NestedCase_free x ⇔ NestedCase_free y) ∧
    (letrecs_distinct (exp_of x) ⇔ letrecs_distinct (exp_of y)) ∧
    (cexp_wf x ⇔ cexp_wf y)
Proof
  Induct_on `bidir` >> rpt conj_tac >> rpt gen_tac >> simp[] >> strip_tac >>
  gvs[NestedCase_free_def, cexp_wf_def, exp_of_def, letrecs_distinct_def,
      letrecs_distinct_Apps, letrecs_distinct_Lams, EVERY_MAP]
  >- gvs[LIST_REL_EL_EQN, EL_MAP, EVERY_EL]
  >- (
    gvs[LIST_REL_EL_EQN, EL_MAP, EVERY_EL] >>
    Cases_on `xs` >> Cases_on `ys` >> gvs[]
    )
  >- (
    gvs[LIST_REL_EL_EQN, EL_MAP, EVERY_EL] >>
    simp[ELIM_UNCURRY, MAP_MAP_o, combinTheory.o_DEF] >>
    simp[GSYM combinTheory.o_DEF, GSYM MAP_MAP_o] >>
    `MAP FST xs = MAP FST ys` by gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >> simp[] >>
    Cases_on `xs` >> Cases_on `ys` >> gvs[]
    )
  >- (
    once_rewrite_tac[COND_RAND] >>
    simp[letrecs_distinct_def, letrecs_distinct_rows_of] >>
    rpt conj_tac
    >- (
      gvs[LIST_REL_EL_EQN, EL_MAP, EVERY_EL, OPTREL_def] >> eq_tac >> rw[] >>
      rpt $ (first_x_assum drule >> strip_tac) >>
      rpt (pairarg_tac >> gvs[])
      )
    >- (
      gvs[LIST_REL_EL_EQN, EL_MAP, EVERY_EL, OPTREL_def] >> eq_tac >> rw[] >>
      rpt $ (first_x_assum drule >> strip_tac) >>
      rpt (pairarg_tac >> gvs[])
      ) >>
    `MAP FST xs = MAP FST ys ∧ MAP (FST o SND) xs = MAP (FST o SND) ys` by (
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw[] >> last_x_assum drule >> rpt (pairarg_tac >> gvs[])) >>
    `xs = [] ⇔ ys = []` by (Cases_on `xs` >> Cases_on `ys` >> gvs[]) >>
    gvs[LIST_REL_EL_EQN, EL_MAP, EVERY_EL, OPTREL_def] >> eq_tac >> rw[] >>
    rpt $ (first_x_assum drule >> strip_tac) >> rpt (pairarg_tac >> gvs[])
    )
  >~ [`spec_arg`]
  >- cheat (* TODO specialisation *)
  >~ [`push_pull`]
  >- gvs[push_pull_imp_wf_preserved] >>
  rw[] >> eq_tac >> rw[] >> gvs[EVERY_MEM, FORALL_PROD] >> res_tac >> gvs[]
QED

Theorem pres_imp_wf_preserved:
  ∀x y. (x ~~> y) ⇒
    (NestedCase_free x ⇒ NestedCase_free y) ∧
    (letrecs_distinct (exp_of x) ⇒ letrecs_distinct (exp_of y)) ∧
    (cexp_wf x ⇒ cexp_wf y)
Proof
  Induct_on `pres` >> rpt conj_tac >> rpt gen_tac >> simp[] >> strip_tac >>
  gvs[NestedCase_free_def, cexp_wf_def, exp_of_def, letrecs_distinct_def,
      letrecs_distinct_Apps, letrecs_distinct_Lams, EVERY_MAP]
  >- metis_tac[unidir_imp_wf_preserved]
  >- metis_tac[bidir_imp_wf_preserved]
  >- gvs[LIST_REL_EL_EQN, EL_MAP, EVERY_EL]
  >- (
    gvs[LIST_REL_EL_EQN, EL_MAP, EVERY_EL] >>
    Cases_on `xs` >> Cases_on `ys` >> gvs[]
    )
  >- (
    gvs[LIST_REL_EL_EQN, EL_MAP, EVERY_EL] >>
    simp[ELIM_UNCURRY, MAP_MAP_o, combinTheory.o_DEF] >>
    simp[GSYM combinTheory.o_DEF, GSYM MAP_MAP_o] >>
    `MAP FST xs = MAP FST ys` by gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >> simp[] >>
    Cases_on `xs` >> Cases_on `ys` >> gvs[]
    )
  >- (
    once_rewrite_tac[COND_RAND] >>
    simp[letrecs_distinct_def, letrecs_distinct_rows_of] >>
    rpt conj_tac >> strip_tac
    >- (
      gvs[LIST_REL_EL_EQN, EL_MAP, EVERY_EL, OPTREL_def] >> rw[] >>
      rpt $ (first_x_assum drule >> strip_tac) >>
      rpt (pairarg_tac >> gvs[])
      )
    >- (
      gvs[LIST_REL_EL_EQN, EL_MAP, EVERY_EL, OPTREL_def] >> rw[] >>
      rpt $ (first_x_assum drule >> strip_tac) >>
      rpt (pairarg_tac >> gvs[])
      ) >>
    `MAP FST xs = MAP FST ys ∧ MAP (FST o SND) xs = MAP (FST o SND) ys` by (
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw[] >> last_x_assum drule >> rpt (pairarg_tac >> gvs[])) >>
    `xs ≠ [] ⇒ ys ≠ []` by (Cases_on `xs` >> Cases_on `ys` >> gvs[]) >>
    gvs[LIST_REL_EL_EQN, EL_MAP, EVERY_EL, OPTREL_def] >> rw[] >>
    rpt $ (first_x_assum drule >> strip_tac) >> rpt (pairarg_tac >> gvs[])
    )
QED


(*----------------------------------------------------------------------------*
   Proof of preservation of semantics
 *----------------------------------------------------------------------------*)

Theorem unidir_imp_exp_eq:
  ∀x y. (x --> y) ∧
    NestedCase_free x ∧ letrecs_distinct (exp_of x) ∧ cexp_wf x
    ⇒ exp_of x ≅ exp_of y
Proof
  Induct_on ‘unidir’
  \\ rpt strip_tac
  \\ fs [exp_of_def]
  >- (irule pure_demandTheory.Let_not_in_freevars \\ fs [])
  >- (drule_all freshen_cexp_correctness >> simp[])
QED

Theorem can_spec_arg_if_lemma[local]:
  can_spec_arg f vs v ws x y ⇒
  can_spec_arg f vs v ws (if b then Seq Fail x else x)
                         (if b then Seq Fail y else y)
Proof
  rw [] \\ irule can_spec_arg_Prim \\ fs []
  \\ irule can_spec_arg_Prim \\ fs []
QED

Theorem can_spec_arg_Disj[local]:
  f ≠ z ⇒ can_spec_arg f vs v ws (Disj z xs) (Disj z xs)
Proof
  Induct_on ‘xs’ \\ fs [Disj_def] \\ rw []
  >- (irule can_spec_arg_Prim \\ fs [])
  \\ PairCases_on ‘h’ \\ gvs [Disj_def]
  \\ irule can_spec_arg_Prim \\ fs []
  \\ irule_at Any can_spec_arg_Prim \\ fs []
  \\ irule_at Any can_spec_arg_Var \\ fs []
  \\ irule_at Any can_spec_arg_Prim \\ fs []
QED

Theorem can_spec_arg_lets_for[local]:
  ∀xs x y z w.
    can_spec_arg f vs v ws x y ∧ ¬MEM v (MAP SND xs) ∧ ¬MEM f (MAP SND xs) ∧ w ≠ f ⇒
    can_spec_arg f vs v ws (lets_for z w xs x) (lets_for z w xs y)
Proof
  Induct \\ rpt PairCases \\ fs [lets_for_def] \\ rw []
  \\ irule can_spec_arg_App \\ fs []
  \\ irule_at Any can_spec_arg_Prim \\ fs []
  \\ irule_at Any can_spec_arg_Var \\ fs []
  \\ irule can_spec_arg_Lam \\ fs []
QED

Theorem spec_arg_IMP_can_spec_arg:
  ∀f vs v ws x y.
    spec_arg f vs v ws x y ⇒
    can_spec_arg (explode f)
                 (MAP explode vs) (explode v)
                 (MAP explode ws) (exp_of x) (exp_of y)
Proof
  Induct_on ‘spec_arg’ \\ rw []
  >-
   (fs [SF ETA_ss,exp_of_def]
    \\ irule $ (can_spec_arg_Apps_Var |> SIMP_RULE std_ss [mk_apps_def,APPEND_NIL])
    \\ imp_res_tac LIST_REL_LENGTH
    \\ gvs [LIST_REL_MAP] \\ rw []
    \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
    \\ fs [])
  >~ [‘Var’] >-
   (fs [exp_of_def] \\ irule can_spec_arg_Var \\ fs [])
  >~ [‘Lam’] >-
   (Induct_on ‘ns’ \\ fs [exp_of_def,Lams_def]
    \\ rw [] \\ irule can_spec_arg_Lam \\ fs [])
  >~ [‘Let’] >-
   (gvs [exp_of_def]
    \\ irule can_spec_arg_App \\ fs []
    \\ irule can_spec_arg_Lam \\ fs [])
  >~ [‘App’] >-
   (pop_assum mp_tac \\ pop_assum mp_tac
    \\ qid_spec_tac ‘y’
    \\ qid_spec_tac ‘x’
    \\ qid_spec_tac ‘ys’
    \\ Induct_on ‘xs’ \\ Cases_on ‘ys’ \\ fs [Apps_def,exp_of_def]
    \\ rw []
    \\ last_x_assum $ drule_at $ Pos last
    \\ disch_then $ qspecl_then [‘App ARB x' [h']’,‘App ARB y' [h]’] mp_tac
    \\ gvs [exp_of_def,Apps_def]
    \\ disch_then irule
    \\ irule can_spec_arg_App \\ fs [])
  >~ [‘Prim’] >-
   (gvs [exp_of_def,SF ETA_ss]
    \\ irule can_spec_arg_Prim \\ fs [LIST_REL_MAP]
    \\ pop_assum mp_tac
    \\ match_mp_tac LIST_REL_mono \\ fs [])
  >~ [‘Letrec’] >-
   (gvs [exp_of_def,SF ETA_ss]
    \\ irule can_spec_arg_Letrec \\ fs [LIST_REL_MAP]
    \\ gvs [MEM_MAP,MAP_MAP_o,o_DEF,FORALL_PROD] \\ fs [LAMBDA_PROD]
    \\ rewrite_tac [CONJ_ASSOC]
    \\ conj_tac
    >-
     (qpat_x_assum ‘MAP FST _ = MAP FST _’ mp_tac
      \\ qpat_x_assum ‘∀x. bb’ mp_tac
      \\ qpat_x_assum ‘∀x. bb’ mp_tac
      \\ qid_spec_tac ‘ys’
      \\ qid_spec_tac ‘xs’ \\ rpt $ pop_assum kall_tac
      \\ Induct \\ Cases_on ‘ys’
      \\ gvs [] \\ PairCases_on ‘h’ \\ PairCases \\ gvs [UNCURRY]
      \\ metis_tac [])
    \\ last_x_assum mp_tac
    \\ match_mp_tac LIST_REL_mono \\ fs [FORALL_PROD])
  >~ [‘Case’] >-
   (gvs [exp_of_def]
    \\ irule can_spec_arg_if_lemma
    \\ irule can_spec_arg_App \\ fs []
    \\ irule can_spec_arg_Lam \\ fs []
    \\ qpat_x_assum ‘EVERY _ _’ mp_tac
    \\ rpt $ qpat_x_assum ‘MAP _ _ = _’ mp_tac
    \\ last_x_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ Cases_on ‘ys’ \\ gvs [rows_of_def]
    >-
     (Cases_on ‘d’ \\ Cases_on ‘e’ \\ gvs []
      >- (irule can_spec_arg_Prim \\ fs [])
      \\ rpt (CASE_TAC \\ gvs [IfDisj_def])
      \\ irule can_spec_arg_Prim \\ fs []
      \\ irule_at Any can_spec_arg_Prim \\ fs []
      \\ irule can_spec_arg_Disj \\ fs [])
    \\ PairCases_on ‘h’ \\ PairCases \\ gvs [rows_of_def]
    \\ rw []
    \\ irule can_spec_arg_Prim \\ fs []
    \\ irule_at Any can_spec_arg_Prim \\ fs []
    \\ irule_at Any can_spec_arg_Var \\ fs []
    \\ irule can_spec_arg_lets_for \\ fs []
    \\ gvs [o_DEF,MEM_MAP])
QED

Theorem push_pull_imp_exp_eq:
  ∀x y. push_pull x y ⇒ exp_of x ≅ exp_of y
Proof
  Induct_on `push_pull` >> rw[] >> gvs[exp_of_def, cexp_wf_def, exp_eq_refl]
  >- (
    irule exp_eq_trans >> irule_at Any Let_App >>
    irule exp_eq_trans >> irule_at Any exp_eq_App_cong >>
    irule_at Any pure_inline_relTheory.Let_Lam >> simp[freevars_exp_of] >>
    irule_at Any exp_eq_refl >> simp[exp_eq_refl]
    )
  >- (
    irule exp_eq_trans >> irule_at Any Letrec_App >>
    irule exp_eq_trans >> irule_at Any exp_eq_App_cong >>
    irule_at Any Letrec_Lam_weak >> simp[freevars_exp_of] >>
    irule_at Any exp_eq_refl >> simp[exp_eq_refl]
    )
  >- (
    irule exp_eq_trans >> irule_at Any Let_Prim >>
    simp[MAP_MAP_o, combinTheory.o_DEF, exp_of_def, exp_eq_refl]
    )
  >- (
    irule exp_eq_trans >> irule_at Any Letrec_Prim >>
    simp[MAP_MAP_o, combinTheory.o_DEF, exp_of_def, exp_eq_refl]
    )
  >- (
    irule exp_eq_trans >> irule_at Any Let_Apps >>
    simp[MAP_MAP_o, combinTheory.o_DEF, exp_of_def, exp_eq_refl]
    )
  >- (
    irule exp_eq_trans >> irule_at Any Letrec_Apps >>
    simp[MAP_MAP_o, combinTheory.o_DEF, exp_of_def, exp_eq_refl]
    )
  >- (
    Induct_on `xs` >> rw[Lams_def, exp_eq_refl] >>
    irule exp_eq_trans >>
    irule_at Any pure_inline_relTheory.Let_Lam >> simp[freevars_exp_of] >>
    irule exp_eq_Lam_cong >> gvs[]
    )
  >- (
    Induct_on `xs` >> rw[Lams_def, exp_eq_refl] >>
    irule exp_eq_trans >> irule_at Any Letrec_Lam_weak >> simp[freevars_exp_of] >>
    irule exp_eq_Lam_cong >> gvs[]
    )
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> irule exp_eq_trans >>
    irule_at Any pure_inline_relTheory.Let_Letrec >>
    simp[EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> reverse $ rw[] >>
    gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD, freevars_exp_of, DISJOINT_ALT]
    >- (
      irule exp_eq_Letrec_cong >> gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      simp[LIST_REL_MAP, EVERY2_refl_EQ] >> simp[exp_of_def, exp_eq_refl]
      ) >>
    metis_tac[]
    )
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> irule exp_eq_trans >>
    irule_at Any Letrec_distrib_Letrec >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    gvs[MEM_MAP, PULL_EXISTS, FORALL_PROD, DISJOINT_ALT, freevars_exp_of] >>
    rw[] >- metis_tac[] >>
    irule exp_eq_Letrec_cong >> gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[LIST_REL_MAP, EVERY2_refl_EQ] >> simp[exp_of_def, exp_eq_refl]
    )
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY] >> IF_CASES_TAC >> gvs[]
    >- (
      irule exp_eq_trans >> qexists `Fail` >> rpt $ irule_at Any eval_wh_IMP_exp_eq >>
      rw[subst_def, eval_wh_thm] >> rw[bind1_def, subst1_def, eval_wh_thm]
      ) >>
    cheat
    )
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY] >> IF_CASES_TAC >> gvs[]
    >- (
      irule exp_eq_trans >> qexists `Fail` >> rpt $ irule_at Any eval_wh_IMP_exp_eq >>
      rw[subst_def, eval_wh_thm] >> rw[subst_funs_def, bind_def, subst_def, eval_wh_thm]
      ) >>
    cheat
    )
QED

Theorem bidir_imp_exp_eq:
  ∀x y. (x <--> y) ∧
    NestedCase_free x ∧ letrecs_distinct (exp_of x) ∧ cexp_wf x
    ⇒ exp_of x ≅ exp_of y
Proof
  Induct_on ‘bidir’
  \\ rpt strip_tac
  \\ gvs[NestedCase_free_def, cexp_wf_def]
  >- simp [exp_eq_refl]
  >- (
    imp_res_tac bidir_imp_wf_preserved >> gvs[] >>
    simp [Once exp_eq_sym]
    )
  >- (
    imp_res_tac bidir_imp_wf_preserved >> gvs[] >>
    imp_res_tac exp_eq_trans
    )
  >~ [‘Lam’] >-
   (gvs [exp_of_def, letrecs_distinct_Lams]
    \\ pop_assum kall_tac
    \\ Induct_on ‘vs’ \\ fs [Lams_def] \\ rw []
    \\ irule exp_eq_Lam_cong \\ fs [])
  >~ [‘Prim’] >-
   (gvs [exp_of_def, letrecs_distinct_def]
    \\ irule exp_eq_Prim_cong \\ fs []
    \\ gvs [LIST_REL_MAP]
    \\ qpat_x_assum `LIST_REL _ _ _` mp_tac
    \\ match_mp_tac LIST_REL_mono \\ fs [EVERY_MAP, EVERY_MEM])
  >~ [‘App’] >-
   (gvs [exp_of_def, letrecs_distinct_Apps]
    \\ qpat_x_assum `_ ≠ []` kall_tac \\ qpat_x_assum `_ <--> _` kall_tac
    \\ rpt $ pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct using SNOC_INDUCT
    >- (Cases_on ‘ys’ \\ gvs [Apps_def])
    \\ Cases_on ‘ys’ using SNOC_CASES \\ gvs [Apps_def]
    \\ gvs [SNOC_APPEND,Apps_append,Apps_def]
    \\ rw []
    \\ irule exp_eq_App_cong \\ fs [])
  >~ [‘Let’] >-
   (gvs [exp_of_def, letrecs_distinct_def]
    \\ irule exp_eq_App_cong \\ fs []
    \\ irule exp_eq_Lam_cong \\ fs [])
  >~ [‘Letrec’] >-
   (gvs [exp_of_def, letrecs_distinct_def]
    \\ irule exp_eq_Letrec_cong \\ fs []
    \\ last_x_assum mp_tac
    \\ rpt $ qpat_x_assum `EVERY _ _` mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ Cases_on ‘ys’ \\ fs []
    \\ PairCases_on ‘h’ \\ PairCases \\ fs [])
  >~ [‘Case’] >-
   (gvs [exp_of_def]
    \\ ‘MEM v (FLAT (MAP (FST ∘ SND) xs)) = MEM v (FLAT (MAP (FST ∘ SND) ys))’ by
      (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
       \\ qid_spec_tac ‘ys’
       \\ qid_spec_tac ‘xs’
       \\ Induct \\ Cases_on ‘ys’ \\ fs []
       \\ PairCases_on ‘h’ \\ PairCases \\ fs []
       \\ metis_tac [])
    \\ fs []
    \\ gvs[letrecs_distinct_def, letrecs_distinct_rows_of]
    \\ irule exp_eq_App_cong \\ fs []
    \\ irule exp_eq_Lam_cong \\ fs []
    \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ rpt $ qpat_x_assum `EVERY _ _` mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ Cases_on ‘ys’ \\ fs []
    >-
     (fs [rows_of_def] \\ rpt (CASE_TAC \\ gvs [exp_eq_refl])
      \\ gvs [IfDisj_def]
      \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
    >-
     (fs [rows_of_def] \\ rpt (CASE_TAC \\ gvs [exp_eq_refl])
      \\ gvs [IfDisj_def]
      \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]) >>
    rw[] >> rpt (pairarg_tac >> gvs[]) >> gvs[rows_of_def]
    \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
    \\ rename [‘lets_for _ _ zs’]
    \\ Induct_on ‘zs’ \\ gvs [lets_for_def,FORALL_PROD]
    \\ rw []
    \\ irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs []
    )
  >~ [`Annot`]
  >- gvs[exp_of_def]
  (* interesting rules from here onwards *)
  >-
   (fs [exp_of_def]
    \\ irule Letrec_eq_Let_Letrec)
  >-
   (fs [exp_of_def,MAP_MAP_o,o_DEF]
    \\ irule exp_eq_Lams_cong
    \\ ‘MAP (λx. Var (explode x) : exp) vs = MAP Var (MAP explode vs)’ by
          fs [MAP_MAP_o,o_DEF]
    \\ simp [Apps_Lams_Vars])
  >-
   (last_x_assum mp_tac \\ rpt $ pop_assum kall_tac
    \\ Induct_on ‘vs’ \\ gvs [exp_of_def,Lams_def,exp_eq_refl]
    \\ rw [] \\ irule exp_eq_trans
    \\ irule_at (Pos last) exp_eq_Lam_cong
    \\ first_x_assum $ irule_at $ Pos hd
    \\ gvs [EVERY_MEM,FORALL_PROD]
    \\ conj_tac >- metis_tac []
    \\ irule pure_demandTheory.Letrec_Lam_weak
    \\ gvs [EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD,PULL_EXISTS]
    \\ metis_tac [])
  >-
   (gvs [exp_of_def,Lams_append,exp_eq_refl])
  >-
   (gvs [exp_of_def,Apps_append,exp_eq_refl])
  >-
   (gvs [exp_of_def,MAP_MAP_o,o_DEF]
    \\ rw [] \\ irule exp_eq_trans
    \\ irule_at (Pos hd) pure_demandTheory.Letrec_Apps
    \\ gvs [exp_of_def,MAP_MAP_o,o_DEF,exp_eq_refl])
  >-
   (gvs [exp_of_def,MAP_MAP_o,o_DEF]
    \\ rw [] \\ irule exp_eq_trans
    \\ irule_at (Pos hd) pure_demandTheory.Letrec_Apps
    \\ gvs [exp_of_def,MAP_MAP_o,o_DEF,exp_eq_refl]
    \\ irule pure_demandTheory.exp_eq_Apps_cong
    \\ fs [exp_eq_refl,LIST_REL_MAP,LIST_REL_same]
    \\ gvs [EVERY_MEM] \\ rw [] \\ res_tac
    \\ irule pure_demandTheory.Letrec_not_in_freevars
    \\ gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD,IN_DISJOINT]
    \\ metis_tac [])
  >- (
    irule eval_wh_IMP_exp_eq >> simp[exp_of_def] >> rw[] >>
    simp[subst_def, eval_wh_thm, bind1_def, FLOOKUP_SIMP] >>
    DEP_REWRITE_TAC[IMP_closed_subst] >> simp[IN_FRANGE_FLOOKUP]
    )
  >-
   (gvs [exp_of_def,MEM_EL]
    \\ qspec_then ‘MAP (λ(n,x'). (explode n,exp_of x')) l’ mp_tac
                  pure_demandTheory.Letrec_unfold \\ fs []
    \\ gvs [EL_MAP] \\ disch_then drule \\ fs []
    \\ disch_then $ qspec_then ‘T’ mp_tac
    \\ qpat_x_assum ‘_ = EL _ _’ $ assume_tac o GSYM
    \\ simp [])
  >~ [‘spec_arg’] >-
   (gvs [exp_of_def,SF ETA_ss,MAP_MAP_o,o_DEF]
    \\ irule exp_eq_Lams_cong
    \\ drule_then assume_tac spec_arg_IMP_can_spec_arg
    \\ drule letrec_spec_delarg \\ fs [MEM_MAP]
    \\ gvs [exp_of_def,SF ETA_ss,MAP_MAP_o,o_DEF]
    \\ disch_then irule
    \\ qpat_x_assum ‘ALL_DISTINCT _’ mp_tac
    \\ rewrite_tac [GSYM MAP_APPEND]
    \\ qabbrev_tac ‘xs = vs ++ ws’
    \\ qid_spec_tac ‘xs’ \\ Induct \\ fs [])
  >~ [‘Let _ v x (Let _ v x (Let _ w y e))’] >-
   (gvs [exp_of_def]
    \\ irule pure_inline_relTheory.Let_Let_copy \\ fs [])
  >~ [‘exp_of (Let a v x e) ≅ exp_of (Let a v x (Let a v x e))’] >-
   (gvs [exp_of_def] \\ simp [Once exp_eq_sym]
    \\ irule pure_inline_relTheory.Let_dup \\ fs [])
  >~ [‘Let _ v x (Let _ v x (Letrec1 _ w y e))’]
  >- (
    gvs[exp_of_def] >> irule pure_inline_relTheory.Let_Letrec1_copy >> simp[]
    )
  >~ [‘Letrec1 _ v x (Letrec1 _ v x (Let _ w y e))’]
  >- (
    gvs[exp_of_def] >> irule pure_inline_relTheory.Letrec1_Let_copy >> simp[]
    )
  >~ [‘Letrec1 _ v x (Letrec1 _ v x (Letrec1 _ w y e))’]
  >- (
    gvs[exp_of_def] >> irule pure_inline_relTheory.Letrec1_Letrec1_copy >> simp[]
    )
  >~ [‘exp_of (Letrec1 _ f x y) ≅ exp_of (Letrec1 _ f x (Letrec1 _ f x y))’]
  >- (
    simp[exp_of_def] >> simp[Once exp_eq_sym] >>
    irule pure_inline_relTheory.Letrec1_dup
    )
  >~ [`push_pull`]
  >- gvs[push_pull_imp_exp_eq]
QED

Theorem pres_imp_exp_eq:
  ∀x y. (x ~~> y) ∧
    NestedCase_free x ∧ letrecs_distinct (exp_of x) ∧ cexp_wf x
  ⇒ (exp_of x ≅ exp_of y)
Proof
  Induct_on ‘pres’
  \\ rpt strip_tac
  \\ gvs[NestedCase_free_def, cexp_wf_def]
  >- simp [exp_eq_refl]
  >- (
    imp_res_tac pres_imp_wf_preserved >> gvs[] >>
    imp_res_tac exp_eq_trans
    )
  >- imp_res_tac unidir_imp_exp_eq
  >- imp_res_tac bidir_imp_exp_eq
  >~ [‘Lam’] >-
   (gvs [exp_of_def, letrecs_distinct_Lams]
    \\ qpat_x_assum `_ ≠ _` kall_tac
    \\ Induct_on ‘vs’ \\ fs [Lams_def] \\ rw []
    \\ irule exp_eq_Lam_cong \\ fs [])
  >~ [‘Prim’] >-
   (gvs [exp_of_def, letrecs_distinct_def]
    \\ irule exp_eq_Prim_cong \\ fs []
    \\ gvs [LIST_REL_MAP]
    \\ qpat_x_assum `LIST_REL _ _ _` mp_tac
    \\ match_mp_tac LIST_REL_mono \\ fs [EVERY_MAP, EVERY_MEM])
  >~ [‘App’] >-
   (gvs [exp_of_def, letrecs_distinct_Apps]
    \\ qpat_x_assum `_ ≠ []` kall_tac \\ qpat_x_assum `_ ~~> _` kall_tac
    \\ rpt $ pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct using SNOC_INDUCT
    >- (Cases_on ‘ys’ \\ gvs [Apps_def])
    \\ Cases_on ‘ys’ using SNOC_CASES \\ gvs [Apps_def]
    \\ gvs [SNOC_APPEND,Apps_append,Apps_def]
    \\ rw []
    \\ irule exp_eq_App_cong \\ fs [])
  >~ [‘Let’] >-
   (gvs [exp_of_def, letrecs_distinct_def]
    \\ irule exp_eq_App_cong \\ fs []
    \\ irule exp_eq_Lam_cong \\ fs [])
  >~ [‘Letrec’] >-
   (gvs [exp_of_def, letrecs_distinct_def]
    \\ irule exp_eq_Letrec_cong \\ fs []
    \\ last_x_assum mp_tac
    \\ rpt $ qpat_x_assum `EVERY _ _` mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ Cases_on ‘ys’ \\ fs []
    \\ PairCases_on ‘h’ \\ PairCases \\ fs [])
  >~ [‘Case’] >-
   (gvs [exp_of_def]
    \\ ‘MEM v (FLAT (MAP (FST ∘ SND) xs)) = MEM v (FLAT (MAP (FST ∘ SND) ys))’ by
      (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
       \\ qid_spec_tac ‘ys’
       \\ qid_spec_tac ‘xs’
       \\ Induct \\ Cases_on ‘ys’ \\ fs []
       \\ PairCases_on ‘h’ \\ PairCases \\ fs []
       \\ metis_tac [])
    \\ fs []
    \\ gvs[letrecs_distinct_def, letrecs_distinct_rows_of]
    \\ irule exp_eq_App_cong \\ fs []
    \\ irule exp_eq_Lam_cong \\ fs []
    \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ rpt $ qpat_x_assum `EVERY _ _` mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ Cases_on ‘ys’ \\ fs []
    >-
     (fs [rows_of_def] \\ rpt (CASE_TAC \\ gvs [exp_eq_refl])
      \\ gvs [IfDisj_def]
      \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
    >-
     (fs [rows_of_def] \\ rpt (CASE_TAC \\ gvs [exp_eq_refl])
      \\ gvs [IfDisj_def]
      \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]) >>
    rw[] >> rpt (pairarg_tac >> gvs[]) >> gvs[rows_of_def]
    \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
    \\ rename [‘lets_for _ _ zs’]
    \\ Induct_on ‘zs’ \\ gvs [lets_for_def,FORALL_PROD]
    \\ rw []
    \\ irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs []
    )
  >~ [`Annot`]
  >- gvs[exp_of_def]
QED

(**********)

val _ = export_theory ();
