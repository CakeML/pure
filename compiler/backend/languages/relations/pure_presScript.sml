(*
   This theory defines a syntactic relation that preserves both semantics
   and typing.
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
     pure_tcexpTheory pure_tcexp_lemmasTheory
     pure_typingTheory pure_typingPropsTheory;


val exp_of_def = pureLangTheory.exp_of_def;
val rows_of_def = pureLangTheory.rows_of_def;
val lets_for_def = pureLangTheory.lets_for_def;
val freevars_exp_of = pure_cexp_lemmasTheory.freevars_exp_of

val _ = new_theory "pure_pres";

(*----------------------------------------------------------------------------*
   Definition of syntactic relation
 *----------------------------------------------------------------------------*)

Inductive unidir:
[~Let:]
  (∀(x:'a cexp) y v a.
    explode v ∉ freevars (exp_of y) ⇒
    unidir (Let a v x y) y)
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
                       (App d (Var a f) (xs2 ++ ys2))) ∧
[~Var:]
  (∀f vs v ws n a b.
    n ≠ f ⇒
    spec_arg f vs v ws (Var a n) (Var b n :'a cexp)) ∧
[~Lam:]
  (∀f vs v ws ns x y a b.
    spec_arg f vs v ws x y ∧
    ~MEM v ns ∧ ~MEM f ns ⇒
    spec_arg f vs v ws (Lam a ns x) (Lam b ns y)) ∧
[~Let:]
  (∀f vs v ws x1 x2 y1 y2 n.
    spec_arg f vs v ws x1 x2 ∧
    spec_arg f vs v ws y1 y2 ∧
    n ≠ v ∧ n ≠ f ⇒
    spec_arg f vs v ws (Let a n x1 y1) (Let b n x2 y2)) ∧
[~App:]
  (∀f vs v ws f1 g1 xs ys a b.
    spec_arg f vs v ws f1 g1 ∧
    LIST_REL (spec_arg f vs v ws) xs ys ⇒
    spec_arg f vs v ws (App a f1 xs) (App b g1 ys)) ∧
[~Prim:]
  (∀f vs v ws n xs ys a b.
    LIST_REL (spec_arg f vs v ws) xs ys ⇒
    spec_arg f vs v ws (Prim a n xs) (Prim b n ys)) ∧
[~Letrec:]
  (∀f vs v ws x y xs ys a b.
    LIST_REL (spec_arg f vs v ws) (MAP SND xs) (MAP SND ys) ∧
    DISJOINT {v; f} (set (MAP FST xs)) ∧
    MAP FST xs = MAP FST ys ∧
    spec_arg f vs v ws x y ⇒
    spec_arg f vs v ws (Letrec a xs x) (Letrec b ys y)) ∧
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

Inductive bidir:
(* --- standard rules --- *)
[~refl:]
  (∀x.
     bidir x x) ∧
[~sym:]
  (∀x y.
     bidir x y
     ⇒
     bidir y x) ∧
[~trans:]
  (∀x y.
     bidir x y ∧
     bidir y z
     ⇒
     bidir x z) ∧
[~Lam:]
  (∀a b vs x y.
     bidir x y
     ⇒
     bidir (Lam a vs x) (Lam b vs y)) ∧
[~Prim:]
  (∀a b p xs ys.
     LIST_REL bidir xs ys
     ⇒
     bidir (Prim a p xs) (Prim b p ys)) ∧
[~App:]
  (∀a b x xs y ys.
     bidir x y ∧
     LIST_REL bidir xs ys
     ⇒
     bidir (App a x xs) (App b y ys)) ∧
[~Let:]
  (∀a b v x x1 y y1.
     bidir x y ∧
     bidir x1 y1
     ⇒
     bidir (Let a v x x1) (Let b v y y1)) ∧
[~Letrec:]
  (∀a b xs x ys y.
     LIST_REL (λx y. FST x = FST y ∧ bidir (SND x) (SND y)) xs ys ∧
     bidir x y
     ⇒
     bidir (Letrec a xs x) (Letrec b ys y)) ∧
[~Case:]
  (∀a b x y v xs ys d e.
     bidir x y ∧
     LIST_REL (λ(c1,vs1,x) (c2,vs2,y).
                c1 = c2 ∧ vs1 = vs2 ∧ bidir x y) xs ys ∧
     OPTREL (λ(r1,x) (r2,y). r1 = r2 ∧ bidir x y) d e
     ⇒
     bidir (Case a x v xs d) (Case b y v ys e)) ∧
(* --- interesting rules --- *)
[~Letrec_eq_Let_Letrec:]
  (* typing: neither direction proved - needs to reconcile differing polymorphism *)
  (∀a b v x y.
    bidir (Letrec a [(v,x)] y)
          (Let b v (Letrec c [(v,x)] (Var d v)) y)) ∧
  (* typing: => direction proved
             <= direction has mismatching free variables *)
[~App_Lam:]
  (∀a b c vs x.
    bidir (App a (Lam b vs x) (MAP (Var c) vs))
          x) ∧
[~Letrec_Lam:]
  (∀a b c d vs l e.
    EVERY (λ(v,e). DISJOINT (IMAGE explode (set vs)) (freevars (exp_of e)) ∧
                   ~MEM v vs) l
    ⇒
    bidir (Letrec a l (Lam b vs e))
          (Lam c vs (Letrec d l e))) ∧
[~Lam_append:]
  (∀a xs ys x.
    xs ≠ [] ∧ ys ≠ []
    ⇒
    bidir (Lam a (xs ++ ys) x)
          (Lam a xs (Lam a ys x))) ∧
[~App_append:]
  (∀a xs ys x.
    xs ≠ [] ∧ ys ≠ []
    ⇒
    bidir (App a x (xs ++ ys))
          (App a (App a x xs) ys)) ∧
[~Letrec_App:]
  (* typing: => direction proved
             <= direction needs to reconcile differing polymorphism *)
  (∀a l b e es.
    bidir (Letrec a l (App b e es))
          (App b (Letrec a l e) (MAP (Letrec a l) es))) ∧
[~Letrec_App_forget:]
  (∀a b l e es.
    EVERY (λe. DISJOINT (freevars (exp_of e))
                        (IMAGE explode (set (MAP FST l)))) es
    ⇒
    bidir (Letrec a l (App b e es))
          (App b (Letrec a l e) es)) ∧
[~Letrec_unroll:]
  (* typing: => direction proved
             <= direction needs to reconcile differing polymorphism *)
  (∀a b v x l.
    MEM (v,x) l ∧ ALL_DISTINCT (MAP FST l)
    ⇒
    bidir (Letrec a l (Var b v))
          (Letrec a l x)) ∧
[~specialise:]
  (* typing not yet attempted *)
  (∀f vs v ws rhs1 rhs2 a b c d e h rs.
     spec_arg f vs v ws rhs1 rhs2 ∧
     (vs = [] ⇒ ws ≠ []) ∧ ALL_DISTINCT (f::v::vs ++ ws) ∧
     set vs ∪ {v} ∪ set ws ⊆ set rs
     ⇒
     bidir (Lam h rs $ Letrec a [(f,Lam e (vs ++ [v] ++ ws) rhs1)]
                         (App b (Var c f) (MAP (Var d) (vs ++ [v] ++ ws))))
           (Lam h rs $ Letrec a [(f,Lam e (vs ++ ws) rhs2)]
                         (App b (Var c f) (MAP (Var d) (vs ++ ws))))) ∧
[~Let_Let_Let:]
  (* typing: => direction proved
             <= direction needs to reconcile differing polymorphism *)
  (∀v w x y e a.
     v ≠ w ∧
     explode w ∉ freevars (exp_of x) ∧
     explode v ∉ freevars (exp_of x)
     ⇒
     bidir (Let a v x (Let a v x (Let a w y e)))
           (Let a v x (Let a w y (Let a v x e)))) ∧
[~Let_dup:]
  (∀v x e a.
     explode v ∉ freevars (exp_of x)
     ⇒
     bidir (Let a v x e)
           (Let a v x (Let a v x e)))
End

Overload "<-->" = “bidir”
val _ = set_fixity "<-->" (Infixl 480);

Theorem bidir_refl[simp] = bidir_refl;

Theorem bidir_sym:
  ∀x y. (x <--> y) ⇔ (y <--> x)
Proof
  metis_tac [bidir_sym]
QED

Inductive pres:
[~refl:]
  (∀x.
     pres x x) ∧
[~trans:]
  (∀x y.
     pres x y ∧
     pres y z
     ⇒
     pres x z) ∧
[~unidir:]
  (∀x y.
     (x --> y)
     ⇒
     pres x y) ∧
[~bidir:]
  (∀x y.
     (x <--> y)
     ⇒
     pres x y) ∧
[~Lam:]
  (∀a b vs x y.
     pres x y
     ⇒
     pres (Lam a vs x) (Lam b vs y)) ∧
[~Prim:]
  (∀a b p xs ys.
     LIST_REL pres xs ys
     ⇒
     pres (Prim a p xs) (Prim b p ys)) ∧
[~App:]
  (∀a b x xs y ys.
     pres x y ∧
     LIST_REL pres xs ys
     ⇒
     pres (App a x xs) (App b y ys)) ∧
[~Let:]
  (∀a b v x x1 y y1.
     pres x y ∧
     pres x1 y1
     ⇒
     pres (Let a v x x1) (Let b v y y1)) ∧
[~Letrec:]
  (∀a b xs x ys y.
     LIST_REL (λx y. FST x = FST y ∧ pres (SND x) (SND y)) xs ys ∧
     pres x y
     ⇒
     pres (Letrec a xs x) (Letrec b ys y)) ∧
[~Case:]
  (∀a b x y v xs ys d e.
     pres x y ∧
     LIST_REL (λ(c1,vs1,x) (c2,vs2,y).
                c1 = c2 ∧ vs1 = vs2 ∧ pres x y) xs ys ∧
     OPTREL (λ(r1,x) (r2,y). r1 = r2 ∧ pres x y) d e
     ⇒
     pres (Case a x v xs d) (Case b y v ys e))
End

Overload "~~>" = “pres”
val _ = set_fixity "~~>" (Infixl 480);

Theorem pres_refl[simp] = pres_refl;

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
  >- cheat (* TODO specialisation *) >>
  rw[] >> eq_tac >> rw[] >> gvs[EVERY_MEM, FORALL_PROD] >> res_tac
  >- cheat (* App_Lam - not true due to potentially empty `vs` *)
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
  ∀x y. (x --> y) ⇒ (exp_of x ≅ exp_of y)
Proof
  Induct_on ‘unidir’
  \\ rpt strip_tac
  \\ fs [exp_of_def]
  >- (irule pure_demandTheory.Let_not_in_freevars \\ fs [])
QED

Triviality case_lemma:
  x ≅ y ⇒ (if b then Seq Fail x else x) ≅ (if b then Seq Fail y else y)
Proof
  rw [] \\ fs []
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
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

Theorem bidir_imp_exp_eq:
  ∀x y. (x <--> y) ⇒ (exp_of x ≅ exp_of y)
Proof
  Induct_on ‘bidir’
  \\ rpt strip_tac
  >- simp [exp_eq_refl]
  >- simp [Once exp_eq_sym]
  >- imp_res_tac exp_eq_trans
  >~ [‘Lam’] >-
   (gvs [exp_of_def]
    \\ Induct_on ‘vs’ \\ fs [Lams_def] \\ rw []
    \\ irule exp_eq_Lam_cong \\ fs [])
  >~ [‘Prim’] >-
   (gvs [exp_of_def]
    \\ irule exp_eq_Prim_cong \\ fs []
    \\ gvs [LIST_REL_MAP]
    \\ pop_assum mp_tac
    \\ match_mp_tac LIST_REL_mono \\ fs [])
  >~ [‘App’] >-
   (gvs [exp_of_def]
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct using SNOC_INDUCT
    >- (Cases_on ‘ys’ \\ gvs [Apps_def])
    \\ Cases_on ‘ys’ using SNOC_CASES \\ gvs [Apps_def]
    \\ gvs [SNOC_APPEND,Apps_append,Apps_def]
    \\ rw []
    \\ irule exp_eq_App_cong \\ fs [])
  >~ [‘Let’] >-
   (gvs [exp_of_def]
    \\ irule exp_eq_App_cong \\ fs []
    \\ irule exp_eq_Lam_cong \\ fs [])
  >~ [‘Letrec’] >-
   (gvs [exp_of_def]
    \\ irule exp_eq_Letrec_cong \\ fs []
    \\ last_x_assum mp_tac
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
    \\ fs [] \\ irule case_lemma
    \\ irule exp_eq_App_cong \\ fs []
    \\ irule exp_eq_Lam_cong \\ fs []
    \\ pop_assum kall_tac
    \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ Cases_on ‘ys’ \\ fs []
    >-
     (fs [rows_of_def] \\ rpt (CASE_TAC \\ gvs [exp_eq_refl])
      \\ gvs [IfDisj_def]
      \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
    \\ PairCases_on ‘h’ \\ PairCases \\ fs []
    \\ strip_tac \\ gvs [rows_of_def]
    \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
    \\ rename [‘lets_for _ _ zs’]
    \\ Induct_on ‘zs’ \\ gvs [lets_for_def,FORALL_PROD]
    \\ rw []
    \\ irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [])
  (* interesting rules from here onwards *)
  >-
   (fs [exp_of_def]
    \\ irule Letrec_eq_Let_Letrec)
  >-
   (fs [exp_of_def,MAP_MAP_o,o_DEF]
    \\ ‘MAP (λx. Var (explode x) : exp) vs = MAP Var (MAP explode vs)’ by
          fs [MAP_MAP_o,o_DEF]
    \\ simp [Apps_Lams_Vars])
  >-
   (Induct_on ‘vs’ \\ gvs [exp_of_def,Lams_def,exp_eq_refl]
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
  >-
   (gvs [exp_of_def,MEM_EL]
    \\ qspec_then ‘MAP (λ(n,x'). (explode n,exp_of x')) l’ mp_tac
                  pure_demandTheory.Letrec_unfold \\ fs []
    \\ gvs [EL_MAP] \\ disch_then drule \\ fs []
    \\ disch_then $ qspec_then ‘T’ mp_tac
    \\ impl_tac
    >-
     (gvs [MAP_MAP_o,o_DEF,LAMBDA_PROD]
      \\ pop_assum mp_tac
      \\ qmatch_goalsub_abbrev_tac ‘_ xs ⇒ _ ys’
      \\ qsuff_tac ‘xs = MAP implode ys’ \\ gvs []
      >- metis_tac [ALL_DISTINCT_MAP]
      \\ unabbrev_all_tac \\ rpt $ pop_assum kall_tac
      \\ Induct_on ‘l’ \\ gvs [] \\ PairCases \\ fs [])
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
  >~ [‘Let a v x (Let a v x (Let a w y e))’] >-
   (gvs [exp_of_def]
    \\ irule pure_inlineTheory.Let_Let_copy \\ fs [])
  >~ [‘exp_of (Let a v x e) ≅ exp_of (Let a v x (Let a v x e))’] >-
   (gvs [exp_of_def] \\ simp [Once exp_eq_sym]
    \\ irule pure_inlineTheory.Let_dup \\ fs [])
QED

Theorem pres_imp_exp_eq:
  ∀x y. (x ~~> y) ⇒ (exp_of x ≅ exp_of y)
Proof
  Induct_on ‘pres’
  \\ rpt strip_tac
  >- simp [exp_eq_refl]
  >- imp_res_tac exp_eq_trans
  >- imp_res_tac unidir_imp_exp_eq
  >- imp_res_tac bidir_imp_exp_eq
  >~ [‘Lam’] >-
   (gvs [exp_of_def]
    \\ Induct_on ‘vs’ \\ fs [Lams_def] \\ rw []
    \\ irule exp_eq_Lam_cong \\ fs [])
  >~ [‘Prim’] >-
   (gvs [exp_of_def]
    \\ irule exp_eq_Prim_cong \\ fs []
    \\ gvs [LIST_REL_MAP]
    \\ pop_assum mp_tac
    \\ match_mp_tac LIST_REL_mono \\ fs [])
  >~ [‘App’] >-
   (gvs [exp_of_def]
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct using SNOC_INDUCT
    >- (Cases_on ‘ys’ \\ gvs [Apps_def])
    \\ Cases_on ‘ys’ using SNOC_CASES \\ gvs [Apps_def]
    \\ gvs [SNOC_APPEND,Apps_append,Apps_def]
    \\ rw []
    \\ irule exp_eq_App_cong \\ fs [])
  >~ [‘Let’] >-
   (gvs [exp_of_def]
    \\ irule exp_eq_App_cong \\ fs []
    \\ irule exp_eq_Lam_cong \\ fs [])
  >~ [‘Letrec’] >-
   (gvs [exp_of_def]
    \\ irule exp_eq_Letrec_cong \\ fs []
    \\ last_x_assum mp_tac
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
    \\ fs [] \\ irule case_lemma
    \\ irule exp_eq_App_cong \\ fs []
    \\ irule exp_eq_Lam_cong \\ fs []
    \\ pop_assum kall_tac
    \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ Cases_on ‘ys’ \\ fs []
    >-
     (fs [rows_of_def] \\ rpt (CASE_TAC \\ gvs [exp_eq_refl])
      \\ gvs [IfDisj_def]
      \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
    \\ PairCases_on ‘h’ \\ PairCases \\ fs []
    \\ strip_tac \\ gvs [rows_of_def]
    \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
    \\ rename [‘lets_for _ _ zs’]
    \\ Induct_on ‘zs’ \\ gvs [lets_for_def,FORALL_PROD]
    \\ rw []
    \\ irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [])
QED

(*----------------------------------------------------------------------------*
   Proof of preservation of typing
 *----------------------------------------------------------------------------*)

Theorem unidir_preserves_typing:
  ∀x y ns db st env t.
    (x --> y) ∧
    type_tcexp ns db st env (tcexp_of x) t
  ⇒ type_tcexp ns db st env (tcexp_of y) t
Proof
  Induct_on `unidir` >> rw[] >>
  drule $ SRULE [] type_tcexp_NestedCase_free >> strip_tac >> gvs[tcexp_of_def] >>
  gvs[Once type_tcexp_cases] >>
  irule type_tcexp_env_extensional >> goal_assum $ drule_at Any >>
  simp[freevars_tcexp_of] >> gvs[freevars_exp_of] >>
  rw[] >> gvs[]
QED

Triviality ALOOKUP_MAP_3':
  ALOOKUP (MAP (λ(k,v1,v2). (k,v1,f v1 v2)) l) =
  OPTION_MAP (λ(v1,v2). (v1, f v1 v2)) o ALOOKUP l
Proof
  Induct_on `l` >> rw[FUN_EQ_THM] >> pairarg_tac >> gvs[] >>
  IF_CASES_TAC >> gvs[]
QED

Theorem bidir_preserves_typing:
  ∀x y ns db st env t.
    (x <--> y) ∧ namespace_ok ns
  ⇒ (type_tcexp ns db st env (tcexp_of x) t ⇔ type_tcexp ns db st env (tcexp_of y) t)
Proof
  Induct_on `bidir` >> rw[] >> gvs[tcexp_of_def]

(* Boilerplate cases *)
  >- ( (* Lam *)
    once_rewrite_tac[type_tcexp_cases] >> simp[]
    )
  >- ( (* Prim *)
    once_rewrite_tac[type_tcexp_cases] >> simp[] >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >>
    eq_tac >> rw[] >>
    gvs[MAP_EQ_CONS, LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss] >>
    metis_tac[]
    )
  >- ( (* App *)
    once_rewrite_tac[type_tcexp_cases] >> simp[] >> gvs[LIST_REL_EL_EQN, EL_MAP]
    )
  >- ( (* Let *)
    once_rewrite_tac[type_tcexp_cases] >> simp[]
    )
  >- ( (* Letrec *)
    once_rewrite_tac[type_tcexp_cases] >> simp[] >> gvs[miscTheory.map_fst] >>
    `MAP FST xs = MAP FST ys` by gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >> eq_tac >> rw[] >> gvs[] >>
    irule_at Any EQ_REFL >> simp[] >> rw[]
    >- (rpt (first_x_assum drule >> strip_tac) >> rpt (pairarg_tac >> gvs[]))
    >- (Cases_on `ys` >> gvs[])
    >- (rpt (first_x_assum drule >> strip_tac) >> rpt (pairarg_tac >> gvs[]))
    >- (Cases_on `xs` >> gvs[])
    )
  >- ( (* Case *)
    `MAP FST xs = MAP FST ys` by gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, ELIM_UNCURRY] >>
    eq_tac >> rw[Once type_tcexp_cases] >> gvs[]
    >- (
      irule type_tcexp_BoolCase >> gvs[OPTREL_def] >>
      gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP,
          MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss]
      )
    >- (
      rpt (pairarg_tac >> gvs[]) >>
      irule type_tcexp_TupleCase >> gvs[OPTREL_def] >>
      irule_at Any EQ_REFL >> gvs[]
      )
    >- (
      irule type_tcexp_ExceptionCase >> gvs[OPTREL_def] >>
      gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP,
          MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss]
      )
    >- (
      irule type_tcexp_Case >> gvs[] >>
      rpt $ goal_assum $ drule_at Any >>
      gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP,
          MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss] >>
      gvs[OPTREL_def] >> Cases_on `ys` >> gvs[]
      )
    >- (
      irule type_tcexp_BoolCase >> gvs[OPTREL_def] >>
      gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP,
          MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss]
      )
    >- (
      rpt (pairarg_tac >> gvs[]) >>
      irule type_tcexp_TupleCase >> gvs[OPTREL_def] >>
      irule_at Any EQ_REFL >> gvs[]
      )
    >- (
      irule type_tcexp_ExceptionCase >> gvs[OPTREL_def] >>
      gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP,
          MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss]
      )
    >- (
      irule type_tcexp_Case >> gvs[] >>
      rpt $ goal_assum $ drule_at Any >>
      gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP,
          MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss] >>
      gvs[OPTREL_def] >> Cases_on `xs` >> gvs[]
      )
    )

(* Interesting cases *)

  >- ( (* Letrec_eq_Let_Letrec *)
    reverse eq_tac >> rw[]
    >- (
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      qpat_x_assum `type_tcexp _ _ _ _ (Letrec _ _) _` mp_tac >>
      rw[Once type_tcexp_cases] >> gvs[] >>
      qpat_x_assum `type_tcexp _ _ _ _ (Var _) _` mp_tac >>
      rw[Once type_tcexp_cases] >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
      irule type_tcexp_Letrec >> simp[PULL_EXISTS, EXISTS_PROD] >>
      cheat
      )
    >- (
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >> pairarg_tac >> gvs[] >>
      irule type_tcexp_Let >> irule_at Any type_tcexp_Letrec >>
      irule_at Any type_tcexp_Var >> simp[PULL_EXISTS, EXISTS_PROD] >>
      cheat
      )
    )
  >- ( (* App_Lam *)
    simp[MAP_MAP_o, combinTheory.o_DEF, tcexp_of_def, SF ETA_ss] >>
    reverse eq_tac >> rw[]
    >- cheat (* free variables do not match *)
    >- (
      pop_assum mp_tac >>
      ntac 2 $ simp[Once type_tcexp_cases] >> rw[] >> gvs[] >>
      gvs[LIST_REL_MAP1, combinTheory.o_DEF] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      imp_res_tac $ SRULE [] type_tcexp_NestedCase_free >>
      `arg_tys' = arg_tys ∧ t = ret_ty` by (
        drule Functions_eq_imp >> strip_tac >>
        gvs[Functions_APPEND, Functions_def] >>
        Cases_on `cs` >> gvs[Functions_def]) >>
      gvs[] >>
      irule type_tcexp_generalise_env >> goal_assum $ drule_at Any >>
      simp[ALOOKUP_APPEND] >> rw[] >>
      pop_assum mp_tac >> CASE_TAC >> gvs[] >> rw[] >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, EL_MAP] >>
      gvs[LIST_REL_EL_EQN] >> first_x_assum drule >>
      rw[Once type_tcexp_cases] >>
      PairCases_on `s` >> gvs[specialises_def] >> gen_tac >>
      pop_assum $ assume_tac o GSYM >> gvs[] >>
      qspecl_then [`0`,`subs`,`s1`,`0`] assume_tac $
        GSYM subst_db_shift_db_2 >> gvs[] >>
      irule_at (Pos last) EQ_REFL >> simp[] >>
      gvs[EVERY_MAP, EVERY_MEM, type_ok_shift_db]
      )
    )
  >- ( (* Letrec_Lam *)
    eq_tac >> rw[]
    >- (
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      irule type_tcexp_Lam >> simp[] >>
      irule type_tcexp_Letrec >> simp[] >>
      qexists `schemes` >> simp[] >> reverse $ rw[]
      >- (
        irule type_tcexp_env_extensional >>
        goal_assum $ drule_at Any >> rw[] >>
        simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
        simp[ALOOKUP_APPEND] >> CASE_TAC >> gvs[] >- (CASE_TAC >> gvs[]) >>
        qsuff_tac `ALOOKUP (REVERSE (ZIP (MAP FST l, schemes))) x = NONE` >> simp[] >>
        imp_res_tac LIST_REL_LENGTH >>
        gvs[ALOOKUP_NONE, MAP_REVERSE, MAP_ZIP] >> simp[MEM_MAP, FORALL_PROD] >>
        CCONTR_TAC >> gvs[EVERY_MEM] >> last_x_assum drule >>
        simp[] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP] >> simp[EL_MEM]
        ) >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
      first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> rw[] >>
      irule type_tcexp_env_extensional >> goal_assum $ drule_at Any >> rw[] >>
      imp_res_tac $ SRULE [] type_tcexp_NestedCase_free >>
      gvs[freevars_tcexp_of, freevars_exp_of] >>
      `¬ MEM x vs` by (
        gvs[EVERY_MEM, FORALL_PROD, SF DNF_ss, DISJOINT_ALT] >>
        CCONTR_TAC >> gvs[] >> last_x_assum $ drule_at Any >> simp[] >>
        simp[MEM_EL] >> rpt $ goal_assum $ drule_at Any >> simp[]) >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      simp[ALOOKUP_APPEND, ALOOKUP_MAP_3'] >>
      CASE_TAC >> gvs[] >> CASE_TAC >> gvs[] >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_EL]
      )
    >- (
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      irule type_tcexp_Letrec >> simp[] >>
      irule_at Any type_tcexp_Lam >> simp[] >>
      qexists `schemes` >> rw[]
      >- (
        irule type_tcexp_env_extensional >>
        goal_assum $ drule_at Any >> rw[] >>
        simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
        simp[ALOOKUP_APPEND] >> CASE_TAC >> gvs[] >- (CASE_TAC >> gvs[]) >>
        qsuff_tac `ALOOKUP (REVERSE (ZIP (vs, MAP ($, 0n) arg_tys))) x = NONE` >>
        simp[] >> imp_res_tac LIST_REL_LENGTH >>
        gvs[ALOOKUP_NONE, MAP_REVERSE, MAP_ZIP] >> simp[MEM_MAP, FORALL_PROD] >>
        gvs[EVERY_MEM, FORALL_PROD, SF DNF_ss] >>
        last_x_assum irule >>
        imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, EL_MAP] >>
        qexists `SND (EL n l)` >> simp[EL_MEM]
        ) >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
      first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> rw[] >>
      irule type_tcexp_env_extensional >> goal_assum $ drule_at Any >> rw[] >>
      imp_res_tac $ SRULE [] type_tcexp_NestedCase_free >>
      gvs[freevars_tcexp_of, freevars_exp_of] >>
      `¬ MEM x vs` by (
        gvs[EVERY_MEM, FORALL_PROD, SF DNF_ss, DISJOINT_ALT] >>
        CCONTR_TAC >> gvs[] >> last_x_assum $ drule_at Any >> simp[] >>
        simp[MEM_EL] >> rpt $ goal_assum $ drule_at Any >> simp[]) >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      simp[ALOOKUP_APPEND, ALOOKUP_MAP_3'] >>
      CASE_TAC >> gvs[] >> CASE_TAC >> gvs[] >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_EL]
      )
    )
  >- ( (* Lam_append *)
    once_rewrite_tac[type_tcexp_cases] >> simp[] >>
    eq_tac >> rw[] >> gvs[]
    >- (
      irule_at Any type_tcexp_Lam >> gvs[LENGTH_EQ_SUM, Functions_APPEND] >>
      irule_at Any EQ_REFL >> simp[] >> gvs[GSYM ZIP_APPEND, REVERSE_APPEND] >>
      Cases_on `l1` >> Cases_on `l2` >> gvs[]
      )
    >- (
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      qexists `arg_tys ++ arg_tys'` >> simp[Functions_APPEND] >>
      irule_at Any EQ_REFL >> simp[GSYM ZIP_APPEND, REVERSE_APPEND]
      )
    )
  >- ( (* App_append *)
    once_rewrite_tac[type_tcexp_cases] >> simp[] >>
    eq_tac >> rw[] >> gvs[]
    >- (
      gvs[LIST_REL_SPLIT1] >> irule_at Any type_tcexp_App >>
      rpt $ goal_assum $ drule_at Any >> gvs[Functions_APPEND] >>
      Cases_on `ys1` >> Cases_on `ys2` >> gvs[]
      )
    >- (
      qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >> rw[Once type_tcexp_cases] >>
      simp[LIST_REL_SPLIT1, PULL_EXISTS] >>
      rpt $ goal_assum $ drule_at Any >> gvs[Functions_APPEND]
      )
    )
  >- ( (* Letrec_App *)
    reverse eq_tac >> rw[]
    >- cheat (* letrecs can all be typed differently *)
    >- (
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      irule type_tcexp_App >> irule_at Any type_tcexp_Letrec >>
      rpt $ goal_assum $ drule_at Any >> simp[] >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >> simp[tcexp_of_def] >>
      irule type_tcexp_Letrec >> simp[] >>
      rpt $ goal_assum $ drule_at Any >> simp[] >>
      gvs[LIST_REL_EL_EQN, EL_MAP]
      )
    )
  >- ( (* Letrec_App_forget *)
    eq_tac >> rw[]
    >- (
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      irule type_tcexp_App >> irule_at Any type_tcexp_Letrec >>
      qexistsl [`schemes`,`arg_tys`] >> rw[] >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >> first_x_assum drule >> rw[] >>
      irule type_tcexp_env_extensional >> goal_assum $ drule_at Any >>
      rw[ALOOKUP_APPEND] >> CASE_TAC >> gvs[] >> irule FALSITY >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, EL_MAP] >>
      pairarg_tac >> gvs[] >>
      gvs[EVERY_EL] >> last_x_assum drule >> rw[DISJOINT_ALT, PULL_EXISTS] >>
      imp_res_tac $ SRULE [] type_tcexp_NestedCase_free >>
      gvs[freevars_tcexp_of, freevars_exp_of] >>
      simp[MEM_EL, EL_MAP, SF CONJ_ss] >> rpt $ goal_assum drule >> simp[]
      )
    >- (
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
      rw[Once type_tcexp_cases] >>
      irule type_tcexp_Letrec >> simp[] >> goal_assum drule >> simp[] >>
      irule type_tcexp_App >> goal_assum drule >> rw[] >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >> last_x_assum drule >> strip_tac >>
      irule type_tcexp_env_extensional >> goal_assum $ drule_at Any >>
      imp_res_tac $ SRULE [] type_tcexp_NestedCase_free >>
      gvs[freevars_tcexp_of, freevars_exp_of, EVERY_EL, DISJOINT_ALT] >>
      rw[ALOOKUP_APPEND] >> CASE_TAC >> gvs[] >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, EL_MAP, MEM_EL, SF CONJ_ss] >>
      pairarg_tac >> gvs[] >>
      last_x_assum drule >> simp[] >> disch_then $ qspec_then `n'` mp_tac >> simp[]
      )
    )
  >- ( (* Letrec_unroll *)
    once_rewrite_tac[type_tcexp_cases] >> simp[] >> eq_tac >> rw[]
    >- (
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      goal_assum drule >> simp[] >>
      gvs[MAP_MAP_o, o_DEF, LAMBDA_PROD] >> gvs[GSYM FST_THM] >>
      gvs[LIST_REL_EL_EQN, EL_MAP, MEM_EL] >>
      first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
      PairCases_on `s` >> gvs[specialises_def] >>
      `ALOOKUP (REVERSE (ZIP (MAP FST l,schemes))) fn = SOME (vars,scheme)` by (
        DEP_REWRITE_TAC[alookup_distinct_reverse] >> simp[MAP_ZIP] >>
        qspec_then `(ZIP (MAP FST l,schemes))` mp_tac ALOOKUP_ALL_DISTINCT_EL >>
        simp[] >> disch_then drule >> simp[MAP_ZIP, EL_ZIP, EL_MAP]) >>
      gvs[ALOOKUP_APPEND] >>
      drule type_tcexp_subst_db >>
      disch_then $ qspecl_then [`0`,`subs`] mp_tac >>
      simp[MAP_MAP_o, o_DEF, LAMBDA_PROD, subst_db_shift_db_unchanged] >>
      simp[ELIM_UNCURRY]
      )
    >- (
      goal_assum drule >> gvs[MAP_MAP_o, o_DEF, LAMBDA_PROD] >> gvs[GSYM FST_THM] >>
      simp[Once type_tcexp_cases, ALOOKUP_APPEND] >>
      DEP_REWRITE_TAC[alookup_distinct_reverse] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >> simp[MAP_ZIP] >>
      qspec_then `(ZIP (MAP FST l,schemes))` mp_tac ALOOKUP_ALL_DISTINCT_EL >>
      simp[MAP_ZIP, EL_ZIP, EL_MAP] >>
      gvs[MEM_EL] >> qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >>
      disch_then drule >> rw[] >>
      gvs[LIST_REL_EL_EQN] >> first_x_assum drule >> simp[EL_MAP] >>
      pairarg_tac >> rw[] >> gvs[] >>
      Cases_on `EL n schemes` >> rw[specialises_def] >>
      cheat
      )
    )
  >- ( (* specialise *)
    cheat (* TODO *)
    )
  >- ( (* Let_Let_Let*)
    reverse eq_tac >> rw[]
    >- cheat (* lets can be typed differently *)
    >- (
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      rename1 `type_tcexp _ _ (MAP (_ newx) _) _ (_ x) tx` >>
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      rename1 `type_tcexp _ _ (MAP (_ newx2) _) _ (_ x) tx2` >>
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      rename1 `type_tcexp _ _ (MAP (_ newy) _) _ (_ y) ty` >>
      rename1 `type_tcexp _ _ _ _ (_ e) te` >>
      ntac 3 $ irule_at Any type_tcexp_Let >>
      qexistsl [`ty`,`tx2`,`tx2`,`newy`,`newx2`,`newx2`] >> simp[] >>
      imp_res_tac $ SRULE [] type_tcexp_NestedCase_free >>
      gvs[freevars_exp_of] >> rw[] >>
      irule type_tcexp_env_extensional >> goal_assum $ drule_at Any >>
      rw[freevars_tcexp_of] >> gvs[]
      )
    )
  >- ( (* Let_dup *)
    eq_tac >> rw[]
    >- (
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      ntac 2 $ irule_at Any type_tcexp_Let >>
      qexistsl [`t1`,`t1`,`new`,`new`] >> simp[] >>
      imp_res_tac $ SRULE [] type_tcexp_NestedCase_free >>
      gvs[freevars_exp_of] >> rw[] >>
      irule type_tcexp_env_extensional >> goal_assum $ drule_at Any >>
      rw[freevars_tcexp_of] >> gvs[]
      )
    >- (
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      rename1 `type_tcexp _ _ (MAP (_ newx) _) _ (_ x) tx` >>
      irule_at Any type_tcexp_Let >>
      qexistsl [`newx`,`tx`] >> simp[] >>
      imp_res_tac $ SRULE [] type_tcexp_NestedCase_free >>
      gvs[freevars_exp_of] >> rw[] >>
      irule type_tcexp_env_extensional >> goal_assum $ drule_at Any >>
      rw[freevars_tcexp_of] >> gvs[]
      )
    )
QED

Theorem pres_preserves_typing:
  namespace_ok ns ⇒
  ∀x y db st env t.
    (x ~~> y) ∧
    type_tcexp ns db st env (tcexp_of x) t
  ⇒ type_tcexp ns db st env (tcexp_of y) t
Proof
  strip_tac >> Induct_on `pres` >> rw[] >> gvs[tcexp_of_def]
  >- ( (* unidir *)
    drule_all unidir_preserves_typing >> simp[]
    )
  >- ( (* bidir *)
    drule_all bidir_preserves_typing >> strip_tac >> gvs[]
    ) >>

  (* Boilerplate cases *)
  qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac
  >- ( (* Lam *)
    once_rewrite_tac[type_tcexp_cases] >> simp[] >>
    metis_tac[]
    )
  >- ( (* Prim *)
    once_rewrite_tac[type_tcexp_cases] >> simp[] >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    gvs[MAP_EQ_CONS, LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss] >>
    metis_tac[]
    )
  >- ( (* App *)
    once_rewrite_tac[type_tcexp_cases] >> rw[] >> gvs[LIST_REL_EL_EQN, EL_MAP] >>
    metis_tac[]
    )
  >- ( (* Let *)
    once_rewrite_tac[type_tcexp_cases] >> simp[] >> metis_tac[]
    )
  >- ( (* Letrec *)
    once_rewrite_tac[type_tcexp_cases] >> simp[] >> gvs[miscTheory.map_fst] >>
    `MAP FST xs = MAP FST ys` by gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >> gvs[] >>
    irule_at Any EQ_REFL >> simp[] >> rw[]
    >- (rpt (first_x_assum drule >> strip_tac) >> rpt (pairarg_tac >> gvs[]))
    >- (Cases_on `ys` >> gvs[])
    )
  >- ( (* Case *)
    `MAP FST xs = MAP FST ys` by gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, ELIM_UNCURRY] >>
    rw[Once type_tcexp_cases] >> gvs[]
    >- (
      irule type_tcexp_BoolCase >> gvs[OPTREL_def] >>
      gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP,
          MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss]
      )
    >- (
      rpt (pairarg_tac >> gvs[]) >>
      irule type_tcexp_TupleCase >> gvs[OPTREL_def] >>
      irule_at Any EQ_REFL >> gvs[]
      )
    >- (
      irule type_tcexp_ExceptionCase >> gvs[OPTREL_def] >>
      gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP,
          MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss] >>
      metis_tac[]
      )
    >- (
      irule type_tcexp_Case >> gvs[] >>
      rpt $ goal_assum $ drule_at Any >>
      gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP,
          MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY, SF ETA_ss] >>
      gvs[OPTREL_def] >- metis_tac[] >>
      conj_tac >- (Cases_on `ys` >> gvs[])
      >- metis_tac[]
      )
    )
QED

(**********)

val _ = export_theory ();
