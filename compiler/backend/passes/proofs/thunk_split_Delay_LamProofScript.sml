(*
   Proof of thunk_split_Delay_Lam
*)

open HolKernel Parse boolLib bossLib term_tactic pairTheory listTheory;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory arithmeticTheory;
open thunk_cexpTheory mlmapTheory mlstringTheory pure_miscTheory
     thunkLangPropsTheory thunk_semanticsTheory thunk_split_Delay_LamTheory
     thunk_Delay_LamTheory thunk_Let_Delay_VarTheory;

val _ = new_theory "thunk_split_Delay_LamProof";

Definition var_creator_ok_def:
  var_creator_ok vc = (mlmap$map_ok vc ∧ mlmap$cmp_of vc = mlstring$compare)
End

Definition vc_to_set_def:
  vc_to_set vc = IMAGE explode (FDOM (to_fmap vc))
End

Theorem new_var_soundness:
  ∀vc' s'. new_var vc s = (s', vc') ∧ var_creator_ok vc ⇒
           var_creator_ok vc' ∧ explode s' ∉ vc_to_set vc ∧
           vc_to_set vc' = vc_to_set vc ∪ {explode s'}
Proof
  completeInduct_on ‘CARD (FDOM (to_fmap vc) ∩ {s2 | strlen s ≤ strlen s2})’
  \\ gvs [var_creator_ok_def]
  \\ gen_tac \\ gen_tac \\ strip_tac
  \\ gen_tac \\ gen_tac
  \\ simp [Once new_var_def]
  \\ gvs [lookup_thm, FLOOKUP_DEF, SF CONJ_ss]
  \\ IF_CASES_TAC \\ strip_tac
  \\ gvs [insert_thm, vc_to_set_def]
  >- (last_x_assum irule \\ simp []
      \\ last_x_assum $ irule_at (Pos last)
      \\ irule CARD_PSUBSET
      \\ irule_at Any FINITE_INTER
      \\ gvs [finite_mapTheory.FDOM_FINITE, PSUBSET_DEF, SUBSET_DEF, SET_EQ_SUBSET]
      \\ first_x_assum $ irule_at Any
      \\ gvs [lookup_thm, finite_mapTheory.FLOOKUP_DEF])
  \\ simp [Once INSERT_SING_UNION, UNION_COMM]
QED

Theorem lets_for_APPEND:
  lets_for m n (l1 ++ l2) e = lets_for m n l1 (lets_for m n l2 e)
Proof
  Induct_on ‘l1’ \\ gvs [lets_for_def, FORALL_PROD]
QED

Theorem FOLDL_replace_Force_Var:
  ∀map_l map m.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (Var m) map_l
    = Var m
Proof
  Induct \\ gvs [replace_Force_def]
QED

Theorem FOLDL_replace_Force_Prim:
  ∀map_l map op l.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (Prim op l) map_l
    = Prim op (MAP (λe. FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) e map_l) l)
Proof
  Induct \\ gvs [replace_Force_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
QED

Theorem FOLDL_replace_Force_Seq:
  ∀map_l map x y.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (Seq x y) map_l
    = Seq (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) x map_l)
          (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) y map_l)
Proof
  Induct \\ gvs [replace_Force_def]
QED

Theorem FOLDL_replace_Force_Let:
  ∀map_l map m x y.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e)
          (Let (SOME (explode m)) x y) map_l
    = Let (SOME (explode m))
          (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) x map_l)
          (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) y
           (FILTER (λv. v ≠ m) map_l))
Proof
  Induct \\ gvs [replace_Force_def]
  \\ rw []
QED

Theorem FOLDL_replace_Force_App:
  ∀map_l map x y.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (App x y) map_l
    = App (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) x map_l)
          (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) y map_l)
Proof
  Induct \\ gvs [replace_Force_def]
QED

Theorem FOLDL_replace_Force_Apps:
  ∀l map_l map op x.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (Apps x l) map_l
    = Apps (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) x map_l)
           (MAP (λe. FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) e map_l) l)
Proof
  Induct \\ gvs [FOLDL_replace_Force_App]
QED

Theorem FOLDL_replace_Force_Lam:
  ∀map_l map x s.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (Lam s x) map_l
    = Lam s (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) x
             (FILTER (λv. explode v ≠ s) map_l))
Proof
  Induct \\ gvs [replace_Force_def]
  \\ rw []
QED

Theorem FOLDL_replace_Force_Lams:
  ∀vL map_l map x s.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (Lams vL x) map_l
    = Lams vL (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) x
             (FILTER (λv. ¬MEM (explode v) vL) map_l))
Proof
  Induct \\ gvs [FOLDL_replace_Force_Lam, FILTER_FILTER, LAMBDA_PROD]
  \\ rw [] \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs [CONJ_COMM]
QED

Theorem FOLDL_replace_Force_Delay:
  ∀map_l map x.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (Delay x) map_l
    = Delay (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) x map_l)
Proof
  Induct \\ gvs [replace_Force_def]
QED

Theorem FOLDL_replace_Force_Box:
  ∀map_l map x.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (Box x) map_l
    = Box (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) x map_l)
Proof
  Induct \\ gvs [replace_Force_def]
QED

Theorem FOLDL_replace_Force_If:
  ∀map_l map x y z.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (If x y z) map_l
    = If (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) x map_l)
         (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) y  map_l)
         (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) z map_l)
Proof
  Induct \\ gvs [replace_Force_def]
QED

Theorem FOLDL_replace_Force_IsEq:
  ∀map_l map n l b x.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (IsEq n l b x) map_l
    = IsEq n l b (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) x map_l)
Proof
  Induct \\ gvs [replace_Force_def]
QED

Theorem FOLDL_replace_Force_lets_for_1:
  ∀l m1 m2 m3 m4 e.
    ¬MEM m2 l ⇒
    replace_Force (Var m1) (explode m2) (lets_for m3 m4 (MAPi (λi v. (i, v)) (MAP explode l)) e)
    = lets_for m3 m4 (MAPi (λi v. (i, v)) (MAP explode l)) (replace_Force (Var m1) (explode m2) e)
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND, replace_Force_def]
QED

Theorem FOLDL_replace_Force_lets_for_2:
  ∀l m1 m2 m3 m4 e.
    MEM m2 l ⇒
    replace_Force (Var m1) (explode m2) (lets_for m3 m4 (MAPi (λi v. (i, v)) (MAP explode l)) e)
    = lets_for m3 m4 (MAPi (λi v. (i, v)) (MAP explode l)) e
Proof
  Induct using SNOC_INDUCT
  \\ rw []
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND, replace_Force_def]
  \\ rename1 ‘lets_for _ _ (MAPi _ (MAP explode l)) (Let (SOME (explode m2)) _ _)’
  \\ Cases_on ‘MEM m2 l’ \\ gvs [FOLDL_replace_Force_lets_for_1, replace_Force_def]
QED

Theorem FOLDL_replace_Force_lets_for:
  ∀map_l map l m1 m2 x.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e)
          (lets_for m1 (explode m2) (MAPi (λi v. (i, v)) (MAP explode l)) x) (FILTER (λv. v ≠ m2) map_l)
    =
    lets_for m1 (explode m2) (MAPi (λi v. (i, v)) (MAP explode l))
             (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) x
              (FILTER (λv. ¬MEM v l ∧ v ≠ m2) map_l))
Proof
  Induct \\ rw [] \\ gvs [FOLDL_replace_Force_lets_for_1, FOLDL_replace_Force_lets_for_2]
QED

Theorem FOLDL_replace_Force_Force_Var1:
  ∀map_l map x v.
    ¬MEM v map_l ⇒
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (Force (Var (explode v))) map_l
    = Force (Var (explode v))
Proof
  Induct \\ gvs [replace_Force_def]
QED

Theorem FOLDL_replace_Force_Force_Var2:
  ∀map_l map v.
    MEM v map_l ⇒
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (Force (Var (explode v))) map_l
    = Var (explode (to_fmap map ' v))
Proof
  Induct \\ gvs [replace_Force_def]
  \\ rw [FOLDL_replace_Force_Var]
QED

Theorem FOLDL_replace_Force_Force:
  ∀map_l x map.
    (∀v. MEM v map_l ⇒ ¬MEM (to_fmap map ' v) map_l) ∧ (∀v. x ≠ Var v) ⇒
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (Force x) map_l
    = Force (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) x map_l)
Proof
  Induct \\ gvs []
  \\ gen_tac \\ Cases  \\ gvs [replace_Force_def]
  \\ rw []
  >~[‘Let opt _ _’]
  >- (last_x_assum irule
      \\ Cases_on ‘opt’ \\ rw [] \\ gvs [replace_Force_def, AllCaseEqs()])
  \\ rename1 ‘FOLDL _ (Force (replace_Force _ _ (Force e))) _’
  \\ Cases_on ‘e’ \\ gvs [replace_Force_def]
  \\ IF_CASES_TAC \\ gvs [FOLDL_replace_Force_Var]
  \\ irule FOLDL_replace_Force_Force_Var1
  \\ gvs []
QED

Theorem FOLDL_replace_Force_change_map:
  ∀map_l x map1 map2.
    (∀v. MEM v map_l ⇒ map1 ' v = map2 ' v) ⇒
    FOLDL (λe v. replace_Force (Var (explode (map1 ' v))) (explode v) e) x map_l
    =
    FOLDL (λe v. replace_Force (Var (explode (map2 ' v))) (explode v) e) x map_l
Proof
  Induct \\ gvs []
QED

val exp_rel1_def = thunk_Delay_LamTheory.exp_rel_def;
val exp_rel2_def = thunk_Let_Delay_VarTheory.full_exp_rel_def;

Theorem dest_Var_soundness:
  ∀e. dest_Var e = NONE ∧ cexp_wf e ⇒ ∀v. exp_of e ≠ Var v
Proof
  Cases_on ‘e’ \\ gvs [dest_Var_def, exp_of_def, AllCaseEqs()]
  >- (rename1 ‘Prim op xs’ \\ Cases_on ‘op’ \\ gvs [exp_of_def, cexp_wf_def]
      \\ Cases_on ‘xs’ \\ gs [args_ok_def]
      \\ rename1 ‘Prim Seq (h::t)’ \\ Cases_on ‘t’ \\ gvs [exp_of_def])
  >- (rename1 ‘Apps _ (MAP _ l)’
      \\ qspec_then ‘l’ assume_tac SNOC_CASES \\ gvs [cexp_wf_def, FOLDL_APPEND])
  >- (rename1 ‘Lams (MAP _ l) _’
      \\ Cases_on ‘l’ \\ gvs [cexp_wf_def, FOLDL_APPEND])
QED

Theorem split_Delayed_Lam_is_Delay:
  split_Delayed_Lam e vc maps = (e_out, v_out) ∧ is_Delay e ⇒ is_Delay e_out
Proof
  Cases_on ‘e’ \\ simp [is_Delay_def, split_Delayed_Lam_def]
  \\ pairarg_tac \\ rw [] \\ simp [is_Delay_def]
QED

Theorem args_ok_split_Delayed_Lam:
  ∀xs vc s map xs' vc'.
    FOLDR (λe (l',vc). (λ(e', vc'). (e'::l', vc')) (split_Delayed_Lam e vc map)) ([],vc) xs = (xs',vc')
    ∧ args_ok (Cons s) xs
    ⇒ args_ok (Cons s) xs'
Proof
  gvs [args_ok_def, form_of_monad_args_def] \\ rw [] \\ gvs []
  \\ pairarg_tac \\ gvs [split_Delayed_Lam_is_Delay]
  >- (pairarg_tac \\ gvs []
      \\ pairarg_tac \\ gvs []
      \\ dxrule_all_then (irule_at Any) split_Delayed_Lam_is_Delay
      \\ dxrule_all_then irule split_Delayed_Lam_is_Delay)
  >- (pairarg_tac \\ gvs []
      \\ pairarg_tac \\ gvs []
      \\ dxrule_all_then (irule_at Any) split_Delayed_Lam_is_Delay
      \\ dxrule_all_then irule split_Delayed_Lam_is_Delay)
  >- (pairarg_tac \\ gvs []
      \\ pairarg_tac \\ gvs []
      \\ dxrule_all_then (irule_at Any) split_Delayed_Lam_is_Delay
      \\ dxrule_all_then irule split_Delayed_Lam_is_Delay)
  >- dxrule_all_then irule split_Delayed_Lam_is_Delay
  >- (pairarg_tac \\ gvs []
      \\ pairarg_tac \\ gvs []
      \\ dxrule_all_then (irule_at Any) split_Delayed_Lam_is_Delay
      \\ dxrule_all_then irule split_Delayed_Lam_is_Delay)
  >- (pairarg_tac \\ gvs []
      \\ pairarg_tac \\ gvs []
      \\ pairarg_tac \\ gvs []
      \\ pairarg_tac \\ gvs []
      \\ dxrule_all_then (irule_at Any) split_Delayed_Lam_is_Delay
      \\ dxrule_all_then (irule_at Any) split_Delayed_Lam_is_Delay
      \\ dxrule_all_then irule split_Delayed_Lam_is_Delay)
  >- dxrule_all_then irule split_Delayed_Lam_is_Delay
QED

Theorem split_Delay_Lam_soundness_Prim:
  ∀xs. (∀e vc'' map map_l' e_out' vc_out.
         MEM e xs ⇒
         split_Delayed_Lam e vc'' map = (e_out',vc_out) ∧
          ALL_DISTINCT map_l' ∧ freevars (exp_of e) ⊆ vc_to_set vc'' ∧
          boundvars (exp_of e) ⊆ vc_to_set vc'' ∧
          IMAGE explode (set map_l') ⊆ vc_to_set vc'' ∧
          IMAGE explode (FRANGE (to_fmap map)) ⊆ vc_to_set vc'' ∧ cexp_wf e ∧
          DISJOINT (set map_l') (FRANGE (to_fmap map)) ∧
          DISJOINT (freevars (exp_of e))
            (IMAGE explode (FRANGE (to_fmap map))) ∧
          DISJOINT (boundvars (exp_of e))
            (IMAGE explode (FRANGE (to_fmap map))) ∧ map_ok map ∧
          cmp_of map = compare ∧ var_creator_ok vc'' ∧
          FDOM (to_fmap map) = set map_l' ⇒
          ∃e2 e3.
            vc_to_set vc'' ⊆ vc_to_set vc_out ∧ var_creator_ok vc_out ∧
            freevars (exp_of e_out') ⊆ vc_to_set vc_out ∧
            boundvars (exp_of e_out') ⊆ vc_to_set vc_out ∧
            boundvars e2 ∩ COMPL (boundvars (exp_of e)) =
            vc_to_set vc_out ∩ COMPL (vc_to_set vc'') ∧
            thunk_Delay_Lam$exp_rel (exp_of e) e2 ∧ full_exp_rel e2 e3 ∧
            cexp_wf e_out' ∧
            exp_of e_out' =
            FOLDL
              (λe v.
                   replace_Force (Var (explode (to_fmap map ' v)))
                     (explode v) e) e3 map_l') ⇒
       ∀vc vc' xs' map map_l.
         FOLDR (λe (l',vc).
                  (λ(e',vc'). (e'::l',vc')) (split_Delayed_Lam e vc map))
               ([],vc) xs = (xs',vc') ∧ map_ok map ∧ cmp_of map = compare ∧
         var_creator_ok vc ∧ FDOM (to_fmap map) = set map_l ∧
         EVERY (λa. cexp_wf a) xs ∧
         IMAGE explode (set map_l) ⊆ vc_to_set vc ∧
         IMAGE explode (FRANGE (to_fmap map)) ⊆ vc_to_set vc ∧
         DISJOINT (set map_l) (FRANGE (to_fmap map)) ∧
         DISJOINT (IMAGE explode (FRANGE (to_fmap map)))
                  (BIGUNION (set (MAP (λa. freevars a) (MAP (λa. exp_of a) xs)))) ∧
         DISJOINT (IMAGE explode (FRANGE (to_fmap map)))
                  (BIGUNION (set (MAP (λa. boundvars a) (MAP (λa. exp_of a) xs)))) ∧
         BIGUNION (set (MAP (λa. freevars a) (MAP (λa. exp_of a) xs)))
                  ⊆ vc_to_set vc ∧
         BIGUNION (set (MAP (λa. boundvars a) (MAP (λa. exp_of a) xs)))
                  ⊆ vc_to_set vc ∧
         ALL_DISTINCT map_l ⇒
         ∃ys ys'. vc_to_set vc ⊆ vc_to_set vc' ∧ var_creator_ok vc' ∧
              BIGUNION (set (MAP (λa. freevars a) (MAP (λa. exp_of a) xs'))) ⊆
                       vc_to_set vc' ∧
              BIGUNION (set (MAP (λa. boundvars a) (MAP (λa. exp_of a) xs'))) ⊆
                       vc_to_set vc' ∧
              BIGUNION (set (MAP (λa. boundvars a) ys)) ∩
                       COMPL
                       (BIGUNION (set (MAP (λa. boundvars a) (MAP (λa. exp_of a) xs)))) =
              vc_to_set vc' ∩ COMPL (vc_to_set vc) ∧
              LIST_REL thunk_Delay_Lam$exp_rel (MAP (λa. exp_of a) xs) ys ∧
              LIST_REL full_exp_rel ys ys' ∧
              MAP (λa. exp_of a) xs'
              = MAP (λe. FOLDL (λe v.
                                  replace_Force (Var (explode (to_fmap map ' v)))
                                                (explode v) e) e map_l) ys' ∧
              EVERY (λa. cexp_wf a) xs'
Proof
  Induct \\ rw [PULL_EXISTS]
  \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gvs []
  \\ last_x_assum $ dxrule_then $ drule_then $ drule_then $ drule_then $ drule_then mp_tac
  \\ impl_tac >- gvs []
  \\ disch_then $ qx_choose_then ‘ys’ $ qx_choose_then ‘ys'’ assume_tac \\ fs []
  \\ qpat_x_assum ‘LIST_REL _ _ _’ $ irule_at Any
  \\ qpat_x_assum ‘LIST_REL _ _ _’ $ irule_at Any
  \\ simp []
  \\ rename1 ‘_ = h ∨ MEM _ _ ⇒ _’
  \\ last_x_assum $ qspec_then ‘h’ assume_tac \\ fs []
  \\ pop_assum $ drule_then $ drule_then mp_tac \\ simp []
  \\ impl_tac
  >- (rw []
      >~[‘DISJOINT (freevars _) _’]
      >- (irule $ iffLR DISJOINT_SYM
          \\ last_x_assum irule \\ simp [])
      >~[‘DISJOINT (boundvars _) _’]
      >- (irule $ iffLR DISJOINT_SYM
          \\ first_x_assum irule \\ simp [])
      \\ irule SUBSET_TRANS \\ metis_tac [])
  \\ disch_then $ qx_choose_then ‘y’ $ qx_choose_then ‘y'’ assume_tac \\ fs []
  \\ qpat_x_assum ‘full_exp_rel _ _’ $ irule_at Any
  \\ simp [] \\ rw []
  >~[‘(boundvars _ ∪ _) ∩ COMPL _ = _ ∩ COMPL _’]
  >- (gvs [SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
      \\ rpt $ conj_tac \\ gen_tac \\ rename1 ‘x ∉ _’
      \\ rpt $ last_x_assum $ qspec_then ‘x’ assume_tac
      \\ rw [] \\ gvs []
      >- (rename1 ‘MEM s (MAP _ ys)’
          \\ rpt $ last_x_assum $ qspec_then ‘s’ assume_tac \\ gvs [])
      >- (rename1 ‘MEM s (MAP _ ys)’
          \\ rpt $ last_x_assum $ qspec_then ‘s’ assume_tac \\ gvs [])
      \\ rw [DISJ_EQ_IMP] \\ gvs []
      \\ metis_tac [])
  \\ irule SUBSET_TRANS \\ metis_tac []
QED

Theorem lets_for_exp_rel:
  ∀vs e e2. thunk_Delay_Lam$exp_rel e e2 ⇒
            thunk_Delay_Lam$exp_rel (lets_for s n (MAPi (λi v. (i, v)) (MAP explode vs)) e)
                                    (lets_for s n (MAPi (λi v. (i, v)) (MAP explode vs)) e2)
Proof
  Induct using SNOC_INDUCT \\ simp [lets_for_def]
  \\ simp [MAP_APPEND, indexedListsTheory.MAPi_APPEND,
           SNOC_APPEND, lets_for_APPEND, lets_for_def]
  \\ rw [] \\ last_x_assum irule
  \\ gvs [exp_rel1_def]
QED

Theorem lets_for_boundvars_freevars:
  ∀l v n x s. freevars (lets_for v n (MAPi (λi v. (i, v)) l) x) ⊆ s
              ∧ boundvars (lets_for v n (MAPi (λi v. (i, v)) l) x) ⊆ s
              ⇒ freevars x ⊆ s ∧ boundvars x ⊆ s
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND]
  \\ rw []
  \\ last_x_assum $ dxrule_all_then assume_tac
  \\ gvs [freevars_def, boundvars_def, SUBSET_DEF]
  \\ rw [] \\ metis_tac []
QED

Theorem freevars_lets_for_subset:
  ∀l v n x. freevars (lets_for v n (MAPi (λi v. (i, v)) l) x) ⊆ freevars x ∪ {n}
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND]
  \\ rw []
  \\ irule SUBSET_TRANS \\ last_x_assum $ irule_at $ Pos hd
  \\ rw [freevars_def, SUBSET_DEF] \\ gvs []
QED

Theorem boundvars_lets_for:
  ∀l v n x. boundvars (lets_for v n (MAPi (λi v. (i, v)) l) x) = boundvars x ∪ (set l)
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND]
  \\ rw [boundvars_def, SET_EQ_SUBSET, SUBSET_DEF] \\ gvs []
QED

Theorem lets_for_bound_freevars:
  ∀l v n x s. freevars (lets_for v n (MAPi (λi v. (i, v)) l) x) ⊆ s
              ∧ boundvars (lets_for v n (MAPi (λi v. (i, v)) l) x) ⊆ s
              ⇒ freevars x ⊆ s
Proof
  rw [] \\ dxrule_all_then assume_tac lets_for_boundvars_freevars
  \\ gs []
QED

Theorem lets_for_free_boundvars:
  ∀l v n x s. freevars (lets_for v n (MAPi (λi v. (i, v)) l) x) ⊆ s
              ∧ boundvars (lets_for v n (MAPi (λi v. (i, v)) l) x) ⊆ s
              ⇒ boundvars x ⊆ s
Proof
  rw [] \\ dxrule_all_then assume_tac lets_for_boundvars_freevars
  \\ gs []
QED

Theorem in_freevars_or_boundvars_lets_for:
  ∀l v n x m. (m ∈ freevars x ∨ m ∈ boundvars x) ⇒
                m ∈ freevars (lets_for v n (MAPi (λi v. (i, v)) l) x)
                ∨ m ∈ boundvars (lets_for v n (MAPi (λi v. (i, v)) l) x)
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND]
  \\ rw [] \\ last_x_assum irule
  \\ gvs [freevars_def, boundvars_def]
QED

Theorem in_boundvars_lets_for:
  ∀l v n x m. m ∈ boundvars x ⇒
                m ∈ boundvars (lets_for v n (MAPi (λi v. (i, v)) l) x)
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND]
  \\ rw [] \\ last_x_assum irule
  \\ gvs [boundvars_def]
QED

Theorem in_boundvars_lets_for2:
  ∀l v n x m. MEM m l ⇒
                m ∈ boundvars (lets_for v n (MAPi (λi v. (i, v)) l) x)
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND]
  \\ rw []
  >~[‘MEM m _’]
  >- (last_x_assum irule
      \\ gvs [boundvars_def])
  >- (irule in_boundvars_lets_for
      \\ simp [boundvars_def])
QED

Theorem in_freevars_lets_for:
  ∀l v n x m. m ∈ freevars x ⇒
                m ∈ freevars (lets_for v n (MAPi (λi v. (i, v)) l) x)
                ∨ m ∈ boundvars (lets_for v n (MAPi (λi v. (i, v)) l) x)
Proof
  rw [] \\ irule in_freevars_or_boundvars_lets_for
  \\ simp []
QED

Theorem FOLDR_split_Delayed_Lam_LENGTH:
  ∀xs xs' vc vc' map.
    FOLDR (λe (l',vc). (λ(e',vc'). (e'::l',vc')) (split_Delayed_Lam e vc map))
          ([],vc) xs = (xs',vc')
    ⇒ LENGTH xs = LENGTH xs'
Proof
  Induct \\ gvs []
  \\ rw []
  \\ pairarg_tac \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ last_x_assum $ drule_then irule
QED

Theorem FOLDL_delete_ok:
  ∀m v. map_ok m
        ⇒ map_ok (FOLDL delete m vL)
          ∧ cmp_of (FOLDL delete m vL) = cmp_of m
Proof
  Induct_on ‘LENGTH vL’ >> rw [] >>
  rename1 ‘SUC _ = LENGTH vL’ >>
  qspec_then ‘vL’ assume_tac SNOC_CASES >> gvs [FOLDL_APPEND, delete_thm]
QED

Theorem FRANGE_FOLDL_delete:
  ∀vL map : (mlstring, mlstring) map.
    x ∈ FRANGE (to_fmap (FOLDL delete map vL)) ∧ map_ok map
    ⇒ x ∈ FRANGE (to_fmap map)
Proof
  Induct \\ rw [delete_thm]
  \\ last_x_assum $ dxrule_then assume_tac
  \\ gvs [delete_thm]
  \\ rename1 ‘to_fmap map2 \\ h’
  \\ qspecl_then [‘h’, ‘to_fmap map2’] assume_tac $ GEN_ALL FRANGE_DOMSUB_SUBSET
  \\ gvs [SUBSET_DEF]
QED

Theorem FDOM_FOLDL_delete:
  ∀vL map : (mlstring, mlstring) map.
    map_ok map
    ⇒ ∀x. (x ∈ FDOM (to_fmap (FOLDL delete map vL))
       ⇔ x ∈ FDOM (to_fmap map) ∧ ¬MEM x vL)
Proof
  Induct \\ rw [delete_thm]
  \\ last_x_assum $ dxrule_then assume_tac
  \\ simp [CONJ_ASSOC]
QED

Theorem FOLDL_delete_thm:
  ∀vL map.
      map_ok map ∧ ¬MEM v vL ⇒
      to_fmap (FOLDL delete map vL) ' v = to_fmap map ' v
Proof
  Induct \\ gvs []
  \\ rw [] \\ irule EQ_TRANS
  \\ last_x_assum $ irule_at $ Pos hd
  \\ gvs [delete_thm, DOMSUB_FAPPLY_NEQ]
QED

Theorem full_exp_rel_lets_for:
  ∀l n1 n2 x y. full_exp_rel x y
                ⇒ full_exp_rel (lets_for n1 n2 l x) (lets_for n1 n2 l y)
Proof
  Induct \\ gvs [lets_for_def, FORALL_PROD]
  \\ rw [] \\ irule full_exp_rel_Let
  \\ last_x_assum $ drule_then $ irule_at Any
  \\ gvs [full_exp_rel_def]
QED

Theorem split_Delay_Lam_soundness_rows:
  ∀rows. (∀e vc'' map map_l' e_out' vc_out.
         MEM e (MAP (SND o SND) rows) ⇒
         split_Delayed_Lam e vc'' map = (e_out',vc_out) ∧
          ALL_DISTINCT map_l' ∧ freevars (exp_of e) ⊆ vc_to_set vc'' ∧
          boundvars (exp_of e) ⊆ vc_to_set vc'' ∧
          IMAGE explode (set map_l') ⊆ vc_to_set vc'' ∧
          IMAGE explode (FRANGE (to_fmap map)) ⊆ vc_to_set vc'' ∧ cexp_wf e ∧
          DISJOINT (set map_l') (FRANGE (to_fmap map)) ∧
          DISJOINT (freevars (exp_of e))
            (IMAGE explode (FRANGE (to_fmap map))) ∧
          DISJOINT (boundvars (exp_of e))
            (IMAGE explode (FRANGE (to_fmap map))) ∧ map_ok map ∧
          cmp_of map = compare ∧ var_creator_ok vc'' ∧
          FDOM (to_fmap map) = set map_l' ⇒
          ∃e2 e3.
            vc_to_set vc'' ⊆ vc_to_set vc_out ∧ var_creator_ok vc_out ∧
            freevars (exp_of e_out') ⊆ vc_to_set vc_out ∧
            boundvars (exp_of e_out') ⊆ vc_to_set vc_out ∧
            boundvars e2 ∩ COMPL (boundvars (exp_of e)) =
            vc_to_set vc_out ∩ COMPL (vc_to_set vc'') ∧
            thunk_Delay_Lam$exp_rel (exp_of e) e2 ∧ full_exp_rel e2 e3 ∧
            cexp_wf e_out' ∧
            exp_of e_out' =
            FOLDL
              (λe v.
                   replace_Force (Var (explode (to_fmap map ' v)))
                     (explode v) e) e3 map_l') ⇒
       ∀m vc1 vc2 list1 map map_l.
         FOLDR
         (λ(v,vL,expr) (l',vc').
            (λ(expr',vc''). ((v,vL,expr')::l',vc''))
            (split_Delayed_Lam expr vc'
             (FOLDL delete (delete map m) vL))) ([],vc1) rows = (list1,vc2) ∧
         var_creator_ok vc1 ∧ map_ok map ∧ cmp_of map = compare ∧
         EVERY cexp_wf (MAP (SND o SND) rows) ∧
         var_creator_ok vc1 ∧
         DISJOINT (boundvars (rows_of (explode m)
                              (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) rows)))
                  (IMAGE explode (FRANGE (to_fmap map))) ∧
         DISJOINT (freevars (rows_of (explode m)
                             (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) rows)) DIFF
                   {explode m}) (IMAGE explode (FRANGE (to_fmap map))) ∧
         DISJOINT (set map_l) (FRANGE (to_fmap map)) ∧
         m ∉ FRANGE (to_fmap map) ∧
         EVERY (λa. cexp_wf a) (MAP (SND ∘ SND) rows) ∧
         IMAGE explode (set map_l) ⊆ vc_to_set vc1 ∧
         IMAGE explode (FRANGE (to_fmap map)) ⊆ vc_to_set vc1 ∧
         boundvars (rows_of (explode m)
                    (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) rows))
                   ⊆ vc_to_set vc1 ∧
         freevars (rows_of (explode m)
                   (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) rows))
                  ⊆ vc_to_set vc1 ∧
         ALL_DISTINCT map_l ∧
         FDOM (to_fmap map) = set map_l
         ⇒
         ∃x y.
           thunk_Delay_Lam$exp_rel (rows_of (explode m)
                                    (MAP (λ(c, vs, x). (explode c, MAP explode vs, exp_of x))
                                     rows)) x ∧
           full_exp_rel x y ∧
           vc_to_set vc1 ⊆ vc_to_set vc2 ∧ var_creator_ok vc2 ∧
           EVERY cexp_wf (MAP (SND o SND) list1) ∧
           rows_of (explode m) (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) list1)
           = FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e)
                   y (FILTER (λv. v ≠ m) map_l) ∧
           freevars (rows_of (explode m)
                     (MAP (λ(c, vs, x). (explode c, MAP explode vs, exp_of x)) rows))
                    ⊆ vc_to_set vc2 ∧
           boundvars (rows_of (explode m)
                     (MAP (λ(c, vs, x). (explode c, MAP explode vs, exp_of x)) rows))
                    ⊆ vc_to_set vc2 ∧
           freevars (rows_of (explode m)
                     (MAP (λ(c, vs, x). (explode c, MAP explode vs, exp_of x)) list1))
                    ⊆ vc_to_set vc2 ∧
           boundvars (rows_of (explode m)
                     (MAP (λ(c, vs, x). (explode c, MAP explode vs, exp_of x)) list1))
                    ⊆ vc_to_set vc2 ∧
           boundvars x ∩ COMPL (boundvars (rows_of (explode m)
                        (MAP (λ(c, vs, x). (explode c, MAP explode vs, exp_of x)) rows)))
           =  vc_to_set vc2 ∩ COMPL (vc_to_set vc1)
Proof
  Induct \\ rw [PULL_EXISTS, rows_of_def]
  >- simp [exp_rel1_def, exp_rel2_def, FOLDL_replace_Force_Prim]
  \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gvs []
  \\ gvs [rows_of_def, freevars_def, boundvars_def, exp_rel1_def, exp_rel2_def, PULL_EXISTS]
  \\ irule_at Any lets_for_exp_rel
  \\ rename1 ‘exp_rel (exp_of x) _’
  \\ last_x_assum $ qspec_then ‘x’ assume_tac \\ fs []
  \\ last_x_assum $ dxrule_then $ qspec_then ‘map_l’ mp_tac
  \\ impl_tac >- (simp [] \\ gvs [DISJOINT_ALT, SF DNF_ss])
  \\ disch_then $ qx_choose_then ‘x2’ $ qx_choose_then ‘y2’ assume_tac \\ fs []
  \\ qpat_x_assum ‘exp_rel_ _’ $ irule_at $ Pos $ el 2
  \\ first_x_assum $ dxrule_then mp_tac \\ simp []
  \\ disch_then $ qspec_then ‘FILTER (λv. ¬MEM v vs ∧ v ≠ m) map_l’ mp_tac
  \\ impl_tac \\ simp []
  >- (conj_tac
      >- gvs [FILTER_ALL_DISTINCT]
      \\ conj_tac
      >- (irule SUBSET_TRANS
          \\ qpat_x_assum ‘vc_to_set _ ⊆ vc_to_set _’ $ irule_at Any
          \\ irule lets_for_bound_freevars
          \\ first_x_assum $ irule_at Any \\ simp [])
      \\ conj_tac
      >- (irule SUBSET_TRANS
          \\ qpat_x_assum ‘vc_to_set _ ⊆ vc_to_set _’ $ irule_at Any
          \\ irule lets_for_free_boundvars
          \\ first_x_assum $ irule_at Any \\ simp [])
      \\ conj_asm1_tac
      >- (irule SUBSET_TRANS \\ irule_at Any IMAGE_SUBSET
          \\ irule_at (Pos last) SUBSET_TRANS
          \\ qpat_x_assum ‘vc_to_set _ ⊆ vc_to_set _’ $ irule_at Any
          \\ qexists_tac ‘set map_l’
          \\ simp [SUBSET_DEF, MEM_FILTER])
      \\ conj_asm1_tac
      >- (irule_at (Pos last) SUBSET_TRANS
          \\ qpat_x_assum ‘vc_to_set _ ⊆ vc_to_set _’ $ irule_at Any
          \\ rw [SUBSET_DEF]
          \\ dxrule_then assume_tac FRANGE_FOLDL_delete
          \\ gvs [delete_thm, SUBSET_DEF, PULL_EXISTS]
          \\ qpat_x_assum ‘∀x. _ ∈ FRANGE _ ⇒ _’ irule
          \\ rename1 ‘to_fmap map' \\ m’
          \\ qspecl_then [‘m’, ‘to_fmap map'’] assume_tac $ GEN_ALL FRANGE_DOMSUB_SUBSET
          \\ gvs [SUBSET_DEF])
      \\ conj_tac
      >- (gvs [DISJOINT_ALT, MEM_FILTER]
          \\ gen_tac \\ rename1 ‘¬MEM x' _’
          \\ strip_tac \\ strip_tac
          \\ dxrule_then assume_tac FRANGE_FOLDL_delete
          \\ gvs [delete_thm]
          \\ rename1 ‘to_fmap map' \\ m’
          \\ qspecl_then [‘m’, ‘to_fmap map'’] assume_tac $ GEN_ALL FRANGE_DOMSUB_SUBSET
          \\ gvs [SUBSET_DEF]
          \\ first_x_assum $ dxrule_then assume_tac
          \\ first_x_assum $ dxrule_then assume_tac
          \\ rpt $ first_x_assum $ qspec_then ‘x'’ assume_tac \\ gvs [])
      \\ conj_tac
      >- (dxrule_all_then assume_tac lets_for_bound_freevars
          \\ gvs [DISJOINT_ALT, PULL_FORALL, SUBSET_DEF]
          \\ gen_tac \\ rename1 ‘explode xbis ∈ freevars (exp_of x)’
          \\ rpt $ first_x_assum $ qspec_then ‘xbis’ assume_tac
          \\ rpt $ first_x_assum $ qspec_then ‘explode xbis’ assume_tac
          \\ strip_tac \\ strip_tac
          \\ dxrule_then assume_tac FRANGE_FOLDL_delete
          \\ gvs [delete_thm]
          \\ rename1 ‘to_fmap map' \\ m’
          \\ qspecl_then [‘m’, ‘to_fmap map'’] assume_tac $ GEN_ALL FRANGE_DOMSUB_SUBSET
          \\ gvs [SUBSET_DEF]
          >- (rpt $ first_x_assum $ qspec_then ‘xbis’ assume_tac \\ gvs []
              \\ dxrule_then (qspecl_then [‘MAP explode vs’, ‘explode c’, ‘explode m’]
                              assume_tac) in_freevars_lets_for \\ gvs [])
          \\ rpt $ first_x_assum $ qspec_then ‘m’ assume_tac \\ gvs [])
      \\ conj_tac
      >- (gvs [DISJOINT_ALT]
          \\ gen_tac \\ rename1 ‘var ∈ boundvars _ ⇒ _’
          \\ last_x_assum $ qspec_then ‘var’ assume_tac
          \\ gvs [PULL_FORALL]
          \\ gen_tac \\ rename1 ‘_ ⇒ var = explode var_in ⇒ _’
          \\ pop_assum $ qspec_then ‘var_in’ assume_tac
          \\ rw [] \\ strip_tac \\ gs []
          \\ dxrule_then assume_tac FRANGE_FOLDL_delete
          \\ gvs [delete_thm, in_boundvars_lets_for]
          \\ first_x_assum irule
          \\ metis_tac [FRANGE_DOMSUB_SUBSET, SUBSET_DEF])
      \\ rename1 ‘map_ok (FOLDL delete (delete map' m) vs)’
      \\ qspecl_then [‘vs’, ‘delete map' m’] assume_tac $ GEN_ALL FOLDL_delete_ok
      \\ gvs [delete_thm, SET_EQ_SUBSET, SUBSET_DEF, MEM_FILTER]
      \\ qspecl_then [‘vs’, ‘delete map' m’] assume_tac $ GEN_ALL FDOM_FOLDL_delete
      \\ gvs [delete_thm, PULL_EXISTS])
  \\ rw []
  \\ qpat_x_assum ‘thunk_Delay_Lam$exp_rel _ _’ $ irule_at $ Pos hd
  \\ qpat_x_assum ‘full_exp_rel _ _’ $ irule_at $ Pos $ el 2
  \\ simp []
  \\ irule_at (Pos hd) full_exp_rel_lets_for
  \\ first_x_assum $ irule_at $ Pos hd
  \\ rpt $ conj_tac
  >- (irule SUBSET_TRANS \\ metis_tac [])
  >- (simp [FOLDL_replace_Force_If, FOLDL_replace_Force_IsEq,
            FOLDL_replace_Force_Var, FOLDL_replace_Force_lets_for]
      \\ AP_TERM_TAC
      \\ irule FOLDL_replace_Force_change_map
      \\ simp [MEM_FILTER, delete_thm]
      \\ rw [] \\ irule EQ_TRANS \\ irule_at (Pos hd) FOLDL_delete_thm
      \\ simp [delete_thm, DOMSUB_FAPPLY_NEQ])
  >- gvs [SUBSET_DEF]
  >- (irule SUBSET_TRANS \\ irule_at Any SUBSET_TRANS \\ metis_tac [])
  >- (irule SUBSET_TRANS \\ irule_at Any SUBSET_TRANS \\ metis_tac [])
  >- (irule SUBSET_TRANS \\ irule_at Any SUBSET_TRANS \\ metis_tac [])
  >- gvs [SUBSET_DEF]
  >- (irule SUBSET_TRANS
      \\ irule_at (Pos hd) freevars_lets_for_subset
      \\ gvs [SUBSET_DEF])
  >- (irule SUBSET_TRANS \\ metis_tac [])
  >- (simp [boundvars_lets_for]
      \\ gvs [SUBSET_DEF]
      \\ gen_tac \\ rename1 ‘MEM var (MAP _ _) ⇒ var ∈ _’
      \\ rpt $ first_x_assum $ qspec_then ‘var’ assume_tac
      \\ strip_tac
      \\ qpat_x_assum ‘_ ∈ vc_to_set _ ⇒ _ ∈ vc_to_set _’ irule
      \\ qpat_x_assum ‘_ ∈ vc_to_set _ ⇒ _ ∈ vc_to_set _’ irule
      \\ qpat_x_assum ‘_ ∈ boundvars (lets_for _ _ _ _) ⇒ _’ irule
      \\ irule in_boundvars_lets_for2
      \\ simp [])
  >- (irule SUBSET_TRANS \\ metis_tac [])

  >- (gvs [SET_EQ_SUBSET, SUBSET_DEF, boundvars_lets_for]
      \\ rpt $ conj_tac \\ gen_tac
      >- (rename1 ‘_⇒ var ∈ vc_to_set _’
          \\ rpt $ first_x_assum $ qspec_then ‘var’ assume_tac
          \\ rw [] \\ gvs [])
      >- (rename1 ‘_⇒ var ∉ vc_to_set _’
          \\ rpt $ first_x_assum $ qspec_then ‘var’ assume_tac
          \\ rw [] \\ gvs [])
      >- (rename1 ‘_ ∧ var ∉ vc_to_set _ ⇒ _’
          \\ rpt $ first_x_assum $ qspec_then ‘var’ assume_tac
          \\ rw [] \\ gvs []
          \\ Cases_on ‘var ∈ vc_to_set vc'’ \\ gvs [])
      >- (rename1 ‘_ ∧ var ∉ vc_to_set _ ⇒ _’
          \\ rpt $ first_x_assum $ qspec_then ‘var’ assume_tac
          \\ rw [] \\ gvs []))
QED

Theorem boundvars_FOLDL_replace_Force:
  ∀map_l e map.
    boundvars (FOLDL
               (λe v. replace_Force (Var (explode (to_fmap map ' v)))
                                    (explode v) e) e map_l) = boundvars e
Proof
  Induct \\ gvs [] \\ rw[SET_EQ_SUBSET, SUBSET_DEF]
  >- (assume_tac boundvars_replace_Force
      \\ gvs [SUBSET_DEF]
      \\ pop_assum $ dxrule_then assume_tac
      \\ gvs [boundvars_def])
  >- (assume_tac boundvars_replace_Force2
      \\ gvs [SUBSET_DEF])
QED

Theorem GENLIST_K_T:
  ∀l. GENLIST (K T) (SUC l) = T::GENLIST (K T) l
Proof
  Induct \\ gvs [GENLIST]
QED

Theorem letrec_split_soundness:
  ∀binds binds2 vc vc2 map map2 s.
    letrec_split binds vc map = (binds2, vc2, map2) ∧ map_ok map ∧
    EVERY (cexp_wf o SND) binds ∧ var_creator_ok vc ∧ FINITE s ∧
    DISJOINT (vc_to_set vc2) s
    ⇒ ∃vL. LENGTH binds = LENGTH vL ∧ ALL_DISTINCT vL ∧
           EVERY (λv. v ∉ s ∧ v ∉ vc_to_set vc) vL ∧
           MAP (λ(v,e). (explode v, exp_of e)) binds2
           = FLAT (MAP2 (λ(v1, e) (v2, b).
                           case e of
                           | Delay e2 =>
                               if is_Lam e2 ∧ b
                               then [(v2, e2); (v1, Delay (Var v2))]
                               else [(v1, e)]
                           | _ => [(v1, e)])
                   (MAP (λ(v,e). (explode v, exp_of e)) binds)
                   (ZIP (vL, GENLIST (K T) (LENGTH binds)))) ∧
           var_creator_ok vc2 ∧
           vc_to_set vc ⊆ vc_to_set vc2
Proof
  Induct \\ gvs [letrec_split_def, FORALL_PROD, GENLIST_K_T]
  \\ rpt $ gen_tac \\ CASE_TAC \\ rw []
  >- (pairarg_tac \\ gs []
      \\ last_x_assum $ drule_then mp_tac
      \\ simp [delete_thm]
      \\ disch_then $ drule_then $ drule_then $ qx_choose_then ‘vL’ assume_tac
      \\ Q.REFINE_EXISTS_TAC ‘_::vL’ \\ gvs []
      \\ rename1 ‘FINITE s’
      \\ ‘∃v. ¬MEM v vL ∧ v ∉ s ∧ v ∉ vc_to_set vc’
        by  (‘INFINITE 𝕌(:string)’ by simp []
             \\ dxrule_then assume_tac $ iffLR NOT_IN_FINITE
             \\ pop_assum $ qspec_then ‘set vL ∪ s ∪ vc_to_set vc’ assume_tac
             \\ gvs [GSYM CONJ_ASSOC]
             \\ pop_assum irule
             \\ gvs [vc_to_set_def])
      \\ first_x_assum $ irule_at Any
      \\ rename1 ‘dest_Delay_Lam p2 = NONE’
      \\ Cases_on ‘p2’ \\ gvs [dest_Delay_Lam_def, exp_of_def, cexp_wf_def]
      >~[‘Prim op l’]
      >- (Cases_on ‘op’ \\ simp [exp_of_def]
          \\ Cases_on ‘l’ \\ simp [exp_of_def]
          \\ rename1 ‘Prim Seq (h::l)’ \\ Cases_on ‘l’ \\ simp [exp_of_def]
          \\ rename1 ‘Prim Seq (h::g::l)’ \\ Cases_on ‘l’ \\ simp [exp_of_def])
      >~[‘Apps _ (MAP _ l)’]
      >- (qspec_then ‘l’ assume_tac SNOC_CASES
          \\ gvs [FOLDL_APPEND, exp_of_def, cexp_wf_def])
      >~[‘Lams (MAP _ l) _’]
      >- (Cases_on ‘l’ \\ gvs [cexp_wf_def])
      \\ rename1 ‘dest_Delay_Lam (Delay e) = NONE’
      \\ Cases_on ‘e’ \\ gvs [dest_Delay_Lam_def, is_Lam_def, exp_of_def, cexp_wf_def]
      >~[‘Prim op l’]
      >- (Cases_on ‘op’ \\ simp [exp_of_def]
          \\ Cases_on ‘l’ \\ simp [exp_of_def]
          \\ rename1 ‘Prim Seq (h::l)’ \\ Cases_on ‘l’ \\ simp [exp_of_def]
          \\ rename1 ‘Prim Seq (h::g::l)’ \\ Cases_on ‘l’ \\ simp [exp_of_def])
      >~[‘Apps _ (MAP _ l)’]
      >- (qspec_then ‘l’ assume_tac SNOC_CASES
          \\ gvs [FOLDL_APPEND, exp_of_def, cexp_wf_def]))
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ last_x_assum $ drule_then assume_tac
  \\ gs [insert_thm]
  \\ dxrule_then assume_tac new_var_soundness \\ gs []
  \\ first_x_assum $ drule_then $ drule_then $ qx_choose_then ‘vL’ assume_tac
  \\ qexists_tac ‘explode name2::vL’ \\ simp []
  \\ gvs [DISJOINT_ALT, EVERY_CONJ]
  \\ rpt $ conj_tac
  >- gvs [EVERY_MEM]
  \\ rename1 ‘dest_Delay_Lam p_2 = SOME _’
  \\ Cases_on ‘p_2’ \\ gvs [dest_Delay_Lam_def, exp_of_def]
  \\ rename1 ‘dest_Delay_Lam (Delay e) = SOME _’
  \\ Cases_on ‘e’ \\ gvs [dest_Delay_Lam_def, Lams_split, cexp_wf_def, is_Lam_def, exp_of_def]
QED

Theorem UNION_INTER:
  ∀A B C. (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C)
Proof
  gvs [SET_EQ_SUBSET, SUBSET_DEF]
QED

Theorem split_Delay_Lam_soundness_lemma:
  ∀vc map map_l e_out vc_out.
    split_Delayed_Lam e vc map = (e_out, vc_out) ∧
    ALL_DISTINCT map_l ∧
    freevars  (exp_of e) ⊆ vc_to_set vc ∧
    boundvars (exp_of e) ⊆ vc_to_set vc ∧
    IMAGE explode (set map_l) ⊆ vc_to_set vc ∧
    IMAGE explode (FRANGE (to_fmap map)) ⊆ vc_to_set vc ∧
    cexp_wf e ∧
    DISJOINT (set map_l) (FRANGE (to_fmap map)) ∧
    DISJOINT (freevars (exp_of e)) (IMAGE explode (FRANGE (to_fmap map))) ∧
    DISJOINT (boundvars (exp_of e)) (IMAGE explode (FRANGE (to_fmap map))) ∧
    map_ok map ∧ cmp_of map = compare ∧ var_creator_ok vc ∧
    FDOM (to_fmap map) = set map_l ⇒
    ∃e2 e3.
      vc_to_set vc ⊆ vc_to_set vc_out ∧ var_creator_ok vc_out ∧
      freevars  (exp_of e_out) ⊆ vc_to_set vc_out ∧
      boundvars (exp_of e_out) ⊆ vc_to_set vc_out ∧
      (boundvars e2) ∩ (COMPL (boundvars (exp_of e))) = vc_to_set vc_out ∩ COMPL (vc_to_set vc) ∧
      thunk_Delay_Lam$exp_rel (exp_of e) e2 ∧
      thunk_Let_Delay_Var$full_exp_rel e2 e3 ∧
      cexp_wf e_out ∧
      exp_of e_out
      = (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) e3 map_l)
Proof

  completeInduct_on ‘cexp_size e’
  \\ Cases \\ strip_tac
  \\ gvs [split_Delayed_Lam_def, exp_of_def, freevars_def, boundvars_def, cexp_wf_def]
  >~[‘Var _’]
  >- (rw [] \\ gvs [FOLDL_replace_Force_Var, exp_rel1_def, exp_rel2_def, boundvars_def])
  >~[‘dest_Delay_Lam e1’]
  >- (CASE_TAC
      >~[‘dest_Delay_Lam _ = SOME _’]
      >- (rw []
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ dxrule_then assume_tac new_var_soundness \\ gs [PULL_FORALL]
          \\ rename1 ‘Let m e1 e2’
          \\ Cases_on ‘e1’ \\ gs [dest_Delay_Lam_def, exp_of_def]
          \\ rename1 ‘dest_Delay_Lam (Delay e1)’ \\ Cases_on ‘e1’ \\ gvs [dest_Delay_Lam_def]
          \\ rename1 ‘Lam vL e1’
          \\ last_assum $ qspec_then ‘e2’ mp_tac
          \\ last_x_assum $ qspec_then ‘Lam vL e1’ mp_tac
          \\ simp [cexp_size_def]
          \\ disch_then $ drule_then $ drule_then mp_tac
          \\ gvs [SUBSET_DEF, freevars_def, boundvars_def, cexp_wf_def]
          \\ disch_then $ qx_choose_then ‘e1_mid’ assume_tac
          \\ rename1 ‘insert map2 name name2’ \\ rename1 ‘set map_l’
          \\ disch_then $ drule_then $ qspec_then ‘name::(FILTER (λv. v ≠ name) map_l)’ mp_tac
          \\ impl_tac
          >- (rw [] \\ gvs [PULL_EXISTS, MEM_FILTER, FILTER_ALL_DISTINCT]
              >- (rename1 ‘x ∈ freevars _’
                  \\ rpt $ first_x_assum $ qspec_then ‘x’ assume_tac \\ gvs []
                  \\ Cases_on ‘x = explode name’ \\ gvs [])
              >- (gvs [insert_thm, IN_FRANGE, PULL_EXISTS, FAPPLY_FUPDATE_THM]
                  \\ IF_CASES_TAC \\ gvs [])
              >- (gvs [DISJOINT_ALT, MEM_FILTER, insert_thm, IN_FRANGE, PULL_EXISTS,
                       FAPPLY_FUPDATE_THM]
                  \\ rw [] \\ strip_tac \\ gvs [PULL_FORALL]
                  \\ rename1 ‘k = name’ \\ Cases_on ‘k = name’ \\ gvs [])
              >- (gvs [insert_thm, IN_FRANGE, PULL_EXISTS, FAPPLY_FUPDATE_THM]
                  \\ gen_tac \\ IF_CASES_TAC \\ gvs []
                  \\ strip_tac \\ gvs [])
              >- (gvs [DISJOINT_ALT, MEM_FILTER, insert_thm, IN_FRANGE, PULL_EXISTS,
                       FAPPLY_FUPDATE_THM]
                  \\ rw [] \\ strip_tac \\ gvs [PULL_FORALL]
                  >- (last_x_assum $ dxrule_then assume_tac
                      \\ rename1 ‘explode name2 ≠ explode k ⇒ _’
                      \\ Cases_on ‘name2 = k’ \\ gvs [])
                  \\ rename1 ‘k = name’ \\ Cases_on ‘k = name’ \\ gvs []
                  >- (last_x_assum $ drule_then assume_tac
                      \\ rename1 ‘explode name2 ≠ explode k ⇒ _’
                      \\ Cases_on ‘name2 = k’ \\ gvs [])
                  \\ first_x_assum $ drule_then assume_tac \\ gs [])
              >- (gvs [DISJOINT_ALT, MEM_FILTER, insert_thm, IN_FRANGE, PULL_EXISTS,
                       FAPPLY_FUPDATE_THM]
                  \\ rw [] \\ strip_tac \\ gvs [PULL_FORALL]
                  \\ rename1 ‘k = name’ \\ Cases_on ‘k = name’ \\ gvs [])
              >- gvs [insert_thm]
              >- (rw [SET_EQ_SUBSET, SUBSET_DEF, insert_thm, MEM_FILTER]
                  \\ gs []))
          \\ disch_then $ qx_choose_then ‘e2_mid’ assume_tac
          \\ gvs [FOLDL_replace_Force_Let, FOLDL_replace_Force_Delay]
          \\ irule_at Any thunk_Delay_LamTheory.exp_rel_Let_Delay_Lam
          \\ gvs [exp_of_def, FOLDL_replace_Force_Lams, PULL_EXISTS]
          \\ first_assum $ irule_at $ Pos $ el 2
          \\ first_assum $ irule_at $ Pos $ el 2
          \\ irule_at Any full_exp_rel_Let_Delay_Var
          \\ first_assum $ irule_at $ Pos $ el 3
          \\ first_assum $ irule_at $ Pos $ el 3
          \\ simp [exp_rel2_def]
          \\ qexists_tac ‘explode name2’ \\ rw []
          >- (dxrule_then assume_tac  thunk_Delay_LamTheory.exp_rel_freevars
              \\ strip_tac
              \\ rpt $ first_x_assum $ qspec_then ‘explode name2’ assume_tac
              \\ Cases_on ‘name = name2’ \\ gvs [])
          >- (gs [SET_EQ_SUBSET, SUBSET_DEF]
              \\ rpt $ first_x_assum $ qspec_then ‘explode name2’ assume_tac
              \\ gvs [])
          >- simp [is_Lam_def, Lams_split]
          >- (strip_tac \\ last_x_assum $ drule_then assume_tac
              \\ Cases_on ‘name2 = name’ \\ gvs [])
          >- (strip_tac \\ gvs [])
          >- gvs [freevars_def]
          >- gvs [boundvars_def]
          >- (gvs [boundvars_def, boundvars_Lams, SET_EQ_SUBSET, SUBSET_DEF, DISJ_IMP_THM]
              \\ rw [] \\ gvs []
              >- (rename1 ‘x ∉ vc_to_set _’
                  \\ rpt $ last_x_assum $ qspec_then ‘x’ assume_tac
                  \\ gvs [])
              >- (rw [DISJ_EQ_IMP]
                  \\ rename1 ‘x = explode _’
                  \\ rpt $ last_x_assum $ qspec_then ‘x’ assume_tac
                  \\ gvs [])
              >- (rename1 ‘x ∉ vc_to_set _’
                  \\ rpt $ last_x_assum $ qspec_then ‘x’ assume_tac
                  \\ gvs [])
              >- (rename1 ‘x ∉ vc_to_set _’
                  \\ rpt $ last_x_assum $ qspec_then ‘x’ assume_tac
                  \\ gvs [])
              >- (rename1 ‘x ∉ vc_to_set _’
                  \\ rpt $ last_x_assum $ qspec_then ‘x’ assume_tac
                  \\ gvs [])
              >- (strip_tac \\ gvs []))
          \\ gvs [FOLDL_replace_Force_Let, FOLDL_replace_Force_Delay, FOLDL_replace_Force_Var]
          \\ ‘EVERY (λv. v ≠ name2) map_l’
            by (gvs [EVERY_MEM] \\ strip_tac
                \\ last_x_assum $ drule_then assume_tac
                \\ gs [])
          \\ dxrule_then assume_tac $ iffRL FILTER_EQ_ID \\ simp []
          \\ ‘to_fmap (insert map2 name name2) ' name = name2’ by simp [insert_thm]
          \\ simp []
          \\ irule FOLDL_replace_Force_change_map
          \\ gvs [insert_thm, MEM_FILTER, FAPPLY_FUPDATE_THM])
      \\ rw []
      \\ pairarg_tac \\ fs [] \\ pairarg_tac
      \\ gvs [exp_of_def, freevars_def, boundvars_def, PULL_FORALL, cexp_size_def]
      \\ rename1 ‘Let (SOME (explode m)) (exp_of e1) (exp_of e2)’
      \\ last_assum $ qspec_then ‘e2’ mp_tac
      \\ last_x_assum $ qspec_then ‘e1’ assume_tac
      \\ gvs []
      \\ pop_assum $ drule_all_then $ qx_choose_then ‘e1_mid’ assume_tac
      \\ rename1 ‘set map_l’
      \\ disch_then $ drule_then $ qspec_then ‘FILTER (λv. v ≠ m) map_l’ mp_tac
      \\ impl_tac
      >- (gvs [FILTER_ALL_DISTINCT, SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
          \\ rw []
          >- metis_tac []
          >- metis_tac [MEM_FILTER]
          >- (rename1 ‘explode x2 ∈ _’
              \\ qspecl_then [‘x2’, ‘[m]’] assume_tac $ GEN_ALL FRANGE_FOLDL_delete
              \\ fs []
              \\ pop_assum $ drule_then assume_tac
              \\ gvs [])
          >- (gvs [DISJOINT_ALT, MEM_FILTER, delete_thm]
              \\ rw []
              \\ qpat_x_assum ‘∀x. MEM _ _ ⇒ _ ∉ FRANGE _’ $ drule_then assume_tac
              \\ strip_tac
              \\ rename1 ‘to_fmap map2 \\ m’
              \\ qspecl_then [‘m’, ‘to_fmap map2’] assume_tac $ GEN_ALL FRANGE_DOMSUB_SUBSET
              \\ gvs [SUBSET_DEF])
          >- (gvs [DISJOINT_ALT, IN_FRANGE, delete_thm, PULL_FORALL]
              \\ rw []
              \\ rename1 ‘(to_fmap map2 \\ m) ' k’
              \\ Cases_on ‘k = m’ \\ gs [DOMSUB_FAPPLY_NEQ]
              \\ Cases_on ‘to_fmap map2 ' k = m’ \\ gvs [])
          >- (gvs [DISJOINT_ALT, IN_FRANGE, delete_thm, PULL_FORALL]
              \\ rw []
              \\ rename1 ‘(to_fmap map2 \\ m) ' k’
              \\ Cases_on ‘k = m’ \\ gs [DOMSUB_FAPPLY_NEQ]
              \\ Cases_on ‘to_fmap map2 ' k = m’ \\ gvs [])
          >- simp [delete_thm]
          >- gvs [MEM_FILTER, delete_thm]
          >- gvs [MEM_FILTER, delete_thm])
      \\ disch_then $ qx_choose_then ‘e2_mid’ assume_tac
      \\ irule_at Any full_exp_rel_Let \\ fs [cexp_wf_def]
      \\ irule_at Any thunk_Delay_LamTheory.exp_rel_Let
      \\ first_x_assum $ irule_at $ Pos hd
      \\ first_x_assum $ irule_at $ Pos hd
      \\ first_x_assum $ irule_at $ Pos hd
      \\ first_x_assum $ irule_at $ Pos hd
      \\ simp [FOLDL_replace_Force_Let]
      \\ gvs [SUBSET_DEF]
      \\ rename1 ‘delete map2 m’ \\ rename1 ‘set map_l’
      \\ rename1 ‘FOLDL _ e3b _’
      \\ conj_tac
      >- (gvs [boundvars_def, SET_EQ_SUBSET, SUBSET_DEF]
          \\ rpt $ conj_tac \\ gen_tac \\ rename1 ‘x ∉ _’
          \\ rpt $ last_x_assum $ qspec_then ‘x’ assume_tac
          \\ rw [] \\ gvs []
          >- (rw [DISJ_EQ_IMP] \\ gvs [])
          \\ strip_tac \\ gvs [])
      \\ qspecl_then [‘FILTER (λv. v ≠ m) map_l’,
                      ‘e3b’, ‘to_fmap map2’,
                      ‘to_fmap (delete map2 m)’] mp_tac FOLDL_replace_Force_change_map
      \\ impl_tac \\ simp [] \\ simp [MEM_FILTER, delete_thm]
      \\ rw [DOMSUB_FAPPLY_NEQ])
  >~[‘Prim op xs’]
  >- (Cases_on ‘op’
      >~[‘Seq’]
      >- (Cases_on ‘xs’ \\ gvs [args_ok_def]
          \\ rename1 ‘LENGTH t = 1’ \\ Cases_on ‘t’ \\ rw []
          \\ rename1 ‘Prim Seq [x1; x2]’
          \\ gvs [exp_of_def, freevars_def, boundvars_def, split_Delayed_Lam_def,
                  cexp_size_def, PULL_FORALL]
          \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gvs [] \\ pairarg_tac \\ gvs []
          \\ last_assum $ qspec_then ‘x2’ assume_tac \\ fs []
          \\ pop_assum $ drule_all_then $ qx_choose_then ‘x2_mid’ assume_tac
          \\ last_x_assum $ qspec_then ‘x1’ assume_tac \\ gs []
          \\ pop_assum $ drule_then $ drule_then mp_tac \\ impl_tac
          >- (simp [] \\ rpt $ conj_tac \\ irule_at Any SUBSET_TRANS \\ metis_tac [])
          \\ disch_then $ qx_choose_then ‘x1_mid’ assume_tac
          \\ gvs [exp_of_def, freevars_def, boundvars_def, cexp_wf_def,
                  args_ok_def, FOLDL_replace_Force_Seq]
          \\ irule_at Any thunk_Delay_LamTheory.exp_rel_Let
          \\ first_x_assum $ irule_at $ Pos hd
          \\ first_x_assum $ irule_at $ Pos hd
          \\ gvs [exp_rel2_def, FOLDL_replace_Force_Seq, PULL_EXISTS]
          \\ qpat_x_assum ‘full_exp_rel _ _’ $ irule_at Any
          \\ qpat_x_assum ‘full_exp_rel _ _’ $ irule_at Any
          \\ rw []
          >- (irule SUBSET_TRANS \\ metis_tac [])
          >- (irule SUBSET_TRANS \\ metis_tac [])
          >- (irule SUBSET_TRANS \\ metis_tac [])
          \\ gvs [boundvars_def, SET_EQ_SUBSET, SUBSET_DEF]
          \\ rpt $ conj_tac \\ gen_tac \\ rename1 ‘x ∉ _’
          \\ rpt $ last_x_assum $ qspec_then ‘x’ assume_tac
          \\ rw [] \\ gvs []
          \\ rw [DISJ_EQ_IMP] \\ gvs [])
      \\ gvs [split_Delayed_Lam_def, FOLDL_replace_Force_Prim, exp_of_def,
              exp_rel1_def, PULL_EXISTS, exp_rel2_def]
      \\ rw []
      \\ pairarg_tac \\ gvs [exp_of_def, cexp_wf_def, freevars_def, boundvars_def, PULL_FORALL]
      \\ qspec_then ‘xs’ mp_tac split_Delay_Lam_soundness_Prim
      \\ (impl_tac
          >- (rw [] \\ rename1 ‘MEM e xs’ \\ last_x_assum $ qspec_then ‘e’ assume_tac
              \\ assume_tac cexp_size_lemma \\ fs []
              \\ first_x_assum $ dxrule_then assume_tac
              \\ gvs [cexp_size_def]
              \\ pop_assum kall_tac \\ pop_assum kall_tac \\ pop_assum kall_tac
              \\ pop_assum $ drule_all_then $ qx_choose_then ‘e2’ assume_tac
              \\ qexists_tac ‘e2’ \\ gvs []))
      \\ disch_then $ drule_then $ drule_then $ drule_then $ drule_then $ drule_then mp_tac
      \\ gvs [DISJOINT_SYM]
      \\ disch_then $ qx_choose_then ‘ys’ $ qx_choose_then ‘ys'’ assume_tac \\ fs []
      \\ qpat_x_assum ‘LIST_REL _ _ _’ $ irule_at Any
      \\ qpat_x_assum ‘LIST_REL _ _ _’ $ irule_at Any \\ simp []
      >- (drule_then assume_tac args_ok_split_Delayed_Lam \\ gvs [PULL_FORALL]
          \\ pop_assum kall_tac \\ qpat_x_assum ‘args_ok _ _’ kall_tac)
      >- (drule_then assume_tac FOLDR_split_Delayed_Lam_LENGTH
          \\ gvs [args_ok_def]))
  >~[‘Apps (exp_of f) (MAP _ args)’]
  >- (gvs [split_Delayed_Lam_def, FOLDL_replace_Force_Apps, exp_of_def, PULL_EXISTS]
      \\ rw []
      \\ pairarg_tac \\ gs [] \\ pairarg_tac
      \\ gvs [exp_of_def, PULL_FORALL, freevars_Apps, boundvars_Apps, cexp_wf_def]
      \\ qspec_then ‘args’ mp_tac split_Delay_Lam_soundness_Prim
      \\ impl_tac
      >- (rw [] \\ rename1 ‘MEM e args’ \\ last_x_assum $ qspec_then ‘e’ assume_tac
          \\ assume_tac cexp_size_lemma \\ fs []
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gvs [cexp_size_def]
          \\ pop_assum kall_tac \\ pop_assum kall_tac \\ pop_assum kall_tac
          \\ pop_assum $ drule_all_then $ qx_choose_then ‘e2’ assume_tac
          \\ qexists_tac ‘e2’ \\ gvs [])
      \\ last_x_assum $ qspec_then ‘f’ assume_tac \\ gvs [cexp_size_def]
      \\ pop_assum $ drule_then $ drule_then $ drule_then $ drule_then $ mp_tac
      \\ gvs [DISJOINT_SYM]
      \\ disch_then $ qx_choose_then ‘f1’ $ qx_choose_then ‘f2’ assume_tac \\ gvs []
      \\ disch_then $ drule_then $ drule_then $ drule_then $ drule_then $ drule_then mp_tac
      \\ impl_tac
      >- (gvs [GSYM PULL_FORALL, SF ETA_ss]
          \\ rw [] \\ irule SUBSET_TRANS \\ metis_tac [])
      \\ disch_then $ qx_choose_then ‘ys1’ $ qx_choose_then ‘ys2’ assume_tac
      \\ dxrule_then assume_tac FOLDR_split_Delayed_Lam_LENGTH
      \\ qexists_tac ‘Apps f1 ys1’ \\ qexists_tac ‘Apps f2 ys2’
      \\ gvs [SF ETA_ss, FOLDL_replace_Force_Apps] \\ rw []
      >- (irule SUBSET_TRANS \\ metis_tac [])
      >- (irule SUBSET_TRANS \\ metis_tac [])
      >- (irule SUBSET_TRANS \\ metis_tac [])
      >- (gvs [boundvars_Apps, SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
          \\ rpt $ conj_tac \\ gen_tac \\ rename1 ‘x ∉ _’
          \\ rpt $ last_x_assum $ qspec_then ‘x’ assume_tac
          \\ rw [] \\ gvs []
          >- first_x_assum $ drule_all_then irule
          >- (rename1 ‘MEM s (MAP boundvars _)’
              \\ rpt $ first_x_assum $ qspec_then ‘s’ assume_tac
              \\ gvs [])
          >- (rw [DISJ_EQ_IMP] \\ gvs []
              \\ metis_tac []))
      >- (gvs [thunk_Delay_LamTheory.exp_rel_Apps]
          \\ metis_tac [])
      >- (gvs [thunk_Let_Delay_VarTheory.full_exp_rel_Apps,
               FOLDL_replace_Force_Apps]
          \\ metis_tac [])
      >- (strip_tac \\ gvs []))
  >~[‘Lams (MAP _ vL) (exp_of e)’]
  >- (gvs [split_Delayed_Lam_def, FOLDL_replace_Force_Lams, exp_of_def, PULL_EXISTS]
      \\ rw []
      \\ pairarg_tac \\ gs [PULL_FORALL]
      \\ last_x_assum $ qspec_then ‘e’ assume_tac \\ gs [cexp_size_def]
      \\ rename1 ‘set map_l’
      \\ pop_assum $ drule_then $ qspec_then ‘FILTER (λv. ¬MEM v vL) map_l’ mp_tac
      \\ simp [] \\ impl_tac
      >- (gvs [FOLDL_delete_ok, freevars_Lams, boundvars_Lams, SUBSET_DEF,
               PULL_EXISTS, DISJOINT_ALT, FILTER_ALL_DISTINCT]
          \\ rw []
          >- (rename1 ‘x ∈ _’
              \\ rpt $ first_x_assum $ qspec_then ‘x’ assume_tac \\ gvs []
              \\ Cases_on ‘¬MEM x (MAP explode vL)’ \\ gvs [])
          >- (rename1 ‘explode x ∈ _’
              \\ rpt $ first_x_assum $ qspec_then ‘x’ assume_tac
              \\ gvs [MEM_FILTER, MEM_MAP])
          >- (first_x_assum irule
              \\ dxrule_then irule FRANGE_FOLDL_delete
              \\ simp [])
          >- (strip_tac
              \\ dxrule_then assume_tac FRANGE_FOLDL_delete
              \\ gvs [MEM_FILTER])
          >- (rename1 ‘explode x ∈ _’
              \\ rpt $ first_x_assum $ qspec_then ‘explode x’ assume_tac
              \\ strip_tac
              \\ dxrule_then assume_tac FRANGE_FOLDL_delete
              \\ gvs [MEM_MAP])
          >- (rename1 ‘explode x ∈ _’
              \\ rpt $ first_x_assum $ qspec_then ‘explode x’ assume_tac
              \\ strip_tac
              \\ dxrule_then assume_tac FRANGE_FOLDL_delete
              \\ gvs [MEM_MAP])
          \\ simp [SET_EQ_SUBSET, SUBSET_DEF, FDOM_FOLDL_delete, MEM_FILTER])
      \\ disch_then $ qx_choose_then ‘e_mid’ $ qx_choose_then ‘e_end’ assume_tac
      \\ qexists_tac ‘Lams (MAP explode vL) e_mid’
      \\ qexists_tac ‘Lams (MAP explode vL) e_end’
      \\ gvs [exp_of_def, freevars_Lams, boundvars_Lams, SUBSET_DEF, PULL_EXISTS, cexp_wf_def]
      \\ rw []
      >- (rename1 ‘x ∈ _’
          \\ rpt $ first_x_assum $ qspec_then ‘x’ assume_tac \\ gvs [])
      >- (rename1 ‘x ∈ _’
          \\ rpt $ first_x_assum $ qspec_then ‘x’ assume_tac \\ gvs [])
      >- (gvs [SET_EQ_SUBSET, SUBSET_DEF]
          \\ rpt $ conj_tac \\ gen_tac \\ rename1 ‘x ∉ _’
          \\ rpt $ last_x_assum $ qspec_then ‘x’ assume_tac
          \\ rw [] \\ gvs [])
      >- (gvs [thunk_Delay_LamTheory.exp_rel_Lams]
          \\ metis_tac [])
      >- (gvs [thunk_Let_Delay_VarTheory.full_exp_rel_Lams]
          \\ metis_tac [])
      >- (gvs [FOLDL_replace_Force_Lams]
          \\ AP_THM_TAC \\ AP_TERM_TAC
          \\ gvs [MEM_MAP]
          \\ irule FOLDL_replace_Force_change_map
          \\ gvs [MEM_FILTER]
          \\ rw []
          \\ irule FOLDL_delete_thm
          \\ simp []))
  >~[‘Letrec _ _’]

  >- (gvs [exp_of_def, PULL_EXISTS, PULL_FORALL] \\ rw []
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gvs []
      \\ simp [exp_rel1_def]
      \\ ‘∀A B. B ⇒ A ∨ B’ by simp [] \\ pop_assum $ irule_at Any
      \\ gvs [PULL_EXISTS]
      \\ drule_then mp_tac letrec_split_soundness
      \\ rename1 ‘map_ok (FOLDL _ map2 l)’
      \\ qspecl_then [‘MAP FST l’, ‘map2’] assume_tac $ GEN_ALL FOLDL_delete_ok
      \\ gvs [FOLDL_MAP, combinTheory.o_DEF, LAMBDA_PROD, EVERY_MAP]
      \\ rename1 ‘FINITE _ ∧ DISJOINT (vc_to_set vc') _ ⇒ _’
      \\ rename1 ‘FOLDR _ _ _ = (binds2, vc2)’
      \\ rename1 ‘split_Delayed_Lam _ _ _ = (expr2, _)’
      \\ ‘FINITE ((boundvars (exp_of (Letrec binds2 expr2))) ∩ COMPL (vc_to_set vc'))’
        by (irule FINITE_INTER
            \\ disj1_tac
            \\ cheat)
      \\ disch_then $ dxrule_then mp_tac
      \\ simp [DISJOINT_ALT]
      \\ disch_then $ qx_choose_then ‘vL’ assume_tac \\ fs []
      \\ qpat_x_assum ‘ALL_DISTINCT _’ $ irule_at Any
      \\ gvs [GSYM PULL_FORALL]


      \\ cheat)
  >~[‘rows_of _ (MAP _ rows)’]

  >- (gvs [SF CONJ_ss]
      \\ rw []
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gvs [PULL_FORALL]
      \\ rename1 ‘FOLDR _ ([], vc1) rows = (list1, vc2)’
      \\ ‘MAP FST rows = MAP FST list1 ∧
          MAP (FST o SND) rows = MAP (FST o SND) list1’
        by (pop_assum mp_tac
            \\ rpt $ pop_assum kall_tac
            \\ qid_spec_tac ‘vc2’ \\ qid_spec_tac ‘list1’
            \\ Induct_on ‘rows’ \\ gvs [FORALL_PROD]
            \\ rw []
            \\ pairarg_tac \\ gs []
            \\ pairarg_tac \\ gvs [])
      \\ irule_at Any thunk_Delay_LamTheory.exp_rel_Let
      \\ rename1 ‘cexp_size (Case e m rows)’
      \\ ‘cexp_size e < cexp_size (Case e m rows)’ by simp [cexp_size_def]
      \\ last_assum $ dxrule_then $ drule_then mp_tac
      \\ rename1 ‘set map_l’
      \\ disch_then $ qspec_then ‘map_l’ mp_tac
      \\ gvs [freevars_def, boundvars_def]
      \\ disch_then $ qx_choose_then ‘e_mid’ $ qx_choose_then ‘e_end’ assume_tac \\ fs []
      \\ first_x_assum $ irule_at $ Pos hd
      \\ irule_at Any full_exp_rel_Let
      \\ first_x_assum $ irule_at $ Pos hd
      \\ gvs [exp_of_def, FOLDL_replace_Force_Let, boundvars_def, freevars_def, cexp_wf_def, cexp_size_def]
      \\ ‘list1 ≠ []’ by (strip_tac \\ gvs []) \\ simp []
      \\ irule_at (Pos $ el 3) SUBSET_TRANS
      \\ first_assum $ irule_at $ Pos hd
      \\ qpat_x_assum ‘split_Delayed_Lam e _ _ = _’ kall_tac
      \\ gvs [COMPL_UNION, UNION_INTER]
      \\ ‘∀A B C. A ∩ (B ∩ C ∩ (COMPL A)) = {} : string -> bool’
        by (rpt $ gen_tac
            \\ irule $ iffRL SET_EQ_SUBSET
            \\ rpt $ irule_at Any $ iffRL SUBSET_DEF
            \\ rw []
            \\ rename1 ‘x ∉ A ∨ _ ∨ x ∈ A’
            \\ Cases_on ‘x ∈ A’ \\ simp [])
      \\ simp []
      \\ pop_assum kall_tac
      \\ ‘vc_to_set vc1 ⊆ vc_to_set vc2 ⇒
          (vc_to_set vc2 ∩ (COMPL (vc_to_set vc1))) ∪ (vc_to_set vc1 ∩ (COMPL (vc_to_set vc)))
          = vc_to_set vc2 ∩ (COMPL (vc_to_set vc))’
        by (gvs [SET_EQ_SUBSET, SUBSET_DEF]
            \\ strip_tac \\ gen_tac
            \\ rename1 ‘x ∈ vc_to_set _’
            \\ rpt $ last_x_assum $ qspec_then ‘x’ assume_tac
            \\ strip_tac \\ strip_tac \\ gvs [])
      \\ irule_at (Pos $ el 10) EQ_TRANS
      \\ pop_assum $ irule_at Any

      \\ qspec_then ‘rows’ mp_tac split_Delay_Lam_soundness_rows
      \\ impl_tac
      >- (gen_tac \\ rename1 ‘MEM e2 (MAP (SND o SND) rows)’
          \\ last_x_assum $ qspec_then ‘e2’ assume_tac
          \\ rpt $ gen_tac \\ strip_tac
          \\ ‘cexp_size e2 < cexp1_size rows’
            by (assume_tac cexp_size_lemma \\ fs []
                \\ first_x_assum irule
                \\ gvs [MEM_MAP]
                \\ rename1 ‘SND (SND y)’ \\ PairCases_on ‘y’
                \\ gvs []
                \\ first_x_assum $ irule_at Any)
          \\ gvs []
          \\ strip_tac
          \\ first_x_assum $ drule_all_then assume_tac
          \\ gvs []
          \\ metis_tac [])
      \\ strip_tac
      \\ pop_assum $ drule_then assume_tac \\ gvs [SF ETA_ss]
      \\ pop_assum $ drule_then mp_tac \\ simp []
      \\ impl_tac
      >- (rw []
          >- (irule SUBSET_TRANS \\ metis_tac [])
          >- (irule SUBSET_TRANS \\ metis_tac [])
          >- (irule SUBSET_TRANS \\ metis_tac [])
          >- (irule SUBSET_TRANS
              \\ qpat_x_assum ‘vc_to_set _ ⊆ vc_to_set _’ $ irule_at $ Pos last
              \\ gvs [SUBSET_DEF] \\ rw [] \\ metis_tac []))
      \\ rw [] \\ simp []
      \\ first_x_assum $ irule_at Any
      \\ simp [] \\ rw []
      >- (gvs [SET_EQ_SUBSET, SUBSET_DEF]
          \\ rw [] \\ metis_tac [])
      >- (irule SUBSET_TRANS \\ metis_tac [])
      >- gvs [SUBSET_DEF]
      >- (irule SUBSET_TRANS \\ metis_tac [])
      >- gvs []
      \\ gvs [SUBSET_DEF])
  >~[‘Delay _’]
  >- (rename1 ‘split_Delayed_Lam e _ _’
      \\ rpt $ gen_tac \\ pairarg_tac
      \\ gvs [PULL_FORALL] \\ strip_tac
      \\ last_x_assum $ qspec_then ‘e’ assume_tac \\ fs [cexp_size_def]
      \\ pop_assum $ drule_all_then $ qx_choose_then ‘e_mid’ assume_tac
      \\ gvs [exp_of_def, FOLDL_replace_Force_Delay, exp_rel1_def, exp_rel2_def,
              freevars_def, boundvars_def, cexp_wf_def, PULL_EXISTS]
      \\ metis_tac [])
  >~[‘Box _’]
  >- (rename1 ‘split_Delayed_Lam e _ _’
      \\ rpt $ gen_tac \\ pairarg_tac
      \\ gvs [PULL_FORALL] \\ strip_tac
      \\ last_x_assum $ qspec_then ‘e’ assume_tac \\ fs [cexp_size_def]
      \\ pop_assum $ drule_all_then $ qx_choose_then ‘e_mid’ assume_tac
      \\ gvs [exp_of_def, FOLDL_replace_Force_Box, exp_rel1_def, exp_rel2_def,
              freevars_def, boundvars_def, cexp_wf_def, PULL_EXISTS]
      \\ metis_tac [])
  >~[‘Force (exp_of e)’]
  >- (Cases_on ‘dest_Var e’ \\ gvs []
      >~[‘dest_Var e = SOME v’]
      >- (Cases_on ‘e’ \\ gvs [dest_Var_def, cexp_wf_def, boundvars_def, freevars_def, exp_of_def]
          \\ rpt $ gen_tac \\ CASE_TAC \\ strip_tac
          \\ gvs [exp_of_def, freevars_def, boundvars_def, lookup_thm, FLOOKUP_DEF, cexp_wf_def]
          >- (gvs [FOLDL_replace_Force_Force_Var1, exp_rel1_def, exp_rel2_def, boundvars_def])
          \\ gvs [exp_rel1_def, exp_rel2_def, boundvars_def]
          \\ conj_tac
          >- (gvs [SUBSET_DEF, PULL_EXISTS]
              \\ qpat_x_assum ‘∀x. _ ∈ FRANGE _ ⇒ _ ∈ _’ irule
              \\ gvs [IN_FRANGE]
              \\ metis_tac [])
          \\ gvs [FOLDL_replace_Force_Force_Var2])
      \\ rpt $ gen_tac \\ pairarg_tac \\ strip_tac \\ gvs [cexp_size_def, PULL_FORALL]
      \\ last_x_assum $ qspec_then ‘e’ assume_tac \\ fs []
      \\ pop_assum $ drule_all_then $ qx_choose_then ‘e_mid’ assume_tac
      \\ gvs [cexp_size_def, exp_of_def, freevars_def, boundvars_def, cexp_wf_def,
              exp_rel1_def, exp_rel2_def, PULL_EXISTS]
      \\ qpat_assum ‘full_exp_rel _ _’ $ irule_at Any \\ simp []
      \\ irule $ GSYM FOLDL_replace_Force_Force
      \\ conj_tac
      >- (gen_tac \\ strip_tac
          \\ Cases_on ‘e_mid’ \\ gvs [exp_rel2_def]
          \\ Cases_on ‘e’ \\ gvs [exp_rel1_def, dest_Var_def, exp_of_def]
          >- (rename1 ‘exp_of (Prim op l)’ \\ Cases_on ‘op’ \\ gvs [exp_rel1_def, exp_of_def]
              \\ Cases_on ‘l’ \\ gvs [exp_rel1_def, exp_of_def]
              \\ rename1 ‘Prim  Seq (h::t)’ \\ Cases_on ‘t’ \\ gvs [exp_rel1_def, exp_of_def]
              \\ rename1 ‘Prim  Seq (h::h2::t)’ \\ Cases_on ‘t’ \\ gvs [exp_rel1_def, exp_of_def])
          >- (rename1 ‘Apps _ (MAP _ l)’
              \\ qspec_then ‘l’ assume_tac SNOC_CASES
              \\ gvs [FOLDL_APPEND, exp_rel1_def, cexp_wf_def])
          >- (rename1 ‘Lams (MAP _ l) _’
              \\ Cases_on ‘l’
              \\ gvs [exp_rel1_def, cexp_wf_def])
          >- gvs [exp_rel1_def, cexp_wf_def])
      \\ gvs [DISJOINT_ALT]
      \\ rw [] \\ strip_tac \\ first_x_assum $ drule_then irule
      \\ simp [IN_FRANGE]
      \\ metis_tac [])
QED

val _ = export_theory ();
