(*
   Proof of thunk_split_Delay_Lam
*)
Theory thunk_split_Delay_LamProof
Ancestors
  pair list string option sum pair list alist finite_map pred_set
  rich_list wellorder arithmetic mlmap mlstring pure_misc
  thunkLangProps thunkLang_primitives thunk_semantics var_set
  thunk_cexp thunkLang thunk_exp_of pure_vars
  thunk_split_Delay_Lam thunk_Delay_Lam thunk_Let_Delay_Var
Libs
  term_tactic dep_rewrite


Theorem FOLDL_replace_Force_Var:
  ∀map_l map m.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (Var m) map_l
    = Var m
Proof
  Induct \\ gvs [replace_Force_def]
QED

Theorem FOLDL_replace_Force_Prim:
  ∀map_l map op l.  FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e)
                          (Prim op l) map_l
                    = Prim op (MAP (λe. FOLDL (λe v. replace_Force
                                                     (Var (explode (to_fmap map ' v))) (explode v) e) e map_l) l)
Proof
  Induct \\ gvs [replace_Force_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
QED

Theorem FOLDL_replace_Force_Monad:
  ∀map_l map mop l.  FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e)
                          (Monad mop l) map_l
                    = Monad mop (MAP (λe. FOLDL (λe v. replace_Force
                                                     (Var (explode (to_fmap map ' v))) (explode v) e) e map_l) l)
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

Theorem FOLDL_replace_Force_Letrec:
  ∀map_l map b e.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (Letrec b e)  map_l
    = Letrec (MAP (λ(v, e). (v, FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e)
                                   e (FILTER (λv. ¬MEM (explode v) (MAP FST b)) map_l))) b)
             (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) e
              (FILTER (λv. ¬MEM (explode v) (MAP FST b)) map_l))
Proof
  Induct \\ gvs [replace_Force_def]
  >- (Induct \\ gvs [FORALL_PROD])
  \\ rw []
  >- (irule LIST_EQ \\ gvs [EL_MAP]
      \\ rw [] \\ pairarg_tac \\ simp []
      \\ pairarg_tac \\ gvs []
      \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM])
  \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
QED


Theorem FOLDL_replace_Force_lets_for_1:
  ∀l m1 m2 m3 m4 m5 e.
    ¬MEM m2 l ⇒
    replace_Force (Var m1) (explode m2) (lets_for m3 m4 m5 (MAPi (λi v. (i, v)) (MAP explode l)) e)
    = lets_for m3 m4 m5 (MAPi (λi v. (i, v)) (MAP explode l)) (replace_Force (Var m1) (explode m2) e)
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND, replace_Force_def]
QED

Theorem FOLDL_replace_Force_lets_for_2:
  ∀l m1 m2 m3 m4 m5 e.
    MEM m2 l ⇒
    replace_Force (Var m1) (explode m2) (lets_for m3 m4 m5 (MAPi (λi v. (i, v)) (MAP explode l)) e)
    = lets_for m3 m4 m5 (MAPi (λi v. (i, v)) (MAP explode l)) e
Proof
  Induct using SNOC_INDUCT
  \\ rw []
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND, replace_Force_def]
  \\ rename1 ‘lets_for _ _ _ (MAPi _ (MAP explode l)) (Seq _ (Let (SOME (explode m2)) _ _))’
  \\ Cases_on ‘MEM m2 l’ \\ gvs [FOLDL_replace_Force_lets_for_1, replace_Force_def]
QED

Theorem FOLDL_replace_Force_lets_for:
  ∀map_l map l m1 m2 x.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e)
          (lets_for (LENGTH l) m1 (explode m2) (MAPi (λi v. (i, v)) (MAP explode l)) x) map_l
    =
    lets_for (LENGTH l) m1 (explode m2) (MAPi (λi v. (i, v)) (MAP explode l))
             (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) x
               (FILTER (λv. ¬MEM v l) map_l))
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
  >~[‘Apps _ _’]
  >- (rename1 ‘Apps _ (MAP _ l)’
      \\ qspec_then ‘l’ assume_tac SNOC_CASES
      \\ gvs [cexp_wf_def, MAP_SNOC, FOLDL_SNOC])
  >~[‘Lams _ _’]
  >- (rename1 ‘Lams (MAP _ l) _’
      \\ Cases_on ‘l’ \\ gvs [cexp_wf_def, FOLDL_APPEND])
  >- (rename1 ‘Case m l opt’
      \\ gs [cexp_wf_def]
      \\ Cases_on ‘l’ \\ simp [rows_of_def]
      \\ pairarg_tac \\ simp [rows_of_def])
QED

Theorem split_Delayed_Lam_is_Delay:
  split_Delayed_Lam e vc maps = (e_out, v_out) ∧ is_Delay e ⇒ is_Delay e_out
Proof
  Cases_on ‘e’ \\ simp [is_Delay_def, split_Delayed_Lam_def]
  \\ pairarg_tac \\ rw [] \\ simp [is_Delay_def]
QED

(*Theorem args_ok_split_Delayed_Lam:
  ∀xs vc s map xs' vc'.
    FOLDR (λe (l',vc). (λ(e', vc'). (e'::l', vc')) (split_Delayed_Lam e vc map)) ([],vc) xs = (xs',vc')
    ∧ args_ok (Cons s) xs
    ⇒ args_ok (Cons s) xs'
Proof
  gvs [args_ok_def] \\ rw [] \\ gvs []
  \\ pairarg_tac \\ gvs [split_Delayed_Lam_is_Delay]
  >- (dxrule_then assume_tac split_Delayed_Lam_is_Delay
      \\ gs [is_Delay_def]
      \\ rename1 ‘is_Delay exp’
      \\ Cases_on ‘exp’ \\ gs [is_Delay_def])
  >- (dxrule_then assume_tac split_Delayed_Lam_is_Delay
      \\ gs [is_Delay_def]
      \\ rename1 ‘is_Delay exp’
      \\ Cases_on ‘exp’ \\ gs [is_Delay_def])
  \\ pairarg_tac \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ dxrule_then assume_tac split_Delayed_Lam_is_Delay
  >~[‘[Delay _; _; _]’]
  >- (pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ dxrule_then assume_tac split_Delayed_Lam_is_Delay
      \\ dxrule_then assume_tac split_Delayed_Lam_is_Delay
      \\ gs [is_Delay_def]
      \\ rpt (rename1 ‘is_Delay exp1’
              \\ Cases_on ‘exp1’ \\ gs [is_Delay_def])
      \\ gvs [])
  \\ dxrule_then assume_tac split_Delayed_Lam_is_Delay
  \\ gs [is_Delay_def]
  \\ rename1 ‘exp1 = Delay _ ∧ exp2 = Delay _’
  \\ Cases_on ‘exp1’ \\ gs [is_Delay_def]
  \\ Cases_on ‘exp2’ \\ gs [is_Delay_def]
QED*)

Theorem split_Delay_Lam_soundness_Prim:
  ∀xs. (∀e vc'' map map_l' e_out' vc_out.
         MEM e xs ⇒
         split_Delayed_Lam e vc'' map = (e_out',vc_out) ∧
          ALL_DISTINCT map_l' ∧ freevars (exp_of e) ⊆ set_of vc'' ∧
          boundvars (exp_of e) ⊆ set_of vc'' ∧
          IMAGE explode (set map_l') ⊆ set_of vc'' ∧
          IMAGE explode (FRANGE (to_fmap map)) ⊆ set_of vc'' ∧ cexp_wf e ∧
          DISJOINT (set map_l') (FRANGE (to_fmap map)) ∧
          DISJOINT (freevars (exp_of e))
            (IMAGE explode (FRANGE (to_fmap map))) ∧
          DISJOINT (boundvars (exp_of e))
            (IMAGE explode (FRANGE (to_fmap map))) ∧ map_ok map ∧
          cmp_of map = compare ∧ vars_ok vc'' ∧
          FDOM (to_fmap map) = set map_l' ⇒
          ∃e2 e3.
            cns_arities e = cns_arities e_out' ∧
            set_of vc'' ⊆ set_of vc_out ∧ vars_ok vc_out ∧
            freevars (exp_of e_out') ⊆ set_of vc_out ∧
            boundvars (exp_of e_out') ⊆ set_of vc_out ∧
            boundvars e2 ∩ COMPL (boundvars (exp_of e)) =
            set_of vc_out ∩ COMPL (set_of vc'') ∧
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
         vars_ok vc ∧ FDOM (to_fmap map) = set map_l ∧
         EVERY (λa. cexp_wf a) xs ∧
         IMAGE explode (set map_l) ⊆ set_of vc ∧
         IMAGE explode (FRANGE (to_fmap map)) ⊆ set_of vc ∧
         DISJOINT (set map_l) (FRANGE (to_fmap map)) ∧
         DISJOINT (IMAGE explode (FRANGE (to_fmap map)))
                  (BIGUNION (set (MAP (λa. freevars a) (MAP (λa. exp_of a) xs)))) ∧
         DISJOINT (IMAGE explode (FRANGE (to_fmap map)))
                  (BIGUNION (set (MAP (λa. boundvars a) (MAP (λa. exp_of a) xs)))) ∧
         BIGUNION (set (MAP (λa. freevars a) (MAP (λa. exp_of a) xs)))
                  ⊆ set_of vc ∧
         BIGUNION (set (MAP (λa. boundvars a) (MAP (λa. exp_of a) xs)))
                  ⊆ set_of vc ∧
         ALL_DISTINCT map_l ⇒
         ∃ys ys'.
           BIGUNION (set (MAP (λa. cns_arities a) xs)) = BIGUNION (set (MAP (λa. cns_arities a) xs')) ∧
           set_of vc ⊆ set_of vc' ∧ vars_ok vc' ∧
           BIGUNION (set (MAP (λa. freevars a) (MAP (λa. exp_of a) xs'))) ⊆
                    set_of vc' ∧
           BIGUNION (set (MAP (λa. boundvars a) (MAP (λa. exp_of a) xs'))) ⊆
                    set_of vc' ∧
           BIGUNION (set (MAP (λa. boundvars a) ys)) ∩
                    COMPL
                    (BIGUNION (set (MAP (λa. boundvars a) (MAP (λa. exp_of a) xs)))) =
           set_of vc' ∩ COMPL (set_of vc) ∧
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
            thunk_Delay_Lam$exp_rel (lets_for l s n (MAPi (λi v. (i, v)) (MAP explode vs)) e)
                                    (lets_for l s n (MAPi (λi v. (i, v)) (MAP explode vs)) e2)
Proof
  Induct using SNOC_INDUCT \\ simp [lets_for_def]
  \\ simp [MAP_APPEND, indexedListsTheory.MAPi_APPEND,
           SNOC_APPEND, lets_for_APPEND, lets_for_def]
  \\ rw [] \\ last_x_assum irule
  \\ gvs [exp_rel1_def]
QED

Theorem lets_for_boundvars_freevars:
  ∀l v n x s len. freevars (lets_for len v n (MAPi (λi v. (i, v)) l) x) ⊆ s
              ∧ boundvars (lets_for len v n (MAPi (λi v. (i, v)) l) x) ⊆ s
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
  ∀l v n x len. freevars (lets_for len v n (MAPi (λi v. (i, v)) l) x) ⊆ freevars x ∪ {n}
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND]
  \\ rw []
  \\ irule SUBSET_TRANS \\ last_x_assum $ irule_at $ Pos hd
  \\ rw [freevars_def, SUBSET_DEF] \\ gvs []
QED

Theorem boundvars_lets_for:
  ∀l v n x len. boundvars (lets_for len v n (MAPi (λi v. (i, v)) l) x) = boundvars x ∪ (set l)
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND]
  \\ rw [boundvars_def, SET_EQ_SUBSET, SUBSET_DEF] \\ gvs []
QED

Theorem lets_for_bound_freevars:
  ∀l v n x s len. freevars (lets_for len v n (MAPi (λi v. (i, v)) l) x) ⊆ s
              ∧ boundvars (lets_for len v n (MAPi (λi v. (i, v)) l) x) ⊆ s
              ⇒ freevars x ⊆ s
Proof
  rw [] \\ dxrule_all_then assume_tac lets_for_boundvars_freevars
  \\ gs []
QED

Theorem lets_for_free_boundvars:
  ∀l v n x s len. freevars (lets_for len v n (MAPi (λi v. (i, v)) l) x) ⊆ s
              ∧ boundvars (lets_for len v n (MAPi (λi v. (i, v)) l) x) ⊆ s
              ⇒ boundvars x ⊆ s
Proof
  rw [] \\ dxrule_all_then assume_tac lets_for_boundvars_freevars
  \\ gs []
QED

Theorem in_freevars_or_boundvars_lets_for:
  ∀l v n x m len. (m ∈ freevars x ∨ m ∈ boundvars x) ⇒
                m ∈ freevars (lets_for len v n (MAPi (λi v. (i, v)) l) x)
                ∨ m ∈ boundvars (lets_for len v n (MAPi (λi v. (i, v)) l) x)
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND]
  \\ rw [] \\ last_x_assum irule
  \\ gvs [freevars_def, boundvars_def]
QED

Theorem in_boundvars_lets_for:
  ∀l v n x m len. m ∈ boundvars x ⇒
                m ∈ boundvars (lets_for len v n (MAPi (λi v. (i, v)) l) x)
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND]
  \\ rw [] \\ last_x_assum irule
  \\ gvs [boundvars_def]
QED

Theorem in_boundvars_lets_for2:
  ∀l v n x m len. MEM m l ⇒
                m ∈ boundvars (lets_for len v n (MAPi (λi v. (i, v)) l) x)
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
  ∀l v n x m len. m ∈ freevars x ⇒
                m ∈ freevars (lets_for len v n (MAPi (λi v. (i, v)) l) x)
                ∨ m ∈ boundvars (lets_for len v n (MAPi (λi v. (i, v)) l) x)
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
  qspec_then ‘vL’ assume_tac SNOC_CASES >> gvs [FOLDL_SNOC, delete_thm]
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
  ∀l n1 n2 x y len. full_exp_rel x y
                ⇒ full_exp_rel (lets_for len n1 n2 l x) (lets_for len n1 n2 l y)
Proof
  Induct \\ gvs [lets_for_def, FORALL_PROD]
  \\ rw [] \\ irule full_exp_rel_Let
  \\ irule_at Any full_exp_rel_Let
  \\ last_x_assum $ drule_then $ irule_at Any
  \\ gvs [full_exp_rel_def]
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

Theorem exp_rel_Disj:
  ∀l m. thunk_Delay_Lam$exp_rel (Disj m l) (Disj m l)
Proof
  Induct \\ gs [Disj_def, exp_rel1_def, FORALL_PROD]
QED

Theorem full_exp_rel_Disj:
  ∀l m. full_exp_rel (Disj m l) (Disj m l)
Proof
  Induct \\ gs [Disj_def, exp_rel2_def, FORALL_PROD]
QED

Theorem boundvars_Disj:
  ∀l m. boundvars (Disj m l) = ∅
Proof
  Induct \\ gs [Disj_def, boundvars_def, FORALL_PROD]
QED

Theorem replace_Force_Disj:
  ∀l m v1 v2. replace_Force v1 v2 (Disj m l) = Disj m l
Proof
  Induct \\ gs [Disj_def, replace_Force_def, FORALL_PROD]
QED

Theorem FOLDL_replace_Force_Disj:
  ∀map_l map l m v1 v2.
    FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) (Disj m l) map_l = Disj m l
Proof
  Induct \\ gs [replace_Force_Disj]
QED

Theorem split_Delay_Lam_soundness_rows:
  ∀rows fallthrough. (∀e vc'' map map_l' e_out' vc_out.
         MEM e (MAP (SND o SND) rows) ∨ (∃a. fallthrough = SOME (a, e)) ⇒
         split_Delayed_Lam e vc'' map = (e_out',vc_out) ∧
          ALL_DISTINCT map_l' ∧ freevars (exp_of e) ⊆ set_of vc'' ∧
          boundvars (exp_of e) ⊆ set_of vc'' ∧
          IMAGE explode (set map_l') ⊆ set_of vc'' ∧
          IMAGE explode (FRANGE (to_fmap map)) ⊆ set_of vc'' ∧ cexp_wf e ∧
          DISJOINT (set map_l') (FRANGE (to_fmap map)) ∧
          DISJOINT (freevars (exp_of e))
            (IMAGE explode (FRANGE (to_fmap map))) ∧
          DISJOINT (boundvars (exp_of e))
            (IMAGE explode (FRANGE (to_fmap map))) ∧ map_ok map ∧
          cmp_of map = compare ∧ vars_ok vc'' ∧
          FDOM (to_fmap map) = set map_l' ⇒
         ∃e2 e3.
           cns_arities e = cns_arities e_out' ∧
           set_of vc'' ⊆ set_of vc_out ∧ vars_ok vc_out ∧
           freevars (exp_of e_out') ⊆ set_of vc_out ∧
           boundvars (exp_of e_out') ⊆ set_of vc_out ∧
           boundvars e2 ∩ COMPL (boundvars (exp_of e)) =
           set_of vc_out ∩ COMPL (set_of vc'') ∧
           thunk_Delay_Lam$exp_rel (exp_of e) e2 ∧ full_exp_rel e2 e3 ∧
           cexp_wf e_out' ∧
           exp_of e_out' =
           FOLDL
           (λe v.
              replace_Force (Var (explode (to_fmap map ' v)))
                            (explode v) e) e3 map_l') ⇒
       ∀m vc1 vc2 vc3 list1 map map_l fallthrough'.
         FOLDR
         (λ(v,vL,expr) (l',vc').
            (λ(expr',vc''). ((v,vL,expr')::l',vc''))
            (split_Delayed_Lam expr vc'
             (FOLDL delete map vL))) ([],vc2) rows = (list1,vc3) ∧
         vars_ok vc1 ∧ map_ok map ∧ cmp_of map = compare ∧
         EVERY cexp_wf (MAP (SND o SND) rows) ∧
         OPTION_ALL (λ(_, e). cexp_wf e) fallthrough ∧
         vars_ok vc1 ∧
         DISJOINT (boundvars (rows_of (explode m)
                              (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) rows)
                              (OPTION_MAP (λ(a, e). (MAP (explode ## I) a, exp_of e)) fallthrough)))
                  (IMAGE explode (FRANGE (to_fmap map))) ∧
         DISJOINT (freevars (rows_of (explode m)
                             (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) rows)
                             (OPTION_MAP (λ(a, e). (MAP (explode ## I) a, exp_of e)) fallthrough)))
                  (IMAGE explode (FRANGE (to_fmap map))) ∧
         DISJOINT (set map_l) (FRANGE (to_fmap map)) ∧
         EVERY (λa. cexp_wf a) (MAP (SND ∘ SND) rows) ∧
         IMAGE explode (set map_l) ⊆ set_of vc1 ∧
         IMAGE explode (FRANGE (to_fmap map)) ⊆ set_of vc1 ∧
         boundvars (rows_of (explode m)
                    (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) rows)
                    (OPTION_MAP (λ(a, e). (MAP (explode ## I) a, exp_of e)) fallthrough))
                   ⊆ set_of vc1 ∧
         freevars (rows_of (explode m)
                   (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) rows)
                   (OPTION_MAP (λ(a, e). (MAP (explode ## I) a, exp_of e)) fallthrough))
                  ⊆ set_of vc1 ∧
         ALL_DISTINCT map_l ∧
         FDOM (to_fmap map) = set map_l ∧
         ((fallthrough', vc2) = case fallthrough of
                              | NONE => (NONE, vc1)
                              | SOME (a, exp) => let (exp, vc) = split_Delayed_Lam exp vc1 map in
                                                   (SOME (a, exp), vc))
         ⇒
         ∃x y.
           BIGUNION (set (MAP (λ(cn, vs, e). cns_arities e) rows))
           = BIGUNION (set (MAP (λ(cn, vs, e). cns_arities e) list1)) ∧
           set (MAP (λ(cn, vs, e). (explode cn, LENGTH vs)) rows)
           = set (MAP (λ(cn, vs, e). (explode cn, LENGTH vs)) list1) ∧
           OPTION_MAP (λ(a, e). set (MAP (λ(cn, ar). (explode cn, ar)) a)) fallthrough
           = OPTION_MAP (λ(a, e). set (MAP (λ(cn, ar). (explode cn, ar)) a)) fallthrough' ∧
           OPTION_MAP (λ(a, e). cns_arities e) fallthrough
           = OPTION_MAP (λ(a, e). cns_arities e) fallthrough' ∧
           thunk_Delay_Lam$exp_rel (rows_of (explode m)
                                    (MAP (λ(c, vs, x). (explode c, MAP explode vs, exp_of x))
                                     rows)
                                    (OPTION_MAP (λ(a, e). (MAP (explode ## I) a, exp_of e)) fallthrough)) x ∧
           full_exp_rel x y ∧
           set_of vc1 ⊆ set_of vc2 ∧ vars_ok vc2 ∧
           set_of vc2 ⊆ set_of vc3 ∧ vars_ok vc3 ∧
           EVERY cexp_wf (MAP (SND o SND) list1) ∧
           OPTION_ALL (λ(_,e). cexp_wf e) fallthrough' ∧
           ((fallthrough = NONE ⇒ rows ≠ []) ⇒ (fallthrough' = NONE ⇒ list1 ≠ [])) ∧
           rows_of (explode m) (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) list1)
                   (OPTION_MAP (λ(a, e). (MAP (explode ## I) a, exp_of e)) fallthrough')
           = FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e)
                   y map_l ∧
           freevars (rows_of (explode m)
                     (MAP (λ(c, vs, x). (explode c, MAP explode vs, exp_of x)) rows)
                     (OPTION_MAP (λ(a, e). (MAP (explode ## I) a, exp_of e)) fallthrough'))
                    ⊆ set_of vc3 ∧
           boundvars (rows_of (explode m)
                      (MAP (λ(c, vs, x). (explode c, MAP explode vs, exp_of x)) rows)
                      (OPTION_MAP (λ(a, e). (MAP (explode ## I) a, exp_of e)) fallthrough'))
                    ⊆ set_of vc3 ∧
           freevars (rows_of (explode m)
                     (MAP (λ(c, vs, x). (explode c, MAP explode vs, exp_of x)) list1)
                     (OPTION_MAP (λ(a, e). (MAP (explode ## I) a, exp_of e)) fallthrough'))
                    ⊆ set_of vc3 ∧
           boundvars (rows_of (explode m)
                      (MAP (λ(c, vs, x). (explode c, MAP explode vs, exp_of x)) list1)
                      (OPTION_MAP (λ(a, e). (MAP (explode ## I) a, exp_of e)) fallthrough'))
                    ⊆ set_of vc3 ∧
           boundvars x ∩ COMPL (boundvars (rows_of (explode m)
                                           (MAP (λ(c, vs, x). (explode c, MAP explode vs, exp_of x)) rows)
                                           (OPTION_MAP (λ(a, e). (MAP (explode ## I) a, exp_of e)) fallthrough)))
           =  set_of vc3 ∩ COMPL (set_of vc1)
Proof
  Induct \\ rw [PULL_EXISTS, rows_of_def]
  >- (rename1 ‘OPTION_MAP _ fallthrough’
      \\ Cases_on ‘fallthrough’ \\ gs []
      \\ simp [exp_rel1_def, exp_rel2_def, FOLDL_replace_Force_Prim]
      \\ pop_assum mp_tac
      \\ CASE_TAC
      \\ pairarg_tac \\ gs []
      \\ strip_tac
      \\ simp [exp_rel1_def, exp_rel2_def, PULL_EXISTS]
      \\ first_x_assum $ dxrule_then $ dxrule_then assume_tac
      \\ gs [freevars_def, boundvars_def]
      \\ qpat_x_assum ‘thunk_Delay_Lam$exp_rel _ _’ $ irule_at Any
      \\ simp [FOLDL_replace_Force_If, freevars_def, boundvars_def]
      \\ irule_at Any EQ_REFL
      \\ simp [FOLDL_replace_Force_Prim]
      \\ irule_at Any exp_rel_Disj
      \\ irule_at Any full_exp_rel_Disj
      \\ simp [FOLDL_replace_Force_Disj, boundvars_Disj]
      \\ metis_tac [SUBSET_TRANS])
  \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gvs []
  \\ gvs [rows_of_def, freevars_def, boundvars_def, exp_rel1_def, exp_rel2_def, PULL_EXISTS]
  \\ irule_at Any lets_for_exp_rel
  \\ rename1 ‘exp_rel (rows_of _ _ (OPTION_MAP _ fallthrough)) _’
  \\ last_x_assum $ qspec_then ‘fallthrough’ mp_tac
  \\ impl_tac
  >- (gen_tac \\ rename1 ‘MEM expr (MAP _ _) ∨ _’
      \\ first_x_assum $ qspec_then ‘expr’ assume_tac
      \\ rpt $ strip_tac
      \\ first_x_assum irule
      \\ simp [])
  \\ disch_then $ dxrule_then assume_tac
  \\ gs []
  \\ pop_assum $ qspecl_then [‘m’, ‘vc1’, ‘map_l’, ‘fallthrough'’] mp_tac
  \\ simp []
  \\ strip_tac
  \\ qpat_x_assum ‘thunk_Delay_Lam$exp_rel (rows_of _ _ _) _’ $ irule_at Any
  \\ rename1 ‘thunk_Delay_Lam$exp_rel (exp_of e) _’
  \\ last_x_assum $ qspec_then ‘e’ assume_tac \\ fs []
  \\ first_x_assum $ dxrule_then $ qspec_then ‘FILTER (λv. ¬MEM v vs) map_l’ mp_tac
  \\ impl_tac
  >- (simp [] \\ gvs [DISJOINT_ALT, SF DNF_ss]
      \\  rw []
      >- simp [FILTER_ALL_DISTINCT]
      >- (dxrule_all_then assume_tac lets_for_bound_freevars
          \\ metis_tac [SUBSET_TRANS])
      >- (dxrule_all_then assume_tac lets_for_free_boundvars
          \\ metis_tac [SUBSET_TRANS])
      >- (irule SUBSET_TRANS
          \\ qpat_x_assum ‘set_of _ ⊆ set_of _’ $ irule_at $ Pos last
          \\ irule SUBSET_TRANS
          \\ qpat_x_assum ‘set_of _ ⊆ set_of _’ $ irule_at $ Pos last
          \\ gs [SUBSET_DEF]
          \\ rw [MEM_FILTER]
          \\ gvs [])
      >- (irule SUBSET_TRANS
          \\ qpat_x_assum ‘set_of _ ⊆ set_of _’ $ irule_at $ Pos last
          \\ irule SUBSET_TRANS
          \\ qpat_x_assum ‘set_of _ ⊆ set_of _’ $ irule_at $ Pos last
          \\ gs [SUBSET_DEF]
          \\ rw []
          \\ dxrule_then assume_tac FRANGE_FOLDL_delete
          \\ gs [])
      >- (gvs [DISJOINT_ALT, MEM_FILTER]
          \\ rename1 ‘MEM var _’
          \\ strip_tac
          \\ dxrule_then assume_tac FRANGE_FOLDL_delete
          \\ gs [])
      >- (gvs [DISJOINT_ALT, MEM_FILTER]
          \\ rename1 ‘explode var ∈ _’
          \\ strip_tac
          \\ dxrule_then assume_tac FRANGE_FOLDL_delete
          \\ gvs [SUBSET_DEF]
          \\ rpt $ first_x_assum $ qspec_then ‘var’ assume_tac \\ gvs []
          \\ rename1 ‘lets_for (LENGTH vs) (explode c) (explode m) _ (exp_of e)’
          \\ qspecl_then [‘MAP explode vs’, ‘explode c’, ‘explode m’, ‘exp_of e’, ‘explode var’, ‘LENGTH vs’]
                         assume_tac in_freevars_or_boundvars_lets_for
          \\ gvs [])
      >- (gvs [DISJOINT_ALT, MEM_FILTER]
          \\ rename1 ‘explode var ∈ _’
          \\ strip_tac
          \\ dxrule_then assume_tac FRANGE_FOLDL_delete
          \\ gvs [SUBSET_DEF]
          \\ first_x_assum $ dxrule_then assume_tac
          \\ rpt $ first_x_assum $ qspec_then ‘var’ assume_tac \\ gvs []
          \\ rename1 ‘lets_for (LENGTH vs) (explode c) (explode m) _ (exp_of e)’
          \\ qspecl_then [‘MAP explode vs’, ‘explode c’, ‘explode m’, ‘exp_of e’, ‘explode var’, ‘LENGTH vs’]
                         assume_tac in_freevars_or_boundvars_lets_for
          \\ gvs [])
      >- (rename1 ‘map_ok (FOLDL delete map' vs)’
          \\ qspecl_then [‘vs’, ‘map'’] assume_tac $ GEN_ALL FOLDL_delete_ok
          \\ gs [])
      >- (rename1 ‘cmp_of (FOLDL delete map' vs) = _’
          \\ qspecl_then [‘vs’, ‘map'’] assume_tac $ GEN_ALL FOLDL_delete_ok
          \\ gs [])
      >- (rename1 ‘FDOM (to_fmap (FOLDL delete map' vs)) = _’
          \\ qspecl_then [‘vs’, ‘map'’] assume_tac $ GEN_ALL FDOM_FOLDL_delete
          \\ simp [SET_EQ_SUBSET, SUBSET_DEF]
          \\ gvs [MEM_FILTER]))
  \\ disch_then $ qx_choose_then ‘x2’ $ qx_choose_then ‘y2’ assume_tac \\ fs []
  \\ qpat_x_assum ‘exp_rel_ _’ $ irule_at Any
  \\ qpat_x_assum ‘full_exp_rel_ _’ $ irule_at Any
  \\ irule_at Any full_exp_rel_lets_for
  \\ qpat_x_assum ‘full_exp_rel_ _’ $ irule_at Any
  \\ rpt $ conj_tac
  >- metis_tac [SUBSET_TRANS]
  >- (simp [FOLDL_replace_Force_If, FOLDL_replace_Force_IsEq,
            FOLDL_replace_Force_Var, FOLDL_replace_Force_lets_for]
      \\ AP_TERM_TAC
      \\ irule FOLDL_replace_Force_change_map
      \\ simp [MEM_FILTER, delete_thm]
      \\ rw [] \\ irule EQ_TRANS \\ irule_at (Pos hd) FOLDL_delete_thm
      \\ simp [delete_thm, DOMSUB_FAPPLY_NEQ])
  >- gvs [SUBSET_DEF]
  >- (irule SUBSET_TRANS \\ metis_tac [])
  >- metis_tac [SUBSET_TRANS]
  >- metis_tac [SUBSET_TRANS]
  >- gvs [SUBSET_DEF]
  >- (irule SUBSET_TRANS
      \\ irule_at (Pos hd) freevars_lets_for_subset
      \\ gvs [SUBSET_DEF])
  >- (irule SUBSET_TRANS \\ metis_tac [])
  >- (gvs [boundvars_lets_for, SUBSET_DEF, boundvars_FOLDL_replace_Force]
      \\ rw [] \\ gvs [])
  >- (irule SUBSET_TRANS \\ metis_tac [])
  >- (gvs [SET_EQ_SUBSET, SUBSET_DEF, boundvars_lets_for]
      \\ rpt $ conj_tac \\ gen_tac
      >- (rename1 ‘_⇒ var ∈ set_of _’
          \\ rpt $ first_x_assum $ qspec_then ‘var’ assume_tac
          \\ rw [] \\ gvs [])
      >- (rename1 ‘_⇒ var ∉ set_of _’
          \\ rpt $ first_x_assum $ qspec_then ‘var’ assume_tac
          \\ rw [] \\ gvs [])
      >- (rename1 ‘_ ∧ var ∉ set_of _ ⇒ _’
          \\ rpt $ first_x_assum $ qspec_then ‘var’ assume_tac
          \\ rw [] \\ gvs []
          \\ Cases_on ‘var ∈ set_of vc'’ \\ gvs [])
      >- (rename1 ‘_ ∧ var ∉ set_of _ ⇒ _’
          \\ rpt $ first_x_assum $ qspec_then ‘var’ assume_tac
          \\ rw [] \\ gvs []
          \\ strip_tac \\ gvs []))
QED

Theorem GENLIST_K_T:
  ∀l. GENLIST (K T) (SUC l) = T::GENLIST (K T) l
Proof
  Induct \\ gvs [GENLIST]
QED

Theorem unfold_Delay_Lam_Eq:
  ∀e1 e2 e3 p v.
    dest_Delay_Lam e1 = NONE ∧
    cexp_ok_bind e1 ∧
    cexp_wf e1 ∧
    thunk_Delay_Lam$exp_rel (exp_of e1) e2 ∧
    full_exp_rel e2 e3 ⇒
    unfold_Delay_Lam (p, e3) (v, T) = [(p, e3)]
Proof
  Cases
  \\ gs [cexp_ok_bind_def, cexp_wf_def, exp_of_def]
  \\ rw []
  \\ gvs [Lams_split, exp_rel1_def, exp_rel2_def, unfold_Delay_Lam_def]
  \\ rename1 ‘dest_Delay_Lam (Delay c)’
  \\ Cases_on ‘c’
  \\ gs [cexp_wf_def, exp_of_def, exp_rel1_def, exp_rel2_def,
         unfold_Delay_Lam_def, is_Lam_def, dest_Delay_Lam_def]
  >- (rename1 ‘Apps _ (MAP _ l)’
      \\ qspec_then ‘l’ assume_tac SNOC_CASES
      \\ gs [exp_rel1_def, exp_rel2_def, is_Lam_def, FOLDL_MAP, FOLDL_SNOC])
  >- (rename1 ‘rows_of _ (MAP _ l) (OPTION_MAP _ fall)’
      \\ Cases_on ‘l’
      \\ gs [exp_rel1_def, exp_rel2_def, is_Lam_def, FOLDL_APPEND, rows_of_def]
      \\ pairarg_tac \\ gs [rows_of_def, exp_rel1_def, exp_rel2_def, is_Lam_def])
QED

Theorem unfold_Delay_Lam_Eq2:
  ∀e1 e2 e3 p v.
    dest_Delay_Lam e1 = NONE ∧
    cexp_ok_bind e1 ∧
    cexp_wf e1 ∧
    thunk_Delay_Lam$exp_rel (exp_of e1) e2 ⇒
    unfold_Delay_Lam (p, e2) (v, T) = [(p, e2)]
Proof
  Cases
  \\ gs [cexp_ok_bind_def, cexp_wf_def, exp_of_def]
  \\ rw []
  \\ gvs [Lams_split, exp_rel1_def, unfold_Delay_Lam_def]
  \\ rename1 ‘dest_Delay_Lam (Delay c)’
  \\ Cases_on ‘c’
  \\ gs [cexp_wf_def, exp_of_def, exp_rel1_def,
         unfold_Delay_Lam_def, is_Lam_def, dest_Delay_Lam_def]
  >- (rename1 ‘Apps _ (MAP _ l)’
      \\ qspec_then ‘l’ assume_tac SNOC_CASES
      \\ gs [exp_rel1_def, is_Lam_def, FOLDL_MAP, FOLDL_SNOC])
  >- (rename1 ‘rows_of _ (MAP _ l) (OPTION_MAP _ fall)’
      \\ Cases_on ‘l’ \\ fs []
      \\ gs [exp_rel1_def, is_Lam_def, FOLDL_APPEND, rows_of_def]
      \\ pairarg_tac \\ gs [rows_of_def, exp_rel1_def, is_Lam_def])
QED

Theorem MAP_FST_change_expL:
  ∀l1 l2 vL. LENGTH l1 = LENGTH vL ∧ LIST_REL full_exp_rel (MAP SND l1) (MAP SND l2) ∧
             MAP FST l1 = MAP FST l2 ⇒
             MAP FST (FLAT (MAP2 unfold_Delay_Lam l1 (ZIP (vL, GENLIST (K T) (LENGTH vL)))))
             = MAP FST (FLAT (MAP2 unfold_Delay_Lam l2 (ZIP (vL, GENLIST (K T) (LENGTH vL)))))
Proof
  Induct using SNOC_INDUCT \\ gvs [FORALL_PROD]
  \\ gen_tac \\ gen_tac
  \\ gen_tac \\ rename1 ‘LIST_REL _ (MAP SND (SNOC _ _)) (MAP SND l2)’
  \\ qspec_then ‘l2’ assume_tac SNOC_CASES \\ gs []
  \\ gen_tac \\ rename1 ‘SUC (LENGTH _) = LENGTH vL’
  \\ qspec_then ‘vL’ assume_tac SNOC_CASES \\ gs [LIST_REL_SNOC, MAP_SNOC]
  \\ once_rewrite_tac [ADD_SYM]
  \\ gs [GSYM arithmeticTheory.SUC_ONE_ADD, GENLIST, GSYM ZIP_APPEND]
  \\ gvs [ZIP_SNOC, SNOC_APPEND]
  \\ simp [MAP2_APPEND, LIST_REL_EL_EQN]
  \\ rw []
  \\ once_rewrite_tac [GSYM LIST_REL_eq]
  \\ irule LIST_REL_APPEND_suff
  \\ once_rewrite_tac [LIST_REL_eq]
  \\ conj_tac
  >- (last_x_assum irule
      \\ gs [LIST_REL_EL_EQN])
  \\ simp [FST_THM]
  \\ pairarg_tac \\ gs []
  \\ rename1 ‘full_exp_rel exp1 exp2’
  \\ Cases_on ‘exp1’ \\ gs [full_exp_rel_def, unfold_Delay_Lam_def]
  \\ rename1 ‘full_exp_rel exp1b exp2b’
  \\ Cases_on ‘exp1b’ \\ gs [full_exp_rel_def, is_Lam_def]
QED

Theorem MEM_FLAT_MAP2_change:
  ∀l1 l2 vL v e1. LIST_REL full_exp_rel (MAP SND l1) (MAP SND l2) ∧
       LENGTH l1 = LENGTH vL ∧ MAP FST l1 = MAP FST l2 ∧
       MEM (v, e1) (FLAT (MAP2 unfold_Delay_Lam l1 (ZIP (vL, GENLIST (K T) (LENGTH vL))))) ⇒
      ∃e2. MEM (v, e2) (FLAT (MAP2 unfold_Delay_Lam l2 (ZIP (vL, GENLIST (K T) (LENGTH vL))))) ∧
           full_exp_rel e1 e2
Proof
  Induct using SNOC_INDUCT \\ gvs [FORALL_PROD]
  \\ gen_tac \\ gen_tac
  \\ gen_tac \\ rename1 ‘LIST_REL _ (MAP SND (SNOC _ _)) (MAP SND l2)’
  \\ qspec_then ‘l2’ assume_tac SNOC_CASES \\ gs []
  \\ gen_tac \\ rename1 ‘SUC (LENGTH _) = LENGTH vL’
  \\ qspec_then ‘vL’ assume_tac SNOC_CASES \\ gs [LIST_REL_SNOC, MAP_SNOC]
  \\ once_rewrite_tac [ADD_SYM]
  \\ gs [GSYM arithmeticTheory.SUC_ONE_ADD, GENLIST, SNOC_APPEND, GSYM ZIP_APPEND]
  \\ simp [MAP2_APPEND, LIST_REL_EL_EQN]
  \\ gs [LIST_REL_EL_EQN]
  \\ rw []
  \\ last_x_assum $ drule_then assume_tac
  \\ rpt $ pop_assum $ drule_then assume_tac
  \\ gvs [MAP2_APPEND]
  >- (pop_assum $ dxrule_then assume_tac
      \\ metis_tac [])
  \\ rename1 ‘full_exp_rel p_2 (SND x)’
  \\ pop_assum kall_tac
  \\ gs [SND_THM] \\ pairarg_tac \\ gs []
  \\ Cases_on ‘∃exp1. p_2 = Delay exp1’
  \\ gs [full_exp_rel_def, unfold_Delay_Lam_def]
  >- (Cases_on ‘is_Lam exp1’ \\ gs []
      >- (first_assum $ irule_at Any
          \\ disj2_tac
          \\ Cases_on ‘exp1’ \\ gs [is_Lam_def, full_exp_rel_def])
      >- (gs [full_exp_rel_def]
          \\ disj2_tac
          \\ Cases_on ‘exp1’ \\ gs [is_Lam_def, full_exp_rel_def])
      >- (gs [full_exp_rel_def, PULL_EXISTS]
          \\ first_assum $ irule_at Any
          \\ disj2_tac
          \\ Cases_on ‘exp1’ \\ gs [is_Lam_def, full_exp_rel_def]))
  \\ rename1 ‘full_exp_rel _ e2’
  \\ qexists_tac ‘e2’
  \\ Cases_on ‘p_2’ \\ gs [unfold_Delay_Lam_def]
  \\ gs [full_exp_rel_def, unfold_Delay_Lam_def]
QED

Theorem MEM_FLAT_MAP2_change2:
  ∀l1 l2 vL v e2. LIST_REL full_exp_rel (MAP SND l1) (MAP SND l2) ∧
       LENGTH l1 = LENGTH vL ∧ MAP FST l1 = MAP FST l2 ∧
       MEM (v, e2) (FLAT (MAP2 unfold_Delay_Lam l2 (ZIP (vL, GENLIST (K T) (LENGTH vL))))) ⇒
      ∃e1. MEM (v, e1) (FLAT (MAP2 unfold_Delay_Lam l1 (ZIP (vL, GENLIST (K T) (LENGTH vL))))) ∧
           full_exp_rel e1 e2
Proof
  Induct using SNOC_INDUCT \\ gvs [FORALL_PROD]
  \\ gen_tac \\ gen_tac
  \\ gen_tac \\ rename1 ‘LIST_REL _ (MAP SND (SNOC _ _)) (MAP SND l2)’
  \\ qspec_then ‘l2’ assume_tac SNOC_CASES \\ gs []
  \\ gen_tac \\ rename1 ‘SUC (LENGTH _) = LENGTH vL’
  \\ qspec_then ‘vL’ assume_tac SNOC_CASES \\ gs [LIST_REL_SNOC, MAP_SNOC]
  \\ once_rewrite_tac [ADD_SYM]
  \\ gs [GSYM arithmeticTheory.SUC_ONE_ADD, GENLIST, SNOC_APPEND, GSYM ZIP_APPEND]
  \\ simp [MAP2_APPEND, LIST_REL_EL_EQN]
  \\ gs [LIST_REL_EL_EQN]
  \\ rw []
  \\ last_x_assum $ drule_then assume_tac
  \\ rpt $ pop_assum $ drule_then assume_tac
  \\ gvs [MAP2_APPEND]
  >- (pop_assum $ dxrule_then assume_tac
      \\ metis_tac [])
  \\ rename1 ‘full_exp_rel p_2 (SND x)’
  \\ pop_assum kall_tac
  \\ gs [SND_THM] \\ pairarg_tac \\ gs []
  \\ Cases_on ‘∃exp1. p_2 = Delay exp1’
  \\ gs [full_exp_rel_def, unfold_Delay_Lam_def]
  >- (Cases_on ‘is_Lam exp1’ \\ gvs []
      >- (Cases_on ‘exp1’ \\ gs [is_Lam_def, full_exp_rel_def]
          >- (rename1 ‘_ ∨ _ = Lam s exp ∨ _’
              \\ qexists_tac ‘Lam s exp’
              \\ gs [full_exp_rel_def])
          \\ irule_at Any full_exp_rel_Delay
          \\ irule_at Any full_exp_rel_Var
          \\ gvs [])
      >- (qexists_tac ‘Delay exp1’
          \\ gs []
          \\ gs [full_exp_rel_def]
          \\ first_assum $ irule_at Any
          \\ Cases_on ‘exp1’ \\ gs [is_Lam_def, full_exp_rel_def]))
  \\ qexists_tac ‘p_2’
  \\ conj_tac
  >- (Cases_on ‘p_2’ \\ gs []
      \\ gs [full_exp_rel_def, unfold_Delay_Lam_def])
  \\ rename1 ‘full_exp_rel _ y’
  \\ Cases_on ‘y’ \\ gs [unfold_Delay_Lam_def]
  \\ Cases_on ‘p_2’ \\ gs [full_exp_rel_def]
QED

Theorem MEM_FLAT_MAP2_obtain:
  ∀l1 l2 vL v e2. LIST_REL full_exp_rel (MAP SND l1) (MAP SND l2) ∧
       LENGTH l1 = LENGTH vL ∧ MAP FST l1 = MAP FST l2 ∧
       MEM (v, e2) l1 ⇒
      ∃e1 v. MEM (v, e1) (FLAT (MAP2 unfold_Delay_Lam l2 (ZIP (vL, GENLIST (K T) (LENGTH vL))))) ∧
           boundvars e1 = boundvars e2
Proof
  Induct using SNOC_INDUCT \\ gvs [FORALL_PROD]
  \\ gen_tac \\ gen_tac
  \\ gen_tac \\ rename1 ‘LIST_REL _ (MAP SND (SNOC _ _)) (MAP SND l2)’
  \\ qspec_then ‘l2’ assume_tac SNOC_CASES \\ gs []
  \\ gen_tac \\ rename1 ‘SUC (LENGTH _) = LENGTH vL’
  \\ qspec_then ‘vL’ assume_tac SNOC_CASES \\ gs [LIST_REL_SNOC, MAP_SNOC]
  \\ once_rewrite_tac [ADD_SYM]
  \\ gs [GSYM arithmeticTheory.SUC_ONE_ADD, GENLIST, SNOC_APPEND, GSYM ZIP_APPEND]
  \\ simp [MAP2_APPEND, LIST_REL_EL_EQN]
  \\ gs [LIST_REL_EL_EQN]
  \\ rw []
  \\ last_x_assum $ drule_then assume_tac
  \\ rpt $ pop_assum $ drule_then assume_tac
  \\ gvs [MAP2_APPEND]
  >- (gs [SND_THM] \\ pairarg_tac \\ gs []
      \\ rename1 ‘full_exp_rel e2 _’
      \\ drule_then assume_tac $ GSYM full_exp_rel_boundvars
      \\ Cases_on ‘e2’
      \\ gs [full_exp_rel_def, unfold_Delay_Lam_def]
      >~[‘is_Lam _’]
      >- (IF_CASES_TAC \\ gs []
          >- (rename1 ‘_ = Delay y2’
              \\ qexists_tac ‘y2’
              \\ gs [boundvars_def]
              \\ metis_tac [])
          \\ rename1 ‘¬is_Lam y2’
          \\ qexists_tac ‘Delay y2’ \\ gs [boundvars_def]
          \\ metis_tac [])
      \\ metis_tac [])
  \\ metis_tac []
QED

Theorem LIST_REL_FLAT:
  ∀l1 l2 R. LIST_REL (LIST_REL R) l1 l2 ⇒ LIST_REL R (FLAT l1) (FLAT l2)
Proof
  Induct \\ gvs [LIST_REL_CONS1, PULL_EXISTS]
  \\ rw []
  \\ last_x_assum $ dxrule
  \\ drule_then assume_tac LIST_REL_LENGTH
  \\ gvs [LIST_REL_APPEND_EQ]
QED

Theorem LIST_REL_full_exp_rel_MAP_unfold_Delay_Lam:
  ∀expL1 expL2 vL.
    EVERY ok_bind (MAP SND expL1) ∧
    LIST_REL full_exp_rel (MAP SND expL1) (MAP SND expL2) ∧ LENGTH expL1 = LENGTH vL ⇒
         LIST_REL full_exp_rel
          (FLAT
             (MAP (MAP SND)
                (MAP2 unfold_Delay_Lam expL1
                   (ZIP (vL,GENLIST (K T) (LENGTH vL))))))
          (FLAT
             (MAP (MAP SND)
                (MAP2 unfold_Delay_Lam expL2
                   (ZIP (vL,GENLIST (K T) (LENGTH vL))))))
Proof
  rw []
  \\ irule LIST_REL_FLAT
  \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_MAP2, EVERY_EL]
  \\ gen_tac \\ rename1 ‘n < _’
  \\ rpt $ last_x_assum $ qspec_then ‘n’ assume_tac
  \\ gs [SND_THM]
  \\ pairarg_tac \\ simp [EL_ZIP]
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ strip_tac \\ conj_asm1_tac
  >- (Cases_on ‘SND (EL n expL1)’
      \\ gvs [full_exp_rel_def, unfold_Delay_Lam_def]
      \\ rename1 ‘EL n expL1 = (_, Delay e4)’
      \\ Cases_on ‘e4’ \\ gvs [is_Lam_def, full_exp_rel_def])
  \\ rw [EL_MAP] \\ gs []
  \\ Cases_on ‘SND (EL n expL1)’ \\ gvs [ok_bind_def, full_exp_rel_def, unfold_Delay_Lam_def]
  \\ rename1 ‘EL n expL1 = (_, Delay e4)’
  \\ Cases_on ‘e4’ \\ gvs [is_Lam_def, full_exp_rel_def]
  >- (rename1 ‘EL n2 [_; _]’ \\ Cases_on ‘n2’ \\ gvs [full_exp_rel_def]
      \\ rename1 ‘SUC n2 < 2’ \\ Cases_on ‘n2’ \\ gvs [full_exp_rel_def])
  >- (disj2_tac \\ metis_tac [])
  >- (disj2_tac \\ metis_tac [])
QED

Theorem FOLDL_replace_Force_comm1:
  ∀l e map h. ¬MEM h l ∧ DISJOINT ({h} ∪ set l) (FRANGE $ to_fmap map) ∧ {h} ∪ set l ⊆ (FDOM $ to_fmap map) ⇒
              FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e)
               (replace_Force (Var (explode (to_fmap map ' h))) (explode h) e) l
              = replace_Force (Var (explode (to_fmap map ' h))) (explode h)
                              (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) e l)
Proof
  Induct \\ gvs []
  \\ rw []
  \\ irule EQ_TRANS \\ last_x_assum $ irule_at $ Pos last
  \\ simp []
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ irule replace_Force_COMM
  \\ gvs [freevars_def]
  \\ conj_tac \\ strip_tac
  >- (first_x_assum irule
      \\ simp [IN_FRANGE]
      \\ metis_tac [])
  >- (qpat_x_assum ‘_ ∉ FRANGE _’ kall_tac
      \\ qpat_x_assum ‘_ ∉ FRANGE _’ irule
      \\ simp [IN_FRANGE]
      \\ metis_tac [])
QED

Theorem FOLDL_replace_Force_comm:
  ∀l1 l2 map e. ALL_DISTINCT (l1 ++ l2) ∧ DISJOINT (set (l1 ++ l2)) (FRANGE (to_fmap map)) ∧
                set (l1 ++ l2) ⊆ FDOM (to_fmap map) ⇒
                FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) e (l1 ++ l2)
                = FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) e (l2 ++ l1)
Proof
  Induct \\ gs [FOLDL_APPEND]
  \\ rw []
  \\ irule EQ_TRANS
  \\ last_x_assum $ irule_at Any
  \\ simp [] \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ irule FOLDL_replace_Force_comm1
  \\ simp []
QED

Theorem boundvars_Delay:
  ∀e. boundvars (Delay e) = boundvars e
Proof
  simp [boundvars_def]
QED

Theorem letrec_split_vc_growing:
  ∀l1 vc1 m l2 vc2 m2.
    letrec_split l1 vc1 m = (l2, vc2, m2) ∧ vars_ok vc1
    ⇒ vars_ok vc2 ∧ set_of vc1 ⊆ set_of vc2
Proof
  Induct \\ gs [letrec_split_def, FORALL_PROD]
  \\ rpt $ gen_tac \\ CASE_TAC
  \\ gvs []
  >- (strip_tac \\ pairarg_tac
      \\ rename1 ‘letrec_split _ _ _ = (_, vc, _)’
      \\ Cases_on ‘vc’ \\ gs []
      \\ last_x_assum $ drule_then assume_tac
      \\ gs [])
  >- (strip_tac \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ rename1 ‘invent_var _ _ = (_, var_creator')’
      \\ Cases_on ‘var_creator'’ \\ gs []
      \\ last_x_assum $ drule_then assume_tac
      \\ dxrule_then assume_tac invent_var_thm
      \\ gs [SUBSET_DEF])
QED

Theorem split_Delayed_Lam_vc_growing_lemma:
  ∀l. (∀m. m < list_size cexp_size l ⇒
           ∀e. m = cexp_size e ⇒
                ∀vc m e2 vc2.
                  split_Delayed_Lam e vc m = (e2,vc2) ∧ vars_ok vc ⇒
                  set_of vc ⊆ set_of vc2 ∧ vars_ok vc2) ⇒
      ∀vc m l2 vc2.
        FOLDR (λe (l', vc').
                 let (e', vc'') = split_Delayed_Lam e vc' m in
                   (e'::l', vc'')) ([], vc) l = (l2, vc2) ∧ vars_ok vc ⇒
        set_of vc ⊆ set_of vc2 ∧ vars_ok vc2
Proof
  Induct \\ gs []
  \\ gen_tac \\ strip_tac
  \\ last_x_assum mp_tac
  \\ impl_tac
  >- (gen_tac \\ strip_tac \\ rename1 ‘m < _’
      \\ last_x_assum $ qspec_then ‘m’ assume_tac
      \\ gs [cexp_size_def])
  \\ last_x_assum $ qspec_then ‘cexp_size h’ assume_tac
  \\ gs [cexp_size_def]
  \\ last_x_assum $ qspec_then ‘h’ assume_tac
  \\ strip_tac
  \\ rpt $ gen_tac
  \\ strip_tac
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ first_x_assum $ drule_then assume_tac
  \\ last_x_assum $ drule_then assume_tac
  \\ gs []
  \\ metis_tac [SUBSET_TRANS]
QED

Theorem split_Delayed_Lam_vc_growing_lemma2:
  ∀l. (∀m. m < list_size (pair_size mlstring_size cexp_size) l ⇒
           ∀e. m = cexp_size e ⇒
                ∀vc m e2 vc2.
                  split_Delayed_Lam e vc m = (e2,vc2) ∧ vars_ok vc ⇒
                  set_of vc ⊆ set_of vc2 ∧ vars_ok vc2) ⇒
      ∀vc m l2 vc2 binds' vc1 m2.
        letrec_split l vc m = (binds', vc1, m2) ∧
        FOLDR (λ(v, e) (l', vc').
                 let (e', vc'') = split_Delayed_Lam e vc' m2 in
                   ((v, e')::l', vc'')) ([], vc1) binds' = (l2, vc2) ∧ vars_ok vc ⇒
        set_of vc ⊆ set_of vc2 ∧ vars_ok vc2
Proof
  Induct \\ gs [letrec_split_def]
  \\ gen_tac \\ strip_tac
  \\ last_x_assum mp_tac
  \\ impl_tac
  >- (gen_tac \\ strip_tac \\ rename1 ‘m < _’
      \\ last_x_assum $ qspec_then ‘m’ assume_tac
      \\ gs [cexp_size_def])
  \\ last_x_assum $ qspec_then ‘cexp_size (SND h)’ assume_tac
  \\ Cases_on ‘h’
  \\ gs [cexp_size_def]
  \\ rename1 ‘cexp_size h1’
  \\ last_x_assum $ qspec_then ‘h1’ assume_tac
  \\ strip_tac
  \\ rpt $ gen_tac
  \\ strip_tac
  \\ gs [letrec_split_def]
  \\ Cases_on ‘dest_Delay_Lam h1’ \\ gs []
  >- (pairarg_tac \\ gs []
      \\ first_x_assum $ drule_then assume_tac
      \\ qpat_x_assum ‘_::_ = _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM
      \\ gs []
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ last_x_assum $ drule_then assume_tac
      \\ gs [] \\ metis_tac [SUBSET_TRANS])
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ qpat_x_assum ‘_::_ = _’ assume_tac
  \\ dxrule_then assume_tac EQ_SYM
  \\ gs []
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ last_x_assum $ dxrule_then $ dxrule_then assume_tac
  \\ Cases_on ‘h1’ \\ gs [dest_Delay_Lam_def]
  \\ gs [split_Delayed_Lam_def]
  \\ rename1 ‘Delay c’
  \\ Cases_on ‘c’ \\ gs [dest_Delay_Lam_def]
  \\ last_x_assum $ qspecl_then [‘vc''’, ‘m2’] assume_tac
  \\ dxrule_then assume_tac invent_var_thm
  \\ gs [SUBSET_DEF]
QED

Theorem split_Delayed_Lam_vc_growing_lemma3:
  ∀l. (∀m. m < list_size (pair_size mlstring_size
                          (pair_size (list_size mlstring_size) cexp_size)) l ⇒
           ∀e. m = cexp_size e ⇒
                ∀vc m e2 vc2.
                  split_Delayed_Lam e vc m = (e2,vc2) ∧ vars_ok vc ⇒
                  set_of vc ⊆ set_of vc2 ∧ vars_ok vc2) ⇒
      ∀vc m l2 vc2.
        FOLDR (λ(v, vL, e) (l', vc').
                 let (e', vc'') = split_Delayed_Lam e vc' (FOLDL delete m vL) in
                   ((v, vL, e')::l', vc'')) ([], vc) l = (l2, vc2) ∧ vars_ok vc ⇒
        set_of vc ⊆ set_of vc2 ∧ vars_ok vc2
Proof
  Induct \\ gs []
  \\ gen_tac \\ strip_tac
  \\ last_x_assum mp_tac
  \\ impl_tac
  >- (gen_tac \\ strip_tac \\ rename1 ‘m < _’
      \\ last_x_assum $ qspec_then ‘m’ assume_tac
      \\ gs [cexp_size_def])
  \\ last_x_assum $ qspec_then ‘cexp_size (SND (SND h))’ assume_tac
  \\ Cases_on ‘SND h’ \\ Cases_on ‘h’ \\ gs []
  \\ gs [cexp_size_def]
  \\ rename1 ‘cexp_size expr’
  \\ last_x_assum $ qspec_then ‘expr’ assume_tac
  \\ strip_tac
  \\ rpt $ gen_tac
  \\ strip_tac
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ first_x_assum $ drule_then assume_tac
  \\ last_x_assum $ drule_then assume_tac
  \\ gs []
  \\ metis_tac [SUBSET_TRANS]
QED

Theorem split_Delayed_Lam_set_of_growing:
  ∀vc m e2 vc2. split_Delayed_Lam e vc m = (e2, vc2) ∧ vars_ok vc
                  ⇒ set_of vc ⊆ set_of vc2 ∧ vars_ok vc2
Proof
  completeInduct_on ‘cexp_size e’
  \\ Cases \\ gvs [split_Delayed_Lam_def]
  \\ strip_tac \\ gvs []
  >~[‘Prim op’]
  >- (pop_assum mp_tac
      \\ Induct_on ‘l’ \\ gs []
      \\ simp [cexp_size_def]
      \\ gen_tac \\ strip_tac
      \\ rpt $ gen_tac \\ strip_tac
      \\ irule_at Any SUBSET_TRANS
      \\ last_x_assum mp_tac
      \\ impl_tac
      >- (gen_tac \\ strip_tac
          \\ rename1 ‘value < _’
          \\ last_x_assum $ qspec_then ‘value’ assume_tac
          \\ gs [cexp_size_def])
      \\ rename [‘split_Delayed_Lam _ _ m’, ‘set_of vc ⊆ _’]
      \\ disch_then $ qspecl_then [‘vc’, ‘m’] assume_tac
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ first_x_assum $ irule_at (Pos hd)
      \\ last_x_assum irule
      \\ first_x_assum $ irule_at Any
      \\ gs [])
  >~[‘Monad op’]
  >- (pop_assum mp_tac
      \\ Induct_on ‘l’ \\ gs []
      \\ simp [cexp_size_def]
      \\ gen_tac \\ strip_tac
      \\ rpt $ gen_tac \\ strip_tac
      \\ irule_at Any SUBSET_TRANS
      \\ last_x_assum mp_tac
      \\ impl_tac
      >- (gen_tac \\ strip_tac
          \\ rename1 ‘value < _’
          \\ last_x_assum $ qspec_then ‘value’ assume_tac
          \\ gs [cexp_size_def])
      \\ rename [‘split_Delayed_Lam _ _ m’, ‘set_of vc ⊆ _’]
      \\ disch_then $ qspecl_then [‘vc’, ‘m’] assume_tac
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ first_x_assum $ irule_at (Pos hd)
      \\ last_x_assum irule
      \\ first_x_assum $ irule_at Any
      \\ gs [])
  >~[‘App’]
  >- (rpt $ gen_tac \\ strip_tac
      \\ pairarg_tac \\ gs []
      \\ last_assum $ qspec_then ‘cexp_size c’ mp_tac
      \\ simp [cexp_size_def]
      \\ disch_then $ qspec_then ‘c’ assume_tac
      \\ gs []
      \\ pop_assum $ dxrule_then assume_tac
      \\ gs []
      \\ irule_at Any SUBSET_TRANS
      \\ first_x_assum $ irule_at Any
      \\ irule split_Delayed_Lam_vc_growing_lemma
      \\ gs []
      \\ pairarg_tac \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ gen_tac \\ strip_tac
      \\ rename1 ‘value < _’
      \\ last_x_assum $ qspec_then ‘value’ assume_tac
      \\ gs [cexp_size_def])
  >~[‘Lam’]
  >- (rpt $ gen_tac \\ strip_tac
      \\ last_x_assum irule
      \\ pairarg_tac \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ simp [cexp_size_def])
  >~[‘Let opt e1 e2’]
  >- (rpt $ gen_tac \\ strip_tac
      \\ gs [PULL_FORALL]
      \\ last_assum $ qspec_then ‘e1’ assume_tac
      \\ last_x_assum $ qspec_then ‘e2’ assume_tac
      \\ gs [cexp_size_def]
      \\ Cases_on ‘opt’ \\ gs [split_Delayed_Lam_def]
      >- (pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ first_x_assum $ dxrule_then assume_tac
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gs []
          \\ metis_tac [SUBSET_TRANS])
      \\ Cases_on ‘dest_Delay_Lam e1’ \\ gs []
      >- (pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ first_x_assum $ dxrule_then assume_tac
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gs []
          \\ metis_tac [SUBSET_TRANS])
      >- (pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ Cases_on ‘e1’ \\ gs [dest_Delay_Lam_def, split_Delayed_Lam_def]
          \\ first_x_assum $ dxrule_then assume_tac
          \\ first_x_assum $ qspecl_then [‘vc'’, ‘m’] assume_tac
          \\ rename1 ‘dest_Delay_Lam (Delay c)’
          \\ Cases_on ‘c’ \\ gs [dest_Delay_Lam_def]
          \\ dxrule_then assume_tac invent_var_thm
          \\ gs []
          \\ metis_tac [SUBSET_TRANS]))
  >~[‘Letrec’]
  >- (rpt $ gen_tac \\ strip_tac
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs [cexp_size_def]
      \\ qspec_then ‘l’ mp_tac split_Delayed_Lam_vc_growing_lemma2
      \\ impl_tac
      >- (gen_tac \\ strip_tac
          \\ rename1 ‘value < _’
          \\ last_x_assum $ qspec_then ‘value’ assume_tac
          \\ gs [])
      \\ disch_then $ dxrule_then assume_tac
      \\ gs []
      \\ last_x_assum $ qspec_then ‘cexp_size c’ assume_tac \\ gs []
      \\ pop_assum $ qspec_then ‘c’ assume_tac \\ gs []
      \\ pop_assum $ dxrule_then assume_tac \\ gs []
      \\ metis_tac [SUBSET_TRANS])
  >~[‘Case’]
  >- (rpt $ gen_tac \\ strip_tac
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs [cexp_size_def]
      \\ qspec_then ‘l’ mp_tac split_Delayed_Lam_vc_growing_lemma3
      \\ impl_tac
      >- (gen_tac \\ strip_tac
          \\ rename1 ‘value < _’
          \\ last_x_assum $ qspec_then ‘value’ assume_tac
          \\ gs [])
      \\ gs []
      \\ disch_then $ dxrule_then assume_tac
      \\ BasicProvers.FULL_CASE_TAC \\ gvs[]
      \\ BasicProvers.FULL_CASE_TAC \\ gvs[]
      \\ pairarg_tac \\ gs []
      \\ rename1 ‘split_Delayed_Lam fall’
      \\ last_x_assum $ qspec_then ‘cexp_size fall’ assume_tac \\ gs [cexp_size_def]
      \\ pop_assum $ qspec_then ‘fall’ assume_tac \\ gs []
      \\ pop_assum $ dxrule_then assume_tac \\ gs []
      \\ metis_tac [SUBSET_TRANS]
      )
  >~[‘Delay’]
  >- (rpt $ gen_tac \\ strip_tac
      \\ last_x_assum irule
      \\ pairarg_tac \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ simp [cexp_size_def])
  >~[‘Force’]
  >-(rpt $ gen_tac \\ CASE_TAC
     >- (strip_tac
         \\ last_x_assum irule
         \\ pairarg_tac \\ gs []
         \\ first_x_assum $ irule_at Any
         \\ simp [cexp_size_def])
     >- (CASE_TAC \\ rw [] \\ simp []))
QED

Theorem FOLDR_split_vc_ok:
  ∀l vc map l2 vc2.
     FOLDR (λ(v,e) (l,vc). (λ(e2,vc2). ((v,e2)::l,vc2)) (split_Delayed_Lam e vc map))
           ([],vc) l = (l2,vc2) ∧ vars_ok vc
     ⇒ vars_ok vc2
Proof
  Induct \\ gs [FORALL_PROD]
  \\ rw []
  \\ pairarg_tac \\ gs []
  \\ rename1 ‘FOLDR _ _ _ = (_, vc)’
  \\ Cases_on ‘vc’ \\ gs []
  \\ last_x_assum $ dxrule_then assume_tac
  \\ pairarg_tac \\ gs []
  \\ dxrule_then assume_tac split_Delayed_Lam_set_of_growing
  \\ gs []
QED

Theorem boundvars_replace_Force_Var:
  ∀e v1 v2. boundvars (replace_Force (Var v1) v2 e) = boundvars e
Proof
  rw [SET_EQ_SUBSET, boundvars_replace_Force2]
  \\ mp_tac boundvars_replace_Force
  \\ rw [SUBSET_DEF]
  \\ first_x_assum $ dxrule_then assume_tac
  \\ gs [boundvars_def]
QED

Theorem letrec_split_soundness:
  ∀binds.
    (∀e. MEM e (MAP SND binds) ⇒
         ∀vc'⁴' map map_l' e_out' vc_out.
           split_Delayed_Lam e vc'⁴' map = (e_out',vc_out) ∧
           ALL_DISTINCT map_l' ∧ freevars (exp_of e) ⊆ set_of vc'⁴' ∧
           boundvars (exp_of e) ⊆ set_of vc'⁴' ∧
           IMAGE explode (set map_l') ⊆ set_of vc'⁴' ∧
           IMAGE explode (FRANGE (to_fmap map)) ⊆ set_of vc'⁴' ∧
           cexp_wf e ∧ DISJOINT (set map_l') (FRANGE (to_fmap map)) ∧
           DISJOINT (freevars (exp_of e))
                    (IMAGE explode (FRANGE (to_fmap map))) ∧
           DISJOINT (boundvars (exp_of e))
                    (IMAGE explode (FRANGE (to_fmap map))) ∧ map_ok map ∧
           cmp_of map = compare ∧ vars_ok vc'⁴' ∧
           FDOM (to_fmap map) = set map_l' ⇒
           ∃e2 e3.
             cns_arities e = cns_arities e_out' ∧
             set_of vc'⁴' ⊆ set_of vc_out ∧ vars_ok vc_out ∧
             freevars (exp_of e_out') ⊆ set_of vc_out ∧
             boundvars (exp_of e_out') ⊆ set_of vc_out ∧
             boundvars e2 ∩ COMPL (boundvars (exp_of e)) =
             set_of vc_out ∩ COMPL (set_of vc'⁴') ∧
             thunk_Delay_Lam$exp_rel (exp_of e) e2 ∧ full_exp_rel e2 e3 ∧ cexp_wf e_out' ∧
             exp_of e_out' =
             FOLDL (λe v.
                      replace_Force (Var (explode (to_fmap map ' v)))
                                    (explode v) e) e3 map_l')
    ⇒ ∀binds2 binds3 vc vc2 vc3 map map2 s mapl.
        letrec_split binds vc map = (binds2, vc2, map2) ∧ map_ok map ∧
        FOLDR (λ(v,e) (l, vc).(λ(e2, vc2). ((v, e2)::l, vc2)) (split_Delayed_Lam e vc map2))
              ([], vc2) binds2 = (binds3, vc3) ∧
        EVERY (cexp_wf o SND) binds ∧ vars_ok vc ∧ FINITE s ∧
        EVERY cexp_ok_bind (MAP SND binds) ∧
        EVERY (λ(v, e). explode v ∈ set_of vc ∧
                        explode v ∉ IMAGE explode (FRANGE (to_fmap map)) ∧
                        DISJOINT (freevars (exp_of e)) (IMAGE explode (FRANGE (to_fmap map))) ∧
                        DISJOINT (boundvars (exp_of e)) (IMAGE explode (FRANGE (to_fmap map))) ∧
                        freevars (exp_of e) ⊆ set_of vc ∧
                        boundvars (exp_of e) ⊆ set_of vc) binds ∧
        (∀v. v ∈ s ⇒ v ∈ set_of vc ∨ v ∉ set_of vc3) ∧
        ALL_DISTINCT (MAP FST binds) ∧ ALL_DISTINCT mapl ∧
        DISJOINT (FDOM (to_fmap map)) (FRANGE (to_fmap map)) ∧
        FDOM (to_fmap map) = set mapl ∧ cmp_of map = compare ∧
        IMAGE explode (FDOM (to_fmap map)) ⊆ set_of vc ∧
        IMAGE explode (FRANGE (to_fmap map)) ⊆ set_of vc
        ⇒ ∃vL expL1 expL2 mapl1 mapl2.
            BIGUNION (set (MAP (λ(v,e'). cns_arities e') binds))
            = BIGUNION (set (MAP (λ(v,e'). cns_arities e') binds3)) ∧
            ALL_DISTINCT (MAP FST expL1) ∧
            MAP (explode o FST) binds = MAP FST expL1 ∧
            MAP (explode o FST) binds = MAP FST expL2 ∧
            EVERY ok_bind (MAP SND expL1) ∧
            LIST_REL thunk_Delay_Lam$exp_rel (MAP (exp_of o SND) binds) (MAP SND expL1) ∧
            LIST_REL full_exp_rel (MAP SND expL1) (MAP SND expL2) ∧
            LENGTH binds = LENGTH vL ∧ ALL_DISTINCT vL ∧
            EVERY (λv. v ∉ s ∧ v ∉ set_of vc) vL ∧
            EVERY (λv. EVERY (λ(v2,e). v ∉ boundvars e) expL1) vL ∧
            vars_ok vc3 ∧ set_of vc2 ⊆ set_of vc3 ∧
            vars_ok vc2 ∧ set_of vc  ⊆ set_of vc2 ∧
            EVERY (λ(v, e). freevars (exp_of e) ⊆ set_of vc3 ∧ boundvars (exp_of e) ⊆ set_of vc3
                            ∧ explode v ∈ set_of vc3 ∧ cexp_wf e) binds3 ∧
            ALL_DISTINCT (MAP FST binds3) ∧ (binds ≠ [] ⇒ binds3 ≠ []) ∧
            LIST_REL (λ(v1, e1) (v2, e2). explode v1 = v2 ∧ exp_of e1 =
                              FOLDL (λe v. replace_Force (Var (explode (to_fmap map2 ' v)))
                                                         (explode v) e) e2 (mapl2 ++ mapl1))
                     binds3 (FLAT (MAP2 unfold_Delay_Lam expL2
                                                         (ZIP (vL,GENLIST (K T) (LENGTH vL))))) ∧
            EVERY (λv. explode (to_fmap map2 ' v) ∈ set_of vc3 ∧
                       explode (to_fmap map2 ' v) ∉ set_of vc) mapl2 ∧
            mapl1 = FILTER (λv. ¬MEM v (MAP FST binds)) mapl ∧
            EVERY (λv. MEM (explode v, Delay (Var $ explode (to_fmap map2 ' v)))
                           (FLAT (MAP2 unfold_Delay_Lam
                                  expL1 (ZIP (vL, GENLIST (K T) (LENGTH vL)))))
                      ∧ MEM (explode (to_fmap map2 ' v)) $ MAP FST
                             (FLAT (MAP2 unfold_Delay_Lam
                                    expL1 (ZIP (vL, GENLIST (K T) (LENGTH vL)))))) mapl2 ∧
            ALL_DISTINCT (mapl1 ++ mapl2) ∧
            DISJOINT (FDOM $ to_fmap map2) (FRANGE $ to_fmap map2) ∧
            DISJOINT (IMAGE explode (FRANGE $ to_fmap map2))
                     (BIGUNION $ set (MAP boundvars
                        (MAP SND (FLAT (MAP2 unfold_Delay_Lam
                                        expL2 (ZIP (vL, GENLIST (K T) (LENGTH vL)))))))) ∧
            IMAGE explode (FDOM $ to_fmap map2) ⊆ set_of vc ∧
            IMAGE explode (FRANGE (to_fmap map2)) ⊆ set_of vc3 ∧
            FDOM (to_fmap map2) = set (mapl1 ++ mapl2) ∧ cmp_of map2 = compare ∧ map_ok map2 ∧
            set mapl2 ⊆ set (MAP FST binds3) ∧
            EVERY cexp_ok_bind (MAP SND binds3) ∧
            ALL_DISTINCT (MAP FST (FLAT (MAP2 unfold_Delay_Lam
                                         expL1 (ZIP (vL, GENLIST (K T) (LENGTH vL)))))) ∧
            FILTER (λv. ¬MEM (explode v) (MAP FST (FLAT (MAP2 unfold_Delay_Lam expL2
                                                         (ZIP (vL,GENLIST (K T) (LENGTH vL))))))) mapl
            = FILTER (λv. ¬MEM v (MAP FST binds)) mapl ∧
            EVERY (λv. to_fmap map ' v = to_fmap map2 ' v) mapl1 ∧
            (BIGUNION (set (MAP (boundvars o exp_of o SND) binds3)) ∪ set (MAP (explode o FST) binds3))
            ∩ COMPL (BIGUNION (set (MAP (boundvars o exp_of o SND) binds)) ∪ set (MAP (explode o FST) binds))
            = set_of vc3 ∩ COMPL (set_of vc)
Proof

  Induct \\ gvs [letrec_split_def, FORALL_PROD, GENLIST_K_T]
  >- (rw [] \\ gvs [])
  \\ rpt $ gen_tac \\ CASE_TAC \\ rw []
  >- (pairarg_tac \\ gs []
      \\ qpat_x_assum ‘_::_ = _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM \\ gvs []
      \\ pairarg_tac \\ gs []
      \\ last_x_assum $ drule_then mp_tac
      \\ simp [delete_thm]
      \\ pairarg_tac \\ gs []
      \\ rename1 ‘split_Delayed_Lam _ vc _ = (e2, _, _)’
      \\ Cases_on ‘vc’ \\ gs []
      \\ rename1 ‘split_Delayed_Lam _ (vcf, vcs) _ = (e2, _, _)’
      \\ rename1 ‘FINITE s’
      \\ disch_then $ qspecl_then [‘s ∪ (boundvars (exp_of e2) DIFF (set_of (vcf, vcs)))’,
                                   ‘FILTER (λv. v ≠ p_1) mapl’] mp_tac
      \\ impl_tac
      >- (gs [SUBSET_DEF, DISJOINT_ALT, PULL_EXISTS, FILTER_ALL_DISTINCT, FINITE_boundvars]
          \\ rw []
          >- (gs [EVERY_MEM] \\ rw []
              \\ first_x_assum $ dxrule_then assume_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ conj_tac
              >- (strip_tac \\ qpat_x_assum ‘v ∉ FRANGE _’ irule
                  \\ gs [IN_FRANGE, DOMSUB_FAPPLY_THM]
                  \\ first_x_assum $ irule_at Any \\ gs [])
              \\ rw [] \\ first_x_assum $ drule_then assume_tac
              \\ strip_tac
              \\ gs [IN_FRANGE, DOMSUB_FAPPLY_THM])
          >- (first_x_assum $ dxrule_then assume_tac \\ gs []
              \\ dxrule_then assume_tac split_Delayed_Lam_set_of_growing
              \\ drule_then assume_tac FOLDR_split_vc_ok
              \\ dxrule_then assume_tac letrec_split_vc_growing
              \\ gs []
              \\ disj2_tac \\ strip_tac
              \\ gvs [SUBSET_DEF])
          >- simp []
          >- (last_x_assum $ dxrule_then assume_tac
              \\ gs [IN_FRANGE, DOMSUB_FAPPLY_THM]
              \\ rw [] \\ gs [])
          >- simp [SET_EQ_SUBSET, SUBSET_DEF, MEM_FILTER]
          >- (first_x_assum irule
              \\ gs [IN_FRANGE, DOMSUB_FAPPLY_THM]
              \\ metis_tac []))
      \\ disch_then $ qx_choose_then ‘vL’ $ qx_choose_then ‘expL1’ $ qx_choose_then ‘expL2’
                    $ qx_choose_then ‘mapl2’ assume_tac
      \\ rename1 ‘dest_Delay_Lam p2 = NONE’
      \\ last_x_assum $ qspec_then ‘p2’ assume_tac \\ gs []
      \\ pop_assum $ dxrule_then
                   $ qspec_then ‘FILTER (λv. ¬MEM v (MAP FST binds) ∧ v ≠ p_1) mapl ++ mapl2’
                   mp_tac
      \\ gs [FILTER_FILTER]
      \\ impl_tac
      >- (rw []
          >- metis_tac [SUBSET_TRANS]
          >- metis_tac [SUBSET_TRANS]
          >- gvs [SUBSET_DEF, PULL_EXISTS, MEM_FILTER]
          >- metis_tac [SUBSET_TRANS]
          >- (gs [DISJOINT_ALT, EVERY_MEM]
              \\ rw [] \\ strip_tac
              \\ gs [IN_FRANGE]
              >- (dxrule_then assume_tac EQ_SYM
                  \\ last_x_assum $ dxrule_then assume_tac
                  \\ gs []
                  \\ rename1 ‘to_fmap _ ' k’
                  \\ pop_assum $ qspec_then ‘k’ assume_tac
                  \\ qpat_x_assum ‘∀x. MEM _ (FILTER _ _) ⇒ _’ $ drule_then assume_tac
                  \\ gs [DOMSUB_FAPPLY_THM, MEM_FILTER])
              \\ last_x_assum $ drule_then assume_tac
              \\ pop_assum kall_tac
              \\ last_x_assum $ drule_then assume_tac
              \\ gvs [SUBSET_DEF])
          >- (gs [DISJOINT_ALT, EVERY_MEM]
              \\ rw [] \\ strip_tac
              \\ gs [IN_FRANGE]
              >- (dxrule_then assume_tac EQ_SYM
                  \\ last_x_assum $ dxrule_then assume_tac
                  \\ gs []
                  \\ rename1 ‘to_fmap _ ' k’
                  \\ pop_assum $ qspec_then ‘k’ assume_tac
                  \\ qpat_x_assum ‘∀x. MEM _ (FILTER _ _) ⇒ _’ $ drule_then assume_tac
                  \\ gs [DOMSUB_FAPPLY_THM, MEM_FILTER])
              \\ last_x_assum $ drule_then assume_tac
              \\ pop_assum kall_tac
              \\ last_x_assum $ drule_then assume_tac
              \\ gvs [SUBSET_DEF]))
      \\ disch_then $ qx_choose_then ‘expr2’ $ qx_choose_then ‘expr3’ assume_tac \\ gs []
      \\ Q.REFINE_EXISTS_TAC ‘_::vL’ \\ simp [PULL_EXISTS]
      \\ rename1 ‘FINITE s’
      \\ ‘∃v. ¬MEM v vL ∧ v ∉ s ∧ v ∉ set_of (vcf, vcs) ∧
              v ∉ boundvars expr2 ∧ v ∉ BIGUNION (set (MAP (λ(v, e). boundvars e) expL1))’
        by  (‘INFINITE 𝕌(:string)’ by simp []
             \\ dxrule_then assume_tac $ iffLR NOT_IN_FINITE
             \\ pop_assum $ qspec_then ‘set vL ∪ s ∪ set_of (vcf, vcs) ∪
                      boundvars expr2 ∪ BIGUNION (set (MAP (λ(v,e). boundvars e) expL1))’ assume_tac
             \\ gvs [GSYM CONJ_ASSOC]
             \\ pop_assum irule
             \\ gvs [set_of_def, FINITE_boundvars, MEM_MAP, PULL_EXISTS, FORALL_PROD])
      \\ first_x_assum $ irule_at Any
      \\ gs []
      \\ rename1 ‘LIST_REL thunk_Delay_Lam$exp_rel _ (MAP SND expL1)’
      \\ qexists_tac ‘MAP SND expL1’ \\ simp []
      \\ once_rewrite_tac [CONJ_COMM]
      \\ rename1 ‘_ ≠ p_1 ∧ ¬MEM _ (MAP FST binds)’
      \\ ‘FILTER (λv. ¬MEM v (MAP FST binds) ∧ v ≠ p_1) mapl
          = FILTER (λv. v ≠ p_1 ∧ ¬MEM v (MAP FST binds)) mapl’
        by simp [CONJ_COMM]
      \\ gs []
      \\ qpat_assum ‘ALL_DISTINCT (_ ++ _)’ $ irule_at Any
      \\ qpat_assum ‘exp_rel _ _’ $ irule_at Any
      \\ Q.REFINE_EXISTS_TAC ‘(_, expr3)::expL2’ \\ simp []
      \\ Q.REFINE_EXISTS_TAC ‘(_, expr2)::expL1’ \\ simp []
      \\ qpat_x_assum ‘_::_ = _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM \\ gvs []
      \\ rw [GENLIST_K_T]
      >- (qpat_x_assum ‘MAP (explode o FST) _ = _’ assume_tac
          \\ dxrule_then assume_tac EQ_SYM \\ gs []
          \\ strip_tac \\ gvs [MEM_MAP])
      >- (rename1 ‘exp_rel (exp_of p2) _’
          \\ Cases_on ‘p2’
          \\ gs [cexp_ok_bind_def, cexp_wf_def, exp_of_def, Lams_split, exp_rel1_def])
      >- (strip_tac \\ gs [SUBSET_DEF])
      >- gs [EVERY_CONJ]
      >- (simp [EVERY_MEM, FORALL_PROD]
          \\ rw [] \\ rename1 ‘MEM (var, expr) _’
          \\ first_x_assum $ qspec_then ‘boundvars expr’ assume_tac
          \\ gs [MEM_MAP, FORALL_PROD]
          \\ pop_assum $ qspecl_then [‘var’, ‘expr’] assume_tac \\ gs [])
      >- (gs [EVERY_CONJ, boundvars_FOLDL_replace_Force]
          \\ dxrule_then assume_tac full_exp_rel_boundvars
          \\ rpt $ qpat_x_assum ‘EVERY _ vL’ mp_tac
          \\ qpat_x_assum ‘boundvars _ ∩ COMPL _ = _’ mp_tac
          \\ qpat_x_assum ‘boundvars (exp_of _) ⊆ _’ mp_tac
          \\ simp []
          \\ rpt $ pop_assum kall_tac
          \\ rw [] \\ gs [EVERY_MEM]
          \\ rw [] \\ strip_tac
          \\ rpt $ first_x_assum $ drule_then assume_tac \\ gs []
          \\ gs [SET_EQ_SUBSET, SUBSET_DEF]
          \\ rename1 ‘var ∈ _’
          \\ rpt $ last_x_assum $ qspec_then ‘var’ assume_tac
          \\ gs [])
      >- metis_tac [SUBSET_TRANS]
      >- gvs [SUBSET_DEF]
      >- (gs [EVERY_MEM] \\ gen_tac \\ strip_tac
          \\ last_x_assum $ dxrule_then assume_tac
          \\ pairarg_tac \\ gvs [SUBSET_DEF])
      >- (gs [LIST_REL_EL_EQN]
          \\ strip_tac \\ gs [MEM_EL]
          \\ first_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs [EL_MAP]
          \\ qspecl_then [‘expL2’, ‘vL’, ‘GENLIST (K T) (LENGTH vL)’] assume_tac Letrec_Delay_SUBSET
          \\ gs [SUBSET_DEF, MEM_EL, PULL_EXISTS]
          \\ pop_assum $ drule_then assume_tac
          \\ gs [EL_MAP]
          >- (rename1 ‘n2 < LENGTH expL2’
              \\ last_x_assum $ qspec_then ‘n2’ assume_tac \\ gs [EL_MAP]
              \\ ‘EL n2 (MAP FST expL1) = EL n2 (MAP (explode o FST) binds)’ by simp []
              \\ gs [EL_MAP])
          >- gs [EVERY_EL])
      >- (qpat_x_assum ‘LIST_REL exp_rel _ _’ kall_tac
          \\ qpat_x_assum ‘LIST_REL full_exp_rel _ _’ kall_tac
          \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
          \\ simp []
          \\ disch_then $ irule_at Any
          \\ simp [EXISTS_PROD]
          \\ dxrule_all_then assume_tac unfold_Delay_Lam_Eq
          \\ gs [FOLDL_replace_Force_comm])
      >- (gvs [EVERY_MEM]
          \\ gvs [SUBSET_DEF])
      >- gs [EVERY_MEM]
      >- (drule_all_then assume_tac unfold_Delay_Lam_Eq
          \\ gs []
          \\ qpat_x_assum ‘EVERY (λv. _ ∈ _ ∧ _ ∉ _) _’ mp_tac
          \\ qpat_x_assum ‘EVERY (λv. _ = _) _’ mp_tac
          \\ qpat_x_assum ‘DISJOINT (boundvars _) (IMAGE explode (FRANGE _))’ mp_tac
          \\ dxrule thunk_Delay_LamTheory.exp_rel_boundvars
          \\ dxrule full_exp_rel_boundvars
          \\ qpat_x_assum ‘boundvars _ ∩ _ = _ ∩ _’ mp_tac
          \\ qpat_x_assum ‘IMAGE explode (FRANGE _) ⊆ _’ kall_tac
          \\ qpat_x_assum ‘IMAGE explode (FRANGE _) ⊆ _’ mp_tac
          \\ rpt $ qpat_x_assum ‘set_of _ ⊆ set_of _’ mp_tac
          \\ qpat_x_assum ‘FDOM _ = _ ∪ _’ mp_tac
          \\ qpat_x_assum ‘FDOM _ = _ ’ mp_tac
          \\ qpat_x_assum ‘boundvars (exp_of _) ⊆ _’ mp_tac
          \\ rpt $ pop_assum kall_tac
          \\ rw [EVERY_MEM]
          \\ gs [DISJOINT_ALT, IN_FRANGE, PULL_EXISTS]
          \\ rw [] \\ strip_tac
          \\ gs [SUBSET_DEF, SET_EQ_SUBSET]
          >- (first_x_assum $ drule_then assume_tac
              \\ dxrule_then assume_tac EQ_SYM
              \\ gs [MEM_FILTER, DOMSUB_FAPPLY_THM, PULL_EXISTS]
              \\ rename1 ‘explode (to_fmap map' ' k) ∈ _’
              \\ rpt $ first_x_assum $ qspec_then ‘explode (to_fmap map' ' k)’ assume_tac
              \\ last_x_assum $ qspec_then ‘k’ assume_tac
              \\ last_x_assum $ qspec_then ‘k’ assume_tac
              \\ last_x_assum kall_tac
              \\ last_x_assum kall_tac
              \\ last_x_assum kall_tac
              \\ rpt $ first_x_assum $ qspec_then ‘to_fmap map' ' k’ assume_tac
              \\ gs [IN_FRANGE, PULL_EXISTS]
              \\ pop_assum $ qspec_then ‘k’ assume_tac \\ gs [])
          >- (first_x_assum $ dxrule_then assume_tac
              \\ gs []
              \\ rename1 ‘explode (to_fmap map2 ' k) ∈ _’
              \\ rpt $ first_x_assum $ qspec_then ‘explode (to_fmap map2 ' k)’ assume_tac
              \\ gs []))
      >- gvs []
      >- metis_tac [SUBSET_TRANS]
      >- gs [SUBSET_DEF]
      >- (rename1 ‘exp_rel (exp_of p2)’
          \\ Cases_on ‘p2’
          \\ gs [cexp_ok_bind_def, cexp_wf_def, Lams_split, exp_rel1_def, exp_rel2_def]
          >- (gs [FOLDL_replace_Force_Lam]
              \\ rename1 ‘cexp_ok_bind e2’
              \\ Cases_on ‘e2’ \\ gs [cexp_wf_def, cexp_ok_bind_def]
              >- (rename1 ‘Apps _ (MAP _ list)’
                  \\ qspec_then ‘list’ assume_tac SNOC_CASES
                  \\ gs [exp_of_def, FOLDL_MAP, FOLDL_SNOC])
              >- (rename1 ‘rows_of _ (MAP _ list) (OPTION_MAP _ fall)’
                  \\ Cases_on ‘list’ \\ gs [rows_of_def, FOLDL_APPEND]
                  \\ pairarg_tac \\ gs [rows_of_def]))
          >- (gs [FOLDL_replace_Force_Delay]
              \\ rename1 ‘cexp_ok_bind e2’
              \\ Cases_on ‘e2’ \\ gs [cexp_wf_def, cexp_ok_bind_def]
              >- (rename1 ‘Apps _ (MAP _ list)’
                  \\ qspec_then ‘list’ assume_tac SNOC_CASES
                  \\ gs [exp_of_def, FOLDL_MAP, FOLDL_SNOC])
              >- (rename1 ‘rows_of _ (MAP _ list) (OPTION_MAP _ fall)’
                  \\ Cases_on ‘list’ \\ gs [rows_of_def, FOLDL_APPEND]
                  \\ pairarg_tac \\ gs [rows_of_def])))
      >- (gs [ALL_DISTINCT_APPEND]
          \\ drule_all_then assume_tac unfold_Delay_Lam_Eq2
          \\ gs []
          \\ qspecl_then [‘expL1’, ‘expL2’, ‘vL’] assume_tac MAP_FST_change_expL
          \\ gs [] \\ gs [LIST_REL_EL_EQN]
          \\ strip_tac \\ gs [MEM_EL]
          \\ first_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs [EL_MAP]
          \\ qspecl_then [‘expL2’, ‘vL’, ‘GENLIST (K T) (LENGTH vL)’] assume_tac Letrec_Delay_SUBSET
          \\ gs [SUBSET_DEF, MEM_EL, PULL_EXISTS]
          \\ pop_assum $ drule_then assume_tac
          \\ gs [EL_MAP]
          >- (rename1 ‘n2 < LENGTH expL2’
              \\ last_x_assum $ qspec_then ‘n2’ assume_tac \\ gs [EL_MAP]
              \\ ‘EL n2 (MAP FST expL1) = EL n2 (MAP (explode o FST) binds)’ by simp []
              \\ gs [EL_MAP])
          >- gs [EVERY_EL])
      >- (drule_all_then assume_tac unfold_Delay_Lam_Eq
          \\ qpat_x_assum ‘FILTER _ _ = FILTER _ _’ mp_tac
          \\ qpat_x_assum ‘FILTER _ _ = FILTER _ _’ mp_tac
          \\ gs []
          \\ rpt $ pop_assum kall_tac \\ rw []
          \\ irule EQ_TRANS
          \\ last_x_assum $ irule_at Any
          \\ simp [CONJ_COMM])
      >- (qpat_x_assum ‘EVERY (λv. _ ' _ = _ ' _) _’ mp_tac
          \\ rpt $ pop_assum kall_tac
          \\ rw [EVERY_MEM]
          \\ first_x_assum $ drule_then assume_tac
          \\ gs [DOMSUB_FAPPLY_THM, MEM_FILTER])
      >- (qpat_x_assum ‘_ ∩ COMPL _ = _’ mp_tac
          \\ qpat_x_assum ‘_ ∩ COMPL _ = _’ mp_tac
          \\ rpt $ qpat_x_assum ‘set_of _ ⊆ set_of _’ mp_tac
          \\ qpat_x_assum ‘boundvars (exp_of _) ⊆ set_of _’ mp_tac
          \\ qpat_x_assum ‘explode _ ∈ set_of _’ mp_tac
          \\ qpat_x_assum ‘EVERY (λ(v,e). _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ boundvars (exp_of _) ⊆ _) _’ mp_tac
          \\ qpat_x_assum ‘MAP (explode o FST) _ = MAP FST _’ mp_tac
          \\ qpat_x_assum ‘LIST_REL full_exp_rel _ _’ mp_tac
          \\ dxrule full_exp_rel_boundvars
          \\ rpt $ pop_assum kall_tac
          \\ strip_tac \\ gvs [boundvars_FOLDL_replace_Force]
          \\ pop_assum kall_tac
          \\ gs [SET_EQ_SUBSET, GSYM DIFF_INTER_COMPL, DIFF_SUBSET]
          \\ rw []
          >- (gs [SUBSET_DEF] \\ rw []
              \\ first_x_assum $ drule_then mp_tac
              \\ first_x_assum $ drule_then mp_tac
              \\ strip_tac \\ simp [])
          >- (gs [SUBSET_DEF, PULL_EXISTS] \\ rw []
              \\ last_x_assum $ drule_then $ drule_then mp_tac
              \\ strip_tac \\ simp []
              \\ metis_tac [])
          >- (gs [SUBSET_DEF, PULL_EXISTS] \\ rw []
              \\ first_x_assum $ drule_then mp_tac
              \\ strip_tac \\ simp []
              \\ metis_tac [])
          >- (gs [SUBSET_DEF] \\ rw []
              \\ first_x_assum $ drule_then assume_tac
              \\ gs []
              \\ disj2_tac
              \\ strip_tac \\ gvs [])
          >- (gs [SUBSET_DEF, PULL_EXISTS] \\ rw []
              \\ last_x_assum $ drule_then $ drule_then mp_tac
              \\ strip_tac \\ simp []
              \\ metis_tac [])
          >- (gs [SUBSET_DEF, PULL_EXISTS] \\ rw []
              \\ first_x_assum $ drule_then mp_tac
              \\ strip_tac \\ simp []
              \\ metis_tac [])
          >- (gs [SUBSET_DEF] \\ rw []
              \\ first_x_assum $ drule_then mp_tac
              \\ first_x_assum $ drule_then mp_tac
              \\ strip_tac \\ simp []
              \\ metis_tac [])
          >- (gs [SUBSET_DEF, PULL_EXISTS, EVERY_MEM] \\ rw []
              \\ rename1 ‘var ∈ set_of (vc2f, vc2s) ∨ _’
              \\ Cases_on ‘var ∈ set_of (vc2f, vc2s)’ \\ gs []
              \\ rpt $ first_x_assum $ qspec_then ‘var’ assume_tac \\ gs []
              \\ strip_tac \\ gs []
              >- (gvs [MEM_MAP, MEM_EL, PULL_EXISTS]
                  \\ gen_tac
                  \\ rename1 ‘s = boundvars _’
                  \\ Cases_on ‘var ∈ s’ \\ gs []
                  \\ rw [] \\ strip_tac
                  \\ last_x_assum $ dxrule_then assume_tac
                  \\ pairarg_tac \\ gvs [])
              \\ conj_tac
              >- (strip_tac \\ gs [])
              >- (dxrule_then assume_tac EQ_SYM
                  \\ gs []
                  \\ gs [MEM_MAP, MEM_EL, PULL_EXISTS]
                  \\ rw [] \\ strip_tac
                  \\ last_x_assum $ dxrule_then assume_tac
                  \\ pairarg_tac \\ gs []))))

  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ qpat_x_assum ‘_::_ = _’ assume_tac
  \\ dxrule_then assume_tac EQ_SYM \\ gvs []
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ rename1 ‘letrec_split _ var_creator' _ = _’
  \\ Cases_on ‘var_creator'’ \\ gs []
  \\ last_x_assum $ drule_then mp_tac
  \\ simp [delete_thm]
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ rename1 ‘split_Delayed_Lam _ vc _ = (e2', _)’
  \\ Cases_on ‘vc’ \\ gs []
  \\ rename1 ‘letrec_split binds (vcf, vcs) _ = _’
  \\ rename1 ‘FINITE s’
  \\ rename1 ‘invent_var _ _ = (name2, _)’
  \\ rename1 ‘split_Delayed_Lam (Delay _) vc' _ = _’
  \\ Cases_on ‘vc'’ \\ gs []
  \\ rename1 ‘split_Delayed_Lam (Delay _) (vc2f, vc2s) _ = _’
  \\ disch_then $ qspecl_then [‘s ∪ (boundvars (exp_of e2') ∩ COMPL (set_of (vc2f, vc2s))) ∪ {explode name2}’,
                               ‘p_1::FILTER (λv. v ≠ p_1) mapl’] mp_tac
  \\ impl_tac
  >- (gs [SUBSET_DEF, DISJOINT_ALT, PULL_EXISTS, FILTER_ALL_DISTINCT, FINITE_boundvars, insert_thm]
      \\ dxrule_then assume_tac invent_var_thm \\ gs []
      \\ rw []
      >- (gs [EVERY_MEM] \\ rw []
          \\ first_x_assum $ dxrule_then assume_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ conj_tac
          >- (conj_tac
              >- (strip_tac \\ gs [])
              \\ strip_tac
              \\ qpat_x_assum ‘_ ∉ FRANGE _’ irule
              \\ gs [IN_FRANGE, DOMSUB_FAPPLY_THM]
              \\ first_x_assum $ irule_at Any \\ gs [])
          \\ rw [] \\ first_x_assum $ drule_then assume_tac
          \\ strip_tac
          \\ gs [IN_FRANGE, DOMSUB_FAPPLY_THM])
      >- (first_x_assum $ dxrule_then assume_tac \\ gs []
          \\ gs [split_Delayed_Lam_def]
          \\ dxrule_then assume_tac split_Delayed_Lam_set_of_growing
          \\ dxrule_then assume_tac FOLDR_split_vc_ok
          \\ dxrule_then assume_tac letrec_split_vc_growing
          \\ gs []
          \\ disj2_tac \\ strip_tac
          \\ gs [SUBSET_DEF])
      >- gs [split_Delayed_Lam_def]
      >- simp [MEM_FILTER]
      >- (strip_tac \\ gs [])
      >- (strip_tac \\ gs [IN_FRANGE, DOMSUB_FAPPLY_THM, PULL_EXISTS])
      >- (strip_tac \\ gs [])
      >- (last_x_assum $ dxrule_then assume_tac
          \\ strip_tac \\ first_x_assum irule
          \\ gs [IN_FRANGE, DOMSUB_FAPPLY_THM]
          \\ metis_tac [])
      >- (rpt $ pop_assum kall_tac
          \\ rw [SET_EQ_SUBSET, SUBSET_DEF, MEM_FILTER])
      >- simp []
      >- simp []
      >- (disj2_tac
          \\ first_x_assum irule
          \\ gs [IN_FRANGE, DOMSUB_FAPPLY_THM]
          \\ metis_tac []))
  \\ disch_then $ qx_choose_then ‘vL’ $ qx_choose_then ‘expL1’ $ qx_choose_then ‘expL2’
                $ qx_choose_then ‘mapl2’ assume_tac
  \\ rename1 ‘dest_Delay_Lam p2 = SOME _’
  \\ last_x_assum $ qspec_then ‘p2’ assume_tac \\ gs []
  \\ qpat_x_assum ‘split_Delayed_Lam (Delay (Var _)) _ _ = _’ mp_tac
  \\ simp [split_Delayed_Lam_def]
  \\ strip_tac \\ gvs []
  \\ Cases_on ‘p2’ \\ gs [dest_Delay_Lam_def]
  \\ rename1 ‘dest_Delay_Lam (Delay p2)’
  \\ Cases_on ‘p2’ \\ gs [dest_Delay_Lam_def]
  \\ gs [Once split_Delayed_Lam_def]
  \\ rename1 ‘split_Delayed_Lam p2 (vc3f, vc3s) map2 = (e2b, _, _)’
  \\ first_x_assum $ qspecl_then [‘vc3f’, ‘vc3s’, ‘map2’,
                                  ‘p_1::FILTER (λv. ¬MEM v (MAP FST binds) ∧ v ≠ p_1) mapl ++ mapl2’] mp_tac
  \\ gs [FILTER_FILTER]
  \\ impl_tac
  >- (dxrule_then assume_tac invent_var_thm \\ gs []
      \\ rw []
      >- metis_tac [SUBSET_TRANS]
      >- metis_tac [SUBSET_TRANS]
      >- gvs [SUBSET_DEF, PULL_EXISTS, MEM_FILTER]
      >- (irule SUBSET_TRANS
          \\ first_x_assum $ irule_at $ Pos hd
          \\ simp []
          \\ gvs [SUBSET_DEF])
      >- (irule SUBSET_TRANS
          \\ first_x_assum $ irule_at $ Pos hd
          \\ simp []
          \\ gvs [SUBSET_DEF])
      >- (qpat_x_assum ‘freevars _ ⊆ set_of _’ mp_tac
          \\ qpat_x_assum ‘EVERY (λv. _ ∈ _ ∧ _ ∧ _ ∉ _) _’ mp_tac
          \\ qpat_x_assum ‘FDOM _ = _ ∪ _’ mp_tac
          \\ qpat_x_assum ‘FDOM _ = _’ mp_tac
          \\ qpat_x_assum ‘EVERY (λv. _ ' _ = _ ' _) _’ mp_tac
          \\ qpat_x_assum ‘DISJOINT (freevars _) (IMAGE explode _)’ mp_tac
          \\ qpat_x_assum ‘_ ' _ = _ ' _’ mp_tac
          \\ qpat_x_assum ‘map_ok _’ mp_tac
          \\ qpat_x_assum ‘map_ok _’ mp_tac
          \\ qpat_x_assum ‘explode _ ∉ set_of _’ mp_tac
          \\ rpt $ pop_assum kall_tac
          \\ gs [DISJOINT_ALT, EVERY_MEM]
          \\ rw [] \\ strip_tac
          \\ gs [IN_FRANGE]
          >- gs [insert_thm, SUBSET_DEF]
          >- (dxrule_then assume_tac EQ_SYM
              \\ last_x_assum $ dxrule_then assume_tac
              \\ gs [insert_thm, FAPPLY_FUPDATE_THM]
              \\ rename1 ‘to_fmap _ ' k’
              \\ pop_assum $ qspec_then ‘k’ assume_tac
              \\ qpat_x_assum ‘∀x. MEM _ (FILTER _ _) ⇒ _’ $ drule_then assume_tac
              \\ gs [DOMSUB_FAPPLY_THM, MEM_FILTER])
          \\ last_x_assum $ drule_then assume_tac
          \\ pop_assum kall_tac
          \\ last_x_assum $ drule_then assume_tac
          \\ gvs [SUBSET_DEF])
      >- (qpat_x_assum ‘boundvars _ ⊆ set_of _’ mp_tac
          \\ qpat_x_assum ‘EVERY (λv. _ ∈ _ ∧ _ ∧ _ ∉ _) _’ mp_tac
          \\ qpat_x_assum ‘FDOM _ = _ ∪ _’ mp_tac
          \\ qpat_x_assum ‘FDOM _ = _’ mp_tac
          \\ qpat_x_assum ‘EVERY (λv. _ ' _ = _ ' _) _’ mp_tac
          \\ qpat_x_assum ‘DISJOINT (boundvars _) (IMAGE explode _)’ mp_tac
          \\ qpat_x_assum ‘_ ' _ = _ ' _’ mp_tac
          \\ qpat_x_assum ‘map_ok _’ mp_tac
          \\ qpat_x_assum ‘map_ok _’ mp_tac
          \\ qpat_x_assum ‘explode _ ∉ set_of _’ mp_tac
          \\ rpt $ pop_assum kall_tac
          \\ gs [DISJOINT_ALT, EVERY_MEM]
          \\ rw [] \\ strip_tac
          \\ gs [IN_FRANGE]
          >- gs [insert_thm, SUBSET_DEF]
          >- (dxrule_then assume_tac EQ_SYM
              \\ last_x_assum $ dxrule_then assume_tac
              \\ gs [insert_thm, FAPPLY_FUPDATE_THM]
              \\ rename1 ‘to_fmap _ ' k’
              \\ pop_assum $ qspec_then ‘k’ assume_tac
              \\ qpat_x_assum ‘∀x. MEM _ (FILTER _ _) ⇒ _’ $ drule_then assume_tac
              \\ gs [DOMSUB_FAPPLY_THM, MEM_FILTER])
          \\ last_x_assum $ drule_then assume_tac
          \\ pop_assum kall_tac
          \\ last_x_assum $ drule_then assume_tac
          \\ gvs [SUBSET_DEF]))
  \\ disch_then $ qx_choose_then ‘expr2’ $ qx_choose_then ‘expr3’ assume_tac \\ gs []
  \\ qexists_tac ‘explode name2::vL’ \\ simp [PULL_EXISTS]
  \\ rename1 ‘LIST_REL thunk_Delay_Lam$exp_rel _ (MAP SND expL1)’
  \\ Q.REFINE_EXISTS_TAC ‘(_, expr2)::expL1’ \\ simp []
  \\ Q.REFINE_EXISTS_TAC ‘(_, expr3)::expL2’ \\ simp []
  \\ qexists_tac ‘p_1::mapl2’ \\ gs []
  \\ gs [exp_rel1_def, exp_rel2_def, ok_bind_def, unfold_Delay_Lam_def, GENLIST_K_T]
  \\ rename1 ‘full_exp_rel y1 y2’
  \\ ‘is_Lam y1 ∧ is_Lam y2’ by gvs [cexp_wf_def, Lams_split, exp_rel1_def, exp_rel2_def]
  \\ ‘¬MEM name2 (MAP FST l'')’
    by (rename1 ‘LIST_REL _ l2 (FLAT (MAP2 unfold_Delay_Lam expL2 (ZIP (vL, _))))’
        \\ ‘MAP (explode o FST) l2
            = MAP FST (FLAT (MAP2 unfold_Delay_Lam expL2 (ZIP (vL, GENLIST (K T) (LENGTH vL)))))’
          by (irule LIST_EQ
              \\ rw [] \\ gs [LIST_REL_EL_EQN]
              \\ first_x_assum $ drule_then assume_tac
              \\ pairarg_tac \\ gs [EL_MAP]
              \\ pairarg_tac \\ gs [])
        \\‘¬MEM (explode name2) (MAP (explode o FST) l2)’
          suffices_by (gs [MEM_MAP] \\ metis_tac [])
        \\ simp []
        \\ strip_tac
        \\ qspecl_then [‘expL2’, ‘vL’, ‘GENLIST (K T) (LENGTH vL)’] assume_tac Letrec_Delay_SUBSET
        \\ gs [SUBSET_DEF,  LIST_REL_EL_EQN]
        \\ first_x_assum $ dxrule_then assume_tac
        \\ gs []
        >- (qpat_x_assum ‘MAP (explode o FST) _ = MAP FST _’ kall_tac
            \\ qpat_x_assum ‘MAP (explode o FST) _ = MAP FST _’ assume_tac
            \\ dxrule_then assume_tac EQ_SYM \\ gs []
            \\ qpat_x_assum ‘MEM _ (MAP (explode o FST) _)’ mp_tac
            \\ qpat_x_assum ‘EVERY (λ(v, e). _ ∈ _ ∧ _ ∉ _ ∧ DISJOINT _ _ ∧ _ ∧ _ ∧ _) _’ mp_tac
            \\ dxrule invent_var_thm \\ simp []
            \\ rpt $ pop_assum kall_tac
            \\ rw [] \\ strip_tac
            \\ gs [MEM_MAP, EVERY_MEM]
            \\ first_x_assum  $ dxrule_then assume_tac
            \\ pairarg_tac \\ gs [])
        >- (gs [EVERY_MEM]
            \\ last_x_assum $ dxrule_then assume_tac
            \\ gs []))
  \\ ‘¬MEM p_1 (MAP FST l'')’
    by (rename1 ‘LIST_REL _ l2 (FLAT (MAP2 unfold_Delay_Lam expL2 (ZIP (vL, _))))’
        \\ ‘MAP (explode o FST) l2
            = MAP FST (FLAT (MAP2 unfold_Delay_Lam expL2 (ZIP (vL, GENLIST (K T) (LENGTH vL)))))’
          by (irule LIST_EQ
              \\ rw [] \\ gs [LIST_REL_EL_EQN]
              \\ first_x_assum $ drule_then assume_tac
              \\ pairarg_tac \\ gs [EL_MAP]
              \\ pairarg_tac \\ gs [])
        \\‘¬MEM (explode p_1) (MAP (explode o FST) l2)’
          suffices_by (gs [MEM_MAP] \\ metis_tac [])
        \\ simp []
        \\ strip_tac
        \\ qspecl_then [‘expL2’, ‘vL’, ‘GENLIST (K T) (LENGTH vL)’] assume_tac Letrec_Delay_SUBSET
        \\ gs [SUBSET_DEF,  LIST_REL_EL_EQN]
        \\ first_x_assum $ dxrule_then assume_tac
        \\ gs []
        >- (qpat_x_assum ‘MAP (explode o FST) _ = MAP FST _’ kall_tac
            \\ qpat_x_assum ‘MAP (explode o FST) _ = MAP FST _’ assume_tac
            \\ dxrule_then assume_tac EQ_SYM \\ gs []
            \\ qpat_x_assum ‘¬MEM p_1 (MAP _ binds)’ irule
            \\ qpat_x_assum ‘MEM (explode p_1) (MAP _ binds)’ mp_tac
            \\ rpt $ pop_assum kall_tac
            \\ rw [MEM_MAP] \\ metis_tac [])
        >- gs [EVERY_MEM])
  \\ gs [] \\ rw []
  >- gs [cns_arities_def]
  >- (qpat_x_assum ‘MAP (explode o FST) _ = _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM \\ gs []
      \\ qpat_x_assum ‘¬MEM _ (MAP FST _)’ kall_tac
      \\ qpat_x_assum ‘¬MEM _ (MAP FST _)’ kall_tac
      \\ qpat_x_assum ‘¬MEM _ (MAP FST _)’ mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ strip_tac \\ strip_tac
      \\ first_x_assum irule
      \\ gs [MEM_MAP] \\ metis_tac [])
  >- (strip_tac \\ gs [GSYM CONJ_ASSOC, EVERY_CONJ, EVERY_MEM])
  >- (strip_tac \\ first_x_assum $ dxrule_then assume_tac
      \\ dxrule_then assume_tac invent_var_thm \\ gs []
      \\ gs [SUBSET_DEF])
  >- (dxrule invent_var_thm \\ simp [])
  >- (dxrule_then assume_tac invent_var_thm
      \\ gs [GSYM CONJ_ASSOC, EVERY_CONJ])
  >- (qpat_x_assum ‘boundvars _ ∩ _ = _’ mp_tac
      \\ dxrule invent_var_thm \\ simp []
      \\ qpat_x_assum ‘boundvars (Delay _) ⊆ set_of _’ mp_tac
      \\ rpt $ qpat_x_assum ‘set_of _ ⊆ set_of _’ mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ rw [SET_EQ_SUBSET, GSYM DIFF_INTER_COMPL, DIFF_SUBSET]
      \\ gs [SUBSET_DEF]
      \\ strip_tac \\ gvs []
      \\ rename1 ‘explode name2’
      \\ rpt $ first_x_assum $ qspec_then ‘explode name2’ assume_tac
      \\ gvs [])
  >- (gs [EVERY_MEM, FORALL_PROD]
      \\ qpat_x_assum ‘(BIGUNION _ ∪ _) ∩ _ = _’ mp_tac
      \\ dxrule invent_var_thm \\ simp []
      \\ rpt $ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
      \\ qpat_x_assum ‘∀p1 p2. MEM (_, _) _ ⇒ _ ∧ _ ∧ _ ∧ _ ∧ _ ⊆ _ ∧ _ ⊆ _’ mp_tac
      \\ rpt $ qpat_x_assum ‘set_of _ ⊆ set_of _’ mp_tac
      \\ qpat_x_assum ‘LENGTH _ = LENGTH _’ mp_tac
      \\ qpat_x_assum ‘MAP FST _ = MAP FST _’ mp_tac
      \\ qpat_x_assum ‘MAP (explode o FST) _ = MAP FST _’ mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ rw []
      \\ strip_tac
      \\ dxrule_then assume_tac $ iffLR SET_EQ_SUBSET
      \\ fs []
      \\ qsuff_tac ‘explode name2 ∈ (BIGUNION (set (MAP (boundvars ∘ exp_of ∘ SND) l''))
                                     ∪ set (MAP (explode ∘ FST) l'')) ∩
          COMPL (BIGUNION (set (MAP (boundvars ∘ exp_of ∘ SND) binds)) ∪ set (MAP FST expL1))’
      >- (strip_tac
          \\ dxrule_then assume_tac $ iffLR SUBSET_DEF
          \\ dxrule_then assume_tac $ iffLR SUBSET_DEF
          \\ dxrule_then assume_tac $ iffLR SUBSET_DEF
          \\ dxrule_then assume_tac $ iffLR SUBSET_DEF
          \\ first_x_assum $ drule_then assume_tac
          \\ first_x_assum $ drule_then assume_tac
          \\ gs [])
      \\ rw []
      >- (dxrule_then (qspec_then ‘vL’ assume_tac) MEM_FLAT_MAP2_obtain
          \\ gs [LIST_REL_EL_EQN]
          \\ pop_assum $ dxrule_then assume_tac
          \\ disj1_tac
          \\ gs [MEM_EL]
          \\ last_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs [PULL_EXISTS]
          \\ first_assum $ irule_at Any
          \\ gs [EL_MAP, boundvars_FOLDL_replace_Force])
      >- (rw [DISJ_EQ_IMP]
          \\ strip_tac
          \\ gs [MEM_MAP, SND_THM]
          \\ pairarg_tac \\ gs []
          \\ last_x_assum $ dxrule_then assume_tac
          \\ gs [SUBSET_DEF])
      >- (qpat_x_assum ‘MAP (explode o FST) _ = MAP FST _’ assume_tac
          \\ dxrule_then assume_tac EQ_SYM
          \\ gs []
          \\ strip_tac \\ gs [MEM_MAP, FST_THM]
          \\ pairarg_tac \\ gs []
          \\ last_x_assum $ dxrule_then assume_tac
          \\ gs []))
  >- (gs [EVERY_MEM]
      \\ gen_tac \\ strip_tac
      \\ last_x_assum $ drule_then assume_tac
      \\ dxrule_then assume_tac invent_var_thm
      \\ dxrule_then assume_tac full_exp_rel_boundvars
      \\ gs [FOLDL_replace_Force_Delay, boundvars_FOLDL_replace_Force,
             replace_Force_def, boundvars_def]
      >- (strip_tac
          \\ assume_tac boundvars_replace_Force2
          \\ gs [SUBSET_DEF])
      \\ strip_tac
      \\ qpat_x_assum ‘boundvars _ ∩ COMPL _ = _’ assume_tac
      \\ dxrule_then assume_tac $ iffLR SET_EQ_SUBSET
      \\ gs [GSYM DIFF_INTER_COMPL, DIFF_SUBSET]
      \\ gs [SUBSET_DEF]
      \\ first_x_assum $ drule_then assume_tac
      \\ gs [])
  >- metis_tac [SUBSET_TRANS]
  >- (rpt $ qpat_x_assum ‘set_of _ ⊆ set_of _’ mp_tac
      \\ dxrule invent_var_thm \\ simp [])
  >- gs [FOLDL_replace_Force_Delay, replace_Force_def, freevars_def]
  >- gs [FOLDL_replace_Force_Delay, replace_Force_def, boundvars_def]
  >- (dxrule_then assume_tac invent_var_thm
      \\ gvs [SUBSET_DEF])
  >- gs [cexp_wf_def]
  >- (dxrule_then assume_tac invent_var_thm
      \\ gvs [SUBSET_DEF, freevars_def])
  >- simp [boundvars_def]
  >- (dxrule_then assume_tac invent_var_thm
      \\ gvs [SUBSET_DEF])
  >- simp [cexp_wf_def]
  >- (gs [EVERY_MEM] \\ gen_tac \\ strip_tac
      \\ last_x_assum $ dxrule_then assume_tac
      \\ pairarg_tac \\ gvs [SUBSET_DEF])
  >- (strip_tac
      \\ dxrule_then assume_tac invent_var_thm
      \\ gvs [SUBSET_DEF])
  >- (gs [FOLDL_replace_Force_Delay, replace_Force_def]
      \\ simp [CONJ_COMM]
      \\ irule FOLDL_replace_Force_comm
      \\ qpat_x_assum ‘ALL_DISTINCT (_ ++ _)’ mp_tac
      \\ qpat_x_assum ‘DISJOINT (set (FILTER _ _)) (FRANGE _)’ mp_tac
      \\ simp [CONJ_COMM]
      \\ simp [SUBSET_DEF])
  >- gs [FOLDL_replace_Force_Delay, FOLDL_replace_Force_Var, replace_Force_def]
  >- (qpat_x_assum ‘LIST_REL exp_rel _ _’ kall_tac
      \\ qpat_x_assum ‘LIST_REL full_exp_rel _ _’ kall_tac
      \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
      \\ simp [LIST_REL_EL_EQN]
      \\ rw [] \\ gs []
      \\ first_x_assum $ drule_then assume_tac
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ irule EQ_TRANS
      \\ irule_at (Pos hd) FOLDL_replace_Force_comm
      \\ simp [CONJ_COMM]
      \\ irule_at Any FOLDL_replace_Force_comm
      \\ qpat_x_assum ‘ALL_DISTINCT (_ ++ _)’ mp_tac
      \\ simp [CONJ_COMM]
      \\ gs [ALL_DISTINCT_APPEND, MEM_FILTER]
      \\ qpat_x_assum ‘FDOM _ = _ ∪ _’ mp_tac
      \\ qpat_x_assum ‘DISJOINT _ (FRANGE _)’ mp_tac
      \\ qpat_x_assum ‘DISJOINT _ (FRANGE _)’ mp_tac
      \\ qpat_x_assum ‘¬MEM p_1 mapl2’ mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ rw []
      >- (qpat_x_assum ‘DISJOINT (set (FILTER _ _)) (FRANGE _)’ mp_tac
          \\ simp [CONJ_COMM])
      >- gs [SUBSET_DEF]
      >- (strip_tac \\ gs [])
      >- (rename1 ‘MEM e _’
          \\ first_x_assum $ qspec_then ‘e’ assume_tac
          \\ gs [])
      >- (qpat_x_assum ‘DISJOINT (set (FILTER _ _)) (FRANGE _)’ mp_tac
          \\ simp [CONJ_COMM])
      >- gs [SUBSET_DEF])
  >- (qpat_x_assum ‘IMAGE explode (FRANGE _) ⊆ _’ mp_tac
      \\ rpt $ qpat_x_assum ‘set_of _ ⊆ set_of _’ mp_tac
      \\ qpat_x_assum ‘FDOM _ = _ ∪ _’ mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ rw [SUBSET_DEF]
      \\ gs [PULL_EXISTS, IN_FRANGE])
  >- (qpat_x_assum ‘_ ' _ = _ ' _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM
      \\ gs [insert_thm]
      \\ dxrule invent_var_thm \\ gs [])
  >- (gvs [EVERY_MEM]
      \\ dxrule_then assume_tac invent_var_thm
      \\ gvs [SUBSET_DEF])
  >- (qpat_x_assum ‘_ ' _ = _ ' _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM
      \\ gs [insert_thm])
  >- (qpat_x_assum ‘_ ' _ = _ ' _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM
      \\ gs [insert_thm])
  >- gvs [EVERY_MEM]
  >- (qpat_x_assum ‘ALL_DISTINCT (_ ++ _)’ mp_tac
      \\ simp [CONJ_COMM]
      \\ gs [ALL_DISTINCT_APPEND, MEM_FILTER])
  >- (qpat_x_assum ‘EVERY (λv. _ ∈ _ ∧ _ ∉ _) _’ mp_tac
      \\ qpat_x_assum ‘boundvars _ ∩ COMPL _ = _’ mp_tac
      \\ dxrule full_exp_rel_boundvars
      \\ qpat_x_assum ‘boundvars _ ⊆ set_of _’ mp_tac
      \\ qpat_x_assum ‘boundvars _ ⊆ set_of _’ mp_tac
      \\ dxrule invent_var_thm \\ simp []
      \\ rpt $ qpat_x_assum ‘set_of _ ⊆ set_of _’ mp_tac
      \\ qpat_x_assum ‘FDOM _ = _’ mp_tac
      \\ qpat_x_assum ‘FDOM _ = _’ mp_tac
      \\ qpat_x_assum ‘IMAGE explode (FRANGE _) ⊆ _’ kall_tac
      \\ qpat_x_assum ‘IMAGE explode (FRANGE _) ⊆ _’ mp_tac
      \\ qpat_x_assum ‘IMAGE explode (set _) ⊆ _’ mp_tac
      \\ qpat_x_assum ‘IMAGE explode (set _) ⊆ _’ mp_tac
      \\ qpat_x_assum ‘EVERY (λv. _ ' _ = _ ' _) _’ mp_tac
      \\ qpat_x_assum ‘_ ' _ = _ ' _’ mp_tac
      \\ qpat_x_assum ‘DISJOINT (boundvars _) (IMAGE explode (FRANGE _))’ mp_tac
      \\ simp [insert_thm]
      \\ rpt $ pop_assum kall_tac
      \\ rw [DISJOINT_ALT, IN_FRANGE] \\ strip_tac \\ gvs [boundvars_Delay]
      \\ gs [SET_EQ_SUBSET, GSYM DIFF_INTER_COMPL, DIFF_SUBSET,
             boundvars_FOLDL_replace_Force, boundvars_Delay, replace_Force_def]
      >- (assume_tac boundvars_replace_Force2
          \\ gs [SUBSET_DEF]
          \\ first_x_assum $ drule_then assume_tac
          \\ rename1 ‘explode var ∈ _’
          \\ rpt $ last_x_assum $ qspec_then ‘explode var’ assume_tac \\ gs [])
      >- (gs [EVERY_MEM] \\ last_x_assum $ drule_then assume_tac
          \\ gs [SUBSET_DEF]
          \\ last_x_assum $ drule_then assume_tac
          \\ gs [MEM_FILTER, FAPPLY_FUPDATE_THM]
          \\ rename1 ‘explode (to_fmap map2 ' k) ∈ _’
          \\ rpt $ last_x_assum $ qspec_then ‘explode (to_fmap map2 ' k)’ assume_tac \\ gs []
          \\ gs [IN_FRANGE]
          \\ first_x_assum $ qspec_then ‘k’ assume_tac
          \\ gvs [])
      >- (gs [EVERY_MEM] \\ first_x_assum $ dxrule_then assume_tac
          \\ gs [SUBSET_DEF]
          \\ rename1 ‘explode (to_fmap map2 ' k) ∈ _’
          \\ rpt $ last_x_assum $ qspec_then ‘explode (to_fmap map2 ' k)’ assume_tac \\ gs []))
  >- simp [boundvars_def]
  >- gvs []
  >- gvs [SUBSET_DEF, MEM_FILTER, PULL_EXISTS]
  >- (qpat_x_assum ‘IMAGE explode (set _) ⊆ set_of _’ mp_tac
      \\ qpat_x_assum ‘EVERY (λv. _ ∈ _ ∧ _ ∉ _) _’ mp_tac
      \\ qpat_x_assum ‘set _ ⊆ set (MAP FST _)’ mp_tac
      \\ qpat_x_assum ‘¬MEM name2 (MAP FST _)’ mp_tac
      \\ dxrule invent_var_thm \\ simp []
      \\ rpt $ pop_assum kall_tac
      \\ rw [SUBSET_DEF] \\ gvs [PULL_EXISTS, EVERY_MEM, DISJOINT_ALT]
      \\ first_x_assum $ drule_then assume_tac \\ gs []
      \\ first_x_assum $ drule_then assume_tac \\ gs []
      \\ first_x_assum $ drule_then assume_tac \\ gs [])
  >- metis_tac [SUBSET_TRANS]
  >- (rpt $ pop_assum kall_tac
      \\ rw [SET_EQ_SUBSET, SUBSET_DEF, MEM_FILTER])
  >- gvs [SUBSET_DEF]
  >- (qpat_x_assum ‘split_Delayed_Lam (Lam _ _) _ _ = _’ mp_tac
      \\ simp [split_Delayed_Lam_def]
      \\ pairarg_tac \\ rw []
      \\ simp [cexp_ok_bind_def])
  >- simp [cexp_ok_bind_def]
  >- (strip_tac
      \\ dxrule_then assume_tac invent_var_thm
      \\ gvs [])
  >- (rename1 ‘LIST_REL _ l2 (FLAT (MAP2 unfold_Delay_Lam expL2 (ZIP (vL, _))))’
      \\ ‘MAP FST (FLAT (MAP2 unfold_Delay_Lam expL2 (ZIP (vL, GENLIST (K T) (LENGTH vL)))))
          = MAP (explode o FST) l2’
        by (irule LIST_EQ
            \\ rw [] \\ gs [LIST_REL_EL_EQN]
            \\ first_x_assum $ drule_then assume_tac
            \\ pairarg_tac \\ gs [EL_MAP]
            \\ pairarg_tac \\ gs [])
      \\ qspecl_then [‘expL1’, ‘expL2’, ‘vL’] assume_tac MAP_FST_change_expL
      \\ gs [LIST_REL_EL_EQN]
      \\ strip_tac
      \\ qpat_x_assum ‘¬MEM name2 _’ irule
      \\ gs [MEM_MAP]
      \\ metis_tac [])
  >- (rename1 ‘LIST_REL _ l2 (FLAT (MAP2 unfold_Delay_Lam expL2 (ZIP (vL, _))))’
      \\ ‘MAP FST (FLAT (MAP2 unfold_Delay_Lam expL2 (ZIP (vL, GENLIST (K T) (LENGTH vL)))))
          = MAP (explode o FST) l2’
        by (irule LIST_EQ
            \\ rw [] \\ gs [LIST_REL_EL_EQN]
            \\ first_x_assum $ drule_then assume_tac
            \\ pairarg_tac \\ gs [EL_MAP]
            \\ pairarg_tac \\ gs [])
      \\ qspecl_then [‘expL1’, ‘expL2’, ‘vL’] assume_tac MAP_FST_change_expL
      \\ gs [LIST_REL_EL_EQN]
      \\ strip_tac
      \\ qpat_x_assum ‘¬MEM p_1 _’ irule
      \\ gs [MEM_MAP]
      \\ metis_tac [])
  >- (rename1 ‘LIST_REL _ l2 (FLAT (MAP2 unfold_Delay_Lam expL2 (ZIP (vL, _))))’
      \\ ‘MAP FST (FLAT (MAP2 unfold_Delay_Lam expL2 (ZIP (vL, GENLIST (K T) (LENGTH vL)))))
          = MAP (explode o FST) l2’
        by (irule LIST_EQ
            \\ rw [] \\ gs [LIST_REL_EL_EQN]
            \\ first_x_assum $ drule_then assume_tac
            \\ pairarg_tac \\ gs [EL_MAP]
            \\ pairarg_tac \\ gs [])
      \\ gs []
      \\ ‘¬MEM (explode p_1) (MAP (explode o FST) l2)’
        by (strip_tac
            \\ qpat_x_assum ‘¬MEM p_1 _’ irule
            \\ gs [MEM_MAP]
            \\ metis_tac [])
      \\ gs []
      \\ qpat_x_assum ‘FILTER _ _ = FILTER _ _’ mp_tac
      \\ simp [CONJ_COMM]
      \\ strip_tac
      \\ irule EQ_TRANS
      \\ pop_assum $ irule_at Any
      \\ simp [GSYM CONJ_ASSOC]
      \\ simp [GSYM FILTER_FILTER]
      \\ irule $ iffRL FILTER_EQ_ID
      \\ simp [EVERY_MEM]
      \\ qpat_x_assum ‘IMAGE explode (set mapl) ⊆ _’ mp_tac
      \\ dxrule invent_var_thm \\ simp []
      \\ rpt $ pop_assum kall_tac
      \\ rw [] \\ strip_tac
      \\ gs [MEM_FILTER, SUBSET_DEF, PULL_EXISTS])
  >- (qpat_x_assum ‘EVERY (λv. _ ' _ = _ ' _) _’ mp_tac
      \\ simp [CONJ_COMM, insert_thm]
      \\ rpt $ pop_assum kall_tac
      \\ rw [EVERY_MEM, MEM_FILTER]
      \\ rename1 ‘v ≠ _’
      \\ last_x_assum $ qspec_then ‘v’ assume_tac
      \\ gs [FAPPLY_FUPDATE_THM])
  >- (qpat_x_assum ‘_ ∩ COMPL _ = _’ mp_tac
      \\ qpat_x_assum ‘_ ∩ COMPL _ = _’ mp_tac
      \\ rpt $ qpat_x_assum ‘set_of _ ⊆ set_of _’ mp_tac
      \\ qpat_x_assum ‘boundvars (Delay _) ⊆ set_of _’ mp_tac
      \\ qpat_x_assum ‘explode _ ∈ set_of _’ mp_tac
      \\ qpat_x_assum ‘EVERY (λ(v,e). _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ boundvars (exp_of _) ⊆ _) _’ mp_tac
      \\ qpat_x_assum ‘MAP (explode o FST) _ = MAP FST _’ mp_tac
      \\ qpat_x_assum ‘LIST_REL full_exp_rel _ _’ mp_tac
      \\ qpat_x_assum ‘Delay (exp_of _) = _’ mp_tac
      \\ qpat_x_assum ‘explode _ ∈ set_of _’ mp_tac
      \\ dxrule full_exp_rel_boundvars
      \\ dxrule invent_var_thm \\ simp []
      \\ rpt $ pop_assum kall_tac
      \\ strip_tac
      \\ gvs [boundvars_FOLDL_replace_Force, replace_Force_def, boundvars_Delay,
              FOLDL_replace_Force_Delay, boundvars_replace_Force_Var]
      \\ pop_assum kall_tac
      \\ gs [SET_EQ_SUBSET, GSYM DIFF_INTER_COMPL, DIFF_SUBSET]
      \\ rw []
      >- (gs [SUBSET_DEF] \\ rw []
          \\ first_x_assum $ drule_then mp_tac
          \\ first_x_assum $ drule_then mp_tac
          \\ strip_tac \\ simp [])
      >- gs [boundvars_def]
      >- (gs [SUBSET_DEF, PULL_EXISTS] \\ rw []
          \\ last_x_assum $ drule_then $ drule_then mp_tac
          \\ strip_tac \\ simp []
          \\ metis_tac [])
      >- (gs [SUBSET_DEF, PULL_EXISTS] \\ rw []
          \\ first_x_assum $ drule_then mp_tac
          \\ strip_tac \\ simp []
          \\ metis_tac [])
      >- (gs [SUBSET_DEF] \\ rw []
          \\ first_x_assum $ drule_then kall_tac
          \\ first_x_assum $ drule_then assume_tac
          \\ gvs []
          \\ disj1_tac \\ disj1_tac
          \\ disj2_tac
          \\ metis_tac [])
      >- (gs [SUBSET_DEF] \\ rw []
          \\ first_x_assum $ drule_then assume_tac
          \\ gs []
          \\ disj2_tac
          \\ strip_tac \\ gvs [])
      >- gs [boundvars_def]
      >- (gs [SUBSET_DEF, PULL_EXISTS] \\ rw []
          \\ last_x_assum $ drule_then $ drule_then mp_tac
          \\ strip_tac \\ simp []
          \\ metis_tac [])
      >- (gs [SUBSET_DEF, PULL_EXISTS] \\ rw []
          \\ first_x_assum $ drule_then mp_tac
          \\ strip_tac \\ simp []
          \\ metis_tac [])
      >- (gs [SUBSET_DEF] \\ rw []
          \\ first_x_assum $ drule_then mp_tac
          \\ first_x_assum $ drule_then mp_tac
          \\ strip_tac \\ simp []
          \\ metis_tac [])
      >- (gs [SUBSET_DEF, PULL_EXISTS, EVERY_MEM] \\ rw []
          \\ rename1 ‘var ∈ set_of (vc2f, vc2s) ∨ _’
          \\ Cases_on ‘var ∈ set_of (vc2f, vc2s)’ \\ gs []
          \\ qpat_x_assum ‘∀v. _ ⇒ _ ∈ set_of (vc2f, vc2s)’ $ qspec_then ‘var’ assume_tac \\ gs []
          \\ conj_tac
          >- (rw [DISJ_EQ_IMP] \\ strip_tac
              \\ gs [MEM_MAP, SND_THM]
              \\ pairarg_tac \\ gs []
              \\ last_x_assum $ drule_then assume_tac
              \\ gs [])
          \\ conj_tac
          >- (strip_tac \\ gs [])
          \\ qpat_x_assum ‘MAP (explode o FST) _ = MAP FST _’ assume_tac
          \\ dxrule_then assume_tac EQ_SYM
          \\ strip_tac \\ gs []
          \\ gs [MEM_MAP, FST_THM]
          \\ pairarg_tac \\ gs []
          \\ last_x_assum $ drule_then assume_tac
          \\ gs []))
QED

Theorem UNION_INTER:
  ∀A B C. (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C)
Proof
  gvs [SET_EQ_SUBSET, SUBSET_DEF]
QED

Theorem FINITE_boundvars:
  ∀e. FINITE (boundvars e)
Proof
  Induct using freevars_ind \\ gvs [boundvars_def]
  \\ gvs [MEM_MAP, PULL_EXISTS, FORALL_PROD]
  \\ rw [] \\ last_x_assum $ dxrule_then irule
QED

Theorem FOLDL_replace_Force_freevars:
  ∀l e v map. v ∈ freevars (FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) e l)
  ⇒  ((∃v2. MEM v2 l ∧ v = explode (to_fmap map ' v2)) ∨ v ∈ freevars e)
Proof
  Induct \\ gvs []
  \\ rw [] \\ last_x_assum $ dxrule_then assume_tac
  \\ gvs []
  >- (disj1_tac \\ metis_tac [])
  \\ assume_tac freevars_replace_Force_SUBSET
  \\ gvs [SUBSET_DEF]
  \\ pop_assum $ dxrule_then assume_tac \\ gvs [freevars_def]
  \\ disj1_tac \\ metis_tac []
QED

Theorem MAP_FST_FOLDL_MAP_replace_Force:
  ∀l1 l2. MAP FST (FOLDL (λl (v1, v2). MAP (λ(v, e). (v, replace_Force (Var v2) v1 e)) l) l2 l1) = MAP FST l2
Proof
  Induct \\ simp []
  \\ simp [FORALL_PROD, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
QED

Theorem FOLDL_replace_Force_ZIP:
  ∀mapl e map. FOLDL (λe (v1, v2). replace_Force (Var v2) v1 e) e
                       (ZIP (MAP explode mapl,
                             MAP (λv. explode (to_fmap map ' v)) mapl))
                 = FOLDL (λe v. replace_Force (Var (explode (to_fmap map ' v))) (explode v) e) e mapl
Proof
  Induct \\ gvs []
QED

Theorem MAP_FST_FOLDL_no_change:
  ∀l1 l2. MAP FST (FOLDL (λl (v1, v2). MAP (λ(v, e). (v, replace_Force (Var v2) v1 e)) l) l2 l1) = MAP FST l2
Proof
  Induct \\ gvs [FORALL_PROD]
  \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
QED

Theorem FOLDL_MAP_comm:
  ∀l1 l2. FOLDL (λl (v1, v2). MAP (λ(v, e). (v, replace_Force (Var v2) v1 e)) l) l2 l1
          = MAP (λ(v, e).
                   (v, FOLDL (λe (v1, v2). replace_Force (Var v2) v1 e) e l1)) l2
Proof
  Induct \\ gvs [FORALL_PROD]
  >- (Induct \\ gvs [FORALL_PROD])
  \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
QED

Theorem split_Delayed_Lam_soundness_lemma:
  ∀vc map map_l e_out vc_out.
    split_Delayed_Lam e vc map = (e_out, vc_out) ∧
    ALL_DISTINCT map_l ∧
    freevars  (exp_of e) ⊆ set_of vc ∧
    boundvars (exp_of e) ⊆ set_of vc ∧
    IMAGE explode (set map_l) ⊆ set_of vc ∧
    IMAGE explode (FRANGE (to_fmap map)) ⊆ set_of vc ∧
    cexp_wf e ∧
    DISJOINT (set map_l) (FRANGE (to_fmap map)) ∧
    DISJOINT (freevars (exp_of e)) (IMAGE explode (FRANGE (to_fmap map))) ∧
    DISJOINT (boundvars (exp_of e)) (IMAGE explode (FRANGE (to_fmap map))) ∧
    map_ok map ∧ cmp_of map = compare ∧ vars_ok vc ∧
    FDOM (to_fmap map) = set map_l ⇒
    ∃e2 e3.
      cns_arities e = cns_arities e_out ∧
      set_of vc ⊆ set_of vc_out ∧ vars_ok vc_out ∧
      freevars  (exp_of e_out) ⊆ set_of vc_out ∧
      boundvars (exp_of e_out) ⊆ set_of vc_out ∧
      (boundvars e2) ∩ (COMPL (boundvars (exp_of e))) = set_of vc_out ∩ COMPL (set_of vc) ∧
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
  >- (rw []
      \\ gvs [FOLDL_replace_Force_Var, exp_rel1_def, exp_rel2_def, boundvars_def, cns_arities_def])
  >~[‘thunk_cexp$Let opt e1 e2’]

  >- (Cases_on ‘opt’ \\ gs [split_Delayed_Lam_def, cns_arities_def]
      >~[‘Let NONE _ _’]
      >- (gvs [freevars_def, boundvars_def, cexp_size_def, PULL_FORALL]
          \\ rw []
          \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
          \\ last_assum $ qspec_then ‘e1’ assume_tac \\ fs []
          \\ pop_assum $ drule_all_then $ qx_choose_then ‘e1_mid’ assume_tac
          \\ last_x_assum $ qspec_then ‘e2’ assume_tac \\ gs []
          \\ pop_assum $ drule_then $ drule_then mp_tac \\ impl_tac
          >- (simp [] \\ rpt $ conj_tac \\ irule_at Any SUBSET_TRANS \\ metis_tac [])
          \\ disch_then $ qx_choose_then ‘e2_mid’ assume_tac
          \\ gvs [exp_of_def, freevars_def, boundvars_def, cexp_wf_def,
                  args_ok_def, FOLDL_replace_Force_Seq]
          \\ irule_at Any thunk_Delay_LamTheory.exp_rel_Let
          \\ first_x_assum $ irule_at $ Pos hd
          \\ first_x_assum $ irule_at $ Pos hd
          \\ gvs [exp_rel2_def, FOLDL_replace_Force_Seq, PULL_EXISTS, cns_arities_def]
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
      \\ CASE_TAC
      >~[‘dest_Delay_Lam _ = SOME _’]
      >- (rw []
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ dxrule_then assume_tac invent_var_thm \\ gs [PULL_FORALL]
          \\ rename1 ‘Let (SOME (explode m)) (exp_of e1) (exp_of e2)’
          \\ Cases_on ‘e1’ \\ gs [dest_Delay_Lam_def, exp_of_def]
          \\ rename1 ‘dest_Delay_Lam (Delay e1)’ \\ Cases_on ‘e1’
          \\ gvs [dest_Delay_Lam_def, cns_arities_def]
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
                  >- (rename1 ‘explode name2 ∈ freevars _’
                      \\ last_x_assum $ qspec_then ‘explode name2’ assume_tac
                      \\ last_x_assum $ qspec_then ‘explode name2’ assume_tac
                      \\ gs [])
                  \\ rename1 ‘k = name’ \\ Cases_on ‘k = name’ \\ gvs []
                  >- (rename1 ‘explode name2 ∈ freevars _’
                      \\ last_x_assum $ qspec_then ‘explode name2’ assume_tac
                      \\ gs [])
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
          >- (strip_tac \\ rename1 ‘explode name2 ∈ freevars _’
              \\ last_x_assum $ qspec_then ‘explode name2’ assume_tac
              \\ gs [])
          >- (strip_tac \\ gvs [])
          >- gs [cns_arities_def]
          >- gvs [freevars_def]
          >- gvs [boundvars_def]
          >- (gvs [boundvars_def, boundvars_Lams, SET_EQ_SUBSET, SUBSET_DEF, DISJ_IMP_THM]
              \\ rw [] \\ gvs [])
          >- (gvs [boundvars_def, boundvars_Lams, SET_EQ_SUBSET, SUBSET_DEF, DISJ_IMP_THM]
              \\ rw [] \\ gvs [])
          >- (gvs [boundvars_def, boundvars_Lams, SET_EQ_SUBSET, SUBSET_DEF, DISJ_IMP_THM]
              \\ rw [] \\ gvs [])
          >- (gvs [boundvars_def, boundvars_Lams, SET_EQ_SUBSET, SUBSET_DEF, DISJ_IMP_THM]
              \\ rw [] \\ gvs [])
          >- (gvs [SET_EQ_SUBSET, SUBSET_DEF, boundvars_def]
              \\ rw []
              \\ rename1 ‘var ∈ _’
              \\ rpt $ last_x_assum $ qspec_then ‘var’ assume_tac \\ gvs []
              \\ rename1 ‘var ∈ set_of vc1 ⇒ var = explode name2’
              \\ Cases_on ‘var ∈ set_of vc1’ \\ gs []
              \\ Cases_on ‘var = explode name2’
              \\ gs [boundvars_FOLDL_replace_Force]
              \\ rename1 ‘var ∉ set_of vc2 ⇒ _’
              \\ Cases_on ‘var ∈ set_of vc2’ \\ gs [])
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
      \\ simp [FOLDL_replace_Force_Let, cns_arities_def]
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
  >~[‘args_ok op xs’] (* Prim *)

  >- (Cases_on ‘op’
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
      \\ gvs [DISJOINT_SYM, cns_arities_def]
      \\ disch_then $ qx_choose_then ‘ys’ $ qx_choose_then ‘ys'’ assume_tac \\ fs []
      \\ qpat_assum ‘LIST_REL _ _ _’ $ irule_at Any
      \\ qpat_assum ‘LIST_REL _ _ _’ $ irule_at Any \\ simp []
      \\ drule_then assume_tac FOLDR_split_Delayed_Lam_LENGTH \\ gs [args_ok_def])
  >~[‘num_mop_args mop = LENGTH xs’] (* Monad *)

  >- (gvs [split_Delayed_Lam_def, FOLDL_replace_Force_Monad, exp_of_def,
              exp_rel1_def, PULL_EXISTS, exp_rel2_def]
      \\ rw []
      \\ pairarg_tac \\ gvs [exp_of_def, cexp_wf_def, freevars_def, boundvars_def, PULL_FORALL]
      \\ qspec_then ‘xs’ mp_tac split_Delay_Lam_soundness_Prim
      \\ impl_tac
      >- (rw [] \\ rename1 ‘MEM e xs’ \\ last_x_assum $ qspec_then ‘e’ assume_tac
          \\ assume_tac cexp_size_lemma \\ fs []
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gvs [cexp_size_def]
          \\ pop_assum kall_tac \\ pop_assum kall_tac \\ pop_assum kall_tac
          \\ pop_assum $ drule_all_then $ qx_choose_then ‘e2’ assume_tac
          \\ qexists_tac ‘e2’ \\ gvs [])
      \\ disch_then $ drule_then $ drule_then $ drule_then $ drule_then $ drule_then mp_tac
      \\ gvs [DISJOINT_SYM, cns_arities_def]
      \\ disch_then $ qx_choose_then ‘ys’ $ qx_choose_then ‘ys'’ assume_tac \\ fs []
      \\ qpat_assum ‘LIST_REL _ _ _’ $ irule_at Any
      \\ qpat_assum ‘LIST_REL _ _ _’ $ irule_at Any \\ simp []
      \\ drule_then assume_tac FOLDR_split_Delayed_Lam_LENGTH \\ gs [])
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
      \\ gvs [SF ETA_ss, FOLDL_replace_Force_Apps, cns_arities_def] \\ rw []
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
      \\ gvs [exp_of_def, freevars_Lams, boundvars_Lams, SUBSET_DEF, PULL_EXISTS, cexp_wf_def, cns_arities_def]
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
      \\ gvs [PULL_EXISTS, GSYM PULL_FORALL]
      \\ rename1 ‘Letrec l c’
      \\ qspec_then ‘l’ mp_tac letrec_split_soundness
      \\ impl_tac
      >- (gen_tac \\ strip_tac
          \\ rename1 ‘MEM expr (MAP SND _)’
          \\ last_x_assum $ qspec_then ‘expr’ mp_tac
          \\ impl_tac \\ simp []
          \\ assume_tac cexp_size_lemma
          \\ gs [MEM_MAP, SND_THM]
          \\ pairarg_tac \\ gs []
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gs [cexp_size_def])
      \\ disch_then $ dxrule_then mp_tac
      \\ simp []
      \\ disch_then $ qspecl_then [‘{}’, ‘map_l’] mp_tac
      \\ simp []
      \\ impl_tac
      >- (rw []
          >- (gs [EVERY_MEM]
              \\ rw [] \\ first_x_assum $ dxrule_then assume_tac
              \\ pairarg_tac \\ gs [])
          >- (gs [EVERY_MEM, MEM_MAP]
              \\ rw [] \\ first_x_assum $ dxrule_then assume_tac
              \\ pairarg_tac \\ gs [])
          \\ rw [EVERY_MEM]
          \\ gs [SUBSET_DEF, PULL_EXISTS, MEM_MAP, FORALL_PROD]
          \\ rename1 ‘MEM e l’
          \\ last_x_assum kall_tac
          \\ pairarg_tac \\ gs []
          \\ rw []
          >- (last_x_assum $ dxrule_then assume_tac
              \\ gs [])
          >- (gs [DISJOINT_ALT, MEM_MAP, PULL_EXISTS]
              \\ first_x_assum $ drule_then irule
              \\ gs [])
          >- (qpat_x_assum ‘DISJOINT (_ DIF _) _’ mp_tac
              \\ qpat_x_assum ‘DISJOINT (set (MAP FST _)) _’ mp_tac
              \\ rw [DISJOINT_ALT]
              \\ rename1 ‘explode var ∈ _’
              \\ first_x_assum $ qspec_then ‘explode var’ assume_tac
              \\ first_x_assum $ qspec_then ‘explode var’ assume_tac
              \\ Cases_on ‘MEM (explode var) (MAP FST (MAP (λ(n,x). (explode n, exp_of x)) l))’ \\ gs []
              \\ first_x_assum irule
              \\ disj2_tac
              \\ gs [MEM_MAP, PULL_EXISTS]
              \\ first_x_assum $ irule_at Any
              \\ simp [])
          >- (first_x_assum $ dxrule_then assume_tac
              \\ gs [])
          >- (rename1 ‘var ∈ _’
              \\ Cases_on ‘MEM var (MAP (explode o FST) l)’ \\ gs []
              >- (gs [MEM_MAP, FST_THM]
                  \\ pairarg_tac \\ gs []
                  \\ last_x_assum $ dxrule_then irule)
              \\ last_x_assum irule
              \\ conj_tac
              >- gvs [MEM_MAP, FORALL_PROD]
              \\ disj2_tac
              \\ first_x_assum $ irule_at Any
              \\ simp [])
          >- first_x_assum $ drule_all_then irule)
      \\ disch_then $ qx_choose_then ‘vL’ $ qx_choose_then ‘expL1’
                    $ qx_choose_then ‘expL2’ $ qx_choose_then ‘mapl2’ assume_tac
      \\ last_x_assum $ qspec_then ‘c’ assume_tac \\ gvs [cexp_size_def]
      \\ pop_assum $ dxrule_then $ qspec_then
                   ‘mapl2 ++ FILTER (λv. ¬MEM v (MAP FST l)) map_l’ mp_tac
      \\ impl_tac
      >- (gvs [ALL_DISTINCT_APPEND] \\ rpt $ conj_tac
          >- (rw [] \\ strip_tac \\ first_x_assum $ dxrule_then irule \\ simp [])
          >- (gvs [SUBSET_DEF]
              \\ rw [] \\ rename1 ‘x ∈ set_of _’
              \\ rpt $ last_x_assum $ qspec_then ‘x’ assume_tac \\ gvs []
              \\ metis_tac [])
          >- gvs [SUBSET_DEF]
          >- gvs [SUBSET_DEF]
          >- gvs [SUBSET_DEF]
          >- (simp [DISJOINT_ALT, PULL_FORALL]
              \\ gen_tac \\ strip_tac \\ strip_tac
              \\ gs [IN_FRANGE]
              >- (gs [EVERY_MEM]
                  \\ first_x_assum $ drule_then assume_tac
                  \\ qpat_x_assum ‘DISJOINT ((_ ∪ _) DIFF _) _’ mp_tac
                  \\ simp [DISJOINT_ALT]
                  \\ qexists_tac ‘explode $ to_fmap map' ' k’
                  \\ simp []
                  \\ qpat_x_assum ‘DISJOINT (set (MAP FST _)) _’ mp_tac
                  \\ simp [DISJOINT_ALT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
                  \\ disch_then $ qspec_then ‘explode $ to_fmap map' ' k’ assume_tac
                  \\ gs [MEM_MAP, FORALL_PROD, PULL_EXISTS]
                  \\ conj_asm2_tac \\ gs []
                  \\ gs [IN_FRANGE]
                  \\ first_x_assum $ irule_at Any
                  \\ gs [MEM_FILTER])
              \\ gs [EVERY_MEM]
              \\ last_x_assum $ dxrule_then assume_tac
              \\ gvs [SUBSET_DEF]
              \\ metis_tac [])
          >- (simp [DISJOINT_ALT, PULL_FORALL]
              \\ gen_tac \\ strip_tac \\ strip_tac
              \\ gs [IN_FRANGE]
              >- (gs [EVERY_MEM]
                  \\ first_x_assum $ drule_then assume_tac
                  \\ rename1 ‘to_fmap map' ' k = to_fmap _ ' _’
                  \\ qpat_x_assum ‘DISJOINT (boundvars _) _’ mp_tac
                  \\ simp [DISJOINT_ALT]
                  \\ qexists_tac ‘explode $ to_fmap map' ' k’
                  \\ simp [IN_FRANGE]
                  \\ gs [MEM_FILTER]
                  \\ metis_tac [])
              \\ gs [EVERY_MEM]
              \\ last_x_assum $ dxrule_then assume_tac
              \\ gvs [SUBSET_DEF]
              \\ metis_tac [])
          >- simp [UNION_COMM])
      \\ disch_then $ qx_choose_then ‘e2’ $ qx_choose_then ‘e3’ assume_tac
      \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
      \\ first_assum $ irule_at $ Pos $ el 2
      \\ simp []
      \\ qpat_assum ‘thunk_Delay_Lam$exp_rel _ _’ $ irule_at Any
      \\ simp []
      \\ qexists_tac ‘vL’ \\ simp []
      \\ irule_at Any full_exp_rel_Letrec_Delay_Var
      \\ qpat_assum ‘full_exp_rel _ _’ $ irule_at Any
      \\ qexists_tac ‘ZIP (MAP explode mapl2, MAP (λv. explode $ to_fmap maps2 ' v) mapl2)’
      \\ qexists_tac ‘FLAT (MAP2 unfold_Delay_Lam expL2 (ZIP (vL, GENLIST (K T) (LENGTH vL))))’
      \\ qexists_tac ‘GENLIST (K T) (LENGTH vL)’
      \\ simp [MAP_FLAT, MAP_ZIP, cns_arities_def]
      \\ rpt $ conj_tac
      >- (simp [GSYM MAP_FLAT]
          \\ irule MAP_FST_change_expL
          \\ simp []
          \\ gs [LIST_REL_EL_EQN])
      >- (simp [EVERY_FLAT, EVERY_EL]
          \\ rw [EL_MAP, EL_MAP2, EL_ZIP, EL_GENLIST]
          \\ rename1 ‘unfold_Delay_Lam (EL n expL1)’
          \\ Cases_on ‘EL n expL1’
          \\ gvs [EVERY_EL] \\ rpt $ first_x_assum $ qspec_then ‘n’ assume_tac
          \\ gvs [EL_MAP]
          \\ Cases_on ‘SND (EL n expL1)’ \\ gvs [ok_bind_def, unfold_Delay_Lam_def]
          \\ CASE_TAC \\ gvs [ok_bind_def]
          \\ rename1 ‘EL n2 [_; _]’
          \\ Cases_on ‘n2’ \\ gvs [ok_bind_def]
          >- (rename1 ‘is_Lam e5’ \\ Cases_on ‘e5’ \\ gvs [is_Lam_def, ok_bind_def])
          >- (rename1 ‘SUC n2 < 2’ \\ Cases_on ‘n2’ \\ gvs [ok_bind_def]))
      >- (gvs [LIST_REL_EL_EQN, EVERY_FLAT, EVERY_EL]
          \\ rw [EL_MAP, EL_MAP2, EL_ZIP, EL_GENLIST]
          \\ rename1 ‘unfold_Delay_Lam (EL n expL2)’
          \\ Cases_on ‘EL n expL2’
          \\ rpt $ first_x_assum $ qspec_then ‘n’ assume_tac
          \\ gvs [EL_MAP]
          \\ Cases_on ‘SND (EL n expL1)’
          \\ gvs [ok_bind_def, full_exp_rel_def, unfold_Delay_Lam_def]
          \\ rename1 ‘is_Lam e4’
          \\ Cases_on ‘e4’ \\ gvs [ok_bind_def, is_Lam_def]
          \\ rename1 ‘EL n2 [_; _]’
          \\ Cases_on ‘n2’ \\ gvs [ok_bind_def]
          \\ rename1 ‘SUC n2 < 2’ \\ Cases_on ‘n2’ \\ gvs [ok_bind_def])
      >- (irule LIST_REL_full_exp_rel_MAP_unfold_Delay_Lam
          \\ simp []
          \\ gs [LIST_REL_EL_EQN])
      >- gvs [ALL_DISTINCT_APPEND]
      >- (gvs [EVERY_EL, EL_ZIP, EL_MAP, PULL_EXISTS]
          \\ gen_tac \\ strip_tac
          \\ first_x_assum $ drule_then assume_tac
          \\ gvs [MAP_FLAT]
          \\ rw []
          >- (qpat_x_assum ‘∀s. MEM s (FLAT _) ⇒ DISJOINT _ _’ mp_tac
              \\ qpat_x_assum ‘_ < LENGTH _’ mp_tac
              \\ qpat_x_assum ‘_ < LENGTH _’ mp_tac
              \\ qpat_x_assum ‘FDOM _ = _’ mp_tac
              \\ rpt $ pop_assum kall_tac
              \\ rw [] \\ gvs [MEM_EL, PULL_EXISTS]
              \\ gvs [GSYM MAP_FLAT]
              \\ first_x_assum $ drule_then assume_tac
              \\ gvs [EL_MAP, DISJOINT_ALT, PULL_EXISTS]
              \\ pairarg_tac \\ gs []
              \\ first_x_assum irule
              \\ simp [IN_FRANGE]
              \\ irule_at Any EQ_REFL
              \\ simp [EL_MEM])
          >- (dxrule_then assume_tac full_exp_rel_boundvars
              \\ dxrule_then assume_tac EQ_SYM
              \\ gs []
              \\ dxrule thunk_Delay_LamTheory.exp_rel_boundvars
              \\ qpat_x_assum ‘boundvars _ ∩ COMPL _ = _’ mp_tac
              \\ qpat_x_assum ‘∀n. _ < _ ⇒ _ ∈ _ ∧ _ ∉ _’ dxrule
              \\ qpat_x_assum ‘boundvars (exp_of _) ⊆ set_of _’ mp_tac
              \\ rpt $ pop_assum kall_tac
              \\ rw [SET_EQ_SUBSET, SUBSET_DEF]
              \\ qmatch_goalsub_abbrev_tac ‘v ∉ _’
              \\ rpt $ last_x_assum $ qspec_then ‘v’ assume_tac
              \\ gvs [])
          >- (qpat_x_assum ‘∀n. _ < _ ⇒ _ ∈ _ ∧ _ ∉ _’ drule
              \\ gs [SUBSET_DEF]
              \\ rename1 ‘EL n mapl2 ≠ _’
              \\ rpt $ last_x_assum $ qspec_then ‘explode $ EL n mapl2’ assume_tac
              \\ gvs [EL_MEM]
              \\ rw [] \\ strip_tac
              \\ dxrule_then assume_tac EQ_SYM
              \\ gvs []))
      >- (gvs [EVERY_EL] \\ rw []
          \\ last_x_assum $ drule_then assume_tac
          \\ last_x_assum $ drule_then assume_tac
          \\ gvs [EL_MAP]
          \\ pairarg_tac \\ gs []
          \\ rename1 ‘ok_bind (exp_of p2)’
          \\ Cases_on ‘p2’
          \\ gvs [cexp_ok_bind_def, ok_bind_def, exp_of_def, cexp_wf_def, Lams_split])
      >- metis_tac [LENGTH_MAP]
      >- (gvs [EVERY_MEM]
          \\ rw [] \\ last_x_assum $ dxrule_then assume_tac
          >- (pop_assum mp_tac \\ pop_assum mp_tac
              \\ qpat_x_assum ‘set (MAP FST _) ⊆ _’ mp_tac
              \\ rpt $ pop_assum kall_tac
              \\ pairarg_tac \\ rw []
              \\ gvs [SUBSET_DEF, MEM_MAP, PULL_EXISTS]
              \\ last_x_assum $ dxrule_then assume_tac
              \\ strip_tac
              \\ gvs [])
          >- (qpat_x_assum ‘LIST_REL thunk_Delay_Lam$exp_rel _ _’ mp_tac
              \\ pop_assum mp_tac \\ pop_assum mp_tac
              \\ qpat_x_assum ‘(_ ∪ _) DIFF _ ⊆ _’ mp_tac
              \\ qpat_x_assum ‘set (MAP FST _) ⊆ _’ mp_tac
              \\ rpt $ pop_assum kall_tac
              \\ pairarg_tac \\ rw []
              \\ gvs [SUBSET_DEF, MEM_MAP, PULL_EXISTS]
              \\ strip_tac
              \\ first_assum irule
              \\ last_x_assum irule
              \\ conj_tac
              >- (simp [FORALL_PROD]
                  \\ rw [] \\ strip_tac
                  \\ last_x_assum $ dxrule_then assume_tac
                  \\ fs [])
              \\ disj2_tac
              \\ gs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
              \\ first_x_assum $ drule_then assume_tac
              \\ first_assum $ irule_at Any
              \\ pairarg_tac \\ gs [EL_MAP]
              \\ dxrule_then assume_tac thunk_Delay_LamTheory.exp_rel_freevars
              \\ fs [SND_THM]
              \\ pairarg_tac \\ gvs [])
          >- (strip_tac \\ gvs [SUBSET_DEF]
              \\ rename1 ‘v ∉ set_of _’
              \\ rpt $ first_x_assum $ qspec_then ‘v’ assume_tac
              \\ gvs [])
          >- (strip_tac \\ gvs [SUBSET_DEF]))
      >- metis_tac [SUBSET_TRANS]
      >- (qpat_x_assum ‘LIST_REL thunk_Delay_Lam$exp_rel _ _’ kall_tac
          \\ gvs [exp_of_def, freevars_def, SUBSET_DEF]
          \\ rw []
          \\ gvs [MEM_EL, LIST_REL_EL_EQN, EVERY_EL]
          \\ rename1 ‘x ∈ EL n _’
          \\ rpt $ first_x_assum $ qspec_then ‘n’ assume_tac
          \\ gvs [EL_MAP]
          \\ pairarg_tac \\ gvs []
          \\ pairarg_tac \\ gvs [])
      >- (gvs [exp_of_def, boundvars_def, SUBSET_DEF]
          \\ rw []
          \\ gvs [MEM_EL, LIST_REL_EL_EQN, EVERY_EL, EL_MAP]
          >- (last_x_assum $ drule_then mp_tac
              \\ pop_assum mp_tac \\ pop_assum mp_tac
              \\ qpat_x_assum ‘∀x. _ ∈ set_of _ ⇒ _ ∈ set_of _’ mp_tac
              \\ rpt $ pop_assum kall_tac
              \\ pairarg_tac \\ rw []
              \\ pairarg_tac \\ gs [])
          >- (last_x_assum $ drule_then mp_tac
              \\ qpat_x_assum ‘∀x. _ ∈ set_of _ ⇒ _ ∈ set_of _’ mp_tac
              \\ rpt $ pop_assum kall_tac
              \\ pairarg_tac \\ rw []
              \\ pairarg_tac \\ gs []))
      >- (qpat_x_assum ‘full_exp_rel _ _’ mp_tac
          \\ qpat_x_assum ‘thunk_Delay_Lam$exp_rel _ _’ mp_tac
          \\ qpat_x_assum ‘_ ∩ COMPL _ = _’ mp_tac
          \\ qpat_x_assum ‘_ ∩ COMPL _ = _’ mp_tac
          \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
          \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
          \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
          \\ qpat_x_assum ‘EVERY _ binds''’ mp_tac
          \\ qpat_x_assum ‘MAP FST expL2 = MAP FST expL1’ mp_tac
          \\ qpat_x_assum ‘LENGTH _ = LENGTH _’ mp_tac
          \\ qpat_x_assum ‘set_of _ ⊆ set_of _’ mp_tac
          \\ qpat_x_assum ‘set_of _ ⊆ set_of _’ mp_tac
          \\ qpat_x_assum ‘set_of _ ⊆ set_of _’ mp_tac
          \\ qpat_x_assum ‘freevars _ ∪ _ DIFF _ ⊆ set_of _’ mp_tac
          \\ qpat_x_assum ‘boundvars (exp_of _) ⊆ set_of _’ mp_tac
          \\ qpat_x_assum ‘BIGUNION _ ⊆ set_of _’ mp_tac
          \\ qpat_x_assum ‘set (MAP FST _) ⊆ set_of _’ mp_tac
          \\ rpt $ pop_assum kall_tac
          \\ rw []
          \\ gs [SET_EQ_SUBSET, boundvars_def]
          \\ rw []
          >- (gs [GSYM DIFF_INTER_COMPL, DIFF_SUBSET]
              \\ rw []
              >- (gvs [SUBSET_DEF] \\ rw [] \\ metis_tac [])
              >- (simp [BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, FORALL_PROD]
                  \\ rw []
                  \\ drule_then (qspec_then ‘vL’ assume_tac) MEM_FLAT_MAP2_change
                  \\ gs [LIST_REL_EL_EQN]
                  \\ pop_assum $ dxrule_then assume_tac
                  \\ gs [MEM_EL]
                  \\ last_x_assum $ drule_then assume_tac
                  \\ pairarg_tac \\ gs [EVERY_EL]
                  \\ last_x_assum $ drule_then assume_tac
                  \\ gvs []
                  \\ qpat_x_assum ‘(_, _) = _’ assume_tac
                  \\ dxrule_then assume_tac EQ_SYM
                  \\ gvs []
                  \\ dxrule_then assume_tac full_exp_rel_boundvars
                  \\ gs [boundvars_FOLDL_replace_Force]
                  \\ gs [SUBSET_DEF])
              >- (qspecl_then [‘expL1’, ‘expL2’, ‘vL’] assume_tac MAP_FST_change_expL
                  \\ gs [] \\ gs [LIST_REL_EL_EQN]
                  \\ pop_assum $ kall_tac
                  \\ rw [SUBSET_DEF]
                  \\ gs [MEM_MAP, MEM_EL, EVERY_EL, LIST_REL_EL_EQN]
                  \\ simp [PULL_EXISTS]
                  \\ last_x_assum $ drule_then assume_tac
                  \\ last_x_assum $ drule_then assume_tac
                  \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                  \\ gvs [SUBSET_DEF]))
          >- (gs [GSYM DIFF_INTER_COMPL, DIFF_SUBSET]
              \\ rw []
              >- (gvs [SUBSET_DEF] \\ rw [] \\ metis_tac [])
              >- (qpat_x_assum ‘BIGUNION _ ⊆ BIGUNION _ ∪ _ ∪ COMPL _’ assume_tac
                  \\ gs [SUBSET_DEF]
                  \\ gen_tac \\ rename1 ‘x ∈ _’
                  \\ strip_tac
                  \\ first_x_assum $ qspec_then ‘x’ mp_tac
                  \\ impl_tac
                  >- (gs [MEM_MAP, PULL_EXISTS]
                      \\ pairarg_tac \\ gs []
                      \\ drule_then (qspec_then ‘vL’ assume_tac) MEM_FLAT_MAP2_change
                      \\ gs [] \\ gs [LIST_REL_EL_EQN]
                      \\ pop_assum $ dxrule_then assume_tac
                      \\ gs [MEM_EL, PULL_EXISTS]
                      \\ first_assum $ irule_at Any
                      \\ last_x_assum $ drule_then assume_tac
                      \\ pairarg_tac \\ gs []
                      \\ qpat_x_assum ‘(_, _) = _’ assume_tac
                      \\ dxrule_then assume_tac EQ_SYM
                      \\ gs []
                      \\ dxrule_then assume_tac full_exp_rel_boundvars
                      \\ gs [boundvars_FOLDL_replace_Force])
                 \\ metis_tac [])
              >- (qspecl_then [‘expL1’, ‘expL2’, ‘vL’] assume_tac MAP_FST_change_expL
                  \\ gs [] \\ gs [LIST_REL_EL_EQN]
                  \\ pop_assum $ kall_tac
                  \\ rw [SUBSET_DEF]
                  \\ gs [MEM_MAP, MEM_EL, EVERY_EL, LIST_REL_EL_EQN]
                  \\ simp [PULL_EXISTS]
                  \\ last_x_assum $ drule_then assume_tac
                  \\ last_x_assum $ drule_then assume_tac
                  \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                  \\ qpat_x_assum ‘set (MAP _ _) ⊆ (BIGUNION _) ∪ _ ∪ COMPL _’ mp_tac
                  \\ simp [SUBSET_DEF]
                  \\ rename1 ‘explode v1 = _’
                  \\ disch_then $ qspec_then ‘explode v1’ mp_tac
                  \\ impl_tac
                  >- (gvs [MEM_MAP, MEM_EL, PULL_EXISTS]
                      \\ first_assum $ irule_at Any
                      \\ gs [])
                  \\ rw [MEM_MAP, MEM_EL] \\ metis_tac []))
          >- (gs [GSYM DIFF_INTER_COMPL, DIFF_SUBSET]
              \\ rename1 ‘set_of vc3 ⊆ _’
              \\ simp [SUBSET_DEF] \\ rw []
              \\ rename1 ‘x ∈ set_of vc3’
              \\ qpat_x_assum ‘set_of vc3 ⊆ _ ∪ boundvars _’ mp_tac
              \\ simp [SUBSET_DEF]
              \\ disch_then $ qspec_then ‘x’ assume_tac \\ gs []
              \\ qpat_x_assum ‘set_of vc3 ⊆ _ ∪ _’ mp_tac
              \\ simp [SUBSET_DEF]
              \\ disch_then $ qspec_then ‘x’ assume_tac \\ gs []
              \\ qpat_x_assum ‘set_of _ ⊆ _’ mp_tac
              \\ simp [SUBSET_DEF]
              \\ disch_then $ qspec_then ‘x’ assume_tac \\ gs []
              \\ qpat_x_assum ‘set_of _ ⊆ _’ mp_tac
              \\ simp [SUBSET_DEF]
              \\ disch_then $ qspec_then ‘x’ assume_tac \\ gs []
              >- (disj2_tac \\ disj1_tac \\ disj2_tac
                  \\ gs [MEM_MAP, MEM_EL, LIST_REL_EL_EQN, PULL_EXISTS]
                  \\ last_x_assum $ drule_then assume_tac
                  \\ pairarg_tac \\ gs []
                  \\ pairarg_tac \\ gs []
                  \\ qspecl_then [‘expL1’, ‘expL2’, ‘vL’] assume_tac MEM_FLAT_MAP2_change2
                  \\ gs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
                  \\ pop_assum $ drule_then assume_tac \\ gs []
                  \\ first_assum $ irule_at Any
                  \\ dxrule_then assume_tac EQ_SYM
                  \\ gs []
                  \\ pop_assum kall_tac
                  \\ dxrule_then assume_tac full_exp_rel_boundvars
                  \\ gs []
                  \\ pop_assum kall_tac
                  \\ pop_assum kall_tac
                  \\ gs [boundvars_FOLDL_replace_Force])
              >- (qspecl_then [‘expL1’, ‘expL2’, ‘vL’] assume_tac MAP_FST_change_expL
                  \\ gs [] \\ gs [LIST_REL_EL_EQN]
                  \\ pop_assum kall_tac
                  \\ disj2_tac \\ disj2_tac
                  \\ gs [MEM_MAP, MEM_EL, PULL_EXISTS]
                  \\ last_x_assum $ drule_then assume_tac
                  \\ first_assum $ irule_at Any
                  \\ pairarg_tac \\ gs []
                  \\ pairarg_tac \\ gs []))
          >- (gs [GSYM DIFF_INTER_COMPL, DIFF_SUBSET]
              \\ rename1 ‘set_of vc3 ⊆ _’
              \\ simp [SUBSET_DEF] \\ rw []
              \\ rename1 ‘x ∈ set_of vc3’
              \\ rename1 ‘set_of vc3 ⊆ set_of vc2 ∪ _’
              \\ Cases_on ‘x ∈ set_of vc’ \\ gs []
              \\ qpat_x_assum ‘_ ⊆ _ ∪ set_of vc’ mp_tac
              \\ qpat_x_assum ‘_ ⊆ _ ∪ set_of vc’ mp_tac
              \\ qpat_x_assum ‘_ ⊆ set_of vc’ mp_tac
              \\ qpat_x_assum ‘_ ⊆ set_of vc’ mp_tac
              \\ qpat_x_assum ‘_ ⊆ set_of vc ∪ _’ mp_tac
              \\ qpat_x_assum ‘_ ⊆ set_of vc’ mp_tac
              \\ simp [SUBSET_DEF] \\ strip_tac \\ strip_tac
              \\ strip_tac \\ strip_tac \\ strip_tac \\ strip_tac
              \\ rpt $ first_x_assum $ qspec_then ‘x’ assume_tac
              \\ gs []))
      >- (simp [cexp_wf_def]
          \\ gs [EVERY_EL]
          \\ rw [EL_MAP]
          \\ rpt $ last_x_assum $ drule_then mp_tac
          \\ simp [EL_MAP]
          \\ rpt $ pop_assum kall_tac
          \\ pairarg_tac \\ rw [])
      >- (simp [exp_of_def, FOLDL_replace_Force_Letrec]
          \\ rw [FOLDL_APPEND]
          >- (simp [MAP_FST_FOLDL_no_change]
              \\ simp [FOLDL_MAP_comm]
              \\ simp [FOLDL_replace_Force_ZIP]
              \\ irule LIST_EQ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
              \\ rw [] \\ last_x_assum $ drule_then assume_tac
              \\ pairarg_tac \\ gs [FOLDL_APPEND]
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ pop_assum mp_tac
              \\ dxrule_then assume_tac EQ_SYM
              \\ strip_tac \\ gs []
              \\ irule FOLDL_replace_Force_change_map
              \\ gvs [EVERY_MEM]
              \\ rw [] \\ first_x_assum $ drule_then assume_tac
              \\ rw [] \\ rename1 ‘to_fmap (FOLDL _ map' l) ' v = _’
              \\ qspecl_then [‘v’, ‘MAP FST l’, ‘map'’] assume_tac $ GEN_ALL FOLDL_delete_thm
              \\ gs [FOLDL_MAP, LAMBDA_PROD, MEM_FILTER])
          \\ simp [MAP_FST_FOLDL_MAP_replace_Force, FOLDL_replace_Force_ZIP]
          \\ irule FOLDL_replace_Force_change_map
          \\ gvs [EVERY_MEM]
          \\ rw [] \\ first_x_assum $ drule_then assume_tac
          \\ gvs [MEM_FILTER]
          \\ dxrule_then assume_tac EQ_SYM \\ gs []
          \\ rename1 ‘to_fmap (FOLDL _ map' l) ' v = to_fmap _ ' _’
          \\ qspecl_then [‘v’, ‘MAP FST l’, ‘map'’] assume_tac $ GEN_ALL FOLDL_delete_thm
          \\ gvs [FOLDL_MAP, LAMBDA_PROD]))
  >~[‘rows_of _ (MAP _ rows) (OPTION_MAP _ fallthrough)’]

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
            \\ pairarg_tac \\ gs []
            \\ rename1 ‘vc' = (_, _) ⇒ _’
            \\ Cases_on ‘vc'’ \\ gvs [])
      \\ qspecl_then [‘rows’, ‘fallthrough’] mp_tac split_Delay_Lam_soundness_rows
      \\ impl_tac
      >- (gen_tac \\ rename1 ‘MEM e2 (MAP (SND o SND) rows)’
          \\ last_x_assum $ qspec_then ‘e2’ assume_tac
          \\ rpt $ gen_tac \\ strip_tac
          >- (‘cexp_size e2 < list_size (pair_size mlstring_size (pair_size (list_size mlstring_size) cexp_size)) rows’
                by (assume_tac cexp_size_lemma \\ fs []
                    \\ first_x_assum irule
                    \\ gvs [MEM_MAP]
                    \\ rename1 ‘SND (SND y)’ \\ PairCases_on ‘y’
                    \\ gvs []
                    \\ first_x_assum $ irule_at Any)
              \\ gvs [cexp_size_def]
              \\ strip_tac
              \\ first_x_assum $ drule_all_then assume_tac
              \\ gvs []
              \\ metis_tac [])
          >- (gvs [cexp_size_def]
              \\ strip_tac
              \\ first_x_assum $ drule_all_then assume_tac
              \\ gvs []
              \\ metis_tac []))
      \\ strip_tac
      \\ pop_assum $ drule_then assume_tac \\ gvs [SF ETA_ss]
      \\ rename1 ‘split_Delayed_Lam _ vc _’
      \\ pop_assum $ qspecl_then [‘m’, ‘vc’, ‘map_l’, ‘fallthrough'’] mp_tac
      \\ simp []
      \\ impl_tac
      >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
          \\ rw []
          >- (first_x_assum $ dxrule_then assume_tac
              \\ fs [])
          >- (Cases_on ‘fallthrough’ \\ fs []
              \\ rename1 ‘UNCURRY _ x’
              \\ Cases_on ‘x’ \\ fs [])
          >- (first_x_assum $ dxrule_then assume_tac
              \\ fs []))
      \\ rw [] \\ simp []
      \\ qpat_x_assum ‘thunk_Delay_Lam$exp_rel _ _’ $ irule_at Any
      \\ rpt $ first_x_assum $ irule_at Any
      \\ rw [] \\ gvs []
      >- (gs [cns_arities_def, SF ETA_ss]
          \\ CASE_TAC \\ gs []
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs [])
      >- metis_tac [SUBSET_TRANS]
      >- (gs [cexp_wf_def] \\ rw []
          >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
              \\ reverse $ rw []
              >- first_x_assum $ drule_then irule
              \\ gs [MEM_EL, PULL_EXISTS]
              \\ qpat_x_assum ‘MAP (FST o SND) _ = _’ mp_tac
              \\ once_rewrite_tac [GSYM LIST_REL_eq]
              \\ strip_tac
              \\ dxrule_then assume_tac $ iffLR LIST_REL_EL_EQN
              \\ gs [EL_MAP]
              \\ first_x_assum $ drule_then assume_tac
              \\ last_x_assum $ drule_then assume_tac
              \\ fs [SND_THM, FST_THM]
              \\ pairarg_tac \\ fs []
              \\ pairarg_tac \\ fs []
              \\ pairarg_tac \\ fs []
              \\ pairarg_tac \\ gs [])
          >- (strip_tac \\ fs [])
          >- (Cases_on  ‘fallthrough'’ \\ gs []
              \\ pairarg_tac \\ fs []
              \\ pairarg_tac \\ fs [UNCURRY])
          >- (Cases_on  ‘fallthrough'’ \\ gs []
              \\ pairarg_tac \\ fs []
              \\ pairarg_tac \\ fs [UNCURRY])))
  >~[‘Delay _’]

  >- (rename1 ‘split_Delayed_Lam e _ _’
      \\ rpt $ gen_tac \\ pairarg_tac
      \\ gvs [PULL_FORALL] \\ strip_tac
      \\ last_x_assum $ qspec_then ‘e’ assume_tac \\ fs [cexp_size_def]
      \\ pop_assum $ drule_all_then $ qx_choose_then ‘e_mid’ assume_tac
      \\ gvs [exp_of_def, FOLDL_replace_Force_Delay, exp_rel1_def, exp_rel2_def,
              freevars_def, boundvars_def, cexp_wf_def, PULL_EXISTS, cns_arities_def]
      \\ metis_tac [])
  >~[‘Force (exp_of e)’]

  >- (Cases_on ‘dest_Var e’ \\ gvs []
      >~[‘dest_Var e = SOME v’]
      >- (Cases_on ‘e’ \\ gvs [dest_Var_def, cexp_wf_def, boundvars_def, freevars_def, exp_of_def]
          \\ rpt $ gen_tac \\ CASE_TAC \\ strip_tac
          \\ gvs [exp_of_def, freevars_def, boundvars_def, lookup_thm, FLOOKUP_DEF, cexp_wf_def]
          >- (gvs [FOLDL_replace_Force_Force_Var1, exp_rel1_def, exp_rel2_def, boundvars_def, cns_arities_def])
          \\ gvs [exp_rel1_def, exp_rel2_def, boundvars_def, cns_arities_def]
          \\ conj_tac
          >- (gvs [SUBSET_DEF, PULL_EXISTS]
              \\ qpat_x_assum ‘∀x. _ ∈ FRANGE _ ⇒ _ ∈ _’ irule
              \\ gvs [IN_FRANGE]
              \\ metis_tac [])
          \\ gvs [FOLDL_replace_Force_Force_Var2])
      \\ rpt $ gen_tac \\ pairarg_tac \\ strip_tac \\ gvs [cexp_size_def, PULL_FORALL, cns_arities_def]
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
          >- (rename1 ‘Apps _ (MAP _ l)’
              \\ qspec_then ‘l’ assume_tac SNOC_CASES
              \\ gvs [FOLDL_MAP, FOLDL_SNOC, exp_rel1_def, cexp_wf_def])
          >- (rename1 ‘Lams (MAP _ l) _’
              \\ Cases_on ‘l’
              \\ gvs [exp_rel1_def, cexp_wf_def])
          >- (rename1 ‘Case m l fallthrough’
              \\ Cases_on ‘l’ \\ gs [rows_of_def, exp_rel1_def, exp_rel2_def]
              >- (Cases_on ‘fallthrough’ \\ gs [cexp_wf_def]
                  \\ pairarg_tac \\ gs [exp_rel1_def])
              >- (pairarg_tac \\ gs [exp_rel1_def, rows_of_def])))
      \\ gvs [DISJOINT_ALT]
      \\ rw [] \\ strip_tac \\ first_x_assum $ drule_then irule
      \\ simp [IN_FRANGE]
      \\ metis_tac [])
QED

Theorem split_Delayed_Lam_soundness:
  ∀e vc e_out vc_out.
     split_Delayed_Lam e vc (empty compare) = (e_out, vc_out) ∧
     closed (exp_of e) ∧
     pure_semantics$safe_itree (semantics (exp_of e) Done []) ∧
     boundvars (exp_of e) ⊆ set_of vc ∧
     vars_ok vc ∧
     cexp_wf e
     ⇒ cexp_wf e_out ∧
       cns_arities e = cns_arities e_out ∧
       boundvars (exp_of e_out) ⊆ set_of vc_out ∧
       closed (exp_of e_out) ∧
       vars_ok vc_out ∧
       semantics (exp_of e) Done [] = semantics (exp_of e_out) Done []
Proof
  rpt $ gen_tac \\ strip_tac
  \\ dxrule_then (qspec_then ‘[]’ assume_tac) split_Delayed_Lam_soundness_lemma
  \\ gs [closed_def, empty_thm, TotOrd_compare]
  \\ drule_then assume_tac delay_lam_semantics
  \\ dxrule_then assume_tac thunk_Delay_LamTheory.exp_rel_freevars
  \\ drule_then assume_tac full_let_delay_var_semantics
  \\ dxrule_then assume_tac full_exp_rel_freevars
  \\ gs [closed_def]
QED

Theorem split_delated_lam_soundness:
  ∀e vc e_out vc_out.
     split_delated_lam do_it e vc = (e_out, vc_out) ∧
     closed (exp_of e) ∧
     pure_semantics$safe_itree (semantics (exp_of e) Done []) ∧
     boundvars (exp_of e) ⊆ set_of vc ∧
     vars_ok vc ∧
     cexp_wf e
     ⇒ cexp_wf e_out ∧
       cns_arities e = cns_arities e_out ∧
       boundvars (exp_of e_out) ⊆ set_of vc_out ∧
       closed (exp_of e_out) ∧
       vars_ok vc_out ∧
       semantics (exp_of e) Done [] = semantics (exp_of e_out) Done []
Proof
  rewrite_tac [split_delated_lam_def]
  \\ reverse $ Cases_on ‘do_it’ >- gvs [] \\ fs []
  \\ rpt gen_tac \\ strip_tac
  \\ drule_all split_Delayed_Lam_soundness \\ simp []
QED
