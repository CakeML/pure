(*
   Formalises the notion of "demand" as used in demand/strictness analysis.
*)
Theory pure_demand
Ancestors
  arithmetic list mlstring alist option pair ltree llist bag
  pred_set relation rich_list finite_map pure_exp pure_value
  pure_eval pure_eval_lemmas pure_exp_lemmas pure_misc
  pure_exp_rel pure_congruence pure_alpha_equiv pure_alpha_equiv
  pure_letrec_cong pure_letrec_seq
Libs
  term_tactic dep_rewrite BasicProvers


(** begin ctxt **)

(* Definitions *)

Datatype:
  ctxt = Nil
       | IsFree mlstring ctxt
       | Bind mlstring exp ctxt
       | RecBind ((mlstring # exp) list) ctxt
End

Definition unfold_ctxt_def:
  unfold_ctxt Nil e = e ∧
  unfold_ctxt (IsFree v c) e = Lam v (unfold_ctxt c e) ∧
  unfold_ctxt (Bind v e c) e2 = Let v e (unfold_ctxt c e2) ∧
  unfold_ctxt (RecBind bL c) e = Letrec bL (unfold_ctxt c e)
End

Definition concat_rev_ctxt_def:
  concat_rev_ctxt Nil c = c ∧
  concat_rev_ctxt (IsFree v c1) c2 = concat_rev_ctxt c1 (IsFree v c2) ∧
  concat_rev_ctxt (Bind v e c1) c2 = concat_rev_ctxt c1 (Bind v e c2) ∧
  concat_rev_ctxt (RecBind bL c1) c2 = concat_rev_ctxt c1 (RecBind bL c2)
End

Definition concat_ctxt_def:
  concat_ctxt Nil c = c ∧
  concat_ctxt (IsFree v c1) c2 = IsFree v (concat_ctxt c1 c2) ∧
  concat_ctxt (Bind v e c1) c2 = Bind v e (concat_ctxt c1 c2) ∧
  concat_ctxt (RecBind bL c1) c2 = RecBind bL (concat_ctxt c1 c2)
End

Definition not_bound_in_ctxt_def:
  not_bound_in_ctxt Nil v = T ∧
  not_bound_in_ctxt (IsFree v1 c) v2 = (v1 ≠ v2 ∧ not_bound_in_ctxt c v2) ∧
  not_bound_in_ctxt (Bind v1 e c) v2 = (v1 ≠ v2 ∧ not_bound_in_ctxt c v2) ∧
  not_bound_in_ctxt (RecBind bL c) v = (not_bound_in_ctxt c v ∧ ¬MEM v (MAP FST bL))
End

Definition eq_when_applied_def:
  (eq_when_applied Nil e1 e2 len = ∀l. len = LENGTH l ⇒ (Apps e1 l) ≈ (Apps e2 l)) ∧
  eq_when_applied (Bind v e c) e1 e2 len = eq_when_applied c (Let v e e1) (Let v e e2) len ∧
  eq_when_applied (IsFree v c) e1 e2 len = (∀e. closed e ⇒ eq_when_applied c (Let v e e1) (Let v e e2) len) ∧
  eq_when_applied (RecBind b c) e1 e2 len = eq_when_applied c (Letrec b e1) (Letrec b e2) len
End

Definition exp_eq_in_ctxt_def:
  exp_eq_in_ctxt Nil = (λe1 e2. e1 ≈ e2) ∧
  exp_eq_in_ctxt (IsFree s c) e1 e2 = (∀e3. closed e3 ⇒ exp_eq_in_ctxt c (Let s e3 e1) (Let s e3 e2)) ∧
  exp_eq_in_ctxt (Bind s e3 c) e1 e2 = exp_eq_in_ctxt c (Let s e3 e1) (Let s e3 e2) ∧
  exp_eq_in_ctxt (RecBind l c) e1 e2 = exp_eq_in_ctxt c (Letrec l e1) (Letrec l e2)
End

Theorem exp_eq_l_refl:
  ∀b l. LIST_REL (λx y. (x ≅? y) b) l l
Proof
  gen_tac
  \\ Induct
  \\ fs [exp_eq_refl]
QED

Theorem concat_Nil:
  ∀c. concat_ctxt c Nil = c
Proof
  Induct >> gvs [concat_ctxt_def]
QED

Theorem exp_eq_unfold_cong:
  ∀c e1 e2 b. (e1 ≅? e2) b ⇒ (unfold_ctxt c e1 ≅? unfold_ctxt c e2) b
Proof
  Induct >> rw [unfold_ctxt_def] >> last_x_assum $ dxrule_then assume_tac >>
  gvs [exp_eq_App_cong, exp_eq_refl, exp_eq_Lam_cong, exp_eq_Letrec_cong, exp_eq_l_refl]
QED

Theorem eq_when_applied_0:
  ∀c e1 e2. exp_eq_in_ctxt c e1 e2 = eq_when_applied c e1 e2 0
Proof
  Induct >>
  gvs [exp_eq_in_ctxt_def, eq_when_applied_def, Apps_def]
QED

Definition ctxt_size_def[allow_rebind]:
  ctxt_size Nil = 0n ∧
  ctxt_size (IsFree s ctxt) = 1 + ctxt_size ctxt ∧
  ctxt_size (Bind s e ctxt) =
    1 + mlstring_size s +  exp_size e + ctxt_size ctxt ∧
  ctxt_size (RecBind sel ctxt) = 1 + exp1_size sel + ctxt_size ctxt
End

(* Preliminaries *)

Theorem exp_eq_Apps_cong:
  ∀l l' b e e'. LIST_REL (λx y. (x ≅? y) b) l l' ⇒ (e ≅? e') b ⇒ (Apps e l ≅? Apps e' l') b
Proof
  Induct
  \\ fs [Apps_def]
  \\ rw [Apps_def]
  \\ fs [Apps_def]
  \\ first_x_assum $ irule
  \\ fs [exp_eq_App_cong]
QED

Theorem exp_eq_Lams_cong:
  ∀l e e' b. (e ≅? e') b ⇒ (Lams l e ≅? Lams l e') b
Proof
  Induct
  \\ rw [Lams_def]
  \\ fs [exp_eq_Lam_cong]
QED

Theorem eval_Prim:
  ∀ope eL eL'. LIST_REL (λe1 e2. eval e1 = eval e2) eL eL' ⇒ eval (Prim ope eL) = eval (Prim ope eL')
Proof
  Cases
  \\ rw [eval_thm]
  >~[‘MAP _ _ = MAP _ _’]
  >- (irule LIST_EQ
      \\ gvs [LIST_REL_EL_EQN, EL_MAP])
  >~[‘AtomOp’]
  >- (fs [eval_def]
      \\ once_rewrite_tac [v_unfold]
      \\ fs [eval_wh_Prim]
      \\ qsuff_tac ‘get_atoms (MAP eval_wh eL') = get_atoms (MAP eval_wh eL)’
      >- (CASE_TAC \\ fs [])
      \\ fs [get_atoms_def]
      \\ qsuff_tac ‘EXISTS error_Atom (MAP eval_wh eL) ⇔ EXISTS error_Atom (MAP eval_wh eL')’
      >- (strip_tac
          \\ IF_CASES_TAC
          \\ simp []
          \\ qsuff_tac ‘MEM wh_Diverge (MAP eval_wh eL) ⇔ MEM wh_Diverge (MAP eval_wh eL')’
          >- (strip_tac
              \\ IF_CASES_TAC
              \\ simp []
              \\ irule LIST_EQ
              \\ rw []
              \\ gvs [LIST_REL_EL_EQN, EL_MAP, EVERY_EL]
              \\ rpt $ first_x_assum drule
              \\ once_rewrite_tac [v_unfold]
              \\ rpt FULL_CASE_TAC
              \\ rw [dest_Atom_def, error_Atom_def])
          \\ eq_tac
          \\ strip_tac
          \\ gvs [MEM_EL, LIST_REL_EL_EQN]
          \\ first_assum $ irule_at Any
          \\ first_assum drule
          \\ once_rewrite_tac [v_unfold]
          \\ rpt FULL_CASE_TAC
          \\ gvs [EL_MAP])
      \\ eq_tac
      \\ strip_tac
      \\ gvs [EXISTS_MEM, MEM_EL, EL_MAP, LIST_REL_EL_EQN]
      \\ rename1 ‘MAP eval_wh eL2’
      \\ qexists_tac ‘eval_wh (EL n eL2)’
      \\ first_x_assum drule
      \\ once_rewrite_tac [v_unfold]
      \\ rpt FULL_CASE_TAC
      \\ fs [error_Atom_def]
      \\ rw []
      \\ first_assum $ irule_at Any
      \\ fs [EL_MAP])
  \\ Cases_on ‘eL’ \\ Cases_on ‘eL'’ \\ fs []
  \\ rename1 ‘LIST_REL _ t1 t2’
  \\ Cases_on ‘t1’ \\ Cases_on ‘t2’ \\ gvs [eval_thm]
  >~[‘Prim Seq (_::_::_)’]
  >- (rename1 ‘LIST_REL _ t1 t2’
      \\ Cases_on ‘t1’ \\ Cases_on ‘t2’
      \\ gvs [eval_thm, eval_def]
      \\ once_rewrite_tac [v_unfold]
      \\ fs [eval_wh_Prim])
  >~[‘Prim If (_::_::_)’]
  >- (rename1 ‘LIST_REL _ t1 t2’
      \\ Cases_on ‘t1’ \\ Cases_on ‘t2’ \\ gvs []
      >~[‘_::_::_::_’]
      >- (rename1 ‘LIST_REL _ t1 t2’
          \\ Cases_on ‘t1’ \\ Cases_on ‘t2’
          \\ gvs [eval_thm, eval_def]
          \\ once_rewrite_tac [v_unfold]
          \\ rw [eval_wh_Prim])
      \\ rw [eval_def]
      \\ once_rewrite_tac [v_unfold]
      \\ rw [eval_wh_Prim])
  \\ rw [eval_def]
  \\ once_rewrite_tac [v_unfold]
  \\ rw [eval_wh_Prim]
QED

Theorem FLOOKUP_LUPDATE:
  ∀l f n v. FLOOKUP (f |++ l) n = SOME v ⇒ MEM (n, v) l ∨ FLOOKUP f n = SOME v
Proof
  Induct
  \\ fs [FUPDATE_LIST_THM]
  \\ PairCases \\ rw []
  \\ first_x_assum $ dxrule_then assume_tac
  \\ gvs [FLOOKUP_UPDATE]
  \\ FULL_CASE_TAC \\ fs []
QED

Theorem Let_Lam:
  ∀v w e1 e2 b. closed e1 ∧ v ≠ w ⇒ (Let v e1 (Lam w e2) ≅? Lam w (Let v e1 e2)) b
Proof
  rw []
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality
  \\ gvs [subst1_def]
  \\ irule exp_eq_Lam_cong
  \\ irule $ iffLR exp_eq_sym
  \\ irule beta_equality
  \\ gvs []
QED

Theorem Let_Lam_weak:
  ∀v w e1 e2 b. v ≠ w ⇒ w ∉ freevars e1 ⇒ (Let v e1 (Lam w e2) ≅? Lam w (Let v e1 e2)) b
Proof
  rw [exp_eq_def, bind_def] >> IF_CASES_TAC >>
  gvs [app_bisimilarity_eq, exp_eq_refl] >>
  rpt (irule_at Any IMP_closed_subst) >>
  drule_then assume_tac $ GSYM subst_fdomsub >>
  gvs [subst_def, DOMSUB_COMMUTES] >>
  irule_at Any Let_Lam >>
  irule_at Any IMP_closed_subst >>
  rw [FRANGE_FLOOKUP]
QED

Theorem FDIFF_DOMSUB:
  ∀f v s. FDIFF (f \\ s) v = (FDIFF f v) \\ s
Proof
  rw [FDIFF_def, fmap_domsub, INTER_COMM]
QED

Theorem MAP_subst_fdomsub:
  ∀v l f. EVERY (λe. v ∉ freevars e) (MAP SND l) ⇒
          MAP (λ(s, e). (s, subst (FDIFF f (set (MAP FST l)) \\ v) e)) l
          = MAP (λ(s, e). (s, subst (FDIFF f (set (MAP FST l))) e)) l
Proof
  rw [EVERY_EL] >> irule LIST_EQ >>
  rw [EL_MAP] >> first_x_assum $ drule_then assume_tac >>
  rename1 ‘EL x l’ >> qabbrev_tac ‘p = EL x l’ >> PairCases_on ‘p’ >>
  gvs [subst_fdomsub, EL_MAP]
QED

Theorem Letrec_Lam:
  ∀l w e b. EVERY (λe. freevars e ⊆ set (MAP FST l)) (MAP SND l) ∧ ¬MEM w (MAP FST l)
          ⇒ (Letrec l (Lam w e) ≅? Lam w (Letrec l e)) b
Proof
  rw []
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality_Letrec
  \\ gvs [subst_funs_eq_subst, subst_def]
  \\ irule exp_eq_Lam_cong
  \\ irule $ iffLR exp_eq_sym
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality_Letrec
  \\ gvs [subst_funs_eq_subst]
  \\ irule eval_IMP_exp_eq
  \\ rw []
  \\ rpt AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ irule $ GSYM DOMSUB_NOT_IN_DOM
  \\ gvs [FDOM_FUPDATE_LIST]
  \\ strip_tac \\ last_x_assum irule
  \\ gvs [MEM_EL]
  \\ first_assum $ irule_at Any
  \\ gvs [EL_MAP]
  \\ rename1 ‘FST (_ p)’
  \\ PairCases_on ‘p’
  \\ fs []
QED

Theorem Letrec_Lam_weak:
  ∀l v e b. EVERY (λe. v ∉ freevars e) (MAP SND l) ∧ ¬ MEM v (MAP FST l)
            ⇒ (Letrec l (Lam v e) ≅? Lam v (Letrec l e)) b
Proof
  rw [exp_eq_def, bind_def] >> IF_CASES_TAC >>
  gvs [app_bisimilarity_eq, exp_eq_refl] >>
  rpt $ irule_at Any IMP_closed_subst >>
  gvs [subst_def, FDIFF_DOMSUB, MAP_subst_fdomsub] >>
  irule_at Any Letrec_Lam >>
  gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, EVERY_EL, EL_MAP] >>
  rw [FRANGE_FLOOKUP]
  >- (rename1 ‘EL n l’ >> qabbrev_tac ‘p = EL n l’ >>
      PairCases_on ‘p’ >>
      ‘∀v. v ∈ FRANGE (FDIFF f (set (MAP FST l))) ⇒ closed v’
        by (rw [FRANGE_FLOOKUP, FLOOKUP_FDIFF] >>
            first_x_assum irule >>
            pop_assum $ irule_at Any) >>
      gvs [freevars_subst, SUBSET_DEF, IN_DIFF, FDOM_FDIFF] >>
      gen_tac >> rename1 ‘MEM x _’ >>
      last_x_assum $ qspecl_then [‘x’] assume_tac >>
      last_x_assum $ qspecl_then [‘x’] assume_tac >>
      rw [] >> gvs []
      >- (last_x_assum $ qspecl_then [‘freevars p1’] assume_tac >>
          gvs [MEM_MAP] >> pop_assum $ qspecl_then [‘EL n l’] assume_tac >>
          gvs [EL_MEM])
      >- (last_x_assum $ qspecl_then [‘freevars p1’] assume_tac >>
          gvs [MEM_MAP] >> pop_assum $ qspecl_then [‘EL n l’] assume_tac >>
          gvs [EL_MEM]) >>
      gvs [MEM_EL] >>
      first_assum $ irule_at Any >>
      rw [EL_MAP] >>
      rename1 ‘FST p2’ >> PairCases_on ‘p2’ >> fs [])
  >- (strip_tac >> last_x_assum irule >>
      gvs [MEM_EL] >> first_assum $ irule_at Any >>
      gvs [EL_MAP] >> rename1 ‘FST p’ >> PairCases_on ‘p’ >>
      fs [])
QED

Theorem Let_not_in_freevars:
  ∀v e e2 b. v ∉ freevars e2 ⇒ (Let v e e2 ≅? e2) b
Proof
  rw [] >>
  irule eval_IMP_exp_eq >>
  dxrule_then assume_tac $ GSYM subst_fdomsub >>
  rw [subst_def, eval_thm, bind1_def, FRANGE_FLOOKUP, IMP_closed_subst]
QED

Theorem Letrec_not_in_freevars:
  ∀l e b. EVERY (λv. v ∉ freevars e) (MAP FST l) ⇒ (Letrec l e ≅? e) b
Proof
  rw [exp_eq_def, bind_def] >> IF_CASES_TAC >>
  gvs [app_bisimilarity_eq, exp_eq_refl] >>
  rpt $ irule_at Any IMP_closed_subst >>
  gvs [subst_def, FRANGE_FLOOKUP] >>
  irule exp_eq_trans >>
  irule_at Any beta_equality_Letrec >>
  conj_asm1_tac
  >- (rw [EVERY_EL, EL_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      rename1 ‘EL n l’ >> qabbrev_tac ‘p = EL n l’ >> PairCases_on ‘p’ >>
      ‘∀v. v ∈ FRANGE (FDIFF f (set (MAP FST l))) ⇒ closed v’
        by (rw [FRANGE_FLOOKUP, FLOOKUP_FDIFF] >>
            first_x_assum irule >>
            pop_assum $ irule_at Any) >>
      gvs [freevars_subst, SUBSET_DEF, IN_DIFF, FDOM_FDIFF] >>
      gen_tac >> rename1 ‘MEM x _’ >>
      last_x_assum $ qspecl_then [‘x’] assume_tac >>
      rw [] >> gvs []
      >- (first_x_assum $ qspecl_then [‘freevars p1’] assume_tac >>
          gvs [MEM_MAP] >> pop_assum $ qspecl_then [‘EL n l’] assume_tac >>
          gvs [EL_MEM]) >>
      gvs [MEM_EL] >>
      first_assum $ irule_at Any >> rw [EL_MAP] >>
      rename1 ‘FST p2’ >> PairCases_on ‘p2’ >> fs []) >>
  dxrule_then assume_tac subst_funs_eq_subst >>
  qspecl_then [‘f’, ‘e’, ‘set (MAP FST l)’] assume_tac $ GSYM subst_FDIFF' >>
  gvs [EVERY_MEM] >>
  rw [exp_eq_refl, IMP_closed_subst, FRANGE_FLOOKUP]
QED

Theorem Let_Letrec:
  ∀s l e1 e2 b. EVERY (λe. s ∉ freevars e) (MAP SND l) ∧ ¬MEM s (MAP FST l)
                ∧ EVERY (λv. v ∉ freevars e1) (MAP FST l)
                ⇒ (Let s e1 (Letrec l e2) ≅? Letrec l (Let s e1 e2)) b
Proof
  rw [] >>
  irule exp_eq_trans >>
  irule_at (Pos hd) exp_eq_App_cong >>
  irule_at (Pos hd) $ iffLR exp_eq_sym >>
  irule_at Any Letrec_Lam_weak >> fs [] >>
  irule_at Any exp_eq_refl >>
  irule $ iffLR exp_eq_sym >>
  irule exp_eq_trans >>
  irule_at Any Letrec_App >>
  irule exp_eq_App_cong >>
  gvs [exp_eq_refl, Letrec_not_in_freevars]
QED

Theorem Let_Let:
  ∀v w e1 e2 e3 b. v ≠ w ∧ v ∉ freevars e2 ∧ w ∉ freevars e1 ⇒
                   (Let v e1 (Let w e2 e3) ≅? Let w e2 (Let v e1 e3)) b
Proof
  rw []
  \\ irule eval_IMP_exp_eq
  \\ rw [subst_def]
  \\ rename1 ‘subst (f \\ _ \\ _)’
  \\ ‘∀v. v ∈ FRANGE f ⇒ closed v’ by (rw [FRANGE_FLOOKUP])
  \\ drule $ GSYM subst_fdomsub
  \\ last_x_assum assume_tac
  \\ last_x_assum assume_tac
  \\ drule $ GSYM subst_fdomsub
  \\ rw [eval_Let, subst_def, bind1_def, IMP_closed_subst, DOMSUB_COMMUTES]
  \\ AP_TERM_TAC
  \\ rw [fmap_domsub, COMPL_UNION]
  \\ irule subst1_subst1
  \\ gvs [IMP_closed_subst]
QED

Theorem Let_Apps:
  ∀eL v e1 e2 b. (Let v e1 (Apps e2 eL) ≅? Apps (Let v e1 e2) (MAP (Let v e1) eL)) b
Proof
  Induct >> rw [Apps_def, exp_eq_refl] >>
  irule exp_eq_trans >> pop_assum $ irule_at Any >>
  irule exp_eq_Apps_cong >> gvs [Let_App, exp_eq_l_refl]
QED

Theorem App_Seq:
  ∀b. (App (Seq p f) e ≅? Seq p (App f e)) b
Proof
  irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_App, eval_wh_Seq]
  \\ fs []
QED

Theorem Apps_Seq:
  ∀eL e e' b. (Apps (Seq e e') eL ≅? Seq e (Apps e' eL)) b
Proof
  Induct >> rw [Apps_def, exp_eq_refl] >>
  irule exp_eq_trans >> pop_assum $ irule_at Any >>
  irule exp_eq_Apps_cong >> gvs [exp_eq_l_refl, App_Seq]
QED

Theorem Proj_Seq2:
  ∀b. (Proj x i (Seq e e') ≅? Seq e (Proj x i e')) b
Proof
  irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_Proj, eval_wh_Seq]
  \\ fs []
QED

Theorem If_Seq:
  ∀e e' e'' e''' b. (If (Seq e e') e'' e''' ≅? Seq e (If e' e'' e''')) b
Proof
  rpt gen_tac
  \\ irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_If, eval_wh_Seq]
  \\ fs []
QED

Theorem Seq_comm:
  Seq (Seq x y) z ≈ Seq (Seq y x) z
Proof
  irule no_err_eval_wh_IMP_exp_eq
  \\ rw [subst_def, no_err_eval_wh_def, eval_wh_Seq]
  \\ fs []
  \\ Cases_on ‘eval_wh (subst f x)’
  \\ Cases_on ‘eval_wh (subst f y)’
  \\ fs []
QED

Theorem If_Seq2:
  ∀e ec et ee.  If ec (Seq e et) (Seq e ee) ≈ Seq e (If ec et ee)
Proof
  rpt gen_tac
  \\ irule no_err_eval_wh_IMP_exp_eq
  \\ rw [no_err_eval_wh_def, freevars_def, subst_def, eval_wh_If, eval_wh_Seq]
  \\ fs []
QED

Theorem IsEq_Seq:
  ∀b b2 e e' n i. (IsEq n i b2 (Seq e e') ≅? Seq e (IsEq n i b2 e')) b
Proof
  rpt gen_tac
  \\ irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_IsEq, eval_wh_Seq]
  \\ fs []
QED

Definition well_written_def:
  well_written (Cons s) l = T ∧
  well_written (Proj s i) [e] = T ∧
  well_written (IsEq s i b) [e] = T ∧
  well_written If [e; e'; e''] = T ∧
  well_written Seq [e; e'] = T ∧
  well_written (AtomOp op) l = T ∧
  well_written _ _ = F
End

Theorem not_well_written_is_fail:
  ∀b ope l.
    ¬ well_written ope l ⇒
    (Prim ope l ≅? Fail) b
Proof
  rw []
  \\ Cases_on ‘ope’
  \\ fs [well_written_def]
  \\ Cases_on ‘l’
  >>~[‘(Prim _ [] ≅? Fail) _’]
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  \\ rename1 ‘hd::tl’
  \\ Cases_on ‘tl’
  \\ fs [well_written_def]
  >>~[‘Prim _ [hd]’]
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  \\ rename1 ‘h0::h1::tl’
  \\ Cases_on ‘tl’
  \\ fs [well_written_def]
  >~[‘Prim If (h0::h1::h2::tl)’]
  >- (Cases_on ‘tl’
      \\ fs [well_written_def]
      \\ irule eval_wh_IMP_exp_eq
      \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  \\ irule eval_wh_IMP_exp_eq
  \\ fs [subst_def, eval_wh_def, eval_wh_to_def]
QED

(* Part on context *)

Theorem eq_when_applied_refl:
  ∀c e len. eq_when_applied c e e len
Proof
  Induct
  \\ gvs [eq_when_applied_def, exp_eq_refl]
QED

Theorem eq_when_applied_l_refl:
  ∀c l len. LIST_REL (λe1 e2. eq_when_applied c e1 e2 len) l l
Proof
  gen_tac
  \\ Induct
  \\ fs [eq_when_applied_refl]
QED

Theorem eq_when_applied_sym:
  ∀c e1 e2 len. eq_when_applied c e1 e2 len ⇔ eq_when_applied c e2 e1 len
Proof
  Induct
  \\ rw [] \\ eq_tac
  \\ gvs [eq_when_applied_def, exp_eq_sym]
QED

Theorem eq_when_applied_trans:
  ∀c e1 e2 e3 len. eq_when_applied c e1 e2 len
                   ∧ eq_when_applied c e2 e3 len
                   ⇒ eq_when_applied c e1 e3 len
Proof
  Induct
  \\ rw []
  \\ gvs [eq_when_applied_def] \\ rw []
  >- (irule exp_eq_trans
      \\ pop_assum $ irule_at Any \\ fs [])
  \\ last_x_assum irule
  \\ first_x_assum $ irule_at Any
  \\ gvs []
QED

Theorem exp_eq_in_ctxt_refl:
  ∀c e. exp_eq_in_ctxt c e e
Proof
  Induct
  \\ gvs [exp_eq_in_ctxt_def, exp_eq_refl]
QED

Theorem exp_eq_in_ctxt_l_refl:
  ∀c l. LIST_REL (exp_eq_in_ctxt c) l l
Proof
  gen_tac
  \\ Induct
  \\ fs [exp_eq_in_ctxt_refl]
QED

Theorem exp_eq_in_ctxt_sym:
  ∀c e1 e2. exp_eq_in_ctxt c e1 e2 ⇔ exp_eq_in_ctxt c e2 e1
Proof
  gvs [eq_when_applied_0, eq_when_applied_sym]
QED

Theorem exp_eq_in_ctxt_trans:
  ∀c e1 e2 e3. exp_eq_in_ctxt c e1 e2 ∧ exp_eq_in_ctxt c e2 e3 ⇒ exp_eq_in_ctxt c e1 e3
Proof
  rw [eq_when_applied_0] >>
  dxrule_then (dxrule_then irule) eq_when_applied_trans
QED

Theorem last_exists:
  ∀l. LENGTH l > 0 ⇒ ∃x t. l = SNOC x t
Proof
  Induct
  \\ fs []
  \\ rw []
  \\ rename1 ‘hd::tl’
  \\ Cases_on ‘tl’
  \\ fs []
QED

Theorem last_Apps:
  ∀l x e. Apps e (l ++ [x]) = App (Apps e l) x
Proof
  Induct
  \\ fs [Apps_def]
QED

Theorem eq_when_applied_SUC:
  ∀c e1 e2 len. eq_when_applied c e1 e2 len
                ⇒ eq_when_applied c e1 e2 (SUC len)
Proof
  Induct >> gvs [eq_when_applied_def] >>
  rpt gen_tac >> strip_tac >> rw [] >>
  qspecl_then [‘l’] assume_tac last_exists >> gvs [last_Apps, SNOC_APPEND] >>
  irule exp_eq_App_cong >>
  last_x_assum $ irule_at Any >>
  gvs [exp_eq_refl]
QED

Theorem eq_when_applied_bigger:
  ∀len2 len1 c e1 e2. eq_when_applied c e1 e2 len1 ∧ len1 ≤ len2
                      ⇒ eq_when_applied c e1 e2 len2
Proof
  Induct >> gvs [] >> gen_tac >>
  rename1 ‘len1 ≤ SUC len2’ >> Cases_on ‘len1 = SUC len2’ >> rw [] >>
  irule eq_when_applied_SUC >> last_x_assum $ dxrule_then irule >>
  gvs []
QED

Theorem exp_eq_in_ctxt_IMP_eq_when_applied:
  ∀c e1 e2 len. exp_eq_in_ctxt c e1 e2 ⇒ eq_when_applied c e1 e2 len
Proof
  Induct >>
  gvs [exp_eq_in_ctxt_def, eq_when_applied_def, exp_eq_Apps_cong, exp_eq_l_refl]
QED

Theorem exp_eq_IMP_exp_eq_in_ctxt:
  ∀c e e'. e ≈ e' ⇒ exp_eq_in_ctxt c e e'
Proof
  Induct
  \\ gvs [exp_eq_in_ctxt_def]
  \\ rw []
  \\ first_x_assum irule
  \\ gvs [exp_eq_Letrec_cong, exp_eq_App_cong, exp_eq_Lam_cong, exp_eq_refl, exp_eq_l_refl]
QED

Theorem exp_eq_IMP_eq_when_applied:
  ∀c e e' len. e ≈ e' ⇒ eq_when_applied c e e' len
Proof
  rw [] \\ irule exp_eq_in_ctxt_IMP_eq_when_applied
  \\ gvs [exp_eq_IMP_exp_eq_in_ctxt]
QED

Theorem exp_eq_in_ctxt_Prim:
  ∀c eL eL' ope. LIST_REL (exp_eq_in_ctxt c) eL eL'
                 ⇒ exp_eq_in_ctxt c (Prim ope eL) (Prim ope eL')
Proof
  Induct
  \\ gvs [exp_eq_in_ctxt_def, exp_eq_refl, exp_eq_Prim_cong]
  \\ rw []
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at Any exp_eq_in_ctxt_trans
  \\ last_x_assum $ irule_at Any
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  >~[‘Letrec’]
  >- (irule_at Any Letrec_Prim
      \\ irule_at Any $ iffLR exp_eq_sym
      \\ irule_at Any Letrec_Prim
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, exp_eq_in_ctxt_def])
  \\ irule_at Any Let_Prim
  \\ irule_at Any $ iffLR exp_eq_sym
  \\ irule_at Any Let_Prim
  \\ gvs [LIST_REL_EL_EQN, EL_MAP, exp_eq_in_ctxt_def]
QED

Theorem Let_App_w_app:
  ∀c s e1 e2 e3 len. eq_when_applied c (Let s e1 (App e2 e3)) (App (Let s e1 e2) (Let s e1 e3)) len
Proof
  rpt gen_tac
  \\ irule exp_eq_IMP_eq_when_applied
  \\ gvs [Let_App]
QED

Theorem Let_App_in_ctxt:
  ∀c s e1 e2 e3. exp_eq_in_ctxt c (Let s e1 (App e2 e3)) (App (Let s e1 e2) (Let s e1 e3))
Proof
  gvs [eq_when_applied_0, Let_App_w_app]
QED

Theorem exp_eq_in_ctxt_App:
  ∀c f1 f2 e1 e2. exp_eq_in_ctxt c f1 f2 ∧ exp_eq_in_ctxt c e1 e2
                  ⇒ exp_eq_in_ctxt c (App f1 e1) (App f2 e2)
Proof
  Induct
  \\ gvs [exp_eq_in_ctxt_def,exp_eq_App_cong]
  \\ rw []
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at Any exp_eq_in_ctxt_trans
  \\ last_x_assum $ irule_at (Pos $ el 2)
  \\ first_x_assum $ irule_at (Pos $ el 2)
  \\ rpt $ last_assum $ irule_at Any
  \\ irule_at (Pos last) $ iffLR exp_eq_in_ctxt_sym
  \\ rpt $ irule_at Any Let_App_in_ctxt
  \\ fs [Letrec_App, exp_eq_IMP_exp_eq_in_ctxt]
QED

Theorem eq_when_applied_App:
  ∀c f1 f2 e1 e2 len. eq_when_applied c f1 f2 (SUC len) ∧ exp_eq_in_ctxt c e1 e2
                  ⇒ eq_when_applied c (App f1 e1) (App f2 e2) len
Proof
  Induct
  \\ gvs [eq_when_applied_def,exp_eq_App_cong, GSYM Apps_def, exp_eq_in_ctxt_def]
  \\ rw []
  >- (irule exp_eq_trans >> last_x_assum $ irule_at Any >>
      gvs [exp_eq_Apps_cong, exp_eq_l_refl, exp_eq_App_cong, exp_eq_refl])
  \\ irule eq_when_applied_trans
  \\ irule_at Any eq_when_applied_trans
  \\ last_x_assum $ irule_at (Pos $ el 2)
  \\ first_x_assum $ irule_at (Pos $ el 2)
  \\ rpt $ last_assum $ irule_at Any
  \\ irule_at (Pos last) $ iffLR eq_when_applied_sym
  \\ rpt $ irule_at Any Let_App_w_app
  \\ fs [Letrec_App, exp_eq_IMP_eq_when_applied]
QED

Theorem SUC_ADD:
  ∀n m. SUC (n + m) = n + SUC m
Proof
  gvs []
QED

Theorem eq_when_applied_Apps:
  ∀eL eL' e e' c len. LIST_REL (exp_eq_in_ctxt c) eL eL' ⇒ eq_when_applied c e e' (len + LENGTH eL)
                  ⇒ eq_when_applied c (Apps e eL) (Apps e' eL') len
Proof
  Induct
  >- (Cases
      \\ fs [Apps_def])
  \\ gen_tac
  \\ Cases
  \\ rw [Apps_def]
  \\ first_x_assum irule
  \\ fs []
  \\ irule eq_when_applied_App
  \\ gvs [SUC_ADD]
QED

Theorem exp_eq_in_ctxt_Apps:
  ∀eL eL' e e' c. LIST_REL (exp_eq_in_ctxt c) eL eL' ⇒ exp_eq_in_ctxt c e e'
                  ⇒ exp_eq_in_ctxt c (Apps e eL) (Apps e' eL')
Proof
  Induct
  >- (Cases
      \\ fs [Apps_def])
  \\ gen_tac
  \\ Cases
  \\ rw [Apps_def]
  \\ first_x_assum irule
  \\ fs []
  \\ irule exp_eq_in_ctxt_App
  \\ gvs [SUC_ADD]
QED

Theorem Let_freevars_in_ctxt:
  ∀c v e e'. v ∉ freevars e' ⇒ exp_eq_in_ctxt c (Let v e e') e'
Proof
  rw []
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_thm, bind1_def, GSYM subst_fdomsub]
  >- (AP_TERM_TAC
      \\ irule subst1_ignore
      \\ rename1 ‘subst f e2’
      \\ qsuff_tac ‘closed (subst f e2)’
      >- rw [closed_def]
      \\ irule IMP_closed_subst
      \\ rw []
      \\ first_x_assum $ irule_at Any
      \\ fs [FRANGE_FLOOKUP]
      \\ pop_assum $ irule_at Any)
  \\ gvs [IMP_closed_subst, FRANGE_FLOOKUP]
QED

Theorem Let_freevars_w_app:
  ∀c v e e' len. v ∉ freevars e' ⇒ eq_when_applied c (Let v e e') e' len
Proof
  rw [] >>
  irule exp_eq_in_ctxt_IMP_eq_when_applied >>
  gvs [Let_freevars_in_ctxt]
QED

Theorem Let_Let_in_ctxt:
  ∀v w e1 e2 e3 c. v ≠ w ∧ v ∉ freevars e2 ∧ w ∉ freevars e1 ⇒
                   exp_eq_in_ctxt c (Let v e1 (Let w e2 e3)) (Let w e2 (Let v e1 e3))
Proof
  rw []
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ gvs [Let_Let]
QED

Theorem Let_Let_eq_w_app:
  ∀v w e1 e2 e3 c len. v ≠ w ∧ v ∉ freevars e2 ∧ w ∉ freevars e1 ⇒
                   eq_when_applied c (Let v e1 (Let w e2 e3)) (Let w e2 (Let v e1 e3)) len
Proof
  rw []
  \\ irule exp_eq_IMP_eq_when_applied
  \\ gvs [Let_Let]
QED

Theorem INFINITE_mlstring[local]:
  INFINITE 𝕌(:mlstring)
Proof
  strip_assume_tac explode_BIJ
  \\ strip_tac
  \\ drule_all pred_setTheory.FINITE_BIJ
  \\ simp [INFINITE_LIST_UNIV]
QED

Theorem exp_eq_in_ctxt_Lam:
  ∀c s e1 e2. exp_eq_in_ctxt (IsFree s c) e1 e2
              ⇒ exp_eq_in_ctxt c (Lam s e1) (Lam s e2)
Proof
  Induct
  \\ fs[exp_eq_in_ctxt_def] \\ rw [exp_eq_in_ctxt_def]
  >- (rw [exp_eq_Lam_strong]
      \\ irule exp_eq_trans
      \\ irule_at Any beta_equality
      \\ fs []
      \\ irule $ iffLR exp_eq_sym
      \\ irule exp_eq_trans
      \\ irule_at (Pos last) beta_equality
      \\ fs [exp_eq_sym])
  >>~ [‘Letrec l (Lam w _)’]
  >- (‘∃s. s ∉ {w} ∪ set (MAP FST l) ∪ BIGUNION (set (MAP (freevars o SND) l))
             ∪ freevars e1 ∪ freevars e2’
        by  (‘INFINITE 𝕌(:mlstring)’ by simp [INFINITE_mlstring]
             \\ dxrule_then assume_tac $ iffLR NOT_IN_FINITE
             \\ pop_assum $ irule_at Any
             \\ rw [FINITE_UNION, FINITE_BIGUNION, MEM_EL]
             \\ gvs [EL_MAP])
      \\ irule exp_eq_in_ctxt_trans
      \\ irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt
      \\ irule_at Any exp_eq_Letrec_cong
      \\ irule_at Any exp_eq_l_refl
      \\ irule_at Any exp_alpha_exp_eq
      \\ irule_at Any exp_alpha_Alpha
      \\ fs [] \\ first_assum $ irule_at Any
      \\ fs []
      \\ irule exp_eq_in_ctxt_trans
      \\ irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt
      \\ irule_at Any Letrec_Lam_weak
      \\ fs [] \\ conj_tac
      >- (rw [EVERY_MEM]
          \\ rename1 ‘MEM e _’ \\ last_x_assum $ qspecl_then [‘freevars e’] assume_tac
          \\ fs [MEM_MAP]
          \\ rename1 ‘e = SND pair’ \\ pop_assum $ qspecl_then [‘pair’] assume_tac
          \\ rw [])
      \\ irule exp_eq_in_ctxt_trans
      \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
      \\ irule_at Any $ iffLR exp_eq_sym
      \\ irule_at Any exp_eq_Letrec_cong
      \\ irule_at Any exp_alpha_exp_eq
      \\ irule_at Any exp_alpha_Alpha
      \\ irule_at Any exp_eq_l_refl
      \\ first_assum $ irule_at Any \\ fs []
      \\ irule exp_eq_in_ctxt_trans
      \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
      \\ irule_at Any $ iffLR exp_eq_sym
      \\ irule_at Any Letrec_Lam_weak
      \\ fs []
      \\ conj_tac
      >- (rw [EVERY_MEM]
          \\ rename1 ‘MEM e _’ \\ last_x_assum $ qspecl_then [‘freevars e’] assume_tac
          \\ fs [MEM_MAP]
          \\ rename1 ‘e = SND pair’ \\ pop_assum $ qspecl_then [‘pair’] assume_tac
          \\ rw [])
      \\ last_x_assum irule \\ rw []
      \\ irule exp_eq_in_ctxt_trans
      \\ irule_at Any exp_eq_in_ctxt_trans
      \\ last_x_assum $ irule_at Any
      \\ irule_at (Pos last) $ iffLR exp_eq_in_ctxt_sym
      \\ rename1 ‘Let s e3 _’ \\ qexists_tac ‘e3’ \\ fs []
      \\ conj_tac
      \\ irule exp_eq_IMP_exp_eq_in_ctxt
      \\ irule exp_eq_trans
      \\ irule_at Any Let_Letrec
      \\ fs []
      \\ irule_at Any exp_eq_Letrec_cong
      \\ irule_at Any $ iffLR exp_eq_sym
      \\ irule_at Any exp_eq_App_cong
      \\ irule_at Any exp_alpha_exp_eq
      \\ irule_at Any exp_alpha_Alpha
      \\ rw [EVERY_MEM, exp_eq_refl, exp_eq_l_refl] \\ fs [closed_def]
      \\ rename1 ‘MEM e _’
      \\ last_x_assum $ qspecl_then [‘freevars e’] assume_tac
      \\ fs [MEM_MAP]
      \\ rename1 ‘e = SND pair’ \\ pop_assum $ qspecl_then [‘pair’] assume_tac
      \\ rw [])
  \\ rename1 ‘Let v e3 (Lam w _)’
  \\ ‘∃s. s ∉ {v} ∪ {w} ∪ freevars e3 ∪ freevars e1 ∪ freevars e2’
    by (‘INFINITE 𝕌(:mlstring)’ by simp [INFINITE_mlstring]
        \\ gvs [NOT_IN_FINITE])
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any exp_eq_App_cong \\ irule_at Any exp_eq_Lam_cong
  \\ irule_at Any exp_alpha_exp_eq
  \\ irule_at Any exp_alpha_Alpha
  \\ fs [] \\ first_assum $ irule_at Any
  \\ irule_at Any exp_eq_refl \\ fs []
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any Let_Lam_weak \\ fs []
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any $ iffLR exp_eq_sym
  \\ irule_at Any exp_eq_App_cong \\ irule_at Any exp_eq_Lam_cong
  \\ irule_at Any exp_alpha_exp_eq
  \\ irule_at Any exp_alpha_Alpha
  \\ first_assum $ irule_at Any
  \\ irule_at Any exp_eq_refl \\ fs []
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any $ iffLR exp_eq_sym
  \\ irule_at Any Let_Lam_weak \\ fs []
  \\ last_x_assum $ irule_at Any
  \\ rw []
  \\ irule exp_eq_in_ctxt_trans \\ irule_at Any exp_eq_in_ctxt_trans
  \\ last_x_assum $ irule_at Any
  \\ rpt $ irule_at Any exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at (Pos $ el 2) $ iffLR exp_eq_sym
  \\ irule_at (Pos $ el 2) exp_eq_trans \\ irule_at (Pos $ el 3) exp_eq_trans
  \\ irule_at (Pos $ el 2) Let_Let \\ irule_at (Pos $ el 6) Let_Let
  \\ rpt $ irule_at Any exp_eq_App_cong
  \\ rpt $ irule_at Any exp_eq_refl
  \\ rpt $ irule_at Any exp_eq_Lam_cong
  \\ rpt $ irule_at Any exp_eq_App_cong
  \\ rpt $ irule_at Any exp_eq_refl
  \\ fs [closed_def] \\ conj_tac
  \\ irule exp_alpha_exp_eq
  \\ irule exp_alpha_Alpha
  \\ fs []
QED

Theorem exp_eq_in_ctxt_Lams:
  ∀vl c e e'. exp_eq_in_ctxt (FOLDL (λc n. IsFree n c) c vl) e e' ⇒
              exp_eq_in_ctxt c (Lams vl e) (Lams vl e')
Proof
  Induct
  \\ rw [Lams_def]
  \\ irule exp_eq_in_ctxt_Lam
  \\ last_x_assum $ irule_at Any
  \\ fs []
QED

Theorem eq_when_applied_Lam:
  ∀c s e1 e2 len. eq_when_applied (IsFree s c) e1 e2 len
              ⇒ eq_when_applied c (Lam s e1) (Lam s e2) (SUC len)
Proof
  Induct
  \\ fs[eq_when_applied_def] \\ rw [eq_when_applied_def]
  >~[‘Apps (Lam s e1) l ≈ Apps (Lam s e2) l’]
  >- (‘∃v. v ∉ BIGUNION (set (MAP freevars l)) ∪ {s} ∪ freevars e1 ∪ freevars e2 ’
        by  (‘INFINITE 𝕌(:mlstring)’ by simp [INFINITE_mlstring]
             \\ dxrule_then assume_tac $ iffLR NOT_IN_FINITE
             \\ pop_assum $ irule_at Any
             \\ rw [FINITE_UNION, FINITE_BIGUNION, MEM_EL]
             \\ gvs [EL_MAP])
      \\ irule exp_eq_trans \\ irule_at (Pos hd) exp_eq_Apps_cong
      \\ irule_at Any exp_eq_l_refl
      \\ irule_at (Pos hd) exp_alpha_exp_eq \\ irule_at Any exp_alpha_Alpha
      \\ fs [] \\ first_assum $ irule_at Any \\ fs [Once exp_eq_sym]
      \\ irule exp_eq_trans \\ irule_at (Pos hd) exp_eq_Apps_cong
      \\ irule_at Any exp_eq_l_refl
      \\ irule_at (Pos hd) exp_alpha_exp_eq \\ irule_at Any exp_alpha_Alpha
      \\ fs [] \\ first_assum $ irule_at Any \\ fs [Once exp_eq_sym]
      \\ Cases_on ‘l’ \\ gvs [Apps_def]
      \\ irule exp_eq_trans \\ irule_at (Pos last) exp_eq_trans
      \\ irule_at (Pos hd) Let_Apps \\ irule_at Any exp_eq_Apps_cong
      \\ irule_at Any $ iffRL LIST_REL_EL_EQN \\ irule_at Any LENGTH_MAP
      \\ irule_at (Pos $ el 2) exp_eq_refl
      \\ conj_asm1_tac
      >- (rw [EL_MAP] \\ irule eval_IMP_exp_eq
          \\ rw [subst_def, eval_thm, IMP_closed_subst, FRANGE_FLOOKUP, bind1_def]
          \\ rename1 ‘EL n t’ \\ first_x_assum $ qspecl_then [‘freevars (EL n t)’] assume_tac
          \\ gvs [GSYM subst_fdomsub, subst1_ignore, closed_def, IMP_closed_subst, FRANGE_FLOOKUP, MEM_MAP]
          \\ pop_assum $ qspecl_then [‘EL n t’] assume_tac
          \\ gvs [MEM_EL])
      \\ once_rewrite_tac [exp_eq_sym]
      \\ irule exp_eq_trans \\ irule_at (Pos last) exp_eq_trans
      \\ irule_at (Pos hd) Let_Apps \\ irule_at Any exp_eq_Apps_cong
      \\ irule_at Any $ iffRL LIST_REL_EL_EQN \\ irule_at Any LENGTH_MAP
      \\ irule_at (Pos $ el 2) exp_eq_refl \\ fs []
      \\ irule_at Any exp_eq_App_cong \\ rw [exp_eq_Lam_strong, exp_eq_refl]
      \\ irule exp_eq_trans \\ irule_at Any beta_equality \\ fs []
      \\ irule $ iffLR exp_eq_sym
      \\ irule exp_eq_trans \\ irule_at (Pos last) beta_equality \\ fs []
      \\ irule exp_eq_trans \\ irule_at Any Let_Apps
      \\ irule exp_eq_trans \\ irule_at Any exp_eq_Apps_cong
      \\ irule_at Any $ iffRL LIST_REL_EL_EQN \\ irule_at Any LENGTH_MAP
      \\ irule_at (Pos $ el 2) $ iffLR exp_eq_sym \\ irule_at Any exp_eq_App_cong
      \\ irule_at (Pos hd) exp_alpha_exp_eq \\ irule_at Any exp_alpha_Alpha \\ fs []
      \\ irule_at (Pos hd) exp_eq_refl
      \\ conj_asm1_tac
      >- (rw [EL_MAP] \\ irule eval_IMP_exp_eq
          \\ rw [subst_def, eval_thm, IMP_closed_subst, FRANGE_FLOOKUP, bind1_def]
          \\ rename1 ‘EL n t’ \\ first_x_assum $ qspecl_then [‘freevars (EL n t)’] assume_tac
          \\ gvs [GSYM subst_fdomsub, subst1_ignore, closed_def, IMP_closed_subst, FRANGE_FLOOKUP, MEM_MAP]
          \\ pop_assum $ qspecl_then [‘EL n t’] assume_tac
          \\ gvs [MEM_EL])
      \\ irule exp_eq_trans \\ last_x_assum $ irule_at Any \\ fs [Once exp_eq_sym]
      \\ irule exp_eq_trans \\ irule_at Any Let_Apps \\ irule exp_eq_Apps_cong
      \\ gvs [LIST_REL_EL_EQN, exp_eq_sym]
      \\ irule exp_eq_App_cong \\ fs [exp_eq_refl]
      \\ irule exp_alpha_exp_eq \\ irule exp_alpha_Alpha \\ fs [])
  >>~ [‘Letrec l (Lam w _)’]
  >- (‘∃s. s ∉ {w} ∪ set (MAP FST l) ∪ BIGUNION (set (MAP (freevars o SND) l))
             ∪ freevars e1 ∪ freevars e2’
        by  (‘INFINITE 𝕌(:mlstring)’ by simp [INFINITE_mlstring]
             \\ dxrule_then assume_tac $ iffLR NOT_IN_FINITE
             \\ pop_assum $ irule_at Any
             \\ rw [FINITE_UNION, FINITE_BIGUNION, MEM_EL]
             \\ gvs [EL_MAP])
      \\ irule eq_when_applied_trans
      \\ irule_at (Pos hd) exp_eq_IMP_eq_when_applied
      \\ irule_at Any exp_eq_Letrec_cong
      \\ irule_at Any exp_eq_l_refl
      \\ irule_at Any exp_alpha_exp_eq
      \\ irule_at Any exp_alpha_Alpha
      \\ fs [] \\ first_assum $ irule_at Any
      \\ fs []
      \\ irule eq_when_applied_trans
      \\ irule_at (Pos hd) exp_eq_IMP_eq_when_applied
      \\ irule_at Any Letrec_Lam_weak
      \\ fs [] \\ conj_tac
      >- (rw [EVERY_MEM]
          \\ rename1 ‘MEM e _’ \\ last_x_assum $ qspecl_then [‘freevars e’] assume_tac
          \\ fs [MEM_MAP]
          \\ rename1 ‘e = SND pair’ \\ pop_assum $ qspecl_then [‘pair’] assume_tac
          \\ rw [])
      \\ irule eq_when_applied_trans
      \\ irule_at (Pos last) exp_eq_IMP_eq_when_applied
      \\ irule_at Any $ iffLR exp_eq_sym
      \\ irule_at Any exp_eq_Letrec_cong
      \\ irule_at Any exp_alpha_exp_eq
      \\ irule_at Any exp_alpha_Alpha
      \\ irule_at Any exp_eq_l_refl
      \\ first_assum $ irule_at Any \\ fs []
      \\ irule eq_when_applied_trans
      \\ irule_at (Pos last) exp_eq_IMP_eq_when_applied
      \\ irule_at Any $ iffLR exp_eq_sym
      \\ irule_at Any Letrec_Lam_weak
      \\ fs []
      \\ conj_tac
      >- (rw [EVERY_MEM]
          \\ rename1 ‘MEM e _’ \\ last_x_assum $ qspecl_then [‘freevars e’] assume_tac
          \\ fs [MEM_MAP]
          \\ rename1 ‘e = SND pair’ \\ pop_assum $ qspecl_then [‘pair’] assume_tac
          \\ rw [])
      \\ last_x_assum irule \\ rw []
      \\ irule eq_when_applied_trans
      \\ irule_at Any eq_when_applied_trans
      \\ last_x_assum $ irule_at Any
      \\ irule_at (Pos last) $ iffLR eq_when_applied_sym
      \\ rename1 ‘Let s e3 _’ \\ qexists_tac ‘e3’ \\ fs []
      \\ conj_tac
      \\ irule exp_eq_IMP_eq_when_applied
      \\ irule exp_eq_trans
      \\ irule_at Any Let_Letrec
      \\ fs []
      \\ irule_at Any exp_eq_Letrec_cong
      \\ irule_at Any $ iffLR exp_eq_sym
      \\ irule_at Any exp_eq_App_cong
      \\ irule_at Any exp_alpha_exp_eq
      \\ irule_at Any exp_alpha_Alpha
      \\ rw [EVERY_MEM, exp_eq_refl, exp_eq_l_refl] \\ fs [closed_def]
      \\ rename1 ‘MEM e _’
      \\ last_x_assum $ qspecl_then [‘freevars e’] assume_tac
      \\ fs [MEM_MAP]
      \\ rename1 ‘e = SND pair’ \\ pop_assum $ qspecl_then [‘pair’] assume_tac
      \\ rw [])
  \\ rename1 ‘Let v e3 (Lam w _)’
  \\ ‘∃s. s ∉ {v} ∪ {w} ∪ freevars e3 ∪ freevars e1 ∪ freevars e2’
    by (‘INFINITE 𝕌(:mlstring)’ by simp [INFINITE_mlstring]
        \\ gvs [NOT_IN_FINITE])
  \\ irule eq_when_applied_trans
  \\ irule_at (Pos hd) exp_eq_IMP_eq_when_applied
  \\ irule_at Any exp_eq_App_cong \\ irule_at Any exp_eq_Lam_cong
  \\ irule_at Any exp_alpha_exp_eq
  \\ irule_at Any exp_alpha_Alpha
  \\ fs [] \\ first_assum $ irule_at Any
  \\ irule_at Any exp_eq_refl \\ fs []
  \\ irule eq_when_applied_trans
  \\ irule_at (Pos hd) exp_eq_IMP_eq_when_applied
  \\ irule_at Any Let_Lam_weak \\ fs []
  \\ irule eq_when_applied_trans
  \\ irule_at (Pos last) exp_eq_IMP_eq_when_applied
  \\ irule_at Any $ iffLR exp_eq_sym
  \\ irule_at Any exp_eq_App_cong \\ irule_at Any exp_eq_Lam_cong
  \\ irule_at Any exp_alpha_exp_eq
  \\ irule_at Any exp_alpha_Alpha
  \\ first_assum $ irule_at Any
  \\ irule_at Any exp_eq_refl \\ fs []
  \\ irule eq_when_applied_trans
  \\ irule_at (Pos last) exp_eq_IMP_eq_when_applied
  \\ irule_at Any $ iffLR exp_eq_sym
  \\ irule_at Any Let_Lam_weak \\ fs []
  \\ last_x_assum $ irule_at Any
  \\ rw []
  \\ irule eq_when_applied_trans \\ irule_at Any eq_when_applied_trans
  \\ last_x_assum $ irule_at Any
  \\ rpt $ irule_at Any exp_eq_IMP_eq_when_applied
  \\ irule_at (Pos $ el 2) $ iffLR exp_eq_sym
  \\ irule_at (Pos $ el 2) exp_eq_trans \\ irule_at (Pos $ el 3) exp_eq_trans
  \\ irule_at (Pos $ el 2) Let_Let \\ irule_at (Pos $ el 6) Let_Let
  \\ rpt $ irule_at Any exp_eq_App_cong
  \\ rpt $ irule_at Any exp_eq_refl
  \\ rpt $ irule_at Any exp_eq_Lam_cong
  \\ rpt $ irule_at Any exp_eq_App_cong
  \\ rpt $ irule_at Any exp_eq_refl
  \\ fs [closed_def] \\ conj_tac
  \\ irule exp_alpha_exp_eq
  \\ irule exp_alpha_Alpha
  \\ fs []
QED

Theorem eq_when_applied_Lams:
  ∀vl c e e' len. eq_when_applied (FOLDL (λc n. IsFree n c) c vl) e e' len ⇒
              eq_when_applied c (Lams vl e) (Lams vl e') (len + LENGTH vl)
Proof
  Induct
  \\ rw [Lams_def, GSYM SUC_ADD]
  \\ irule eq_when_applied_Lam
  \\ last_x_assum $ irule_at Any
  \\ fs []
QED

Theorem exp_eq_in_IsFree_Bind:
  ∀e1 e2 e3 c v. exp_eq_in_ctxt (IsFree v c) e1 e2 ⇒ exp_eq_in_ctxt (Bind v e3 c) e1 e2
Proof
  rpt strip_tac >>
  gvs [exp_eq_in_ctxt_def, exp_eq_in_ctxt_App, exp_eq_in_ctxt_Lam, exp_eq_in_ctxt_refl]
QED

Theorem Apps_Seq_in_ctxt:
  ∀e e2 eL c. exp_eq_in_ctxt c (Apps (Seq e e2) eL) (Seq e (Apps e2 eL))
Proof
  rw [exp_eq_IMP_exp_eq_in_ctxt, Apps_Seq]
QED

Theorem Let_Apps_in_ctxt:
  ∀v e1 e2 eL c. exp_eq_in_ctxt c (Let v e1 (Apps e2 eL)) (Apps (Let v e1 e2) (MAP (Let v e1) eL))
Proof
  rw [Let_Apps, exp_eq_IMP_exp_eq_in_ctxt]
QED

Theorem Letrec_Apps:
  ∀l bL b e. (Letrec bL (Apps e l) ≅? Apps (Letrec bL e) (MAP (Letrec bL) l)) b
Proof
  Induct >> gvs [exp_eq_refl, Apps_def] >>
  rpt gen_tac >>
  irule exp_eq_trans >> pop_assum $ irule_at Any >>
  irule exp_eq_Apps_cong >>
  fs [exp_eq_l_refl, Letrec_App]
QED

Theorem Letrec_Apps_in_ctxt:
  ∀l b e c. exp_eq_in_ctxt c (Letrec b (Apps e l)) (Apps (Letrec b e) (MAP (Letrec b) l))
Proof
  gvs [exp_eq_IMP_exp_eq_in_ctxt, Letrec_Apps]
QED

Theorem APPEND_CONS:
  ∀l1 l2 e. l1 ++ [e] ++ l2 = l1 ++ e::l2
Proof
  Induct >> gvs []
QED

Theorem MAP_PAIR:
  ∀l1 l2 f1 f2. MAP (f1 ## f2) (ZIP (l1, l2)) = ZIP (MAP f1 l1, MAP f2 l2)
Proof
  Induct >> gvs [ZIP_def] >>
  gen_tac >> Cases >> gvs [ZIP_def]
QED

Theorem MAP_perm1:
  ∀l v1 v2. ¬MEM v1 l ∧ ¬MEM v2 l ⇒ MAP (perm1 v1 v2) l = l
Proof
  Induct >> gvs [perm1_def]
QED

Theorem Letrec_rename_lemma:
  ∀ld lc s. ALL_DISTINCT (lc ++ ld) ∧ FINITE s (*∧ DISJOINT (set lc ∪ set ld) s*)
          ⇒ ∃l2 f f_inv. LENGTH ld = LENGTH l2 ∧ DISJOINT (set l2) (s ∪ (set lc) ∪ (set ld))
                         ∧ (∀e. f_inv (f e) = e ∧ f (f_inv e) = e) ∧ ALL_DISTINCT l2
                         ∧ ∀eL1 eL2 e1 b.
                             LENGTH eL1 = LENGTH lc ∧ LENGTH eL2 = LENGTH ld
                             ∧ freevars (Letrec (ZIP (lc ++ ld, eL1 ++ eL2)) e1) ⊆ s
                             ⇒ (Letrec (ZIP (lc ++ ld, eL1 ++ eL2)) e1
                                ≅? Letrec (ZIP (lc ++ l2, MAP f (eL1 ++ eL2))) (f e1)) b
Proof
  Induct >> rw []
  >- (qexists_tac ‘λx. x’ >> qexists_tac ‘λx. x’ >> rw [exp_eq_refl]) >>
  rename1 ‘lc ++ v::ld’ >>
  ‘∃v2. v2 ∉ s ∪ set (lc ++ v::ld)’
    by (‘INFINITE 𝕌(:mlstring)’ by simp [INFINITE_mlstring]
        \\ dxrule_then assume_tac $ iffLR NOT_IN_FINITE
        \\ pop_assum $ irule_at Any \\ rw [FINITE_UNION]) >>
  rename1 ‘v2 ∉ _’ >>
  ‘ALL_DISTINCT (lc ++ [v2] ++ ld)’
    by (gvs [ALL_DISTINCT_APPEND] >> rw [] >> gvs []) >>
  last_x_assum $ drule_then $ qspecl_then [‘s ∪ {v2} ∪ {v}’] assume_tac >>
  gvs [MAP_ZIP] >>
  rename1 ‘DISJOINT _ (set l2)’ >>
  qexists_tac ‘v2::l2’ >>
  rename1 ‘f_inv (f _) = _ ∧ f (f_inv _) = _’ >>
  qexists_tac ‘f o (perm_exp v v2)’ >> qexists_tac ‘(perm_exp v v2) o f_inv’ >>
  gvs [combinTheory.o_DEF, perm_exp_cancel] >>
  rw [] >> gvs [GSYM ZIP_APPEND] >>
  rename1 ‘ZIP (_::_, eL2)’ >> Cases_on ‘eL2’ >> gvs [] >>
  irule exp_eq_trans >>
  irule_at (Pos hd) exp_alpha_exp_eq >> irule_at Any exp_alpha_Letrec_Alpha >>
  qexists_tac ‘v2’ >> gvs [MAP_ZIP] >> rw []
  >>~[‘_ ∉ freevars _’]
  >- (strip_tac >> last_x_assum irule >> gvs [SUBSET_DEF])
  >- (strip_tac >> last_x_assum irule >> gvs [SUBSET_DEF])
  >>~[‘v2 ∉ s' ∨ ¬MEM s' (MAP _ (ZIP (List1, List2)))’]
  >- (gvs [SUBSET_DEF] >>
      qsuff_tac ‘v2 ∉ BIGUNION (set (MAP (λ(fn, e2). freevars e2) (ZIP (List1, List2))))’
      >- gvs [] >>
      strip_tac >> last_x_assum irule >> first_x_assum irule >> gvs [] >>
      disj2_tac >> disj1_tac >> rpt $ first_x_assum $ irule_at Any)
  >- (gvs [SUBSET_DEF] >>
      qsuff_tac ‘v2 ∉ BIGUNION (set (MAP (λ(fn, e2). freevars e2) (ZIP (List1, List2))))’
      >- gvs [] >>
      strip_tac >> last_x_assum irule >> first_x_assum irule >> gvs [] >>
      disj2_tac >> disj2_tac >> disj2_tac >> rpt $ first_x_assum $ irule_at Any) >>
  irule exp_eq_trans >> gvs [MAP_PAIR, MAP_perm1, ALL_DISTINCT_APPEND] >>
  rename1 ‘Letrec (ZIP (lc, MAP _ eL1) ++ (_, _ expr1)::ZIP(_, MAP _ eL2)) (_ expr2)’ >>
  first_x_assum $ qspecl_then [‘MAP (perm_exp v v2) eL1 ++ [perm_exp v v2 expr1]’,
                               ‘MAP (perm_exp v v2) eL2’, ‘perm_exp v v2 expr2’] assume_tac >>
  gvs [GSYM ZIP_APPEND, APPEND_CONS] >>
  pop_assum $ irule_at Any >>
  irule_at Any exp_eq_Letrec_cong >>
  rw [LIST_REL_EL_EQN, MAP_ZIP, exp_eq_refl, SUBSET_DEF]
  >- (rw [EL_APPEND_EQN] >> gvs [EL_MAP, exp_eq_refl] >>
      Cases_on ‘n = LENGTH lc’ >> gvs [exp_eq_refl] >>
      ‘n - LENGTH lc > 0’ by gvs [] >> gvs [EL_CONS, EL_MAP, exp_eq_refl]) >>
  gvs [freevars_eqvt]
  >- (rename1 ‘perm1 v v2 x = v’ >> Cases_on ‘x = v2’ >> gvs [perm1_def] >>
      disj1_tac >>
      Cases_on ‘x = v’ >> gvs [SUBSET_DEF])
  >- (rename1 ‘x ≠ v2’ >> Cases_on ‘x = v’ >> gvs [SUBSET_DEF] >>
      first_x_assum $ irule_at Any >> gvs [] >>
      disj2_tac >> disj1_tac >>
      gvs [MEM_EL, EL_MAP] >> first_assum $ irule_at Any >>
      gvs [EL_MAP, EL_ZIP, freevars_eqvt] >>
      rename1 ‘perm1 v v2 x ∈ _’ >> Cases_on ‘x = v’ >> Cases_on ‘x = v2’ >> gvs [perm1_def])
  >- (rename1 ‘perm1 v v2 x’ >> Cases_on ‘x = v’ >> Cases_on ‘x = v2’ >> gvs [perm1_def, SUBSET_DEF])
  >- (rename1 ‘x ≠ v2’ >> Cases_on ‘x = v’ >> gvs [SUBSET_DEF] >>
      first_x_assum $ irule_at Any >> gvs [] >>
      disj2_tac >> disj2_tac >> disj2_tac >>
      gvs [MEM_EL, EL_MAP] >> first_assum $ irule_at Any >>
      gvs [EL_MAP, EL_ZIP, freevars_eqvt] >>
      rename1 ‘perm1 v v2 x ∈ _’ >> Cases_on ‘x = v’ >> Cases_on ‘x = v2’ >> gvs [perm1_def])
QED

Theorem Letrec_rename:
  ∀l s. ALL_DISTINCT l ∧ FINITE s
        ⇒ ∃l2 f f_inv. LENGTH l = LENGTH l2 ∧ DISJOINT (set l2) (set l ∪ s)
                       ∧ (∀e. f_inv (f e) = e ∧ f (f_inv e) = e)
                       ∧ DISJOINT (set l2) (s ∪ set l) ∧ ALL_DISTINCT l2
                       ∧ ∀eL e1 b. LENGTH eL = LENGTH l
                                   ∧ freevars (Letrec (ZIP (l, eL)) e1) ⊆ s
                                   ⇒ (Letrec (ZIP (l, eL)) e1 ≅? Letrec (ZIP (l2, MAP f eL)) (f e1)) b
Proof
  rw [] >>
  rename1 ‘ALL_DISTINCT l’ >>
  qspecl_then [‘l’, ‘[]’] assume_tac Letrec_rename_lemma >> gvs [] >>
  last_x_assum $ dxrule_then assume_tac >> gvs [] >>
  first_x_assum $ irule_at Any >> gvs [] >>
  rename1 ‘f_inv (f _) = _ ∧ f (f_inv _) = _’ >> qexists_tac ‘f_inv’ >> qexists_tac ‘f’ >>
  rw []
QED

Theorem MAP_FST:
  ∀l. MAP (λ(x, y). x) l = MAP FST l
Proof
  Induct >> gvs [FORALL_PROD]
QED

Theorem Let_Letrec2:
  ∀v e e2 binds b. ¬MEM v (MAP FST binds) ∧ EVERY (λv. v ∉ freevars e) (MAP FST binds)
                   ⇒ (Let v e (Letrec binds e2)
                      ≅? Letrec (MAP (λ(v1, e'''). (v1, Let v e e''')) binds) (Let v e e2)) b
Proof
  rw[exp_eq_def, bind_def] >> rw[] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, subst_def] >>
  simp [app_bisimilarity_eq] >>
  gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP_FST, DIFF_SUBSET, BIGUNION_SUBSET, UNION_SUBSET,
       GSYM SUBSET_INSERT_DELETE] >>
  reverse conj_asm2_tac
  >- (rw []
      >- (rename1 ‘subst (FDIFF (f \\ v) (set (MAP FST binds))) _’ >>
          ‘∀n. n ∈ FRANGE (FDIFF (f \\ v) (set (MAP FST binds))) ⇒ closed n’
            by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT, DOMSUB_FLOOKUP_THM] >>
                   first_x_assum $ dxrule_then irule) >>
          gvs [freevars_subst, DIFF_SUBSET, FDOM_FDIFF, SUBSET_DEF] >>
          rw [] >> gvs [] >> last_x_assum $ dxrule_then assume_tac >> gvs [])
      >- (rename1 ‘subst (FDIFF (f \\ v) (set (MAP FST binds))) _’ >>
          ‘∀n. n ∈ FRANGE (FDIFF (f \\ v) (set (MAP FST binds))) ⇒ closed n’
            by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT, DOMSUB_FLOOKUP_THM] >>
                first_x_assum $ dxrule_then irule) >>
          dxrule_then assume_tac $ iffLR MEM_EL >>
          gvs[freevars_subst, DIFF_SUBSET, FDOM_FDIFF, SUBSET_DEF, EL_MAP] >>
          rename1 ‘n < _’ >> qabbrev_tac ‘pair = EL n binds’ >> PairCases_on ‘pair’ >> gvs [] >>
          qabbrev_tac ‘folded = (λ((p1: mlstring), p2). freevars p2)’ >>
          ‘MEM (folded (EL n binds)) (MAP folded binds)’
            by (gvs [MEM_EL] >> first_assum $ irule_at Any >> gvs [EL_MAP]) >>
          first_x_assum $ dxrule_then assume_tac >> unabbrev_all_tac >> gvs [] >>
          rw [] >> gvs [] >>
          first_x_assum $ dxrule_then assume_tac >> gvs [])
      >- (irule IMP_closed_subst >> gvs [FRANGE_FLOOKUP])
      >- (rename1 ‘subst (FDIFF f (set (MAP FST binds)) \\ v) _’ >>
          ‘∀n. n ∈ FRANGE (FDIFF f (set (MAP FST binds)) \\ v) ⇒ closed n’
            by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT, DOMSUB_FLOOKUP_THM] >>
                   first_x_assum $ dxrule_then irule) >>
          gvs [freevars_subst, DIFF_SUBSET, FDOM_FDIFF, SUBSET_DEF] >>
          rw [] >> gvs [] >> last_x_assum $ dxrule_then assume_tac >> gvs [])
      >- (rename1 ‘subst (FDIFF f (set (MAP FST binds))) _’ >>
          ‘∀n. n ∈ FRANGE (FDIFF f (set (MAP FST binds))) ⇒ closed n’
            by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
                   first_x_assum $ dxrule_then irule) >>
          gvs [freevars_subst, DIFF_SUBSET, FDOM_FDIFF, SUBSET_DEF] >>
          rw [] >> gvs []) >>
      gvs [EVERY_EL, EL_MAP] >> rw [] >>
      rename1 ‘n < _’ >> qabbrev_tac ‘pair = EL n binds’ >> PairCases_on ‘pair’ >> gvs [] >>
      rename1 ‘subst (FDIFF f (set (MAP FST binds))) _’ >>
      ‘∀n. n ∈ FRANGE (FDIFF f (set (MAP FST binds))) ⇒ closed n’
        by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
            first_x_assum $ dxrule_then irule) >>
      gvs [freevars_subst, DIFF_SUBSET, FDOM_FDIFF, SUBSET_DEF] >>
      rw [] >> gvs [] >>
      ‘MEM ((λ(x, y). freevars y) (EL n binds)) (MAP (λ(x, y). freevars y) binds)’
            by (gvs [MEM_EL] >> first_assum $ irule_at Any >> gvs [EL_MAP]) >>
      first_x_assum $ dxrule_then assume_tac >> gvs [] >>
      first_x_assum $ dxrule_then assume_tac >> gvs []) >>
  irule exp_eq_trans >> irule_at Any beta_equality >>
  gvs [IMP_closed_subst, FRANGE_FLOOKUP, subst1_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP_FST] >>
  irule exp_eq_Letrec_cong >>
  gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, LIST_REL_EL_EQN, EL_MAP] >>
  rw []
  >~[‘n < _’]
  >- (qabbrev_tac ‘p = EL n binds’ >> PairCases_on ‘p’ >> gvs [subst_def, Once exp_eq_sym] >>
      irule exp_eq_trans >> irule_at Any beta_equality >>
      irule_at Any IMP_closed_subst >>
      conj_tac
      >- (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
          first_x_assum $ dxrule_then irule) >>
      conj_tac
      >- (rw [SUBSET_DEF, FDIFF_def, FDOM_DRESTRICT]
          >- gvs [SUBSET_DEF] >>
          strip_tac >> gvs [EVERY_MEM]) >>
      rename1 ‘subst (FDIFF f (set (MAP FST binds))) e’ >>
      qspecl_then [‘f’, ‘e’, ‘set (MAP FST binds)’] assume_tac subst_FDIFF' >>
      gvs [EVERY_MEM, FDIFF_def, fmap_domsub, INTER_COMM, exp_eq_refl]) >>
  irule $ iffLR exp_eq_sym >>
  irule exp_eq_trans >> irule_at Any beta_equality >>
  irule_at Any IMP_closed_subst >>
  conj_tac
  >- (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
      first_x_assum $ dxrule_then irule) >>
  conj_tac
  >- (rw [SUBSET_DEF, FDIFF_def, FDOM_DRESTRICT]
      >- gvs [SUBSET_DEF] >>
      strip_tac >> gvs [EVERY_MEM]) >>
  rename1 ‘subst (FDIFF f (set (MAP FST binds))) e’ >>
  qspecl_then [‘f’, ‘e’, ‘set (MAP FST binds)’] assume_tac subst_FDIFF' >>
  gvs [EVERY_MEM, FDIFF_def, fmap_domsub, INTER_COMM, exp_eq_refl]
QED

Theorem eq_IMP_exp_eq:
  ∀x y b. x = y ⇒ (x ≅? y) b
Proof
  rw [exp_eq_refl]
QED

Theorem AP_THM:
  ∀f1 f2 e1 e2. f1 = f2 ∧ e1 = e2 ⇒ f1 e1 = f2 e2
Proof
  rw []
QED

Theorem Letrec_distrib_Letrec:
  ∀binds1 binds2 e b. EVERY (λ(v, e). ¬MEM v (MAP FST binds2)
                                 ∧ DISJOINT (set (MAP FST binds2)) (freevars e))
                                            binds1
                   ⇒ (Letrec binds1 (Letrec binds2 e)
                      ≅? Letrec (MAP (λ(v, e2). (v, Letrec binds1 e2)) binds2) (Letrec binds1 e)) b
Proof
  rw[exp_eq_def, bind_def] >> rw[] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, subst_def] >>
  simp [app_bisimilarity_eq] >>
  gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP_FST, DIFF_SUBSET, BIGUNION_SUBSET, UNION_SUBSET,
       GSYM SUBSET_INSERT_DELETE] >>
  reverse conj_asm2_tac
  >- (rw []
      >- (rename1 ‘subst (FDIFF (FDIFF f (set (MAP FST binds1))) (set (MAP FST binds2))) _’ >>
          ‘∀n. n ∈ FRANGE (FDIFF (FDIFF f (set (MAP FST binds1))) (set (MAP FST binds2))) ⇒ closed n’
            by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
                   first_x_assum $ dxrule_then irule) >>
          gvs [freevars_subst, DIFF_SUBSET, FDOM_FDIFF, SUBSET_DEF] >>
          rw [] >> gvs [] >> last_x_assum $ dxrule_then assume_tac >> gvs [])
      >- (rename1 ‘subst (FDIFF (FDIFF f (set (MAP FST binds1))) (set (MAP FST binds2))) _’ >>
          ‘∀n. n ∈ FRANGE (FDIFF (FDIFF f (set (MAP FST binds1))) (set (MAP FST binds2))) ⇒ closed n’
            by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
                first_x_assum $ dxrule_then irule) >>
          dxrule_then assume_tac $ iffLR MEM_EL >>
          gvs[freevars_subst, DIFF_SUBSET, FDOM_FDIFF, SUBSET_DEF, EL_MAP] >>
          rename1 ‘n < _’ >> qabbrev_tac ‘pair = EL n binds2’ >> PairCases_on ‘pair’ >> gvs [] >>
          qabbrev_tac ‘folded = (λ((p1: mlstring), p2). freevars p2)’ >>
          ‘MEM (folded (EL n binds2)) (MAP folded binds2)’
            by (gvs [MEM_EL] >> first_assum $ irule_at Any >> gvs [EL_MAP]) >>
          first_x_assum $ dxrule_then assume_tac >> unabbrev_all_tac >> gvs [] >>
          rw [] >> gvs [] >>
          first_x_assum $ dxrule_then assume_tac >> gvs [])
      >- (gvs [EVERY_EL, EL_MAP] >> rw [] >>
          rename1 ‘n < _’ >> qabbrev_tac ‘pair = EL n binds1’ >> PairCases_on ‘pair’ >> gvs [] >>
          ‘∀n. n ∈ FRANGE (FDIFF f (set (MAP FST binds1))) ⇒ closed n’
            by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
                first_x_assum $ dxrule_then irule) >>
          gvs [freevars_subst, FDOM_FDIFF, DIFF_SUBSET, SUBSET_DEF] >>
          ‘MEM (EL n (MAP (λ(x,y). freevars y) binds1)) (MAP (λ(x, y). freevars y) binds1)’
               by (irule EL_MEM >> gvs []) >>
          rw [] >> gvs [EL_MAP] >>
          last_x_assum $ dxrule_then $ dxrule_then assume_tac >> gvs [])
      >- (rename1 ‘subst (FDIFF (FDIFF f (set (MAP FST binds2))) (set (MAP FST binds1))) _’ >>
          ‘∀n. n ∈ FRANGE (FDIFF (FDIFF f (set (MAP FST binds2))) (set (MAP FST binds1))) ⇒ closed n’
            by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
                   first_x_assum $ dxrule_then irule) >>
          gvs [freevars_subst, DIFF_SUBSET, FDOM_FDIFF, SUBSET_DEF] >>
          rw [] >> gvs [] >> last_x_assum $ dxrule_then assume_tac >> gvs [])
      >- (rename1 ‘subst (FDIFF (FDIFF f (set (MAP FST binds2))) (set (MAP FST binds1))) _’ >>
          ‘∀n. n ∈ FRANGE (FDIFF (FDIFF f (set (MAP FST binds2))) (set (MAP FST binds1))) ⇒ closed n’
            by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
                first_x_assum $ dxrule_then irule) >>
          dxrule_then assume_tac $ iffLR MEM_EL >> fs [] >>
          rename1 ‘n < _’ >> qabbrev_tac ‘pair = EL n binds1’ >> PairCases_on ‘pair’ >>
          gvs[freevars_subst, DIFF_SUBSET, FDOM_FDIFF, EL_MAP, SUBSET_DEF] >>
          qabbrev_tac ‘folded = (λ((p1: mlstring), p2). freevars p2)’ >>
          ‘MEM (folded (EL n binds1)) (MAP folded binds1)’
            by (gvs [MEM_EL] >> first_assum $ irule_at Any >> gvs [EL_MAP]) >>
          first_x_assum $ dxrule_then assume_tac >> unabbrev_all_tac >> gvs [] >>
          rw [] >> gvs [] >>
          first_x_assum $ dxrule_then assume_tac >> gvs []) >>
      gvs [EVERY_EL, EL_MAP] >> rw [] >>
      rename1 ‘n < _’ >> qabbrev_tac ‘pair = EL n binds2’ >> PairCases_on ‘pair’ >> gvs [] >>
      rename1 ‘subst (FDIFF f (set (MAP FST binds2))) _’ >>
      ‘∀n. n ∈ FRANGE (FDIFF f (set (MAP FST binds2))) ⇒ closed n’
        by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
            first_x_assum $ dxrule_then irule) >>
      gvs [freevars_subst, DIFF_SUBSET, FDOM_FDIFF, SUBSET_DEF] >>
      rw [] >> gvs [] >>
      ‘MEM ((λ(x, y). freevars y) (EL n binds2)) (MAP (λ(x, y). freevars y) binds2)’
            by (gvs [MEM_EL] >> first_assum $ irule_at Any >> gvs [EL_MAP]) >>
      first_x_assum $ dxrule_then assume_tac >> gvs [] >>
      first_x_assum $ dxrule_then assume_tac >> gvs []) >>
  irule exp_eq_trans >> irule_at Any beta_equality_Letrec >>
  gvs [FRANGE_FLOOKUP, subst_funs_eq_subst, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP_FST, subst_def] >>
  irule exp_eq_Letrec_cong >>
  gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, LIST_REL_EL_EQN, EL_MAP] >>
  rw []
  >~[‘n < _’]
  >- (qabbrev_tac ‘p = EL n binds2’ >> PairCases_on ‘p’ >> gvs [subst_def, Once exp_eq_sym] >>
      irule exp_eq_trans >> irule_at Any beta_equality_Letrec >>
      conj_tac
      >- (gvs [EVERY_MEM, FORALL_PROD, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP_FST] >>
          rw [MEM_EL] >> gvs [EL_MAP] >>
          rename1 ‘freevars (_ (EL n2 _))’ >>
          qabbrev_tac ‘pair = EL n2 binds1’ >> PairCases_on ‘pair’ >> gvs [] >>
          qspecl_then [‘FDIFF f (set (MAP FST binds1))’, ‘SND (EL n2 binds1)’, ‘set (MAP FST binds2)’]
                      assume_tac $ GSYM subst_FDIFF' >>
          ‘MEM (EL n2 binds1) binds1’ by (irule EL_MEM >> gvs []) >>
          gvs [] >> last_x_assum $ dxrule_then assume_tac >>
          gvs [DISJOINT_ALT] >>
          first_x_assum irule >>
          gvs [MEM_EL] >> first_assum $ irule_at Any >>
          gvs [EL_MAP, FDIFF_def, INTER_COMM]) >>
      irule exp_eq_trans >>
      irule_at (Pos hd) eq_IMP_exp_eq >>
      irule_at Any AP_THM >> irule_at Any subst_funs_eq_subst >>
      irule_at Any EQ_REFL >>
      gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      conj_tac
      >- (rw [EVERY_EL, MAP_FST, EL_MAP] >>
          rename1 ‘freevars (_ (EL n2 _))’ >>
          qabbrev_tac ‘pair = EL n2 binds1’ >> PairCases_on ‘pair’ >> gvs [] >>
          ‘∀n. n ∈ FRANGE (FDIFF (FDIFF f (set (MAP FST binds2))) (set (MAP FST binds1))) ⇒ closed n’
            by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
                first_x_assum $ dxrule_then irule) >>
          gvs [freevars_subst, FDOM_FDIFF, DIFF_SUBSET, SUBSET_DEF] >> rw [] >> gvs [] >>
          ‘MEM (EL n2 (MAP (λ(x, y). freevars y) binds1)) (MAP (λ(x, y). freevars y) binds1)’
            by (irule EL_MEM >> gvs []) >>
          first_x_assum $ dxrule_then assume_tac >> gvs [EL_MAP] >>
          first_x_assum $ drule_then assume_tac >> gvs [EVERY_EL] >>
          last_x_assum $ drule_then assume_tac >> gvs [DISJOINT_ALT]) >>
      irule eq_IMP_exp_eq >> irule AP_THM >>
      conj_tac
      >- gvs [FDIFF_def, INTER_COMM] >>
      AP_TERM_TAC >>
      gvs [FDIFF_def] >> irule EQ_TRANS >>
      irule_at (Pos last) $ GSYM disjoint_drestrict >>
      gvs [FDOM_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, DISJOINT_ALT, EVERY_MEM] >>
      gvs [FORALL_PROD, LAMBDA_PROD, MAP_FST] >>
      rw []
      >- (strip_tac >> gvs [MEM_MAP] >>
          rename1 ‘FST y1 = FST y2’ >> PairCases_on ‘y1’ >> PairCases_on ‘y2’ >>
          gvs [FORALL_PROD] >>
          last_x_assum $ dxrule_then assume_tac >> gvs []) >>
      AP_TERM_TAC >> irule LIST_EQ >>
      gvs [EL_MAP] >> rw [] >>
      rename1 ‘EL n2 _’ >> qabbrev_tac ‘pair = EL n2 binds1’ >> PairCases_on ‘pair’ >> gvs [] >>
      irule_at Any LIST_EQ >> rw [EL_MAP]
      >- (rename1 ‘_ (EL n3 _)’ >> qabbrev_tac ‘EL_n3_binds1 = EL n3 binds1’ >>
          PairCases_on ‘EL_n3_binds1’ >> gvs [] >>
          rename1 ‘DRESTRICT f _’ >>
          qspecl_then [‘FDIFF f (set (MAP FST binds1))’, ‘SND (EL n3 binds1)’,
                       ‘set (MAP FST binds2)’] assume_tac subst_FDIFF' >>
          ‘MEM (EL n3 binds1) binds1’ by (irule EL_MEM >> gvs []) >> gvs [] >>
          last_x_assum $ dxrule_then assume_tac >>
          gvs [FDIFF_def, INTER_COMM]) >>
      ‘MEM (EL n2 binds1) binds1’ by (irule EL_MEM >> gvs []) >> gvs [] >>
      qspecl_then [‘FDIFF f (set (MAP FST binds1))’, ‘SND (EL n2 binds1)’,
                   ‘set (MAP FST binds2)’] assume_tac subst_FDIFF' >>
      last_x_assum $ dxrule_then assume_tac >>
      gvs [FDIFF_def, INTER_COMM]) >>
  irule $ iffLR exp_eq_sym >> irule exp_eq_trans >> irule_at Any beta_equality_Letrec >>
  gvs [MAP_MAP_o, combinTheory.o_DEF, EVERY_EL, LAMBDA_PROD, MAP_FST, EL_MAP] >>
  rw []
  >~[‘n < _’]
  >- (qabbrev_tac ‘pair1 = EL n binds1’ >> PairCases_on ‘pair1’ >> gvs [] >>
      ‘∀n. n ∈ FRANGE (FDIFF (FDIFF f (set (MAP FST binds2))) (set (MAP FST binds1))) ⇒ closed n’
        by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
            first_x_assum $ dxrule_then irule) >>
      gvs [freevars_subst, FDOM_FDIFF, DIFF_SUBSET, SUBSET_DEF] >>
      rw [] >> gvs []
      >- (first_x_assum $ drule_then assume_tac >>
          ‘∀n. n ∈ FRANGE (FDIFF f (set (MAP FST binds1))) ⇒ closed n’
            by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
                first_x_assum $ dxrule_then irule) >>
          gvs [freevars_subst]) >>
      gvs [MEM_EL] >>
      last_x_assum $ drule_then assume_tac >>
      gvs [DISJOINT_ALT, EL_MAP] >>
      rename1 ‘FST (EL n2 _) ∈ _’ >> first_x_assum $ qspecl_then [‘FST (EL n2 binds2)’] assume_tac >>
      gvs [] >> qsuff_tac ‘F’ >- gvs [] >>
      first_x_assum irule >>
      gvs [MEM_EL] >> first_assum $ irule_at Any >> gvs [EL_MAP]) >>
  irule eq_IMP_exp_eq >> irule AP_THM >>
  conj_tac
  >- gvs [FDIFF_def, INTER_COMM] >>
  irule EQ_TRANS >> irule_at (Pos hd) subst_funs_eq_subst >>
  gvs [EVERY_EL, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP_FST] >>
  rw []
  >~[‘n < _’]
  >- (qabbrev_tac ‘pair1 = EL n binds1’ >> PairCases_on ‘pair1’ >> gvs [EL_MAP] >>
      ‘∀n. n ∈ FRANGE (FDIFF (FDIFF f (set (MAP FST binds2))) (set (MAP FST binds1))) ⇒ closed n’
        by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
            first_x_assum $ dxrule_then irule) >>
      gvs [freevars_subst, FDOM_FDIFF, DIFF_SUBSET, SUBSET_DEF] >>
      rw [] >> gvs []
      >- (first_x_assum $ drule_then assume_tac >>
          ‘∀n. n ∈ FRANGE (FDIFF f (set (MAP FST binds1))) ⇒ closed n’
            by (rw [] >> gvs [FRANGE_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >>
                first_x_assum $ dxrule_then irule) >>
          gvs [freevars_subst]) >>
      gvs [MEM_EL] >>
      last_x_assum $ drule_then assume_tac >>
      gvs [DISJOINT_ALT, EL_MAP] >>
      rename1 ‘FST (EL n2 _) ∈ _’ >> first_x_assum $ qspecl_then [‘FST (EL n2 binds2)’] assume_tac >>
      gvs [] >> qsuff_tac ‘F’ >- gvs [] >>
      first_x_assum irule >>
      gvs [MEM_EL] >> first_assum $ irule_at Any >> gvs [EL_MAP]) >>
  AP_TERM_TAC >>
  gvs [FDIFF_def] >> irule EQ_TRANS >>
  irule_at (Pos last) $ GSYM disjoint_drestrict >>
  gvs [FDOM_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, DISJOINT_ALT, EVERY_MEM] >>
  gvs [FORALL_PROD, LAMBDA_PROD, MAP_FST] >>
  rw []
  >- (strip_tac >> gvs [MEM_EL, EL_MAP] >>
      last_x_assum $ dxrule_then assume_tac >>
      rename1 ‘_ (EL n1 binds1)’ >> qabbrev_tac ‘pair1 = EL n1 binds1’ >> PairCases_on ‘pair1’ >> gvs [] >>
      rename1 ‘EL _ _ = (FST (EL n2 _), _)’ >> first_x_assum $ qspecl_then [‘n2’] assume_tac >>
      gvs [EL_MAP]) >>
  AP_TERM_TAC >> irule LIST_EQ >>
  gvs [EL_MAP] >> rw [] >>
  rename1 ‘EL n1 _’ >> qabbrev_tac ‘pair = EL n1 binds1’ >> PairCases_on ‘pair’ >> gvs [] >>
  irule_at Any LIST_EQ >> rw [EL_MAP]
  >- (rename1 ‘_ (EL n2 _)’ >> qabbrev_tac ‘EL_n2_binds1 = EL n2 binds1’ >>
      PairCases_on ‘EL_n2_binds1’ >> gvs [] >>
      rename1 ‘DRESTRICT f _’ >>
      qspecl_then [‘FDIFF f (set (MAP FST binds1))’, ‘SND (EL n2 binds1)’,
                   ‘set (MAP FST binds2)’] assume_tac subst_FDIFF' >>
      last_x_assum $ drule_then assume_tac >>
      gvs [FDIFF_def, INTER_COMM]) >>
  last_x_assum $ drule_then assume_tac >>
  qspecl_then [‘FDIFF f (set (MAP FST binds1))’, ‘SND (EL n1 binds1)’,
               ‘set (MAP FST binds2)’] assume_tac subst_FDIFF' >>
  gvs [FDIFF_def, INTER_COMM]
QED

Theorem MAP_FST_no_change:
  ∀l f. MAP FST l = MAP FST (MAP (λ(v, e). (v, f e)) l)
Proof
  Induct >> gvs [FORALL_PROD]
QED

Theorem ALL_DISTINCT_FST_MAP:
  ∀l f. ALL_DISTINCT (MAP FST l) ⇒ ALL_DISTINCT (MAP FST (MAP (λ(v,e). (v, f e)) l))
Proof
  gvs [GSYM MAP_FST_no_change]
QED

Theorem exp_eq_in_ctxt_Letrec:
  ∀c binds1 binds2 e1 e2.
    ALL_DISTINCT (MAP FST binds1) ∧
    LIST_REL (λ(v1, e1) (v2, e2). v1 = v2
                                  ∧ exp_eq_in_ctxt (RecBind binds1 c) e1 e2
                                  ∧ exp_eq_in_ctxt (RecBind binds2 c) e1 e2) binds1 binds2
    ∧ exp_eq_in_ctxt (RecBind binds1 c) e1 e2
    ⇒ exp_eq_in_ctxt c (Letrec binds1 e1) (Letrec binds2 e2)
Proof
  Induct >> rw []
  >- (gvs [exp_eq_in_ctxt_def] >>
      irule exp_eq_trans >> first_x_assum $ irule_at Any >>
      irule exp_eq_Letrec_change >>
      gvs [LIST_REL_EL_EQN] >> rw [] >>
      rename1 ‘n < _’ >>
      qabbrev_tac ‘p1 = EL n binds1’ >> PairCases_on ‘p1’ >>
      qabbrev_tac ‘p2 = EL n binds2’ >> PairCases_on ‘p2’ >>
      last_x_assum $ drule_then assume_tac >> gvs []) >>
  ‘MAP FST binds2 = MAP FST binds1’
    by (irule LIST_EQ >> gvs [LIST_REL_EL_EQN] >>
        rw [EL_MAP] >>
        rpt $ first_x_assum $ drule_then assume_tac >>
        rename1 ‘FST p1 = FST p2’ >> PairCases_on ‘p1’ >> PairCases_on ‘p2’ >> gvs [])
  >~[‘exp_eq_in_ctxt (RecBind _ _) (Letrec _ _)’]
  >- (gvs [exp_eq_in_ctxt_def] >>
      irule exp_eq_in_ctxt_trans >> first_x_assum $ irule_at Any >>
      gvs [GSYM exp_eq_in_ctxt_def] >>
      rename1 ‘_ (RecBind l _) (Letrec binds1 e2) (Letrec binds2 _)’ >>
      drule_then assume_tac Letrec_rename >>
      pop_assum $ qspecl_then [‘freevars (Letrec l (Letrec binds1 e2)) ∪ set (MAP FST l)
                                ∪ freevars (Letrec binds1 e2) ∪ freevars (Letrec binds2 e2)’] assume_tac >>
      gvs [freevars_FINITE, FINITE_UNION] >>
      first_assum $ qspecl_then [‘MAP SND binds1’] assume_tac >>
      first_x_assum $ qspecl_then [‘MAP SND binds2’] assume_tac >>
      gvs [GSYM UNZIP_MAP, ZIP_UNZIP] >>
      irule exp_eq_in_ctxt_trans >> irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt >>
      first_assum $ irule_at Any >> gvs [] >>
      ‘ZIP (MAP FST binds1, MAP SND binds2) = binds2’ by metis_tac [ZIP_UNZIP, UNZIP_MAP] >>
      conj_tac
      >- (rw [SUBSET_DEF] >> gvs []) >>
      gvs [] >>
      irule exp_eq_in_ctxt_trans >> irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any $ iffLR exp_eq_sym >> first_assum $ irule_at Any >>
      gvs [LIST_REL_EL_EQN, exp_eq_in_ctxt_def] >>
      irule exp_eq_in_ctxt_trans >> irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any Letrec_distrib_Letrec >>
      gvs [EVERY_MEM, DISJOINT_ALT, MAP_ZIP, FORALL_PROD] >> rw []
      >~[‘¬MEM p1 _’]
      >-(rpt $ first_x_assum $ qspecl_then [‘p1’] assume_tac >>
         pop_assum kall_tac >> pop_assum irule >>
         gvs [MEM_MAP, EXISTS_PROD] >>
         first_x_assum $ irule_at Any)
      >~[‘x ∉ freevars p2’]
      >- (strip_tac >> rpt $ first_x_assum $ qspecl_then [‘x’] assume_tac >>
          gvs [] >>
          pop_assum $ qspecl_then [‘freevars p2’] assume_tac >> gvs [] >>
          pop_assum irule >> gvs [MEM_MAP] >>
          first_x_assum $ irule_at Any >> gvs []) >>
      irule exp_eq_in_ctxt_trans >> irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any $ iffLR exp_eq_sym >> irule_at Any Letrec_distrib_Letrec >>
      gvs [EVERY_MEM, DISJOINT_ALT, MAP_ZIP, FORALL_PROD] >> rw []
      >~[‘¬MEM p1 _’]
      >-(rpt $ first_x_assum $ qspecl_then [‘p1’] assume_tac >>
         pop_assum kall_tac >> pop_assum irule >>
         gvs [MEM_MAP, EXISTS_PROD] >>
         first_x_assum $ irule_at Any)
      >~[‘x ∉ freevars p2’]
      >- (strip_tac >> rpt $ first_x_assum $ qspecl_then [‘x’] assume_tac >>
          gvs [] >>
          pop_assum $ qspecl_then [‘freevars p2’] assume_tac >> gvs [] >>
          pop_assum irule >> gvs [MEM_MAP] >>
          first_x_assum $ irule_at Any >> gvs []) >>
      last_x_assum $ irule_at Any >>
      gvs [exp_eq_in_ctxt_refl, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, EL_MAP, MAP_ZIP, MAP_FST, EL_ZIP] >>
      rw [] >>
      irule exp_eq_in_ctxt_trans >> irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any Letrec_distrib_Letrec >>
      gvs [EVERY_MEM, DISJOINT_ALT, MAP_ZIP, FORALL_PROD] >> rw []
      >>~[‘¬MEM p1 _’]
      >-(rpt $ first_x_assum $ qspecl_then [‘p1’] assume_tac >>
         pop_assum kall_tac >> pop_assum irule >>
         gvs [MEM_MAP, EXISTS_PROD] >>
         first_x_assum $ irule_at Any)
      >-(rpt $ first_x_assum $ qspecl_then [‘p1’] assume_tac >>
         pop_assum kall_tac >> pop_assum irule >>
         gvs [MEM_MAP, EXISTS_PROD] >>
         first_x_assum $ irule_at Any)
      >>~[‘x ∉ freevars p2’]
      >- (strip_tac >> rpt $ first_x_assum $ qspecl_then [‘x’] assume_tac >>
          gvs [] >>
          pop_assum $ qspecl_then [‘freevars p2’] assume_tac >> gvs [] >>
          pop_assum irule >> gvs [MEM_MAP] >>
          first_x_assum $ irule_at Any >> gvs [])
      >- (strip_tac >> rpt $ first_x_assum $ qspecl_then [‘x’] assume_tac >>
          gvs [] >>
          pop_assum $ qspecl_then [‘freevars p2’] assume_tac >> gvs [] >>
          pop_assum irule >> gvs [MEM_MAP] >>
          first_x_assum $ irule_at Any >> gvs []) >>
      irule exp_eq_in_ctxt_trans >> irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any $ iffLR exp_eq_sym >> irule_at Any Letrec_distrib_Letrec >>
      gvs [EVERY_MEM, DISJOINT_ALT, MAP_ZIP, FORALL_PROD] >> rw []
      >>~[‘¬MEM p1 _’]
      >-(rpt $ first_x_assum $ qspecl_then [‘p1’] assume_tac >>
         pop_assum kall_tac >> pop_assum irule >>
         gvs [MEM_MAP, EXISTS_PROD] >>
         first_x_assum $ irule_at Any)
      >-(rpt $ first_x_assum $ qspecl_then [‘p1’] assume_tac >>
         pop_assum kall_tac >> pop_assum irule >>
         gvs [MEM_MAP, EXISTS_PROD] >>
         first_x_assum $ irule_at Any)
      >>~[‘x ∉ freevars p2’]
      >- (strip_tac >> rpt $ first_x_assum $ qspecl_then [‘x’] assume_tac >>
          gvs [] >>
          pop_assum $ qspecl_then [‘freevars p2’] assume_tac >> gvs [] >>
          pop_assum irule >> gvs [MEM_MAP] >>
          first_x_assum $ irule_at Any >> gvs [])
      >- (strip_tac >> rpt $ first_x_assum $ qspecl_then [‘x’] assume_tac >>
          gvs [] >>
          pop_assum $ qspecl_then [‘freevars p2’] assume_tac >> gvs [] >>
          pop_assum irule >> gvs [MEM_MAP] >>
          first_x_assum $ irule_at Any >> gvs []) >>
      irule exp_eq_in_ctxt_trans >> irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any exp_eq_Letrec_cong >> irule_at Any exp_eq_l_refl >>
      last_assum $ irule_at Any >>
      irule_at Any exp_eq_in_ctxt_trans >> irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any exp_eq_Letrec_cong >> irule_at Any exp_eq_l_refl >>
      irule_at Any $ iffLR exp_eq_sym >> last_x_assum $ irule_at Any >>
      last_x_assum $ drule_then assume_tac >> gvs [] >>
      rename1 ‘n < _’ >>
      qabbrev_tac ‘p1 = EL n binds1’ >> PairCases_on ‘p1’ >>
      qabbrev_tac ‘p2 = EL n binds2’ >> PairCases_on ‘p2’ >> gvs [] >>
      gvs [SUBSET_DEF] >> rw [] >> gvs []
      >- (disj1_tac >> disj2_tac >> disj2_tac >> gvs [MEM_MAP] >>
          irule_at Any EL_MEM >> gvs [] >>
          first_assum $ irule_at Any >> gvs [])
      >- (disj1_tac >> disj2_tac >> disj2_tac >> gvs [MEM_MAP] >>
          rpt $ first_x_assum $ irule_at Any >> fs [])
      >- (disj2_tac >> disj2_tac >> gvs [MEM_MAP] >>
          irule_at Any EL_MEM >> gvs [] >>
          first_assum $ irule_at Any >> gvs [])
      >- (disj1_tac >> disj2_tac >> disj2_tac >> gvs [MEM_MAP] >>
          rpt $ first_x_assum $ irule_at Any >> fs [])
      >- (disj1_tac >> disj2_tac >> disj2_tac >> gvs [MEM_MAP] >>
          irule_at Any EL_MEM >> gvs [] >>
          first_assum $ irule_at Any >> gvs [])
      >- (disj2_tac >> disj2_tac >> gvs [MEM_MAP] >>
          rpt $ first_x_assum $ irule_at Any >> fs [])
      >- (disj2_tac >> disj2_tac >> gvs [MEM_MAP] >>
          irule_at Any EL_MEM >> gvs [] >>
          first_assum $ irule_at Any >> gvs [])
      >- (disj2_tac >> disj2_tac >> gvs [MEM_MAP] >>
          rpt $ first_x_assum $ irule_at Any >> fs [])) >>
  gvs [exp_eq_in_ctxt_def] >> rw [] >>
  irule exp_eq_in_ctxt_trans >> first_x_assum $ irule_at Any >> gvs [] >>
  gvs [GSYM exp_eq_in_ctxt_def] >>
  rename1 ‘_ (Bind s e3 _) (Letrec binds1 e2) (Letrec binds2 _)’ >>
  drule_then assume_tac Letrec_rename >>
  pop_assum $ qspecl_then [‘freevars e3 ∪ {s}
                            ∪ freevars (Letrec binds1 e2) ∪ freevars (Letrec binds2 e2)’] assume_tac >>
  gvs [freevars_FINITE, FINITE_UNION] >>
  first_assum $ qspecl_then [‘MAP SND binds1’] assume_tac >>
  first_x_assum $ qspecl_then [‘MAP SND binds2’] assume_tac >>
  gvs [GSYM UNZIP_MAP, ZIP_UNZIP] >>
  irule exp_eq_in_ctxt_trans >> irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt >>
  first_assum $ irule_at Any >> gvs [] >>
  ‘ZIP (MAP FST binds1, MAP SND binds2) = binds2’ by metis_tac [ZIP_UNZIP, UNZIP_MAP] >>
  rw [SUBSET_DEF] >> gvs [] >>
  irule exp_eq_in_ctxt_trans >> irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any $ iffLR exp_eq_sym >> first_assum $ irule_at Any >>
  gvs [LIST_REL_EL_EQN, exp_eq_in_ctxt_def, closed_def] >>
  irule exp_eq_in_ctxt_trans >> irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any Let_Letrec2 >>
  irule_at Any exp_eq_in_ctxt_trans >> irule_at (Pos $ el 2) exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any $ iffLR exp_eq_sym >> irule_at Any Let_Letrec2 >>
  gvs [EVERY_MEM, MAP_ZIP, DISJOINT_ALT] >>
  rw []
  >>~[‘v ∉ freevars e3’]
  >- (strip_tac >> gvs [])
  >- (strip_tac >> gvs []) >>
  last_x_assum irule >>
  gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP_FST, EL_MAP, EL_ZIP, MAP_ZIP, exp_eq_in_ctxt_refl] >>
  rw [] >>
  irule exp_eq_in_ctxt_trans >> irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any Let_Letrec2 >>
  irule_at Any exp_eq_in_ctxt_trans >> irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any $ iffLR exp_eq_sym >> irule_at Any Let_Letrec2 >>
  gvs [EVERY_MEM, MAP_ZIP] >> rw []
  >>~[‘v ∉ freevars e3’]
  >- (strip_tac >> gvs [])
  >- (strip_tac >> gvs []) >>
  irule exp_eq_in_ctxt_trans >> irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any exp_eq_App_cong >> irule_at Any exp_eq_Lam_cong >>
  first_assum $ irule_at Any >>
  irule_at Any $ exp_eq_refl >> gvs [] >>
  irule_at Any exp_eq_in_ctxt_trans >> irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any $ iffLR exp_eq_sym >>
  irule_at Any exp_eq_App_cong >> irule_at Any exp_eq_Lam_cong >>
  first_assum $ irule_at Any >> irule_at Any exp_eq_refl >>
  last_x_assum $ drule_then assume_tac >> gvs [] >>
  rename1 ‘n < _’ >>
  qabbrev_tac ‘p1 = EL n binds1’ >> PairCases_on ‘p1’ >>
  qabbrev_tac ‘p2 = EL n binds2’ >> PairCases_on ‘p2’ >> gvs [] >>
  rw [SUBSET_DEF] >> gvs []
  >- (disj1_tac >> disj2_tac >> disj2_tac >> rw [MEM_EL] >>
      rpt $ first_assum $ irule_at Any >> gvs [EL_MAP])
  >- (disj1_tac >> disj2_tac >> disj2_tac >> rpt $ first_assum $ irule_at Any)
  >- (disj2_tac >> disj2_tac >> rw [MEM_EL] >>
      rpt $ first_assum $ irule_at Any >> gvs [EL_MAP])
  >- (disj1_tac >> disj2_tac >> disj2_tac >> rpt $ first_assum $ irule_at Any)
  >- (disj1_tac >> disj2_tac >> disj2_tac >> rw [MEM_EL] >>
      rpt $ first_assum $ irule_at Any >> gvs [EL_MAP])
  >- (disj2_tac >> disj2_tac >> rpt $ first_assum $ irule_at Any)
  >- (disj2_tac >> disj2_tac >> rw [MEM_EL] >>
      rpt $ first_assum $ irule_at Any >> gvs [EL_MAP])
  >- (disj2_tac >> disj2_tac >> rpt $ first_assum $ irule_at Any)
  >- (disj1_tac >> disj2_tac >> disj2_tac >> rw [MEM_EL] >>
      rpt $ first_assum $ irule_at Any >> gvs [EL_MAP])
  >- (disj1_tac >> disj2_tac >> disj2_tac >> rpt $ first_assum $ irule_at Any)
  >- (disj2_tac >> disj2_tac >> rw [MEM_EL] >>
      rpt $ first_assum $ irule_at Any >> gvs [EL_MAP])
  >- (disj1_tac >> disj2_tac >> disj2_tac >> rpt $ first_assum $ irule_at Any)
  >- (disj1_tac >> disj2_tac >> disj2_tac >> rw [MEM_EL] >>
      rpt $ first_assum $ irule_at Any >> gvs [EL_MAP])
  >- (disj2_tac >> disj2_tac >> rpt $ first_assum $ irule_at Any)
  >- (disj2_tac >> disj2_tac >> rw [MEM_EL] >>
      rpt $ first_assum $ irule_at Any >> gvs [EL_MAP])
  >- (disj2_tac >> disj2_tac >> rpt $ first_assum $ irule_at Any)
QED

Theorem Let_stay:
  ∀v e b. v ∉ freevars e ⇒ (Let v e (Var v) ≅? Let v e e) b
Proof
  rw [] >> irule exp_eq_trans >>
  irule_at Any Let_Var >>
  irule eval_IMP_exp_eq >>
  rw [eval_thm, subst_def, GSYM subst_fdomsub, bind1_def, subst1_ignore,
      closed_def, IMP_closed_subst, FRANGE_FLOOKUP]
QED

Theorem concat_rev_ctxt_size:
  ∀c1 c2. ctxt_size (concat_rev_ctxt c1 c2) = ctxt_size c1 + ctxt_size c2
Proof
  Induct >> gvs [ctxt_size_def, concat_rev_ctxt_def]
QED

Theorem exp_eq_in_ctxt_unfold:
  ∀c2 w e' c1. not_bound_in_ctxt c2 w
               ∧ (∀v. v ∈ freevars e' ⇒ not_bound_in_ctxt c2 v) ∧ w ∉ freevars e'
              ⇒ exp_eq_in_ctxt (Bind w e' c1) (unfold_ctxt c2 (Var w)) (unfold_ctxt c2 e')
Proof
  Induct >> rw [not_bound_in_ctxt_def, exp_eq_in_ctxt_def, unfold_ctxt_def]
  >- gvs [exp_eq_in_ctxt_def, exp_eq_IMP_exp_eq_in_ctxt, Let_stay] >>
  irule exp_eq_in_ctxt_trans >> irule_at Any exp_eq_in_ctxt_trans >>
  irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt >> irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at (Pos hd) $ iffLR exp_eq_sym
  >~[‘Letrec’]
  >- (rpt $ irule_at Any Let_Letrec2 >>
      gvs [GSYM exp_eq_in_ctxt_def, EVERY_MEM] >>
      rw [] >> strip_tac >> first_x_assum $ dxrule_then assume_tac >>
      gvs [])
  >- (rpt $ irule_at Any Let_Lam_weak >>
      irule_at Any exp_eq_in_ctxt_Lam >>
      gvs [GSYM exp_eq_in_ctxt_def] >>
      strip_tac >> first_x_assum $ dxrule_then assume_tac >> fs [])
  >- (rpt $ irule_at Any Let_App >> irule exp_eq_in_ctxt_App >> fs [exp_eq_in_ctxt_refl] >>
      irule exp_eq_in_ctxt_trans >> irule_at Any exp_eq_in_ctxt_trans >>
      irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt >> irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at (Pos hd) $ iffLR exp_eq_sym >>
      rpt $ irule_at Any Let_Lam_weak >>
      irule_at Any exp_eq_in_ctxt_Lam >>
      gvs [GSYM exp_eq_in_ctxt_def] >>
      strip_tac >> first_x_assum $ dxrule_then assume_tac >> fs [])
QED

Theorem concat_rev_unfold:
  ∀c2 c1 e1 e2 len. exp_eq_in_ctxt (concat_rev_ctxt c2 c1) e1 e2
                    = exp_eq_in_ctxt c1 (unfold_ctxt c2 e1) (unfold_ctxt c2 e2)
Proof
  Induct >> gvs [exp_eq_in_ctxt_def, concat_rev_ctxt_def, unfold_ctxt_def] >>
  rw [] >> eq_tac >> rw []
  >- (irule exp_eq_in_ctxt_Lam >> gvs [exp_eq_in_ctxt_def])
  >- gvs [exp_eq_in_ctxt_App, exp_eq_in_ctxt_refl]
QED

Theorem exp_eq_in_ctxt_concat:
  ∀c2 w e' c1. not_bound_in_ctxt c2 w ∧
               (∀v. v ∈ freevars e' ⇒ not_bound_in_ctxt c2 v) ∧ w ∉ freevars e'
               ⇒ exp_eq_in_ctxt (concat_rev_ctxt c2 (Bind w e' c1)) (Var w) e'
Proof
  gvs [exp_eq_in_ctxt_unfold, concat_rev_unfold]
QED

Theorem exp_eq_concat_rev_still_eq:
  ∀c_top c_bot e e'.
    exp_eq_in_ctxt (concat_rev_ctxt c_top Nil) e e'
      ⇒ exp_eq_in_ctxt (concat_rev_ctxt c_top c_bot) e e'
Proof
  Induct >> gvs [concat_ctxt_def, concat_rev_unfold, unfold_ctxt_def, exp_eq_in_ctxt_def] >>
  rw [exp_eq_IMP_exp_eq_in_ctxt]
QED

Theorem exp_eq_concat_still_eq:
  ∀c_top c_bot e e'.
    exp_eq_in_ctxt c_top e e'
      ⇒ exp_eq_in_ctxt (concat_ctxt c_top c_bot) e e'
Proof
  Induct >> gvs [concat_ctxt_def, exp_eq_IMP_exp_eq_in_ctxt, exp_eq_in_ctxt_def]
QED

Theorem eq_when_applied_unfold:
  ∀c2 w e' c1 len. not_bound_in_ctxt c2 w ∧ (∀v. v ∈ freevars e' ⇒ not_bound_in_ctxt c2 v) ∧ w ∉ freevars e'
              ⇒ eq_when_applied (Bind w e' c1) (unfold_ctxt c2 (Var w)) (unfold_ctxt c2 e') len
Proof
  gvs [exp_eq_in_ctxt_IMP_eq_when_applied, exp_eq_in_ctxt_unfold]
QED

Theorem fmap_FOLDL_FOLDR:
  ∀l f f2. ALL_DISTINCT (MAP FST l) ⇒
           FOLDR (flip $|+) f l = FOLDL $|+ f l
Proof
  Induct >> gvs [FORALL_PROD] >> rw [] >>
  dxrule_then assume_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
  gvs [FUPDATE_LIST]
QED

Theorem subst_exp_eq:
  ∀l1 l2 b e e'.
    LIST_REL (λ(v1, e1) (v2, e2). v1 = v2 ∧ (e1 ≅? e2) b ∧ closed e1 ∧ closed e2) l1 l2
    ∧ (e ≅? e') b
    ⇒ (subst (FEMPTY |++ l1) e ≅? subst (FEMPTY |++ l2) e') b
Proof
  Induct using SNOC_INDUCT >> gvs [FUPDATE_LIST, subst_FEMPTY] >> PairCases >>
  Induct using SNOC_INDUCT >> gvs [] >> PairCases >>
  gvs [LIST_REL_SNOC, FUPDATE_LIST, FOLDL_SNOC] >>
  rw [Once subst_subst1_UPDATE] >>
  irule exp_eq_trans >> last_x_assum $ dxrule_then $ irule_at Any >>
  irule_at (Pos hd) exp_eq_trans >> dxrule_then (irule_at $ Pos hd) $ iffLR exp_eq_forall_subst >>
  irule_at Any exp_eq_subst >> first_x_assum $ irule_at (Pos hd) >>
  gvs [GSYM subst_subst1_UPDATE, exp_eq_refl]
QED

(** end ctxt **)

Definition is_bot_def:
  is_bot e = (e = wh_Diverge ∨ e = wh_Error)
End

Theorem is_bot_continuous:
  ∀e k k2. k2 ≤ k ∧ is_bot (eval_wh_to k e) ⇒ is_bot (eval_wh_to k2 e)
Proof
  rw [is_bot_def]
  \\ Cases_on ‘eval_wh_to k2 e = wh_Diverge’
  \\ fs []
  \\ qspecl_then [‘k’, ‘e’, ‘k2’] assume_tac eval_wh_inc
  \\ gvs []
QED

Definition Projs_def:
  Projs [] e = e ∧
  Projs ((x,i)::ps) e = Projs ps (Proj x i e)
End

Theorem freevars_Projs:
  ∀ps e. freevars (Projs ps e) = freevars e
Proof
  Induct >> gvs [freevars_def, Projs_def, FORALL_PROD]
QED

Theorem perm_exp_Projs:
  ∀ps v w e. perm_exp v w (Projs ps e) = Projs ps (perm_exp v w e)
Proof
  Induct >> gvs [perm_exp_def, Projs_def, FORALL_PROD]
QED

Theorem demands_Projs_end:
  ∀ ps x i e. Projs (ps++[(x,i)]) e = Proj x i (Projs ps e)
Proof
  Induct THEN1 rw [Projs_def]
  \\ gen_tac \\ rename1 ‘hd::ps’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
QED

Theorem double_Projs:
  ∀ps' ps e. Projs (ps' ++ ps) e = Projs ps (Projs ps' e)
Proof
  Induct >- rw [Projs_def]
  \\ gen_tac \\ rename1 ‘hd::ps'’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
QED

Theorem exp_eq_Projs_cong:
  ∀ps x y b. (x ≅? y) b ⇒ (Projs ps x ≅? Projs ps y) b
Proof
  Induct \\ fs [Projs_def,FORALL_PROD]
  \\ rw [] \\ first_x_assum irule
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
QED

Theorem Projs_Seq:
  ∀ps e e' b. (Projs ps (Seq e e') ≅? Seq e (Projs ps e')) b
Proof
  Induct
  THEN1 (rw [Projs_def] \\ fs [exp_eq_refl])
  \\ rpt gen_tac
  \\ rename1 ‘hd::ps’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
  \\ irule exp_eq_trans \\ qexists_tac ‘Projs ps (Seq e (Proj hd0 hd1 e'))’
  \\ fs [Proj_Seq2, exp_eq_sym, exp_eq_Projs_cong, Seq_id]
QED

Theorem Let_Projs:
  ∀ps x w y b. (Let w y (Projs ps x) ≅? Projs ps (Let w y x)) b
Proof
  Induct \\ fs [Projs_def,exp_eq_refl,FORALL_PROD] \\ rw []
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ps (Let w y (Proj p_1 p_2 x))’
  \\ conj_tac THEN1 fs []
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Prim_alt]
QED

Theorem Letrec_Projs:
  ∀ps x bL b. (Letrec bL (Projs ps x) ≅? Projs ps (Letrec bL x)) b
Proof
  Induct \\ fs [Projs_def,exp_eq_refl,FORALL_PROD] \\ rw []
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ps (Letrec bL (Proj p_1 p_2 x))’
  \\ conj_tac THEN1 fs []
  \\ irule exp_eq_Projs_cong
  \\ irule exp_eq_trans
  \\ irule_at Any Letrec_Prim
  \\ gvs [exp_eq_refl]
QED

Theorem Projs_subst:
  ∀ps f e. subst f (Projs ps e) = Projs ps (subst f e)
Proof
  Induct THEN1 rw [Projs_def]
  \\ gen_tac
  \\ rename1 ‘Projs (hd::_) _’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def, subst_def]
QED

val _ = set_fixity "demands" (Infixl 480);

Definition demands_def:
  (e demands ((p,v), c)) = (exp_eq_in_ctxt c e (Seq (Projs p (Var v)) e))
End

val _ = set_fixity "needs" (Infixl 480);
Definition needs_def:
  (e needs ((ps, e'), c)) = (exp_eq_in_ctxt c e (Seq (Projs ps e') e))
End

Theorem is_bot_IMP_IMP_needs:
  ∀e ps e' c. (∀f. is_bot (eval_wh (subst f (Projs ps e'))) ⇒ is_bot (eval_wh (subst f e))) ⇒ e needs ((ps, e'), c)
Proof
  rw [needs_def]
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule no_err_eval_wh_IMP_exp_eq
  \\ rw [no_err_eval_wh_def, subst_def, eval_wh_thm]
  \\ first_x_assum $ qspecl_then [‘f’] assume_tac
  \\ gvs [is_bot_def]
QED

Theorem needs_Var_is_demands:
  e needs ((ps, Var v), c) ⇔ e demands ((ps, v), c)
Proof
  rw [needs_def, demands_def] \\ fs []
QED

Theorem needs_in_IsFree_Bind:
  e needs (d, IsFree v c) ⇒ e needs (d, Bind v e2 c)
Proof
  PairCases_on ‘d’
  \\ rw [needs_def, exp_eq_in_IsFree_Bind]
QED

Theorem needs_IsFree_List_lemma:
  ∀d e c v e'.
    e needs (d, FOLDL (λc v. IsFree v c) (IsFree v c) l)
    ⇒ e needs (d, FOLDL (λc v. IsFree v c) (Bind v e' c) l)
Proof
  Induct_on ‘LENGTH l’ >> rw [needs_in_IsFree_Bind] >>
  qspecl_then [‘l’] assume_tac last_exists >>
  rename1 ‘e needs (d, _)’ >> PairCases_on ‘d’ >>
  gvs [FOLDL_APPEND, FORALL_PROD, needs_def, exp_eq_in_ctxt_def, SNOC_APPEND] >>
  rpt strip_tac >>
  irule exp_eq_in_ctxt_trans >> irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt >>
  once_rewrite_tac [exp_eq_sym] >> irule_at Any exp_eq_trans >>
  irule_at (Pos hd) Let_Seq >>
  last_x_assum $ irule_at Any >> irule_at Any exp_eq_Prim_cong >>
  fs [exp_eq_refl] >> irule_at Any Let_Projs >>
  irule_at Any exp_eq_in_ctxt_trans >>
  first_x_assum $ irule_at Any >> fs [] >>
  irule exp_eq_IMP_exp_eq_in_ctxt >>
  irule exp_eq_trans >> irule_at Any Let_Seq >>
  gvs [Let_Projs, exp_eq_Prim_cong, exp_eq_refl]
QED

Theorem needs_IsFree_List:
  ∀l e c d. e needs (d, FOLDL (λc v. IsFree v c) c (MAP FST l))
            ⇒ e needs (d, FOLDL (λc (v, e). Bind v e c) c l)
Proof
  Induct >> rw [] >>
  last_x_assum $ irule_at Any >>
  rename1 ‘IsFree (FST h) c’ >> PairCases_on ‘h’ >>
  gvs [needs_IsFree_List_lemma]
QED

Theorem demands_in_IsFree_Bind:
  e demands (d, IsFree v c) ⇒ e demands (d, Bind v e2 c)
Proof
  PairCases_on ‘d’
  \\ rw [demands_def, exp_eq_in_IsFree_Bind]
QED

Theorem demands_IsFree_List:
  ∀d l e c. e demands (d, FOLDL (λc v. IsFree v c) c (MAP FST l))
            ⇒ e demands (d, FOLDL (λc (v, e). Bind v e c) c l)
Proof
  PairCases
  \\ metis_tac [needs_IsFree_List, needs_Var_is_demands]
QED

Theorem needs_refl:
  ∀e c. e needs (([],e), c)
Proof
  rw [needs_def, Projs_def]
  \\ metis_tac [Seq_id, exp_eq_sym, exp_eq_IMP_exp_eq_in_ctxt]
QED

Theorem needs_Var:
  (Var v) needs (([], Var v), c)
Proof
  fs [needs_refl]
QED

Theorem needs_Proj:
  e needs d ⇒ (Proj n i e) needs d
Proof
  PairCases_on ‘d’
  \\ rename1 ‘((ps, e'), _)’
  \\ rw [needs_def, Projs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq e (Proj n i e)’
  \\ conj_tac >- fs [Proj_Seq, exp_eq_IMP_exp_eq_in_ctxt]
  \\ qabbrev_tac ‘p = Projs ps e'’
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Seq p e) (Proj n i e)’
  \\ conj_tac
  >- (irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_in_ctxt_refl])
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq p (Seq e (Proj n i e))’
  \\ conj_tac >- fs [exp_eq_IMP_exp_eq_in_ctxt, Seq_assoc]
  \\ irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_IMP_exp_eq_in_ctxt, exp_eq_refl, Let_Var]
  \\ metis_tac [exp_eq_IMP_exp_eq_in_ctxt, Proj_Seq, exp_eq_sym]
QED

Theorem needs_Projs:
  ∀ps e d. e needs d ⇒ (Projs ps e) needs d
Proof
  Induct
  >- rw [Projs_def]
  \\ gen_tac \\ rename1 ‘(hd::ps)’ \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
  \\ first_assum $ irule_at Any
  \\ irule needs_Proj
  \\ fs []
QED

Theorem needs_trans:
  e needs ((ps,e'), c) ∧ e' needs ((ps',e''), c) ⇒ e needs ((ps',e''), c)
Proof
  rw [needs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ first_assum $ irule_at Any
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Seq (Projs ps' e'') (Projs ps e')) e’
  \\ conj_tac >-
   (irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_in_ctxt_refl]
    \\ assume_tac needs_Projs \\ metis_tac [needs_def])
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Projs ps' e'') (Seq (Projs ps e') e)’
  \\ conj_tac >- fs [exp_eq_IMP_exp_eq_in_ctxt, Seq_assoc]
  \\ irule exp_eq_in_ctxt_Prim
  \\ fs [exp_eq_in_ctxt_refl, exp_eq_in_ctxt_sym]
QED

Theorem needs_Projs_Var:
  (Proj s i (Var v)) needs (([(s,i)], Var v), c)
Proof
  rw [needs_def, Projs_def]
  \\ metis_tac [exp_eq_IMP_exp_eq_in_ctxt, Seq_id, exp_eq_sym]
QED

Theorem needs_Seq:
  e needs d ⇒ (Seq e e') needs d
Proof
  PairCases_on ‘d’
  \\ rw [needs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Seq (Projs d0 d1) e) e'’
  \\ conj_tac >-
   (irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_in_ctxt_refl])
  \\ fs [exp_eq_IMP_exp_eq_in_ctxt, Seq_assoc]
QED

Theorem needs_Seq2:
  e' needs d ⇒ (Seq e e') needs d
Proof
  PairCases_on ‘d’
  \\ rw [needs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq e (Seq (Projs d0 d1) e')’
  \\ fs [exp_eq_in_ctxt_Prim, exp_eq_in_ctxt_refl]
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any Seq_assoc
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any Seq_comm
  \\ metis_tac [exp_eq_IMP_exp_eq_in_ctxt, Seq_assoc, exp_eq_sym]
QED

Theorem needs_Let1:
  e needs (d, c) ∧ e' demands (([],w), Bind w e c) ⇒ (Let w e e') needs (d, c)
Proof
  PairCases_on ‘d’
  \\ rw [demands_def,needs_def,Projs_def, exp_eq_in_ctxt_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ qabbrev_tac ‘p = (Projs d0 d1)’
  \\ first_assum $ irule_at Any
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Let w e (Var w)) (Let w e e')’
  \\ conj_tac THEN1 fs [exp_eq_IMP_exp_eq_in_ctxt, Let_Seq]
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq e (Let w e e')’
  \\ conj_tac
  THEN1 (irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_IMP_exp_eq_in_ctxt, exp_eq_refl,Let_Var])
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Seq p e) (Let w e e')’
  \\ conj_tac THEN1
   (irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_in_ctxt_refl])
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq p (Seq e (Let w e e'))’
  \\ conj_tac THEN1 fs [exp_eq_IMP_exp_eq_in_ctxt, Seq_assoc]
  \\ irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_in_ctxt_refl]
  \\ once_rewrite_tac [exp_eq_in_ctxt_sym]
  \\ irule exp_eq_in_ctxt_trans
  \\ first_assum $ irule_at Any
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Seq
  \\ irule exp_eq_Prim_cong
  \\ fs [exp_eq_refl, Let_Var]
QED

Theorem needs_Let_Cons: (* expects program to be in ANF *)
  e demands (((s,LENGTH xs)::ps,w), Bind w (Cons s (xs ++ e' ::ys)) c) ⇒
  (Let w (Cons s (xs ++ e'::ys)) e) needs ((ps,e'), c)
Proof
  rw [demands_def,needs_def,Projs_def, exp_eq_in_ctxt_def]
  \\ qabbrev_tac ‘cons = (Cons s (xs ++ e'::ys))’
  \\ irule exp_eq_in_ctxt_trans
  \\ last_assum $ irule_at Any
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any Let_Seq
  \\ irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_IMP_exp_eq_in_ctxt, exp_eq_in_ctxt_refl,Let_Var]
  \\ fs [GSYM Projs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any Let_Projs
  \\ fs [Projs_def]
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule exp_eq_Projs_cong \\ fs [exp_eq_refl,Let_Var]
  \\ irule exp_eq_trans
  \\ irule_at Any exp_eq_Prim_cong \\ fs [PULL_EXISTS]
  \\ irule_at Any Let_Var
  \\ unabbrev_all_tac
  \\ fs [Proj_Cons]
QED

Theorem needs_Let_Proj: (* expects program to be in ANF *)
  e demands ((ps,w), Bind w (Proj s i e') c) ⇒
  (Let w (Proj s i e') e) needs (((s,i)::ps,e'), c)
Proof
  rw [demands_def,needs_def,Projs_def, exp_eq_in_ctxt_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ last_assum $ irule_at Any
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Let w (Proj s i e') (Projs ps (Var w)))
                      (Let w (Proj s i e') e)’
  \\ conj_tac THEN1 fs [exp_eq_IMP_exp_eq_in_ctxt, Let_Seq]
  \\ irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_IMP_exp_eq_in_ctxt, exp_eq_refl,Let_Var]
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ps (Let w (Proj s i e') (Var w))’
  \\ conj_tac THEN1 fs [Let_Projs]
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var]
QED

Theorem needs_App:
  f needs d ⇒ (App f e) needs d
Proof
  PairCases_on ‘d’ \\ rename1 ‘((ps,e'), c)’
  \\ rw [needs_def]
  \\ qabbrev_tac ‘proj = Projs ps e'’
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘App (Seq proj f) e’
  \\ conj_tac THEN1
   (irule exp_eq_in_ctxt_App \\ rw [exp_eq_in_ctxt_refl])
  \\ fs [exp_eq_IMP_exp_eq_in_ctxt, App_Seq]
QED

Theorem needs_If:
  e needs d ⇒ (If e e' e'') needs d
Proof
  PairCases_on ‘d’
  \\ rw [needs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any If_Seq
  \\ irule exp_eq_in_ctxt_Prim
  \\ fs [exp_eq_in_ctxt_refl, exp_eq_in_ctxt_sym]
QED

Theorem needs_If2:
  et needs d ∧ ee needs d ⇒ (If ec et ee) needs d
Proof
  PairCases_on ‘d’
  \\ rw [needs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any If_Seq2
  \\ irule exp_eq_in_ctxt_Prim
  \\ fs [exp_eq_in_ctxt_refl, exp_eq_in_ctxt_sym]
QED

Theorem needs_exp_eq:
  ∀d c e e'. exp_eq_in_ctxt c e e' ⇒ e needs (d, c) ⇒ e' needs (d, c)
Proof
  PairCases
  \\ rw [needs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at Any $ iffLR exp_eq_in_ctxt_sym
  \\ first_assum $ irule_at Any
  \\ irule exp_eq_in_ctxt_trans
  \\ pop_assum $ irule_at Any
  \\ fs [exp_eq_in_ctxt_Prim, exp_eq_in_ctxt_refl]
QED

        (********************************************)

Theorem demands_Var:
  (Var v) demands (([],v), c)
Proof
  metis_tac [needs_Var_is_demands, needs_Var]
QED

Theorem demands_Proj:
  e demands d ⇒
  (Proj n i e) demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_Var_is_demands, needs_Proj]
QED

Theorem demands_Projs:
  e demands d ⇒
  (Projs ps2 e) demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_Var_is_demands, needs_Projs]
QED

Theorem demands_Proj_Var:
  (Proj s i (Var v)) demands (([(s,i)],v), c)
Proof
  rw [demands_def,Projs_def]
  \\ metis_tac [Seq_id,exp_eq_sym, exp_eq_IMP_exp_eq_in_ctxt]
QED

Theorem demands_Seq:
  e demands d ⇒ (Seq e e') demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_Var_is_demands, needs_Seq]
QED

Theorem demands_Seq2:
  e' demands d ⇒ (Seq e e') demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_Var_is_demands, needs_Seq2]
QED

Theorem demands_Let1:
  e demands (d, c) ∧ e' demands (([],w), Bind w e c) ⇒ (Let w e e') demands (d, c)
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_def, needs_Var_is_demands, needs_Let1]
QED

Theorem demands_Let2:
  e' demands ((p,v), Bind w e c) ∧ v ≠ w ⇒ (Let w e e') demands ((p,v), c)
Proof
  rw [demands_def,Projs_def, exp_eq_in_ctxt_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ last_assum $ irule_at Any
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Let w e (Projs p (Var v))) (Let w e e')’
  \\ conj_tac THEN1 fs [exp_eq_IMP_exp_eq_in_ctxt, Let_Seq]
  \\ irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_IMP_exp_eq_in_ctxt, exp_eq_refl,Let_Var]
  \\ qid_spec_tac ‘p’ \\ Induct
  THEN1 fs [exp_eq_IMP_exp_eq_in_ctxt, Projs_def,Let_Var2]
  \\ fs [FORALL_PROD,Projs_def] \\ rw []
  \\ fs [GSYM Projs_def]
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ((p_1,p_2)::p') (Let w e (Var v))’
  \\ conj_tac THEN1 fs [Let_Projs]
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var2]
QED

Theorem demands_Let3:
  ∀e v h ps c. e demands ((ps, v), Bind v (Var h) c) ⇒ (Let v (Var h) e) demands ((ps, h), c)
Proof
  rw [demands_def, exp_eq_in_ctxt_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ last_assum $ irule_at Any
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Seq
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Projs
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var]
QED

Theorem demands_Let_Proj: (* expects program to be in ANF *)
  e demands ((ps,w), Bind w (Proj s i (Var v)) c) ⇒
  (Let w (Proj s i (Var v)) e) demands (((s,i)::ps,v), c)
Proof
  metis_tac [needs_Let_Proj, needs_Var_is_demands]
QED

Theorem demands_Let_Cons: (* expects program to be in ANF *)
  e demands (((s,LENGTH xs)::ps,w), Bind w (Cons s (xs ++ (Var v)::ys)) c) ⇒
  (Let w (Cons s (xs ++ (Var v)::ys)) e) demands ((ps,v), c)
Proof
  metis_tac [needs_Let_Cons, needs_Var_is_demands]
QED

Theorem demands_App:
  f demands d ⇒ (App f e) demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_App, needs_Var_is_demands]
QED

Theorem demands_If:
  e demands d ⇒ (If e e' e'') demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_If, needs_Var_is_demands]
QED

Theorem demands_If2:
  et demands d ∧ ee demands d ⇒ (If ec et ee) demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_If2, needs_Var_is_demands]
QED

Theorem demands_concat:
  ∀c1 c2 d e. e demands (d, c1) ⇒ e demands (d, concat_ctxt c1 c2)
Proof
  gvs [FORALL_PROD, demands_def, exp_eq_concat_still_eq]
QED

Definition well_formed_def:
  well_formed (Cons s) l = (s ≠ s) ∧
  well_formed (Proj s i) l = (∃ e. l = [e]) ∧
  well_formed (IsEq s i b) l = (∃e. l = [e]) ∧
  well_formed If (l: exp list) = (∃e e' e''. l = e::e'::e''::[]) ∧
  well_formed Seq l = (∃e e'. l = e::e'::[]) ∧
  well_formed (AtomOp op) l = (op ≠ op)
End

Theorem demands_Prim:
  e demands d ∧ well_formed ope (e::l) ⇒ Prim ope (e::l) demands d
Proof
  PairCases_on ‘d’
  \\ rw [demands_def]
  \\ qabbrev_tac ‘p = Projs d0 (Var d1)’
  \\ irule exp_eq_in_ctxt_trans \\ qexists_tac ‘Prim ope ((Seq p e)::l)’
  \\ conj_tac
  >- (irule exp_eq_in_ctxt_Prim
      \\ gvs [exp_eq_in_ctxt_refl, LIST_REL_EL_EQN])
  \\ Cases_on ‘ope’ \\ fs [well_formed_def]
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ fs [If_Seq, IsEq_Seq, Proj_Seq2, Seq_assoc]
QED

Theorem demands_IsEq:
  e demands d ⇒ (IsEq n i b e) demands d
Proof
  strip_tac
  \\ irule demands_Prim
  \\ fs [well_formed_def]
QED

Theorem demands_Letrec:
  ∀d b e c. e demands (d, RecBind b c) ∧ ¬MEM (SND d) (MAP FST b) ⇒ Letrec b e demands (d, c)
Proof
  PairCases >> rw [demands_def, exp_eq_in_ctxt_def] >>
  irule exp_eq_in_ctxt_trans >> last_x_assum $ irule_at Any >>
  irule exp_eq_IMP_exp_eq_in_ctxt >> irule exp_eq_trans >>
  irule_at Any Letrec_Prim >> irule exp_eq_Prim_cong >>
  gvs [exp_eq_refl] >>
  irule Letrec_not_in_freevars >>
  gvs [freevars_Projs, EVERY_MEM]
QED

Theorem needs_Projs_reduce:
  ∀ps ps' e e' c. e needs ((ps ++ ps', e'), c) ⇒ e needs ((ps, e'), c)
Proof
  rw [needs_def, double_Projs]
  \\ qabbrev_tac ‘p = Projs ps e'’
  \\ irule exp_eq_in_ctxt_trans \\ qexists_tac ‘Seq (Seq p (Projs ps' p)) e’
  \\ conj_tac
  >- (irule exp_eq_in_ctxt_trans \\ first_assum $ irule_at Any
      \\ irule exp_eq_in_ctxt_Prim
      \\ fs [exp_eq_in_ctxt_refl]
      \\ ‘p needs (([], p), c)’ by fs [needs_refl]
      \\ drule needs_Projs
      \\ rw [needs_def, Projs_def])
  \\ irule exp_eq_in_ctxt_trans \\ qexists_tac ‘Seq p (Seq (Projs ps' p) e)’
  \\ fs [exp_eq_IMP_exp_eq_in_ctxt, Seq_assoc]
  \\ irule exp_eq_in_ctxt_Prim
  \\ fs [exp_eq_in_ctxt_refl, exp_eq_in_ctxt_sym]
QED

Theorem demands_Projs_empty:
  ∀ps v c. (Projs ps (Var v)) demands (([], v), c)
Proof
  rpt gen_tac
  \\ ‘(Projs ps (Var v)) demands ((ps, v), c)’
    by metis_tac [exp_eq_IMP_exp_eq_in_ctxt, Projs_def, demands_def, Seq_id, exp_eq_sym]
  \\ irule $ iffLR needs_Var_is_demands
  \\ irule needs_Projs_reduce
  \\ fs []
  \\ rw [needs_Var_is_demands]
  \\ first_assum $ irule_at Any
QED

Theorem demands_empty_Projs:
  e demands ((ps, v), c) ⇒ e demands (([], v), c)
Proof
  ‘ps = [] ++ ps’ by rw []
  \\ rw []
  \\ metis_tac [needs_Projs_reduce, needs_Var_is_demands]
QED

Theorem demands_Projs_reduce:
  e demands ((ps ++ ps', v), c) ⇒ e demands ((ps, v), c)
Proof
  metis_tac [needs_Projs_reduce, needs_Var_is_demands]
QED

Theorem EXISTS_EL:
  ∀l P. EXISTS P l ⇒ ∃n. n < LENGTH l ∧ P (EL n l)
Proof
  Induct
  \\ fs [EXISTS_DEF]
  \\ rw []
  >- (qexists_tac ‘0’
      \\ fs [])
  \\ first_x_assum $ dxrule
  \\ rw []
  \\ rename1 ‘n < LENGTH l’
  \\ qexists_tac ‘SUC n’
  \\ fs []
QED

Theorem demands_AtomOp:
  ∀d l op. EXISTS (λe. e demands d) l ⇒ Prim (AtomOp op) l demands d
Proof
  gen_tac
  \\ PairCases_on ‘d’
  \\ rw [eval_wh_def, eval_wh_to_def, demands_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at Any exp_eq_in_ctxt_Prim
  \\ drule EXISTS_EL
  \\ rw []
  \\ rename1 ‘exp_eq_in_ctxt c (EL n l) (Seq p _)’
  \\ qexists_tac ‘LUPDATE (Seq p (EL n l)) n l’
  \\ rw [LIST_REL_EL_EQN, EL_LUPDATE]
  >- (IF_CASES_TAC
      \\ fs [exp_eq_in_ctxt_refl])
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule no_err_eval_wh_IMP_exp_eq
  \\ rw [no_err_eval_wh_def, subst_def, eval_wh_Prim_alt, MAP_MAP_o]
  \\ qabbrev_tac ‘l2 = LUPDATE (Seq p (EL n l)) n l’
  >- (qsuff_tac ‘EXISTS error_Atom (MAP (eval_wh o (λa. subst f a)) l2)’
      >- rw [get_atoms_def]
      \\ fs [EXISTS_MEM]
      \\ qexists_tac ‘eval_wh (subst f (EL n l2))’
      \\ unabbrev_all_tac
      \\ rw [LUPDATE_MAP, MEM_LUPDATE, EL_LUPDATE]
      \\ fs [subst_def, eval_wh_Seq])
  >- (Cases_on ‘EXISTS error_Atom (MAP (eval_wh o (λa. subst f a)) l2)’
      >- rw [get_atoms_def]
      \\ qsuff_tac ‘MEM wh_Diverge (MAP (eval_wh ∘ (λa. subst f a)) l2)’
      >- rw [get_atoms_def]
      \\ unabbrev_all_tac
      \\ rw [LUPDATE_MAP, MEM_LUPDATE, subst_def, eval_wh_Seq])
  \\ unabbrev_all_tac
  \\ rw [MAP_GENLIST, Once get_atoms_def]
  >- (fs [EXISTS_MAP]
      \\ drule EXISTS_EL
      \\ rw [EL_LUPDATE]
      \\ rename1 ‘n2 = n’
      \\ Cases_on ‘n2 = n’
      \\ rw []
      \\ fs [subst_def, eval_wh_Seq]
      >- (gvs []
          \\ ‘EXISTS (λx. error_Atom (eval_wh (subst f x))) l’
            by (fs [EXISTS_MEM]
                \\ first_x_assum $ irule_at Any
                \\ fs [EL_MEM])
          \\ rw [get_atoms_def, EXISTS_MAP])
      \\ ‘EXISTS (λx. error_Atom (eval_wh (subst f x))) l’
        by (fs [EXISTS_MEM]
            \\ first_x_assum $ irule_at Any
            \\ fs [EL_MEM])
      \\ rw [get_atoms_def, EXISTS_MAP])
  \\ fs []
  \\ ‘¬ EXISTS error_Atom (MAP (eval_wh o (λa. subst f a)) l)’
    by (rw []
        \\ fs [EVERY_MEM]
        \\ rw []
        \\ fs [MEM_EL]
        \\ rename1 ‘¬error_Atom (EL n2 _)’
        \\ Cases_on ‘n2 = n’
        \\ rw []
        >- (first_x_assum $ qspecl_then [‘eval_wh (subst f (Seq p (EL n l)))’] assume_tac
            \\ fs [eval_wh_Seq, subst_def]
            \\ ‘(if eval_wh (subst f p) = wh_Error then wh_Error
                 else if eval_wh (subst f p) = wh_Diverge then wh_Diverge
                 else eval_wh (subst f (EL n l))) = eval_wh (subst f (EL n l))’ by fs []
            \\ fs [EL_MAP]
            \\ pop_assum kall_tac
            \\ pop_assum irule
            \\ first_assum $ irule_at Any
            \\ rw [EL_MAP, EL_LUPDATE, subst_def, eval_wh_Seq])
        \\ first_x_assum irule
        \\ first_assum $ irule_at Any
        \\ fs [EL_MAP, EL_LUPDATE])
  >- (‘MEM wh_Diverge (MAP (eval_wh o (λa. subst f a)) l)’
        by (fs [MEM_EL]
            \\ first_assum $ irule_at Any
            \\ pop_assum kall_tac
            \\ rename1 ‘EL n2 _’
            \\ Cases_on ‘n2 = n’
            >- (fs [EL_MAP, EL_LUPDATE, LUPDATE_MAP, eval_wh_Seq, subst_def]
                \\ metis_tac [])
            \\ gvs [LENGTH_LUPDATE, EL_MAP, EL_LUPDATE, eval_wh_Seq, subst_def])
      \\ rw [get_atoms_def])
  >- (qsuff_tac ‘MAP (eval_wh o (λa. subst f a)) (LUPDATE (Seq p (EL n l)) n l) = MAP (eval_wh o (λa. subst f a)) l’
      >- (rw [get_atoms_def]
          \\ fs [])
      \\ pop_assum kall_tac
      \\ pop_assum kall_tac
      \\ pop_assum kall_tac
      \\ irule LIST_EQ
      \\ rw [LENGTH_MAP, LENGTH_LUPDATE, EL_MAP, EL_LUPDATE, eval_wh_Seq, subst_def])
QED

Theorem Apps_demands:
  ∀el d e. e demands d ⇒ Apps e el demands d
Proof
  Induct
  \\ fs [Apps_def]
  \\ gen_tac
  \\ rw []
  \\ first_x_assum irule
  \\ fs [demands_App]
QED

Theorem demands_exp_eq:
  ∀d c e e'. exp_eq_in_ctxt c e e' ⇒ e demands (d, c) ⇒ e' demands (d, c)
Proof
  PairCases
  \\ metis_tac [needs_exp_eq, needs_Var_is_demands]
QED

Theorem Letrec_unfold:
  ∀lcs i b. i < LENGTH lcs ∧ ALL_DISTINCT (MAP FST lcs)
            ⇒ (Letrec lcs (Var (FST (EL i lcs))) ≅? Letrec lcs (SND (EL i lcs))) b
Proof
  rw [] >> irule eval_IMP_exp_eq >>
  rw [subst_def, eval_thm, subst_funs_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, bind_def,
      FLOOKUP_DRESTRICT, FDIFF_def]
  >- (gvs [MEM_EL] >> rename1 ‘i < LENGTH _’ >>
      first_x_assum $ qspecl_then [‘i’] assume_tac >> gvs [EL_MAP]) >>
  rename1 ‘FLOOKUP _ (FST (EL i lcs))’ >> rename1 ‘DRESTRICT f _’ >>
  qabbrev_tac ‘bind_fun = λp2.
                            Letrec (MAP  (λ(f',e). (f', subst (DRESTRICT f (COMPL (set (MAP FST lcs)))) e)) lcs)
                                   (subst (DRESTRICT f (COMPL (set (MAP FST lcs)))) p2)’ >>
  qspecl_then [‘lcs’, ‘bind_fun’] assume_tac ALL_DISTINCT_FST_MAP >> gvs [] >>
  drule_then assume_tac fmap_FOLDL_FOLDR >>
  pop_assum $ qspecl_then [‘FEMPTY’] assume_tac >>
  drule_then assume_tac $ iffRL FLOOKUP_FOLDR_UPDATE >>
  pop_assum $ qspecl_then [‘bind_fun (SND (EL i lcs))’, ‘FST (EL i lcs)’, ‘FEMPTY’] assume_tac >>
  gvs [FUPDATE_LIST, DISJOINT_EMPTY, FDOM_FEMPTY, MEM_EL, PAIR] >>
  FULL_CASE_TAC >> unabbrev_all_tac >> gvs [] >>
  rename1 ‘FST (EL i lcs) = EL n (MAP FST lcs)’ >>
  qspecl_then [‘MAP FST lcs’, ‘n’, ‘i’] assume_tac ALL_DISTINCT_EL_IMP >>
  gvs [EL_MAP, PULL_EXISTS] >> rename1 ‘EL i _’ >>
  first_x_assum $ qspecl_then [‘i’] assume_tac >> gvs [EL_MAP] >>
  qabbrev_tac ‘pair = EL i lcs’ >> PairCases_on ‘pair’ >> gvs [eval_thm, subst_funs_def, bind_def] >>
  gvs [FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  rw [] >> gvs []
QED

Theorem demands_Letrec2:
  ∀bL ps i e v c. ALL_DISTINCT (MAP FST bL) ∧ i < LENGTH bL
                  ∧ e demands (([], FST (EL i bL)), RecBind bL c)
                  ∧ (SND (EL i bL)) demands ((ps, v), RecBind bL c)
                  ∧ ¬MEM v (MAP FST bL)
                  ⇒ Letrec bL e demands ((ps, v), c)
Proof
  rw [demands_def, exp_eq_in_ctxt_def, Projs_def] >>
  irule exp_eq_in_ctxt_trans >> first_assum $ irule_at Any >>
  irule exp_eq_in_ctxt_trans >> irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt >> irule_at Any Letrec_Prim >>
  irule exp_eq_in_ctxt_trans >> irule_at (Pos last) exp_eq_in_ctxt_Prim >> gvs [] >>
  irule_at (Pos $ el 2) exp_eq_in_ctxt_refl >>
  irule_at (Pos $ el 3) $ iffLR exp_eq_in_ctxt_sym >> first_x_assum $ irule_at Any >> gvs [] >>
  irule exp_eq_in_ctxt_trans >> irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any exp_eq_Prim_cong >> gvs [] >>
  irule_at (Pos $ el 2) exp_eq_refl >>
  irule_at (Pos $ el 3) $ iffLR exp_eq_sym >> irule_at Any Letrec_Prim >> gvs [] >>
  irule exp_eq_in_ctxt_trans >> irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any Seq_assoc >>
  irule exp_eq_in_ctxt_Prim >> gvs [exp_eq_in_ctxt_refl] >>
  irule exp_eq_in_ctxt_trans >> irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any Letrec_unfold >> gvs [] >>
  irule exp_eq_in_ctxt_trans >> first_x_assum $ irule_at Any >>
  irule exp_eq_IMP_exp_eq_in_ctxt >>
  irule exp_eq_trans >> irule_at Any Letrec_Prim >> gvs [] >>
  irule exp_eq_Prim_cong >> gvs [] >>
  irule_at Any Letrec_not_in_freevars >>
  irule_at Any $ iffLR exp_eq_sym >>
  gvs [Letrec_unfold, freevars_Projs, EVERY_MEM]
QED

Theorem last_Lams:
  ∀l x e. Lams (l ++ [x]) e = Lams l (Lam x e)
Proof
  Induct
  \\ fs [Lams_def]
QED

val _ = set_fixity "fdemands" (Infixl 480);

Definition nb_free_def:
  nb_free Nil = 0 ∧
  nb_free (IsFree v c) = SUC (nb_free c) ∧
  nb_free (Bind v e c) = nb_free c ∧
  nb_free (RecBind b c) = nb_free c
End

Definition fdemands_def:
  f fdemands ((ps, i), len, Nil) = (i < len ∧ (∀l. LENGTH l = len
                                             ⇒ Apps f l needs ((ps, EL i l), Nil))) ∧
  f fdemands (p, len, Bind v e c) = (Let v e f) fdemands (p, len, c) ∧
  f fdemands (p, len, RecBind b c) = (Letrec b f) fdemands (p, len, c) ∧
  f fdemands (p, len, IsFree v c) = ∀e. closed e ⇒ (Let v e f) fdemands (p, len, c)
End

Theorem fdemands_alt:
  ∀(c : ctxt) f ps i len. f fdemands ((ps, i), len, c) ⇒ i < len ∧ ∀l. LENGTH l = len ⇒ (Apps f l) needs ((ps, EL i l), c)
Proof
  Induct >> gvs [fdemands_def] >> rpt gen_tac >> strip_tac
  >~[‘IsFree’]
  >- (rw [needs_def, exp_eq_in_ctxt_def]
      >- (pop_assum $ qspecl_then [‘Fail’] assume_tac >>
          gvs [closed_def] >>
          last_x_assum $ dxrule_then assume_tac >> fs []) >>
      first_x_assum $ dxrule_then assume_tac >>
      gvs [needs_def] >>
      irule exp_eq_in_ctxt_trans >> irule_at Any Let_Apps_in_ctxt >>
      irule exp_eq_in_ctxt_trans >> last_x_assum $ dxrule_then assume_tac >>
      fs [] >> first_x_assum $ irule_at Any >> fs [EL_MAP] >>
      irule exp_eq_IMP_exp_eq_in_ctxt >> irule $ iffLR exp_eq_sym >>
      irule exp_eq_trans >> irule_at Any Let_Seq >>
      gvs [Let_Projs, exp_eq_Prim_cong, Let_Apps])
  >~[‘Bind’]
  >- (last_x_assum $ dxrule_then assume_tac >> fs [needs_def, exp_eq_in_ctxt_def] >> rw [] >>
      irule exp_eq_in_ctxt_trans >> irule_at Any Let_Apps_in_ctxt >>
      irule_at Any exp_eq_in_ctxt_trans >> first_x_assum $ irule_at Any >> fs [EL_MAP] >>
      irule exp_eq_IMP_exp_eq_in_ctxt >> irule $ iffLR exp_eq_sym >>
      irule exp_eq_trans >> irule_at Any Let_Seq >>
      gvs [Let_Projs, exp_eq_Prim_cong, Let_Apps]) >>
  last_x_assum $ dxrule_then assume_tac >> fs [needs_def, exp_eq_in_ctxt_def] >> rw [] >>
  irule exp_eq_in_ctxt_trans >> irule_at Any Letrec_Apps_in_ctxt >>
  irule_at Any exp_eq_in_ctxt_trans >> first_x_assum $ irule_at Any >> fs [EL_MAP] >>
  irule exp_eq_IMP_exp_eq_in_ctxt >> irule $ iffLR exp_eq_sym >>
  irule exp_eq_trans >> irule_at Any Letrec_Prim >>
  gvs [Letrec_Projs, exp_eq_Prim_cong, Letrec_Apps]
QED

Theorem fdemands_eq_w_app:
  ∀c p f f' len. eq_when_applied c f f' len ∧ f fdemands (p, len, c) ⇒ f' fdemands (p, len, c)
Proof
  Induct
  >- (PairCases >> rw [fdemands_def, eq_when_applied_def] >>
      irule needs_exp_eq >> pop_assum $ irule_at Any >>
      gvs [exp_eq_IMP_exp_eq_in_ctxt])
  >~[‘IsFree’]
  >- (rw [fdemands_def] >> last_x_assum irule >>
      first_x_assum $ irule_at Any >> irule_at Any eq_when_applied_App >>
      irule_at Any exp_eq_in_ctxt_refl >> irule_at Any eq_when_applied_Lam >>
      fs []) >>
  rw [fdemands_def, eq_when_applied_def] >> last_x_assum irule >>
  rpt $ pop_assum $ irule_at Any
QED

Theorem fdemands_exp_eq:
  ∀c p f f' len. exp_eq_in_ctxt c f f' ∧ f fdemands (p, len, c) ⇒ f' fdemands (p, len, c)
Proof
  rw [eq_when_applied_0] >>
  irule fdemands_eq_w_app >>
  first_assum $ irule_at Any >>
  irule eq_when_applied_bigger >>
  first_x_assum $ irule_at Any >> fs []
QED

Theorem fdemands_Seq:
  ∀c p len e1 e2. e2 fdemands (p, len, c) ⇒ (Seq e1 e2) fdemands (p, len, c)
Proof
  Induct
  >- (PairCases >> rw [fdemands_def] >>
      irule needs_exp_eq >> irule_at Any needs_Seq2 >> pop_assum $ irule_at Any >>
      irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      gvs [Once exp_eq_sym] >> irule_at Any Apps_Seq) >>
  rw [fdemands_def] >>
  irule fdemands_exp_eq >> last_x_assum $ irule_at Any >>
  first_x_assum $ irule_at Any >>
  once_rewrite_tac [exp_eq_in_ctxt_sym]
  >~[‘Letrec’]
  >- (irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any exp_eq_trans >> irule_at Any Letrec_Prim >>
      gvs [] >> rpt $ irule_at Any exp_eq_refl) >>
  irule_at Any exp_eq_IMP_exp_eq_in_ctxt >> irule_at Any Let_Seq >> fs []
QED

Theorem fdemands_IsFree:
  ∀d c v e len. v ∉ freevars e ∧ e fdemands (d, len, c) ⇒ e fdemands (d, len, IsFree v c)
Proof
  rw [fdemands_def] >> irule fdemands_exp_eq >> first_x_assum $ irule_at Any >>
  irule exp_eq_IMP_exp_eq_in_ctxt >>
  irule eval_IMP_exp_eq >> dxrule $ GSYM subst_fdomsub >>
  rw [subst_def, eval_thm, IMP_closed_subst, FRANGE_FLOOKUP, bind1_def]
QED

Theorem fdemands_Bind:
  ∀d c v e e2 len. v ∉ freevars e ∧ e fdemands (d, len, c) ⇒ e fdemands (d, len, Bind v e2 c)
Proof
  rw [fdemands_def] >> irule fdemands_exp_eq >> first_x_assum $ irule_at Any >>
  irule exp_eq_IMP_exp_eq_in_ctxt >>
  irule eval_IMP_exp_eq >> dxrule $ GSYM subst_fdomsub >>
  rw [subst_def, eval_thm, IMP_closed_subst, FRANGE_FLOOKUP, bind1_def]
QED

Theorem fdemands_RecBind:
  ∀c p l e b. e fdemands (p, l, c)
              ∧ EVERY (λv. v ∉ freevars e) (MAP FST b)
              ⇒ e fdemands (p, l, RecBind b c)
Proof
  rw [fdemands_def] >> irule fdemands_exp_eq >>
  last_x_assum $ irule_at Any >>
  irule exp_eq_IMP_exp_eq_in_ctxt >> irule $ iffLR exp_eq_sym >>
  gvs [Letrec_not_in_freevars]
QED

Theorem fdemands_App:
  ∀c e e2 ps i len. e fdemands ((ps, SUC i), SUC len, c) ⇒ App e e2 fdemands  ((ps, i), len, c)
Proof
  Induct
  >- (rw [fdemands_def, GSYM Apps_def] >>
      rename1 ‘e2::l’ >> pop_assum $ qspecl_then [‘e2::l’] assume_tac >>
      gvs []) >>
  rw [fdemands_def] >> irule fdemands_exp_eq >>
  rpt $ last_x_assum $ irule_at Any >>
  irule_at Any $ iffLR exp_eq_in_ctxt_sym
  >~[‘Letrec’] >- (irule_at Any exp_eq_IMP_exp_eq_in_ctxt >> irule_at Any Letrec_App) >>
  irule_at Any Let_App_in_ctxt
QED

Theorem fdemands_Apps:
  ∀eL c e ps i len. e fdemands ((ps, i + LENGTH eL), len + LENGTH eL, c) ⇒ Apps e eL fdemands  ((ps, i), len, c)
Proof
  Induct >> gvs [Apps_def] >> rw [] >>
  last_x_assum irule >> irule fdemands_App >>
  gvs [SUC_ADD]
QED

Theorem fdemands_App2:
  ∀d e e2 eL len c. e fdemands (([], 0), SUC len, c) ∧ e2 demands (d, c) ∧ LENGTH eL = len
            ⇒ Apps (App e e2) eL demands (d, c)
Proof
  PairCases >> rw [] >>
  dxrule_then assume_tac fdemands_alt >>
  gvs [fdemands_def, GSYM Apps_def, GSYM needs_Var_is_demands] >>
  rename1 ‘e2::eL’ >> last_x_assum $ qspecl_then [‘e2::eL’] assume_tac >>
  irule needs_trans >>
  pop_assum $ irule_at Any >>
  gvs []
QED

Theorem fdemands_subset:
  ∀fdc fdc'.
    (∀n l i c2. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l ⇒ Var n fdemands (([], i), LENGTH l, concat_ctxt c c2))
    ∧ fdc' ⊆ fdc
    ⇒ (∀n l i. (n, l) ∈ fdc' ∧ i < LENGTH l ∧ EL i l ⇒ Var n fdemands (([], i), LENGTH l, concat_ctxt c c2))
Proof
  gvs [SUBSET_DEF]
QED

Theorem fdemands_set_Bind:
  ∀fdc v e.
    (∀n l i c2. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l ⇒ Var n fdemands (([], i), LENGTH l, concat_ctxt c c2))
    ∧ (∀n l. (n, l) ∈ fdc ⇒ n ≠ v)
    ⇒ (∀n l i c2. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l
               ⇒ Var n fdemands (([], i), LENGTH l, concat_ctxt (Bind v e c) c2))
Proof
  rw [concat_ctxt_def]
  \\ irule fdemands_Bind
  \\ gvs []
  \\ strip_tac \\ gvs []
QED

Theorem fdemands_set_IsFree:
  ∀fdc v.
    (∀n l i c2. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l ⇒ Var n fdemands (([], i), LENGTH l, concat_ctxt c c2))
    ∧ (∀l. (v, l) ∉ fdc)
    ⇒ (∀n l i c2. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l
               ⇒ Var n fdemands (([], i), LENGTH l, concat_ctxt (IsFree v c) c2))
Proof
  rw [concat_ctxt_def]
  \\ irule fdemands_IsFree
  \\ gvs []
  \\ strip_tac \\ gvs []
QED

Theorem fdemands_set_FOLDL_IsFree:
  ∀vL fdc c.
    (∀n l i c2. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l ⇒ Var n fdemands (([], i), LENGTH l, concat_ctxt c c2))
    ∧ EVERY (λv. ∀argDs. (v, argDs) ∉ fdc) vL
    ⇒ (∀n l i c2. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l
               ⇒ Var n fdemands (([], i), LENGTH l, concat_ctxt (FOLDL (λc n. IsFree n c) c vL) c2 ))
Proof
  Induct \\ rw [concat_ctxt_def]
  \\ last_x_assum irule
  \\ gvs []
  \\ last_assum $ irule_at Any
  \\ dxrule_then assume_tac fdemands_set_IsFree
  \\ pop_assum $ dxrule_then assume_tac
  \\ fs []
QED

Theorem fdemands_set_RecBind:
  ∀fdc c b.
    (∀n l i c2. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l ⇒ Var n fdemands (([], i), LENGTH l, concat_ctxt c c2))
    ∧ EVERY (λv. ∀argDs. (v, argDs) ∉ fdc) (MAP FST b)
    ⇒ (∀n l i c2. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l
               ⇒ Var n fdemands (([], i), LENGTH l, concat_ctxt (RecBind b c) c2))
Proof
  rw [concat_ctxt_def] >> irule fdemands_RecBind >>
  gvs [EVERY_EL, EL_MAP] >> rw [] >> strip_tac >>
  first_x_assum $ dxrule_then assume_tac >> gvs []
QED

val _ = set_fixity "demands_when_applied" (Infixl 480);

Definition demands_when_applied_def:
  f demands_when_applied ((ps, v), len, c) = eq_when_applied c f (Seq (Projs ps (Var v)) f) len
End

val _ = set_fixity "needs_when_applied" (Infixl 480);

Definition needs_when_applied_def:
  f needs_when_applied ((ps, e), len, c) = eq_when_applied c f (Seq (Projs ps e) f) len
End

Theorem needs_when_applied_0:
  ∀p f c. f needs_when_applied (p, 0, c) = f needs (p, c)
Proof
  PairCases >> gvs [needs_when_applied_def, needs_def, eq_when_applied_0]
QED

Theorem demands_when_applied_0:
  ∀p f c. f demands_when_applied (p, 0, c) = f demands (p, c)
Proof
  PairCases >> gvs [demands_when_applied_def, demands_def, eq_when_applied_0]
QED

Theorem demands_w_app_is_needs_w_app:
  ∀f c ps v e len. f demands_when_applied ((ps, v), len, c) = f needs_when_applied ((ps, Var v), len, c)
Proof
  rw [demands_when_applied_def, needs_when_applied_def]
QED

Theorem eq_when_applied_trans_exp_eq:
  ∀c e1 e2 e3 len.
    exp_eq_in_ctxt c e1 e2 ∧ eq_when_applied c e2 e3 len
    ⇒ eq_when_applied c e1 e3 len
Proof
  rw [] >> irule eq_when_applied_trans >>
  first_x_assum $ irule_at Any >>
  gvs [exp_eq_in_ctxt_IMP_eq_when_applied]
QED

Theorem fdemands_0_App_needs:
  ∀c f e d len. e needs (d, c) ∧ f fdemands (([], 0), SUC len, c)
                ⇒ App f e needs_when_applied (d, len, c)
Proof
  Induct >>
  gvs[FORALL_PROD, needs_when_applied_def, fdemands_def,
      eq_when_applied_def, exp_eq_in_ctxt_def, Projs_def] >>
  rw [GSYM Apps_def]
  >- (irule exp_eq_trans >>
      irule_at (Pos last) $ iffLR exp_eq_sym >> irule_at Any Apps_Seq >>
      rename1 ‘Apps f(e::l)’ >> pop_assum $ qspecl_then [‘e::l’] assume_tac >> fs [] >>
      dxrule_then (dxrule_then assume_tac) needs_trans >>
      gvs [needs_def, exp_eq_in_ctxt_def, Apps_def])
  >~[‘Letrec’]
  >- (irule eq_when_applied_trans_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any Letrec_App >>
      irule_at Any eq_when_applied_trans >> last_x_assum $ irule_at Any >>
      gvs [needs_def, exp_eq_in_ctxt_def] >>
      irule_at Any exp_eq_in_ctxt_trans >> first_x_assum $ irule_at Any >>
      irule_at Any exp_eq_IMP_exp_eq_in_ctxt >> irule_at Any exp_eq_trans >>
      irule_at Any Letrec_Prim >> irule_at Any exp_eq_Prim_cong >>
      gvs [exp_eq_refl] >> irule_at Any Letrec_Projs >>
      irule exp_eq_in_ctxt_IMP_eq_when_applied >> irule exp_eq_IMP_exp_eq_in_ctxt >>
      irule $ iffLR exp_eq_sym >> irule exp_eq_trans >>
      irule_at Any Letrec_Prim >> irule_at Any exp_eq_Prim_cong >>
      gvs [Letrec_App, Letrec_Projs]) >>
  irule eq_when_applied_trans_exp_eq >> irule_at Any Let_App_in_ctxt >>
  irule eq_when_applied_trans >> last_x_assum $ irule_at Any
  >- (gvs [needs_def] >>
      irule_at Any exp_eq_in_ctxt_trans >> irule_at Any exp_eq_in_ctxt_App >>
      irule_at Any exp_eq_in_ctxt_Lam >> last_x_assum $ irule_at Any >>
      irule_at Any exp_eq_in_ctxt_refl >>
      irule_at Any exp_eq_IMP_exp_eq_in_ctxt >> irule_at Any exp_eq_trans >>
      irule_at Any Let_Seq >> irule_at Any exp_eq_Prim_cong >>
      gvs [exp_eq_refl] >> irule_at Any Let_Projs >>
      irule exp_eq_in_ctxt_IMP_eq_when_applied >> irule exp_eq_IMP_exp_eq_in_ctxt >>
      irule $ iffLR exp_eq_sym >> irule exp_eq_trans >>
      irule_at Any Let_Seq >> irule_at Any exp_eq_Prim_cong >>
      gvs [Let_App, Let_Projs])
  >- (gvs [needs_def, exp_eq_in_ctxt_def] >>
      irule_at Any exp_eq_in_ctxt_trans >> last_x_assum $ irule_at Any >> fs [] >>
      irule_at Any exp_eq_IMP_exp_eq_in_ctxt >> irule_at Any exp_eq_trans >>
      irule_at Any Let_Seq >> irule_at Any exp_eq_Prim_cong >>
      gvs [exp_eq_refl] >> irule_at Any Let_Projs >>
      irule exp_eq_in_ctxt_IMP_eq_when_applied >> irule exp_eq_IMP_exp_eq_in_ctxt >>
      irule $ iffLR exp_eq_sym >> irule exp_eq_trans >>
      irule_at Any Let_Seq >> irule_at Any exp_eq_Prim_cong >>
      gvs [Let_App, Let_Projs])
QED

Theorem needs_when_applied_App:
  ∀c p f len e. f needs_when_applied (p, SUC len, c)
                ⇒ (App f e) needs_when_applied (p, len, c)
Proof
  gvs [FORALL_PROD, needs_when_applied_def] >> rw [] >>
  irule eq_when_applied_trans >> irule_at Any eq_when_applied_App >>
  irule_at Any exp_eq_in_ctxt_refl >> pop_assum $ irule_at Any >>
  gvs [exp_eq_IMP_eq_when_applied, App_Seq]
QED

Theorem demands_when_applied_App:
  ∀c p f len e. f demands_when_applied (p, SUC len, c)
                ⇒ (App f e) demands_when_applied (p, len, c)
Proof
  gvs [FORALL_PROD, needs_when_applied_App, demands_w_app_is_needs_w_app]
QED

Theorem demands_when_applied_Apps:
  ∀eL c p f len. f demands_when_applied (p, len + LENGTH eL, c)
                ⇒ (Apps f eL) demands_when_applied (p, len, c)
Proof
  Induct >> rw [Apps_def] >>
  last_x_assum irule >> irule demands_when_applied_App >>
  gvs [SUC_ADD]
QED

Theorem demands_when_applied_Apps2:
  ∀eL i c p f len. f fdemands (([], i), len + LENGTH eL, c) ∧ EL i eL demands (p, c) ∧ i < LENGTH eL
                ⇒ (Apps f eL) demands_when_applied (p, len, c)
Proof
  Induct >> gvs [FORALL_PROD] >>
  gen_tac >> Cases
  >~[‘EL 0’]
  >- (rw [Apps_def] >>
      irule demands_when_applied_Apps >>
      irule $ iffRL demands_w_app_is_needs_w_app >>
      irule fdemands_0_App_needs >>
      gvs [SUC_ADD, needs_Var_is_demands]) >>
  rw [Apps_def] >>
  last_x_assum irule >>
  first_x_assum $ irule_at Any >>
  gvs [fdemands_App, SUC_ADD]
QED

Theorem demands_when_applied_Lam_lemma:
  ∀c p f len e v.
    eq_when_applied c (Lam v f) (Lam v (Seq p f)) (SUC len) ∧ v ∉ freevars p
    ⇒ eq_when_applied c (Lam v f) (Seq p (Lam v f)) (SUC len)
Proof
  Induct >> gvs [eq_when_applied_def]
  >- (rpt gen_tac >> strip_tac >> Cases >> rw [] >>
      irule exp_eq_trans >> last_x_assum $ irule_at Any >>
      gvs [Apps_def] >>
      irule exp_eq_Apps_cong >> gvs [exp_eq_l_refl] >>
      irule exp_eq_trans >> irule_at Any Let_Seq >>
      irule $ iffLR exp_eq_sym >> irule exp_eq_trans >> irule_at Any App_Seq >>
      irule exp_eq_Prim_cong >> fs [exp_eq_refl] >>
      irule eval_IMP_exp_eq >>
      rw [subst_def, bind1_def, FRANGE_FLOOKUP, IMP_closed_subst, eval_thm, GSYM subst_fdomsub]) >>
  rw [] >> irule eq_when_applied_trans_exp_eq
  >~[‘Letrec l (Lam v (Seq p f))’]
  >- (‘∃s. s ∉ {v} ∪ freevars p ∪ freevars f ∪ set (MAP FST l) ∪ BIGUNION (set (MAP freevars (MAP SND l)))’
        by (‘INFINITE 𝕌(:mlstring)’ by simp [INFINITE_mlstring]
             \\ dxrule_then assume_tac $ iffLR NOT_IN_FINITE
             \\ pop_assum $ irule_at Any
             \\ rw [FINITE_UNION, FINITE_BIGUNION, MEM_EL]
             \\ gvs [EL_MAP]) >>
      irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any exp_eq_trans >> irule_at (Pos hd) exp_eq_Letrec_cong >>
      irule_at Any exp_eq_l_refl >>
      irule_at (Pos hd) exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >>
      irule_at Any Letrec_Lam_weak >>
      fs [] >> first_assum $ irule_at Any >> gvs [] >>
      conj_asm1_tac
      >- (rw [EVERY_MEM] >>
          rename1 ‘MEM e (MAP SND l)’ >> first_x_assum $ qspecl_then [‘freevars e’] assume_tac >>
          gvs [MEM_MAP]) >>
      irule_at (Pos hd) eq_when_applied_trans >> last_x_assum $ irule_at Any >>
      irule_at (Pos hd) eq_when_applied_trans_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at (Pos hd) $ iffLR exp_eq_sym >> irule_at Any Letrec_Lam_weak >> fs [] >>
      irule_at (Pos hd) eq_when_applied_trans_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any exp_eq_Letrec_cong >> irule_at Any exp_eq_l_refl >>
      irule_at Any $ iffLR exp_eq_sym >> irule_at Any exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >> fs [] >>
      irule_at (Pos hd) eq_when_applied_trans >> last_x_assum $ irule_at Any >>
      rpt $ irule_at Any exp_eq_IMP_eq_when_applied >> irule_at (Pos hd) $ iffLR exp_eq_sym >>
      irule_at (Pos hd) exp_eq_trans >> irule_at Any Letrec_Prim >>
      irule_at Any exp_eq_Prim_cong >> fs [] >>
      irule_at (Pos hd) exp_eq_refl >> fs [] >>
      irule_at (Pos hd) exp_eq_trans >> irule_at (Pos $ el 2) Letrec_Lam_weak >> fs [] >>
      irule_at Any exp_eq_Letrec_cong >> fs [exp_eq_l_refl] >>
      irule_at (Pos hd) exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >>
      gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      irule exp_eq_trans >> irule_at (Pos hd) exp_eq_Letrec_cong >> irule_at Any exp_eq_l_refl >> fs [] >>
      irule_at (Pos hd) exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >>
      fs [] >> first_assum $ irule_at Any >> fs [] >>
      irule exp_eq_trans >> irule_at Any Letrec_Lam_weak >> fs [perm_exp_def] >>
      irule exp_eq_Lam_cong >>
      irule exp_eq_trans >> irule_at Any Letrec_Prim >>
      irule exp_eq_Prim_cong >> fs [exp_eq_refl] >>
      irule exp_eq_Letrec_cong >> fs [exp_eq_l_refl, Once exp_eq_sym] >>
      irule exp_alpha_exp_eq >> gvs [exp_alpha_perm_irrel]) >>
  rename1 ‘Let w e (Seq p (Lam v f))’ >>
  ‘∃s. s ∉ {v} ∪ {w} ∪ freevars p ∪ freevars f ∪ freevars e’
    by (‘INFINITE 𝕌(:mlstring)’ by simp [INFINITE_mlstring]
        \\ gvs [NOT_IN_FINITE]) >>
  irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any exp_eq_trans >> irule_at (Pos hd) exp_eq_App_cong >>
  irule_at (Pos hd) exp_eq_Lam_cong >> irule_at (Pos $ el 2) exp_eq_refl >>
  irule_at (Pos hd) exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >>
  irule_at Any Let_Lam_weak >>
  fs [] >> first_assum $ irule_at Any >> gvs [] >>
  irule_at (Pos hd) eq_when_applied_trans >> last_x_assum $ irule_at Any >>
  irule_at (Pos hd) eq_when_applied_trans_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at (Pos hd) $ iffLR exp_eq_sym >> irule_at Any Let_Lam_weak >> fs [] >>
  irule_at (Pos hd) eq_when_applied_trans_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any exp_eq_App_cong >> irule_at (Pos hd) exp_eq_Lam_cong >>
  irule_at (Pos $ el 2) exp_eq_refl >>
  irule_at Any $ iffLR exp_eq_sym >> irule_at Any exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >> fs [] >>
  irule_at (Pos hd) eq_when_applied_trans >> last_x_assum $ irule_at Any >>
  rpt $ irule_at Any exp_eq_IMP_eq_when_applied >> irule_at (Pos hd) $ iffLR exp_eq_sym >>
  irule_at (Pos hd) exp_eq_trans >> irule_at Any Let_Seq >>
  irule_at Any exp_eq_Prim_cong >> fs [] >>
  irule_at (Pos hd) exp_eq_refl >> fs [] >>
  irule_at (Pos hd) exp_eq_trans >> irule_at (Pos $ el 2) Let_Lam_weak >> fs [] >>
  irule_at Any exp_eq_App_cong >> irule_at Any exp_eq_Lam_cong >> fs [exp_eq_refl] >>
  irule_at (Pos hd) exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >>
  gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  irule exp_eq_trans >> irule_at Any exp_eq_App_cong >>
  irule_at (Pos hd) exp_eq_Lam_cong >> irule_at (Pos $ el 2) exp_eq_refl >>
  irule_at (Pos hd) exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >>
  fs [] >> first_assum $ irule_at Any >> fs [] >>
  irule exp_eq_trans >> irule_at Any Let_Lam_weak >> fs [perm_exp_def] >>
  irule exp_eq_Lam_cong >>
  irule exp_eq_trans >> irule_at Any Let_Seq >>
  irule exp_eq_Prim_cong >> fs [exp_eq_refl] >>
  irule exp_eq_App_cong >> irule_at Any exp_eq_Lam_cong >> fs [exp_eq_refl, Once exp_eq_sym] >>
  irule exp_alpha_exp_eq >> gvs [exp_alpha_perm_irrel]
QED

Theorem demands_when_applied_Lam:
  ∀c p f len e v. f demands_when_applied (p, len, IsFree v c) ∧ v ≠ SND p
                ⇒ (Lam v f) demands_when_applied (p, SUC len, c)
Proof
  gvs [FORALL_PROD, demands_when_applied_def] >> rw [] >>
  irule demands_when_applied_Lam_lemma >>
  gvs [eq_when_applied_Lam, freevars_Projs]
QED

Theorem demands_when_applied_Lams:
  ∀vL c p f len e. f demands_when_applied (p, len, FOLDL (λc n. (IsFree n c)) c vL) ∧ ¬ MEM (SND p) vL
                ⇒ (Lams vL f) demands_when_applied (p, len + LENGTH vL, c)
Proof
  Induct >> gvs [Lams_def] >>
  rw [GSYM SUC_ADD] >>
  irule demands_when_applied_Lam >>
  gvs []
QED

Theorem needs_when_applied_Seq:
  ∀c p f len e. f needs_when_applied (p, len, c)
                ⇒ (Seq e f) needs_when_applied (p, len, c)
Proof
  Induct >> gvs [FORALL_PROD, needs_when_applied_def, eq_when_applied_def] >> rw []
  >- (irule exp_eq_trans >> irule_at Any Apps_Seq >>
      irule exp_eq_trans >> irule_at Any exp_eq_Apps_cong >>
      irule_at Any exp_eq_l_refl >>
      irule_at (Pos hd) exp_eq_trans >> irule_at (Pos $ el 2) Seq_assoc >>
      irule_at (Pos hd) exp_eq_trans >> irule_at (Pos $ el 2) Seq_comm >>
      irule_at (Pos hd) $ iffLR exp_eq_sym >> irule_at Any Seq_assoc >>
      irule exp_eq_trans >> irule_at (Pos last) $ iffLR exp_eq_sym >>
      irule_at Any Apps_Seq >> irule exp_eq_Prim_cong >>
      gvs [exp_eq_refl])
  >~[‘Letrec’]
  >- (irule eq_when_applied_trans_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any Letrec_Prim >> fs [] >>
      irule eq_when_applied_trans >> last_x_assum $ irule_at Any >>
      irule_at (Pos hd) eq_when_applied_trans >> first_x_assum $ irule_at Any >>
      rpt $ irule_at Any exp_eq_in_ctxt_IMP_eq_when_applied >>
      rpt $ irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at (Pos hd) exp_eq_trans >> irule_at Any Letrec_Prim >>
      irule_at Any exp_eq_Prim_cong >> gvs [exp_eq_refl] >>
      irule_at Any Letrec_Projs >> irule $ iffLR exp_eq_sym >>
      irule_at Any exp_eq_trans >> irule_at Any Letrec_Prim >> irule exp_eq_Prim_cong >>
      gvs [Letrec_Projs] >>
      irule exp_eq_trans >> irule_at Any Letrec_Prim >> gvs [exp_eq_refl]) >>
  irule eq_when_applied_trans_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any Let_Seq >>
  irule eq_when_applied_trans >> last_x_assum $ irule_at Any >>
  irule_at (Pos hd) eq_when_applied_trans >> first_x_assum $ irule_at Any >>
  rpt $ irule_at Any exp_eq_in_ctxt_IMP_eq_when_applied >>
  rpt $ irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at (Pos hd) exp_eq_trans >> irule_at Any Let_Seq >>
  irule_at Any exp_eq_Prim_cong >> gvs [exp_eq_refl] >>
  irule_at Any Let_Projs >> irule $ iffLR exp_eq_sym >>
  irule_at Any exp_eq_trans >> irule_at Any Let_Seq >> irule exp_eq_Prim_cong >>
  gvs [Let_Projs, Let_Seq]
QED

Theorem demands_when_applied_Seq:
  ∀p c  f len e. f demands_when_applied (p, len, c)
                ⇒ (Seq e f) demands_when_applied (p, len, c)
Proof
  gvs [FORALL_PROD, demands_w_app_is_needs_w_app, needs_when_applied_Seq]
QED

Theorem fdemands_0_App_demands:
  ∀c f e d len. e demands (d, c) ∧ f fdemands (([], 0), SUC len, c)
                ⇒ App f e demands_when_applied (d, len, c)
Proof
  gvs [FORALL_PROD, fdemands_0_App_needs, demands_w_app_is_needs_w_app, needs_Var_is_demands]
QED

Theorem demands_when_applied_IsFree_Bind:
  ∀c v e e' d len. e demands_when_applied (d, len, IsFree v c) ∧ SND d ≠ v
                   ⇒ e demands_when_applied (d, len, Bind v e' c)
Proof
  fs [FORALL_PROD] >> rw [] >> simp [demands_when_applied_def, eq_when_applied_def] >>
  dxrule_then assume_tac demands_when_applied_Lam >> gvs [] >>
  dxrule_then assume_tac demands_when_applied_App >>
  gvs [demands_when_applied_def] >>
  irule eq_when_applied_trans >> first_x_assum $ irule_at Any >>
  irule exp_eq_IMP_eq_when_applied >> irule $ iffLR exp_eq_sym >>
  irule exp_eq_trans >> irule_at Any Let_Seq >>
  irule exp_eq_Prim_cong >> fs [exp_eq_refl] >>
  irule exp_eq_trans >> irule_at Any Let_Projs >>
  irule exp_eq_Projs_cong >> irule Let_Var2 >> fs []
QED

Theorem demands_when_applied_Letrec:
  ∀b e d len c. e demands_when_applied (d, len, RecBind b c) ∧ (¬MEM (SND d) (MAP FST b))
                ⇒ Letrec b e demands_when_applied (d, len, c)
Proof
  gvs [FORALL_PROD, demands_when_applied_def, eq_when_applied_def] >> rw [] >>
  irule eq_when_applied_trans >> last_x_assum $ irule_at Any >>
  irule exp_eq_IMP_eq_when_applied >>
  irule exp_eq_trans >> irule_at Any Letrec_Prim >>
  irule exp_eq_Prim_cong >> fs [exp_eq_refl] >>
  irule Letrec_not_in_freevars >>
  gvs [freevars_Projs, EVERY_MEM]
QED

Theorem Lam_fdemands_lemma:
  ∀c v e ps len. Lam v (Seq (Projs ps (Var v)) e) fdemands ((ps, 0), SUC len, c)
Proof
  Induct >> gvs [fdemands_def]
  >- (rw [] >> rename1 ‘HD l’ >> Cases_on ‘l’ >> gvs [Apps_def, needs_def] >>
      irule exp_eq_IMP_exp_eq_in_ctxt >>
      irule exp_eq_trans >> irule_at Any exp_eq_Apps_cong >>
      irule_at Any exp_eq_l_refl >> irule_at Any Let_Seq >>
      irule exp_eq_trans >> irule_at Any exp_eq_Prim_cong >> gvs [] >>
      irule_at Any exp_eq_Apps_cong >> gvs [] >>
      irule_at Any exp_eq_l_refl >> irule_at (Pos hd) $ iffLR exp_eq_sym >>
      irule_at Any Let_Seq >> irule_at Any exp_eq_refl >>
      irule exp_eq_trans >> irule_at Any Apps_Seq >>
      irule exp_eq_trans >> irule_at (Pos hd) exp_eq_Prim_cong >> gvs [] >>
      irule_at Any Let_Projs >> irule_at (Pos $ el 3) exp_eq_refl >> gvs [] >>
      irule exp_eq_trans >> irule_at (Pos hd) exp_eq_Prim_cong >> gvs [] >>
      irule_at (Pos $ el 2) $ iffLR exp_eq_sym >> irule_at (Pos hd) Seq_id >> gvs [] >>
      irule_at Any exp_eq_refl >> irule exp_eq_trans >>
      irule_at Any Seq_assoc >> irule exp_eq_Prim_cong >> gvs [exp_eq_Projs_cong, Let_Var, Once exp_eq_sym] >>
      irule exp_eq_trans >> irule_at Any Apps_Seq >>
      irule exp_eq_Prim_cong >> gvs [exp_eq_refl, Let_Projs]) >>
  rw [] >>
  irule fdemands_exp_eq >>
  irule_at Any exp_eq_IMP_exp_eq_in_ctxt
  >~[‘Letrec lcs (Lam v (Seq _ e))’]
  >- (irule_at Any $ iffLR exp_eq_sym >> irule_at Any exp_eq_trans >>
      irule_at (Pos hd) exp_eq_Letrec_cong >> irule_at Any exp_eq_l_refl >>
      irule_at Any exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >>
      irule_at Any Letrec_Lam_weak >> gvs [perm_exp_def, perm_exp_Projs, perm1_def] >>
      ‘∃s. s ∉ BIGUNION (set (MAP freevars (MAP SND lcs))) ∪ set (MAP FST lcs)
             ∪ {v} ∪ freevars e’
        by (‘INFINITE 𝕌(:mlstring)’ by simp [INFINITE_mlstring] >>
            dxrule_then irule $ iffLR NOT_IN_FINITE >>
            gvs [NOT_IN_FINITE, FINITE_BIGUNION, MEM_MAP] >> rw [] >> fs [freevars_FINITE]) >>
      fs [] >> first_assum $ irule_at Any >>
      gvs [freevars_Projs] >> conj_tac
      >- (rw [EVERY_MEM] >> rename1 ‘MEM e2 (MAP SND _)’ >>
          last_x_assum $ qspecl_then [‘freevars e2’] assume_tac >>
          gvs [MEM_MAP]) >>
      irule fdemands_exp_eq >>
      last_x_assum $ irule_at Any >>
      irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any exp_eq_Lam_cong >>
      irule_at Any $ iffLR exp_eq_sym >> irule_at Any exp_eq_trans >>
      irule_at Any Letrec_Prim >> irule_at Any exp_eq_Prim_cong >>
      fs [] >> irule_at Any exp_eq_refl >>
      irule exp_eq_trans >> irule_at Any Letrec_Projs >>
      irule_at Any exp_eq_Projs_cong >>
      irule Letrec_not_in_freevars >> gvs [EVERY_MEM]) >>
  rename1 ‘Let w e2 (Lam v (Seq _ e1))’ >>
  irule_at Any $ iffLR exp_eq_sym >> irule_at Any exp_eq_trans >>
  irule_at (Pos hd) exp_eq_App_cong >> irule_at (Pos hd) exp_eq_Lam_cong >>
  irule_at (Pos $ el 2) exp_eq_refl >>
  irule_at Any exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >>
  irule_at Any Let_Lam_weak >> gvs [perm_exp_def, perm_exp_Projs, perm1_def] >>
  ‘∃s. s ∉ {w} ∪ freevars e1 ∪ {v} ∪ freevars e2’
    by (‘INFINITE 𝕌(:mlstring)’ by simp [INFINITE_mlstring] >>
        gvs [NOT_IN_FINITE]) >>
  fs [] >> first_assum $ irule_at Any >>
  gvs [freevars_Projs] >>
  irule fdemands_exp_eq >>
  last_x_assum $ irule_at Any >>
  irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any exp_eq_Lam_cong >>
  irule_at Any $ iffLR exp_eq_sym >> irule_at Any exp_eq_trans >>
  irule_at Any Let_Seq >> irule_at Any exp_eq_Prim_cong >>
  fs [] >> irule_at Any exp_eq_refl >>
  irule exp_eq_trans >> irule_at Any Let_Projs >>
  irule_at Any exp_eq_Projs_cong >> gvs [Let_Var2]
QED

Theorem Lam_fdemands:
  ∀c v e ps len. e demands_when_applied ((ps, v), len, IsFree v c)
                 ⇒ Lam v e fdemands ((ps, 0), SUC len, c)
Proof
  rw [demands_when_applied_def] >>
  irule fdemands_eq_w_app >>
  irule_at Any eq_when_applied_Lam >>
  irule_at Any $ iffLR eq_when_applied_sym >>
  first_x_assum $ irule_at Any >>
  gvs [Lam_fdemands_lemma]
QED

Theorem fdemands_Lam:
  ∀c v e len ps n. e fdemands ((ps, n), len, IsFree v c) ⇒ Lam v e fdemands ((ps, SUC n), SUC len, c)
Proof
  Induct >> rw [fdemands_def]
  >- (pop_assum $ qspecl_then [‘Fail’] assume_tac >> gvs [])
  >- (gvs [needs_def, exp_eq_in_ctxt_def] >> irule exp_eq_trans >>
      rename1 ‘LENGTH l = SUC _’ >> Cases_on ‘l’ >> gvs [Apps_def] >>
      irule_at Any exp_eq_Apps_cong >> irule_at Any exp_eq_l_refl >>
      irule_at Any exp_eq_App_cong >> irule_at (Pos hd) exp_alpha_exp_eq >>
      irule_at Any exp_alpha_Alpha >> rename1 ‘EL n t’ >>
      ‘∃s. s ∉ freevars e ∪ {v} ∪ BIGUNION (set (MAP freevars t))’
        by (‘INFINITE 𝕌(:mlstring)’ by simp [INFINITE_mlstring] >>
             dxrule_then assume_tac $ iffLR NOT_IN_FINITE >>
             pop_assum $ irule_at Any >>
             rw [FINITE_UNION, FINITE_BIGUNION, MEM_EL] >>
             gvs [EL_MAP]) >>
      fs [] >> first_assum $ irule_at Any >> fs [] >>
      irule_at Any exp_eq_refl >>
      irule exp_eq_trans >> irule_at (Pos hd) $ iffLR exp_eq_sym >>
      irule_at (Pos hd) exp_eq_trans >> irule_at (Pos hd) Let_Apps >>
      irule_at Any exp_eq_Apps_cong >> irule_at Any exp_eq_refl >>
      irule_at Any $ iffRL LIST_REL_EL_EQN >> irule_at Any LENGTH_MAP >> gvs [EL_MAP] >>
      conj_asm1_tac
      >- (rw [EL_MAP] >> irule Let_not_in_freevars >>
          rename1 ‘freevars (EL n2 t)’ >> last_x_assum $ qspecl_then [‘freevars (EL n2 t)’] assume_tac >>
          gvs [MEM_MAP] >>
          pop_assum $ qspecl_then [‘EL n2 t’] assume_tac >> gvs [EL_MEM]) >>
      irule exp_eq_trans >> irule_at (Pos last) $ iffLR exp_eq_sym >>
      irule_at (Pos hd) exp_eq_trans >> irule_at (Pos hd) exp_eq_Prim_cong >> gvs [] >>
      irule_at (Pos $ el 2) $ iffLR exp_eq_sym >>
      irule_at (Pos hd) exp_eq_trans >> irule_at (Pos hd) Let_Projs >>
      irule_at (Pos hd) exp_eq_Projs_cong >> first_assum $ irule_at (Pos hd) >> gvs [] >>
      irule_at (Pos $ el 2) $ iffLR exp_eq_sym >>
      irule_at (Pos hd) exp_eq_trans >> irule_at (Pos hd) Let_Apps >>
      irule_at (Pos hd) exp_eq_Apps_cong >> irule_at Any exp_eq_App_cong >>
      irule_at (Pos hd) $ iffLR exp_eq_sym >> irule_at (Pos hd) exp_alpha_exp_eq >>
      irule_at (Pos hd) exp_alpha_Alpha >> first_assum $ irule_at Any >> gvs [] >>
      irule_at Any $ iffRL LIST_REL_EL_EQN >> irule_at Any LENGTH_MAP >>
      irule_at (Pos $ el 2) exp_eq_refl >> gvs [EL_MAP] >>
      irule_at (Pos $ el 2) $ iffLR exp_eq_sym >> irule_at Any Let_Seq >>
      irule_at Any exp_eq_App_cong >> fs [exp_eq_refl] >>
      irule_at Any $ iffRL exp_eq_Lam_strong >>
      last_assum $ qspecl_then [‘Fail’] assume_tac >> gvs [] >>
      rw [] >>
      irule exp_eq_trans >> irule_at (Pos hd) $ iffLR exp_eq_sym >>
      irule_at (Pos hd) beta_equality >> fs [] >>
      irule exp_eq_trans >> irule_at Any Let_Apps >>
      irule exp_eq_trans >> irule_at Any exp_eq_Apps_cong >>
      irule_at Any $ iffRL LIST_REL_EL_EQN >> irule_at Any LENGTH_MAP >> gvs [EL_MAP] >>
      irule_at (Pos $ el 2) $ iffLR exp_eq_sym >> irule_at (Pos hd) exp_eq_App_cong >>
      irule_at (Pos hd) exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >> fs [] >>
      irule_at (Pos hd) exp_eq_refl >>
      conj_asm1_tac
      >- (rw [] >> irule Let_not_in_freevars >>
          rename1 ‘freevars (EL n2 t)’ >> last_x_assum $ qspecl_then [‘freevars (EL n2 t)’] assume_tac >>
          gvs [MEM_MAP] >>
          pop_assum $ qspecl_then [‘EL n2 t’] assume_tac >> gvs [EL_MEM]) >>
      irule exp_eq_trans >> last_x_assum $ drule_then assume_tac >>
      pop_assum $ qspecl_then [‘t’] assume_tac >> fs [exp_eq_in_ctxt_def] >> pop_assum $ irule_at Any >>
      irule exp_eq_trans >> irule_at Any beta_equality >> fs [Once exp_eq_sym] >>
      irule exp_eq_trans >> irule_at Any Let_Seq >>
      irule exp_eq_Prim_cong >> fs [] >>
      irule_at Any Let_not_in_freevars >> gvs [freevars_Projs] >>
      irule_at Any exp_eq_trans >> irule_at Any Let_Apps >>
      irule_at Any exp_eq_Apps_cong >> gvs [LIST_REL_EL_EQN, EL_MAP, exp_eq_sym] >>
      irule_at Any exp_eq_App_cong >> fs [exp_eq_refl] >>
      irule_at Any exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >>
      rename1 ‘freevars (EL n t)’ >> last_x_assum $ qspecl_then [‘freevars (EL n t)’] assume_tac >>
      gvs [MEM_MAP] >>
      pop_assum $ qspecl_then [‘EL n t’] assume_tac >> gvs [EL_MEM])
  >~[‘Letrec lcs (Lam v e)’]
  >- (irule fdemands_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any $ iffLR exp_eq_sym >> irule_at Any exp_eq_trans >>
      irule_at (Pos hd) exp_eq_Letrec_cong >> irule_at Any exp_eq_l_refl >>
      irule_at (Pos hd) exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >>
      irule_at Any Letrec_Lam_weak >>
      last_x_assum $ irule_at $ Pos last >>
      ‘∃s. s ∉ {v} ∪ freevars e ∪ set (MAP FST lcs) ∪ BIGUNION (set (MAP freevars (MAP SND lcs)))’
        by (‘INFINITE 𝕌(:mlstring)’ by simp [INFINITE_mlstring] >>
             dxrule_then assume_tac $ iffLR NOT_IN_FINITE >>
             pop_assum $ irule_at Any >>
             rw [FINITE_UNION, FINITE_BIGUNION, MEM_EL] >>
             gvs [EL_MAP]) >>
      fs [] >> first_assum $ irule_at Any >> gvs [fdemands_def] >>
      conj_asm2_tac >> rw [EVERY_MEM]
      >~[‘MEM e2 (MAP SND lcs)’]
      >- (first_x_assum $ qspecl_then [‘freevars e2’] assume_tac >>
          gvs [MEM_MAP]) >>
      irule fdemands_exp_eq >> last_x_assum $ irule_at Any >>
      irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any exp_eq_trans >> irule_at Any Letrec_App >>
      irule_at Any exp_eq_App_cong >> irule_at Any Letrec_not_in_freevars >> gvs [closed_def] >>
      irule exp_eq_trans >> irule_at (Pos $ el 2) Letrec_Lam_weak >>
      irule_at Any exp_eq_Letrec_cong >> gvs [exp_eq_l_refl] >>
      irule exp_alpha_exp_eq >> irule exp_alpha_Alpha >> fs []) >>
  rename1 ‘Let w e2 (Lam v e1)’ >>
  irule fdemands_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any $ iffLR exp_eq_sym >> irule_at Any exp_eq_trans >>
  irule_at (Pos hd) exp_eq_App_cong >> irule_at (Pos hd) exp_eq_Lam_cong >>
  irule_at (Pos $ el 2) exp_eq_refl >>
  irule_at (Pos hd) exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >>
  irule_at Any Let_Lam_weak >>
  last_x_assum $ irule_at $ Pos last >>
  ‘∃s. s ∉ {v} ∪ freevars e1 ∪ freevars e2 ∪ {w}’
    by (‘INFINITE 𝕌(:mlstring)’ by simp [INFINITE_mlstring] >>
        gvs [NOT_IN_FINITE]) >>
  fs [] >> first_assum $ irule_at Any >> gvs [fdemands_def] >>
  rw [] >>
  irule fdemands_exp_eq >> last_x_assum $ irule_at Any >>
  irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any exp_eq_trans >> irule_at Any Let_App >>
  irule_at Any exp_eq_App_cong >> irule_at Any Let_not_in_freevars >> gvs [closed_def] >>
  irule_at Any exp_eq_trans >> irule_at (Pos $ el 2) Let_Lam_weak >>
  irule_at Any exp_eq_App_cong >> irule_at Any exp_eq_refl >>
  irule_at Any exp_eq_Lam_cong >> gvs [] >>
  irule exp_alpha_exp_eq >> irule exp_alpha_Alpha >> fs []
QED

Theorem Lams_fdemands_lemma:
  ∀vl i c e ps len1. i < LENGTH vl ∧ ALL_DISTINCT vl
                     ∧ e demands_when_applied ((ps, EL i vl), len1, FOLDL (λc n. IsFree n c) c vl)
                     ⇒ Lams vl e fdemands ((ps, i), len1 + LENGTH vl, c)
Proof
  Induct >> gvs [Lams_def, FORALL_PROD] >>
  gen_tac >> Cases >> rw [GSYM SUC_ADD]
  >- (irule Lam_fdemands >>
      irule demands_when_applied_Lams >>
      gvs [])
  >- (irule fdemands_Lam >> gvs [])
QED

Theorem Lams_fdemands:
  ∀vl i c e ps len1. i < LENGTH vl ∧ ALL_DISTINCT vl
                     ∧ e demands ((ps, EL i vl), FOLDL (λc n. IsFree n c) c vl)
                     ⇒ Lams vl e fdemands ((ps, i), LENGTH vl, c)
Proof
  rw [GSYM demands_when_applied_0] >>
  dxrule_then (dxrule_then $ dxrule_then assume_tac) Lams_fdemands_lemma >>
  gvs []
QED

Theorem demands_when_applied_exp_eq:
  ∀d e1 e2 len c. exp_eq_in_ctxt c e1 e2 ∧ e1 demands_when_applied (d, len, c)
                  ⇒ e2 demands_when_applied (d, len, c)
Proof
  PairCases >> rw [demands_when_applied_def] >>
  irule eq_when_applied_trans_exp_eq >>
  irule_at Any $ iffLR exp_eq_in_ctxt_sym >> last_assum $ irule_at Any >>
  irule eq_when_applied_trans >> pop_assum $ irule_at Any >>
  irule exp_eq_in_ctxt_IMP_eq_when_applied >>
  irule exp_eq_in_ctxt_Prim >> gvs [exp_eq_in_ctxt_refl]
QED

Theorem demands_IMP_demands_when_applied:
  ∀e c l ps. e demands ((ps, v), c) ⇒ e demands_when_applied ((ps, v), l, c)
Proof
  rw [demands_def, demands_when_applied_def]
  \\ gs [exp_eq_in_ctxt_IMP_eq_when_applied]
QED

(* -------------------- *)

Theorem demands_Fail:
  ∀p. Fail demands p
Proof
  gvs [FORALL_PROD, demands_def] >> rpt $ gen_tac >>
  irule exp_eq_IMP_exp_eq_in_ctxt >>
  irule no_err_eval_IMP_exp_eq >>
  rw [subst_def, no_err_eval_def, v_unfold, eval_wh_thm]
QED

Theorem needs_Fail:
  ∀p. Fail needs p
Proof
  gvs [FORALL_PROD, needs_def] >> rpt $ gen_tac >>
  irule exp_eq_IMP_exp_eq_in_ctxt >>
  irule no_err_eval_IMP_exp_eq >>
  rw [subst_def, no_err_eval_def, v_unfold, eval_wh_thm]
QED

Theorem Fail_Apps:
  ∀l b. (Fail ≅? Apps Fail l) b
Proof
  Induct >> gvs [Apps_def, exp_eq_refl] >>
  rw [] >> irule exp_eq_trans >> first_x_assum $ irule_at Any >>
  irule exp_eq_Apps_cong >> irule_at Any eval_IMP_exp_eq >>
  rw [exp_eq_l_refl, subst_def, eval_thm, dest_Closure_def]
QED

Theorem fdemands_Fail:
  ∀c ps i len. i < len ⇒ Fail fdemands ((ps, i), len, c)
Proof
  Induct >> gvs [fdemands_def] >> rw []
  >- (irule needs_exp_eq >> irule_at Any needs_Fail >>
      gvs [exp_eq_in_ctxt_def, Fail_Apps]) >>
  irule fdemands_exp_eq >> last_x_assum $ irule_at Any >> fs [] >>
  irule exp_eq_IMP_exp_eq_in_ctxt >> irule $ iffLR exp_eq_sym >>
  gvs [Let_not_in_freevars, Letrec_not_in_freevars]
QED

(* -------------------- *)

Theorem IMP_obligation:
  ALL_DISTINCT (MAP FST binds) ∧
  (∀vname args body.
     MEM (vname,args,body) binds
     ⇒
     (* args are distinct *)
     ALL_DISTINCT (MAP FST args) ∧
     (* args are disjoint *)
     DISJOINT (set (MAP FST args)) (set (MAP FST binds)) ∧
     (* body of bound exp only mentions args and other bound names *)
     freevars body SUBSET (set (MAP FST binds) UNION set (MAP FST args)) ∧
     (* every forced var is free in body *)
     set (MAP FST (FILTER SND args)) SUBSET freevars body ∧
     (* there is a reformulation of body, called e, such that 'e ≈ mk_seqs args e' *)
     ∃e.
       reformulate binds body e ∧
       ∀v. MEM (v,T) args ⇒ e demands (([], v), Nil))
  ⇒
  pure_letrec_seq$obligation binds
Proof
  strip_tac
  \\ irule pure_letrec_seqTheory.IMP_obligation
  \\ asm_rewrite_tac []
  \\ rpt gen_tac \\ strip_tac
  \\ first_x_assum $ drule_then strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any
  \\ fs [demands_def,Projs_def,exp_eq_in_ctxt_def]
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘args’
  \\ Induct
  \\ fs [mk_seqs_def,exp_eq_refl,FORALL_PROD]
  \\ rw []
  \\ rename [‘(v,p)::_’]
  \\ Cases_on ‘p’ \\ fs [mk_seqs_def]
  \\ irule exp_eq_trans
  \\ irule_at (Pos $ el 2) pure_congruenceTheory.exp_eq_Prim_cong
  \\ fs [PULL_EXISTS]
  \\ pop_assum $ irule_at $ Pos last \\ fs []
  \\ qexists_tac ‘v’ \\ fs [exp_eq_refl]
QED

Theorem mk_seq_args_demands:
  ∀args i e c. i < LENGTH args ∧ SND (EL i args) ⇒
               mk_seqs args e demands (([], FST (EL i args)), c)
Proof
  Induct \\ gs [FORALL_PROD]
  \\ gen_tac
  \\ Cases \\ gs [mk_seqs_def]
  >- (Cases \\ gs [demands_Var, demands_Seq]
      \\ rw []
      \\ irule demands_Seq2
      \\ last_x_assum irule
      \\ simp [])
  \\ Cases \\ gs []
QED

Inductive find_fixpoint:
[~Var:]
  (∀v c binds.
     find_fixpoint binds (Var v) c {v} {} [])
[~Var_known:]
  (∀v (c : ctxt) binds (args : (mlstring # bool) list) (body : exp).
     MEM (v, args, body) binds ⇒
     find_fixpoint binds (Var v) c {} {} (MAP SND args))
[~App:]
  (∀e1 e2 c binds ds1 ds2 ads1 ads2 l1 l2.
     find_fixpoint binds e1 c ds1 ads1 l1 ∧
     find_fixpoint binds e2 c ds2 ads2 l2 ⇒
     find_fixpoint binds (App e1 e2) c ds1 {} [])
[~App_T:]
  (∀e1 e2 c binds ds1 ds2 ads1 ads2 l1 l2.
     find_fixpoint binds e1 c ds1 ads1 (T::l1) ∧
     find_fixpoint binds e2 c ds2 ads2 l2 ⇒
     find_fixpoint binds (App e1 e2) c ds1 (ads1 ∪ ds2) l1)
[~App_F:]
  (∀e1 e2 c binds ds1 ds2 ads1 ads2 l1 l2.
     find_fixpoint binds e1 c ds1 ads1 (F::l1) ∧
     find_fixpoint binds e2 c ds2 ads2 l2 ⇒
     find_fixpoint binds (App e1 e2) c ds1 ads1 l1)
[~App_empty:]
  (∀e c binds ds ads.
     find_fixpoint binds e c ds ads [] ⇒
     find_fixpoint binds e c (ds ∪ ads) {}  [])
[~Seq:]
  (∀e1 e2 c binds ds1 ds2 ads1 ads2 l1 l2.
     find_fixpoint binds e1 c ds1 ads1 l1 ∧
     find_fixpoint binds e2 c ds2 ads2 l2 ⇒
     find_fixpoint binds (Seq e1 e2) c (ds1 ∪ ds2) ads2 l2)
[~If:]
  (∀e1 e2 e3 c binds ds1 ds2 ds3 ads1 ads2 ads3 l1 l2 l3.
     find_fixpoint binds e1 c ds1 ads1 l1 ∧
     find_fixpoint binds e2 c ds2 ads2 l2 ∧
     find_fixpoint binds e3 c ds3 ads3 l3 ⇒
     find_fixpoint binds (If e1 e2 e3) c (ds1 ∪ (ds2 ∩ ds3)) {} [])
[~If_Fail:]
  (∀e1 e2 c binds ds1 ds2 ads1 ads2 l1 l2.
     find_fixpoint binds e1 c ds1 ads1 l1 ∧
     find_fixpoint binds e2 c ds2 ads2 l2 ⇒
     find_fixpoint binds (If e1 e2 Fail) c (ds1 ∪ ds2) {} [])
[~Proj:]
  (∀binds e n i c ds ads l.
     find_fixpoint binds e c ds ads l ⇒
     find_fixpoint binds (Proj n i e) c ds {} [])
[~IsEq:]
  (∀binds e n i b c ds ads l.
     find_fixpoint binds e c ds ads l ⇒
     find_fixpoint binds (IsEq n i b e) c ds {} [])
[~Atom:]
  (∀binds el dsl c op.
     LIST_REL (λe ds.∃ads l. find_fixpoint binds e c ds ads l) el dsl ⇒
     find_fixpoint binds (Prim (AtomOp op) el) c (BIGUNION (set dsl)) {} [])
[~Lam_F:]
  (∀e c binds ds ads l s.
     find_fixpoint (FILTER (λ(v, _). v ≠ s) binds) e (IsFree s c) ds ads l ⇒
     find_fixpoint binds (Lam s e) c {} (ads DELETE s) (F::l))
[~Lam_T:]
  (∀e c binds ds ads l s.
     (s ∈ ds ∨ s ∈ ads) ∧
     find_fixpoint (FILTER (λ(v, _). v ≠ s) binds) e (IsFree s c) ds ads l ⇒
     find_fixpoint binds (Lam s e) c {} (ads DELETE s) (T::l))
[~Let:]
  (∀e1 e2 c binds ds1 ds2 ads1 ads2 l1 l2 w.
     w ∉ ds2 ∧ w ∉ ads2 ∧
     find_fixpoint binds e1 c ds1 ads1 l1 ∧
     find_fixpoint (FILTER (λ(v, _). v ≠ w) binds) e2 (IsFree w c) ds2 ads2 l2 ⇒
     find_fixpoint binds (Let w e1 e2) c ds2 ads2 l2)
[~Let_demands:]
  (∀e1 e2 c binds ds1 ds2 ads1 ads2 l1 l2 w.
     w ∈ ds2 ∧
     find_fixpoint binds e1 c ds1 ads1 l1 ∧
     find_fixpoint (FILTER (λ(v, _). v ≠ w) binds) e2 (IsFree w c) ds2 ads2 l2 ⇒
     find_fixpoint binds (Let w e1 e2) c (ds2 DELETE w ∪ ds1) (ads2 DELETE w) l2)
[~Subset:]
  (∀e c binds ds1 ds2 ads1 ads2 l1 l2.
     ds2 ⊆ ds1 ∧ ads2 ⊆ ads1 ∧
     LIST_REL (λb1 b2. b2 ⇒ b1) l1 l2 ∧
     find_fixpoint binds e c ds1 ads1 l1 ⇒
     find_fixpoint binds e c ds2 ads2 l2)
[~drop_fd:]
  (∀e c binds ds ads l.
     find_fixpoint binds e c ds ads l ⇒
     find_fixpoint binds e c ds {} [])
[~smaller_binds:]
  (∀e c binds f ds ads l.
     find_fixpoint (FILTER (λ(v, _). f v) binds) e c ds ads l ⇒
     find_fixpoint binds e c ds ads l)
[~refl:]
  (∀e c binds.
     find_fixpoint binds e c {} {}  [])
End

Theorem find_fixpoint_Prim_Lemma:
  ∀eL dsL binds c.
      (∀v args body. MEM (v,args,body) binds ⇒ ALL_DISTINCT (MAP FST args)) ∧
      LIST_REL
          (λe ds.
               ∃ads fds.
                 find_fixpoint binds e c ds ads fds ∧
                 ((∀v args body.
                     MEM (v,args,body) binds ⇒ ALL_DISTINCT (MAP FST args)) ⇒
                  ∃e2.
                    reformulate binds e e2 ∧
                    (∀v. v ∈ ds ⇒ e2 demands (([],v),c) ∧ v ∈ freevars e) ∧
                    (∀v. v ∈ ads ⇒
                         e2 demands_when_applied (([],v),LENGTH fds,c) ∧
                         v ∈ freevars e) ∧
                    ∀i. i < LENGTH fds ∧ EL i fds ⇒
                        e2 fdemands (([],i),LENGTH fds,c))) eL dsL
      ⇒ ∃ys. LIST_REL (reformulate binds) eL ys ∧
             ∀v i. v ∈ EL i dsL ∧ i < LENGTH dsL
                   ⇒ v ∈ freevars (EL i eL) ∧
                     (EL i ys) demands (([], v), c)
Proof
  Induct \\ gs [PULL_EXISTS]
  \\ rw [] \\ gs []
  \\ last_x_assum $ drule_then assume_tac
  \\ last_x_assum $ drule_then assume_tac
  \\ last_x_assum $ drule_then assume_tac
  \\ gs []
  \\ first_x_assum $ irule_at Any
  \\ first_x_assum $ irule_at Any
  \\ gen_tac \\ Cases \\ gvs []
QED

Theorem ALL_DISTINCT_FST_FILTER:
  ∀binds f. ALL_DISTINCT (MAP FST binds)
                  ⇒ ALL_DISTINCT (MAP FST (FILTER (λ(v, _). f v) binds))
Proof
  Induct \\ gs [FORALL_PROD]
  \\ rw []
  \\ gs [MEM_MAP, MEM_FILTER]
QED

Theorem FILTERED_binds_lemma:
  ∀binds binds2 f.
    MAP FST binds = MAP FST binds2 ∧
    LIST_REL (λ(_,a1,_) (_,a2,_). LIST_REL (λ(_,b1) (_,b2). b2 ⇒ b1) a1 a2) binds2 binds ⇒
    LIST_REL (λ(_,a1,_) (_,a2,_). LIST_REL (λ(_,b1) (_,b2). b2 ⇒ b1) a1 a2)
             (FILTER (λ(v,_). f v) binds2) (FILTER (λ(v,_). f v) binds) ∧
    MAP FST (FILTER (λ(v,_). f v) binds) =
    MAP FST (FILTER (λ(v,_). f v) binds2)
Proof
  Induct \\ gs [PULL_EXISTS, FORALL_PROD]
  \\ rw [] \\ gvs []
QED

Theorem find_fixpoint_soundness:
  ∀e binds c ds ads fds.
    find_fixpoint binds e c ds ads fds ∧
    ALL_DISTINCT (MAP FST binds) ∧
    (∀v args body. MEM (v, args, body) binds ⇒ ALL_DISTINCT (MAP FST args)) ⇒
    ∃e2.
      reformulate binds e e2 ∧
      (∀v. v ∈ ds ⇒ e2 demands (([], v), c) ∧ v ∈ freevars e) ∧
      (∀v. v ∈ ads ⇒ e2 demands_when_applied (([], v), LENGTH fds, c) ∧ v ∈ freevars e) ∧
      (∀i. i < LENGTH fds ∧ EL i fds ⇒ e2 fdemands (([], i), LENGTH fds, c))
Proof
  Induct_on ‘find_fixpoint’ \\ rw []
  >- (irule_at Any reformulate_Var
      \\ gs [demands_Var])
  >- (irule_at Any reformulate_partial
      \\ gs [mk_seq_lams_def]
      \\ dxrule_then assume_tac ALOOKUP_ALL_DISTINCT_MEM
      \\ first_x_assum $ qspecl_then [‘(args, body)’, ‘v’] assume_tac
      \\ gs []
      \\ rw []
      \\ qspec_then ‘MAP FST args’ assume_tac Lams_fdemands
      \\ gs []
      \\ first_x_assum irule
      \\ first_x_assum $ dxrule_then assume_tac
      \\ simp [EL_MAP]
      \\ irule mk_seq_args_demands
      \\ gs [EL_MAP])
  >- (irule_at Any reformulate_App
      \\ gs []
      \\ last_x_assum $ drule_then assume_tac
      \\ last_x_assum $ drule_then assume_tac
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ first_x_assum $ irule_at Any
      \\ rw []
      \\ gvs [demands_App])
  >- (irule_at Any reformulate_App
      \\ gs []
      \\ last_x_assum $ drule_then assume_tac
      \\ last_x_assum $ drule_then assume_tac
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ first_x_assum $ irule_at Any
      \\ rw []
      >- (irule demands_App \\ gvs [])
      >- (irule demands_when_applied_App \\ gvs [])
      >- (first_x_assum $ dxrule_then assume_tac \\ gs [])
      >- (simp [demands_w_app_is_needs_w_app]
          \\ irule fdemands_0_App_needs
          \\ simp [needs_Var_is_demands])
      >- (first_x_assum $ dxrule_then assume_tac \\ gs [])
      >- (irule fdemands_App \\ gs []))
  >- (irule_at Any reformulate_App
      \\ gs []
      \\ last_x_assum $ drule_then assume_tac
      \\ last_x_assum $ drule_then assume_tac
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ first_x_assum $ irule_at Any
      \\ rw []
      >- (irule demands_App \\ gvs [])
      >- (irule demands_when_applied_App \\ gvs [])
      >- (irule fdemands_App \\ gs []))
  >- (gs []
      \\ last_x_assum $ drule_then assume_tac
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ rw [] \\ gs []
      >- gs [demands_when_applied_0])
  >~[‘Seq _ _’]
  >- (irule_at Any reformulate_Prim
      \\ gs [PULL_EXISTS]
      \\ last_x_assum $ drule_then assume_tac
      \\ last_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ first_x_assum $ irule_at Any
      \\ rw []
      \\ gs [demands_Seq, demands_Seq2, demands_when_applied_Seq, fdemands_Seq])
  >~[‘If _ _ Fail’]
  >- (irule_at Any reformulate_Prim
      \\ gs [PULL_EXISTS]
      \\ last_x_assum $ drule_then assume_tac
      \\ last_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ first_x_assum $ irule_at Any
      \\ irule_at Any reformulate_refl
      \\ rw []
      \\ gs [demands_If, demands_If2, demands_Fail])
  >~[‘If _ _ _’]
  >- (irule_at Any reformulate_Prim
      \\ gs [PULL_EXISTS]
      \\ last_x_assum $ drule_then assume_tac
      \\ last_x_assum $ drule_then assume_tac
      \\ last_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ first_x_assum $ irule_at Any
      \\ first_x_assum $ irule_at Any
      \\ rw []
      \\ gs [demands_If, demands_If2])
  >~[‘Proj _ _ _’]
  >- (irule_at Any reformulate_Prim
      \\ gs [PULL_EXISTS]
      \\ last_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ rw []
      \\ gs [demands_Proj])
  >~[‘IsEq _ _ _ _’]
  >- (irule_at Any reformulate_Prim
      \\ gs [PULL_EXISTS]
      \\ last_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ rw []
      \\ gs [demands_IsEq])
  >~[‘Prim (AtomOp _) _’]
  >- (irule_at Any reformulate_Prim
      \\ gs [PULL_EXISTS]
      \\ drule_then assume_tac LIST_REL_LENGTH
      \\ dxrule_then (dxrule_then assume_tac) find_fixpoint_Prim_Lemma
      \\ gs []
      \\ drule_then assume_tac LIST_REL_LENGTH
      \\ first_x_assum $ irule_at Any
      \\ rw [MEM_EL]
      \\ last_x_assum $ drule_all_then assume_tac
      \\ gs []
      \\ first_assum $ irule_at Any
      \\ first_assum $ irule_at Any
      \\ gs [EL_MAP]
      \\ irule demands_AtomOp
      \\ gs [EXISTS_MEM, MEM_EL]
      \\ metis_tac [])
  >- (irule_at Any reformulate_Lam
      \\ qpat_x_assum ‘_ ⇒ ∃e. _’ mp_tac
      \\ impl_tac
      >- (qpat_x_assum ‘ALL_DISTINCT _’ mp_tac
          \\ qpat_x_assum ‘∀v args body. _ ⇒ ALL_DISTINCT _’ mp_tac
          \\ rpt $ pop_assum kall_tac
          \\ Induct_on ‘binds’ \\ gs [FORALL_PROD]
          \\ rpt $ gen_tac \\ strip_tac
          \\ strip_tac
          \\ gs []
          \\ last_x_assum mp_tac
          \\ impl_tac
          >- (rw [] \\ last_x_assum irule
              \\ metis_tac [])
          \\ strip_tac
          \\ rw []
          >- (strip_tac \\ gvs [MEM_MAP, MEM_FILTER])
          >- (last_x_assum irule \\ metis_tac [])
          >- first_x_assum $ dxrule_then irule
          >- first_x_assum $ dxrule_then irule)
      \\ strip_tac \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ rw []
      \\ gs [demands_when_applied_Lam]
      \\ rename1 ‘EL i (_::_)’
      \\ Cases_on ‘i’ \\ gs [fdemands_Lam])
  >- (irule_at Any reformulate_Lam
      \\ qpat_x_assum ‘_ ⇒ ∃e. _’ mp_tac
      \\ impl_tac
      >- (qpat_x_assum ‘ALL_DISTINCT _’ mp_tac
          \\ qpat_x_assum ‘∀v args body. _ ⇒ ALL_DISTINCT _’ mp_tac
          \\ rpt $ pop_assum kall_tac
          \\ Induct_on ‘binds’ \\ gs [FORALL_PROD]
          \\ rpt $ gen_tac \\ strip_tac
          \\ strip_tac
          \\ gs []
          \\ last_x_assum mp_tac
          \\ impl_tac
          >- (rw [] \\ last_x_assum irule
              \\ metis_tac [])
          \\ strip_tac
          \\ rw []
          >- (strip_tac \\ gvs [MEM_MAP, MEM_FILTER])
          >- (last_x_assum irule \\ metis_tac [])
          >- first_x_assum $ dxrule_then irule
          >- first_x_assum $ dxrule_then irule)
      \\ strip_tac \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ rw []
      \\ gs [demands_when_applied_Lam]
      \\ rename1 ‘EL i (_::_)’
      \\ Cases_on ‘i’ \\ gs [fdemands_Lam]
      \\ irule Lam_fdemands
      \\ irule demands_IMP_demands_when_applied
      \\ gs [])
  >- (irule_at Any reformulate_Lam
      \\ qpat_x_assum ‘_ ⇒ ∃e. _’ mp_tac
      \\ impl_tac
      >- (qpat_x_assum ‘ALL_DISTINCT _’ mp_tac
          \\ qpat_x_assum ‘∀v args body. _ ⇒ ALL_DISTINCT _’ mp_tac
          \\ rpt $ pop_assum kall_tac
          \\ Induct_on ‘binds’ \\ gs [FORALL_PROD]
          \\ rpt $ gen_tac \\ strip_tac
          \\ strip_tac
          \\ gs []
          \\ last_x_assum mp_tac
          \\ impl_tac
          >- (rw [] \\ last_x_assum irule
              \\ metis_tac [])
          \\ strip_tac
          \\ rw []
          >- (strip_tac \\ gvs [MEM_MAP, MEM_FILTER])
          >- (last_x_assum irule \\ metis_tac [])
          >- first_x_assum $ dxrule_then irule
          >- first_x_assum $ dxrule_then irule)
      \\ strip_tac \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ rw []
      \\ gs [demands_when_applied_Lam]
      \\ rename1 ‘EL i (_::_)’
      \\ Cases_on ‘i’ \\ gs [fdemands_Lam]
      \\ irule Lam_fdemands
      \\ gs [])
  >- (irule_at Any reformulate_App
      \\ irule_at Any reformulate_Lam
      \\ gs []
      \\ last_x_assum $ drule_then assume_tac
      \\ qpat_x_assum ‘_ ⇒ ∃e. _’ mp_tac
      \\ impl_tac
      >- (qpat_x_assum ‘ALL_DISTINCT _’ mp_tac
          \\ qpat_x_assum ‘∀v args body. _ ⇒ ALL_DISTINCT _’ mp_tac
          \\ rpt $ pop_assum kall_tac
          \\ Induct_on ‘binds’ \\ gs [FORALL_PROD]
          \\ rpt $ gen_tac \\ strip_tac
          \\ strip_tac
          \\ gs []
          \\ last_x_assum mp_tac
          \\ impl_tac
          >- (rw [] \\ last_x_assum irule
              \\ metis_tac [])
          \\ strip_tac
          \\ rw []
          >- (strip_tac \\ gvs [MEM_MAP, MEM_FILTER])
          >- (last_x_assum irule \\ metis_tac [])
          >- first_x_assum $ dxrule_then irule
          >- first_x_assum $ dxrule_then irule)
      \\ strip_tac \\ gs []
      \\ qpat_x_assum ‘reformulate (FILTER _ _) _ _’ $ irule_at Any
      \\ first_x_assum $ irule_at Any
      \\ rw [] \\ gs []
      >- (simp [GSYM demands_when_applied_0]
          \\ irule demands_when_applied_App
          \\ irule demands_when_applied_Lam
          \\ simp [demands_when_applied_0]
          \\ strip_tac \\ gs [])
      >- (irule demands_when_applied_App
          \\ irule demands_when_applied_Lam
          \\ gvs []
          \\ strip_tac \\ gs [])
      >- (irule fdemands_App
          \\ irule fdemands_Lam
          \\ gvs []))
  >- (irule_at Any reformulate_App
      \\ irule_at Any reformulate_Lam
      \\ gs []
      \\ last_x_assum $ drule_then assume_tac
      \\ qpat_x_assum ‘_ ⇒ ∃e. _’ mp_tac
      \\ impl_tac
      >- (qpat_x_assum ‘ALL_DISTINCT _’ mp_tac
          \\ qpat_x_assum ‘∀v args body. _ ⇒ ALL_DISTINCT _’ mp_tac
          \\ rpt $ pop_assum kall_tac
          \\ Induct_on ‘binds’ \\ gs [FORALL_PROD]
          \\ rpt $ gen_tac \\ strip_tac
          \\ strip_tac
          \\ gs []
          \\ last_x_assum mp_tac
          \\ impl_tac
          >- (rw [] \\ last_x_assum irule
              \\ metis_tac [])
          \\ strip_tac
          \\ rw []
          >- (strip_tac \\ gvs [MEM_MAP, MEM_FILTER])
          >- (last_x_assum irule \\ metis_tac [])
          >- first_x_assum $ dxrule_then irule
          >- first_x_assum $ dxrule_then irule)
      \\ strip_tac \\ gs []
      \\ qpat_x_assum ‘reformulate (FILTER _ _) _ _’ $ irule_at Any
      \\ first_x_assum $ irule_at Any
      \\ rw [] \\ gs []
      >- (simp [GSYM demands_when_applied_0]
          \\ irule demands_when_applied_App
          \\ irule demands_when_applied_Lam
          \\ simp [demands_when_applied_0])
      >- (simp [GSYM demands_when_applied_0]
          \\ irule fdemands_0_App_demands
          \\ gs []
          \\ rename1 ‘Lam w e2 fdemands (([], 0), 1, c)’
          \\ qspecl_then [‘c’, ‘w’, ‘e2’, ‘[]’, ‘0’] assume_tac Lam_fdemands
          \\ gvs [demands_when_applied_0])
      >- (irule demands_when_applied_App
          \\ irule demands_when_applied_Lam
          \\ gvs []
          \\ strip_tac \\ gs [])
      >- (irule fdemands_App
          \\ irule fdemands_Lam
          \\ gvs []))
  >- (gs []
      \\ first_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ rw [] \\ gvs [SUBSET_DEF, LIST_REL_EL_EQN])
  >- (gs []
      \\ first_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ gs [])
  >- (gs [ALL_DISTINCT_FST_FILTER]
      \\ qpat_x_assum ‘_ ⇒ _’ mp_tac
      \\ impl_tac
      >- (rw [MEM_FILTER]
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gs [])
      \\ strip_tac \\ gs []
      \\ dxrule_all_then assume_tac reformulate_filtered_bind
      \\ first_x_assum $ irule_at Any
      \\ gs [])
  >- irule_at Any reformulate_refl
QED

Theorem find_lower_bind:
  ∀binds binds2 e c ds ads fs.
    find_fixpoint binds e c ds ads fs ∧
    LIST_REL (λ(_, a1, _) (_, a2, _).
                LIST_REL (λ(_, b1) (_, b2). b2 ⇒ b1) a1 a2) binds2 binds ∧
    MAP FST binds = MAP FST binds2 ⇒
    find_fixpoint binds2 e c ds ads fs
Proof
  Induct_on ‘find_fixpoint’ \\ rw []
  >- irule find_fixpoint_Var
  >- (irule find_fixpoint_Subset
      \\ gs []
      \\ irule_at Any find_fixpoint_Var_known
      \\ gvs [MEM_EL, LIST_REL_EL_EQN, PULL_EXISTS]
      \\ first_assum $ irule_at Any
      \\ first_x_assum $ drule_then assume_tac
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ rename1 ‘MAP FST binds = MAP FST binds2’
      \\ rename1 ‘EL n _’
      \\ ‘EL n (MAP FST binds) = EL n (MAP FST binds2)’ by simp []
      \\ gs [EL_MAP]
      \\ rw []
      \\ first_x_assum $ drule_then assume_tac
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs [])
  >- (irule find_fixpoint_App
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ first_x_assum $ irule_at Any \\ gs [])
  >- (irule find_fixpoint_App_T
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ first_x_assum $ irule_at Any \\ gs [])
  >- (irule find_fixpoint_App_F
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ first_x_assum $ irule_at Any \\ gs [])
  >- (irule find_fixpoint_App_empty
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ first_x_assum $ irule_at Any \\ gs [])
  >~[‘Seq _ _’]
  >- (irule find_fixpoint_Seq
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ first_x_assum $ irule_at Any \\ gs [])
  >~[‘If _ _ Fail’]
  >- (irule find_fixpoint_If_Fail
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ first_x_assum $ irule_at Any \\ gs [])
  >~[‘If _ _ _’]
  >- (irule find_fixpoint_If
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ first_x_assum $ irule_at Any \\ gs [])
  >~[‘Proj _ _ _’]
  >- (irule find_fixpoint_Proj
      \\ first_x_assum $ irule_at Any \\ gs [])
  >~[‘IsEq _ _ _ _’]
  >- (irule find_fixpoint_IsEq
      \\ first_x_assum $ irule_at Any \\ gs [])
  >~[‘Prim (AtomOp _) _’]
  >- (irule find_fixpoint_Atom
      \\ gvs [LIST_REL_EL_EQN]
      \\ rw [] \\ last_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ gvs [])
  >- (irule find_fixpoint_Lam_F
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ pop_assum mp_tac
      \\ pop_assum mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ qid_spec_tac ‘binds2’
      \\ Induct_on ‘binds’ \\ gs [PULL_EXISTS, FORALL_PROD]
      \\ rw [])
  >- (irule find_fixpoint_Lam_T
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ pop_assum mp_tac
      \\ pop_assum mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ qid_spec_tac ‘binds2’
      \\ Induct_on ‘binds’ \\ gs [PULL_EXISTS, FORALL_PROD]
      \\ rw [])
  >- (irule find_fixpoint_Lam_T
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ pop_assum mp_tac
      \\ pop_assum mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ qid_spec_tac ‘binds2’
      \\ Induct_on ‘binds’ \\ gs [PULL_EXISTS, FORALL_PROD]
      \\ rw [])
  >- (irule find_fixpoint_Let
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ pop_assum mp_tac
      \\ pop_assum mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ qid_spec_tac ‘binds2’
      \\ Induct_on ‘binds’ \\ gs [PULL_EXISTS, FORALL_PROD]
      \\ rw [])
  >- (irule find_fixpoint_Let_demands
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ first_x_assum $ irule_at Any \\ gs []
      \\ pop_assum mp_tac
      \\ pop_assum mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ qid_spec_tac ‘binds2’
      \\ Induct_on ‘binds’ \\ gs [PULL_EXISTS, FORALL_PROD]
      \\ rw [])
  >- (irule find_fixpoint_Subset
      \\ first_x_assum $ irule_at Any \\ gs [])
  >- (irule find_fixpoint_drop_fd
      \\ first_x_assum $ irule_at Any \\ gs [])
  >- (irule find_fixpoint_smaller_binds
      \\ first_x_assum $ irule_at Any
      \\ dxrule_then (dxrule_then assume_tac) FILTERED_binds_lemma
      \\ metis_tac [])
  >- irule find_fixpoint_refl
QED

Theorem IMP_obligation_fixpoint:
  ALL_DISTINCT (MAP FST binds) ∧
  (∀vname args body.
     MEM (vname,args,body) binds
     ⇒
     (* args are distinct *)
     ALL_DISTINCT (MAP FST args) ∧
     (* args are disjoint *)
     DISJOINT (set (MAP FST args)) (set (MAP FST binds)) ∧
     (* body of bound exp only mentions args and other bound names *)
     freevars body SUBSET (set (MAP FST binds) UNION set (MAP FST args)) ∧
     (* there is a reformulation of body, called e, such that 'e ≈ mk_seqs args e' *)
     (∃ds ads fs. find_fixpoint binds body Nil ds ads fs ∧
                 (∀v. MEM (v, T) args ⇒ v ∈ ds)))
  ⇒
  pure_letrec_seq$obligation binds
Proof
  strip_tac
  \\ irule IMP_obligation
  \\ simp []
  \\ rpt $ gen_tac \\ strip_tac
  \\ last_assum $ drule_then assume_tac
  \\ gs []
  \\ dxrule_then mp_tac find_fixpoint_soundness
  \\ simp []
  \\ impl_tac
  >- (rw []
      \\ last_x_assum $ dxrule_then assume_tac
      \\ gs [])
  \\ rw []
  >- (rw [SUBSET_DEF]
      \\ gs [MEM_MAP, MEM_FILTER, SND_THM]
      \\ pairarg_tac \\ gs [])
  \\ first_x_assum $ irule_at Any
  \\ gvs []
QED

(* -------------------- *)


Definition dest_fd_SND_def:
  dest_fd_SND NONE = {} ∧
  dest_fd_SND (SOME (bL, s)) = s
End

Definition demands_boolList_def:
  demands_boolList d [] = ([], {}) ∧
  demands_boolList d (hd::tl) =
    let (bL, d2) = demands_boolList d tl in
      (((∃ps. (ps, hd) ∈ d)∧ hd ∉ d2)::bL, d2 ∪ {hd})
End

Inductive find: (* i i i o o o *)
[find_trans:]
  (∀e e_mid e2 c fds ds_drop fd_drop ds fd.
     find e c fds ds_drop e_mid fd_drop ∧
     find e_mid c fds ds e2 fd ⇒
     find e c fds ds e2 fd)
[find_Drop_fd:]
  (∀e e' c fds ds fd.
     find e c fds ds e' fd ⇒ find e c fds ds e' NONE)
[find_Create_fd:]
  (∀e e' c fds ds.
     find e c fds ds e' NONE ⇒ find e c fds ds e' (SOME ([], {})))
[find_smaller_fd:]
  (∀e e' c fds ds bL fd fd'.
     find e c fds ds e' (SOME (bL, fd)) ∧ fd' ⊆ fd
     ⇒ find e c fds ds e' (SOME (bL, fd')))
[find_Bottom:]
  (∀e (c:ctxt) (fdc : (mlstring # (bool list)) -> bool).
    find e c fdc {} e NONE)
[find_Seq:]
  (∀e e' c (p:(mlstring#num) list) ds v fdc fd.
    find e c fdc ds e' fd ∧ (p,v) ∈ ds ⇒
    find e c fdc ds (Seq (Var v) e') fd)
[find_Seq2:]
  (∀e e' e2 e2' c ds ds2 fdc fd fd2.
     find e c fdc ds e' fd ∧ find e2 c fdc ds2 e2' fd2 ⇒
     find (Seq e e2) c fdc (ds ∪ ds2) (Seq e' e2') fd2)
[find_If:]
  (∀ec et ee ec' et' ee' c dsc dst dse fdc fd fdt fde.
     find ec c fdc dsc ec' fd
     ∧ find et c fdc dst et' fdt
     ∧ find ee c fdc dse ee' fde
     ⇒ find (If ec et ee) c fdc (dsc ∪ (dst ∩ dse)) (If ec' et' ee') NONE)
[find_Var:]
  (∀n c fdc. find (Var n) c fdc {([],n)} (Var n) NONE)
[find_Var2:]
  (∀n c fdc argsDemanded.
     (n, argsDemanded) ∈ fdc
     ⇒ find (Var n) c fdc {([],n)} (Var n) (SOME (argsDemanded, {})))
[find_No_args:]
  (∀c fdc e e' ds ds'.
     find e c fdc ds e' (SOME ([], ds'))
     ⇒ find e c fdc (ds ∪ ds') e' NONE)
[find_App:]
  (∀f f' e e' fdc c ds ds2 fd1 fd2.
     find f c fdc ds f' fd1 ∧
     find e c fdc ds2 e' fd2 ⇒
     find (App f e) c fdc ds (App f' e') NONE)
[find_App_arg_strict:]
  (∀f f' e e' fdc c ds ds2 ds3 fd argD.
     find f c fdc ds f' (SOME (T::argD, ds3))
     ∧ find e c fdc ds2 e' fd
     ⇒ find (App f e) c fdc ds (App f' e') (SOME (argD, ds2 ∪ ds3)))
[find_App_arg_not_strict:]
  (∀f f' e e' fdc c ds ds2 ds3 fd argD b.
     find f c fdc ds f' (SOME (b::argD, ds3))
     ∧ find e c fdc ds2 e' fd
     ⇒ find (App f e) c fdc ds (App f' e') (SOME (argD, ds3)))
[find_Apps:]
  (∀f f' el el' c ds fdc fd.
     LIST_REL (λe e'. ∃ds fd. find e c fdc ds e' fd) el el' ∧
     find f c fdc ds f' fd ⇒ find (Apps f el) c fdc ds (Apps f' el') NONE)
[find_Apps_fd:]
  (∀f f' el el' c ds ds' fdc bL bL' fd dsL.
     LIST_REL (λe (ds, e'). ∃ fd. find e c fdc ds e' fd) el (ZIP (dsL, el'))
     ∧ LENGTH el' = LENGTH bL ∧ LENGTH dsL = LENGTH el'
     ∧ find f c fdc ds f' (SOME (bL ++ bL', fd))
     ∧ (∀p. p ∈ ds' ⇒ p ∈ fd ∨ ∃i. i < LENGTH bL ∧ p ∈ EL i dsL ∧ EL i bL)
     ⇒ find (Apps f el) c fdc ds (Apps f' el') (SOME (bL', ds')))
[find_Prim:]
  (∀c el el' ope fdc.
     LENGTH el = LENGTH el' ∧ (∀k. k < LENGTH el ⇒ ∃ds fd. find (EL k el) c fdc ds (EL k el') fd)
     ⇒ find (Prim ope el) c fdc {} (Prim ope el') NONE)
[find_Prim1:]
  (∀c el el' ope ds fdc fd.
      LIST_REL (λe e'. ∃ds2 fd2. find e c fdc ds2 e' fd2) el el'
      ∧ find (EL 0 el) c fdc ds (EL 0 el') fd ∧ el ≠ [] ∧ well_formed ope el
      ⇒ find (Prim ope el) c fdc ds (Prim ope el') NONE)
[find_Prim_Fail:]
  (∀c el ope fdc.
     ¬ (well_written ope el) ⇒ find (Prim ope el) c fdc {} Fail NONE)
[find_Proj:]
  (∀e e' n i c ds fdc fd.
     find e c fdc ds e' fd ⇒ find (Proj n i e) c fdc ds (Proj n i e') NONE)
[find_IsEq:]
  (∀e e' n i b c ds fdc fd.
     find e c fdc ds e' fd ⇒ find (IsEq n i b e) c fdc ds (IsEq n i b e') NONE)
[find_Atom:]
  (∀el dsl el' fdc c op fd.
     LENGTH dsl = LENGTH el' ∧
     LIST_REL (λe (ds, e'). find e c fdc ds e' fd) el (ZIP (dsl, el')) ⇒
     find (Prim (AtomOp op) el) c fdc (BIGUNION (set dsl)) (Prim (AtomOp op) el') NONE)
[find_Subset:]
  (∀e e' c ds ds' fdc fdc' fd.
     find e c fdc' ds e' fd
     ∧ (∀ps v. (ps, v) ∈ ds' ⇒ ∃ps'. (ps++ps', v) ∈ ds)
     ∧ fdc' ⊆ fdc
     ⇒ find e c fdc ds' e' fd)
[find_Let:]
  (∀e e' e2 e2' ds ds' c v fdc fdc' fd fd'.
     find e c fdc ds e' fd ∧ find e2 (Bind v e c) fdc' ds' e2' fd'
     ∧ (∀ps. (ps, v) ∉ ds')
     ∧ (∀n argDemands. (n, argDemands) ∈ fdc'
                       ⇒ (n ≠ v ∧ (n, argDemands) ∈ fdc)
                         ∨ (n = v ∧ ∃dset. SOME (argDemands, dset) = fd))
     ∧ (∀l. (l, v) ∉ dest_fd_SND fd')
     ⇒ find (Let v e e2) c fdc ds' (Let v e' e2') fd')
[find_Let2:]
  (∀ e e' e2 e2' ds ds' ds'' c v ps fdc fdc' fd fd'.
     find e c fdc ds e' fd ∧ find e2 (Bind v e c) fdc' ds' e2' fd'
     ∧ (ps,v) ∈ ds'
     ∧ (∀ps' v'. (ps', v') ∈ ds'' ⇒ ((ps', v') ∈ ds' ∧ v' ≠ v) ∨ (ps', v') ∈ ds)
     ∧ (∀n argDemands. (n, argDemands) ∈ fdc'
                       ⇒ (n ≠ v ∧ (n, argDemands) ∈ fdc)
                         ∨ (n = v ∧ ∃dset. SOME (argDemands, dset) = fd))
     ∧ (∀l. (l, v) ∉ dest_fd_SND fd')
     ⇒ find (Let v e e2) c fdc ds'' (Let v e' e2') fd')
[find_Lam:]
  (∀e e' c ds v fdc fd.
     find e (IsFree v c) fdc ds e' fd ∧ (∀argDs. (v, argDs) ∉ fdc)
     ⇒ find (Lam v e) c fdc {} (Lam v e') NONE)
[find_Lams:]
  (∀e e' c ds vl fdc fd.
     find e (FOLDL (λc n. IsFree n c) c vl) fdc ds e' fd
     ∧ EVERY (λv. ∀argDs. (v, argDs) ∉ fdc) vl
     ⇒ find (Lams vl e) c fdc {} (Lams vl e') NONE )
[find_Lams_fd:]
  (∀e e' c ds vl fdc bL.
     find e (FOLDL (λc n. IsFree n c) c vl) fdc ds e' NONE
     ∧ EVERY (λv. ∀argDs. (v, argDs) ∉ fdc) vl
     ∧ bL
     ⇒ find (Lams vl e) c fdc {} (Lams vl e') (SOME (FST (demands_boolList ds vl), {})))
[find_Eq:]
  (∀e1 e2 e3 c fdc ds fd.
     exp_eq_in_ctxt c e1 e2
     ∧ find e2 c fdc ds e3 fd
     ⇒ find e1 c fdc ds e3 fd)
[find_Fail:]
  (∀c fds ds fd. find Fail c fds ds Fail fd)
[find_Letrec:]
  (∀e e' ds ds' c b b' fdc fdc' fd dsL fdL.
     LENGTH b = LENGTH dsL ∧ LENGTH b = LENGTH b' ∧ LENGTH b = LENGTH fdL
     ∧ (∀i. i < LENGTH b
            ⇒ FST (EL i b) = FST (EL i b')
              ∧ find (SND (EL i b)) (RecBind b  c) fdc (EL i dsL) (SND (EL i b')) (EL i fdL)
              ∧ find (SND (EL i b)) (RecBind b' c) fdc  (EL i dsL) (SND (EL i b')) (EL i fdL))
     ∧ find e (RecBind b c) fdc' ds e' fd
     ∧ EVERY (λv. (∀argDs. (v, argDs) ∉ fdc) ∧ (∀ps. (ps, v) ∉ dest_fd_SND fd)) (MAP FST b)
     ∧ (∀v argDs. (v, argDs) ∈ fdc' ⇒
                  (v, argDs) ∈ fdc
                  ∨ (∃i fdSet. FST (EL i b) = v ∧ i < LENGTH b ∧ EL i fdL = SOME (argDs, fdSet)))
     ∧ (∀ps v. (ps, v) ∈ ds'
               ⇒ ¬MEM v (MAP FST b)
                 ∧ ((ps, v) ∈ ds
                    ∨ (∃ps' i. i < LENGTH b ∧ (ps', FST (EL i b)) ∈ ds ∧ (ps, v) ∈ EL i dsL)))
     ∧ ALL_DISTINCT (MAP FST b)
     ⇒ find (Letrec b e) c fdc ds' (Letrec b' e') fd)
[find_Letrec2:]
  (∀e binds c binds2 binds3.
     ALL_DISTINCT (MAP FST binds) ∧
     (∀vname args body. MEM (vname, args, body) binds ⇒
                        ALL_DISTINCT (MAP FST args) ∧
                        DISJOINT (set (MAP FST args)) (set (MAP FST binds)) ∧
                        freevars body ⊆ set (MAP FST binds) ∪ set (MAP FST args) ∧
                        ∃ds ads fs.
                          find_fixpoint binds body Nil ds ads fs ∧
                          (∀v. MEM (v, T) args ⇒ v ∈ ds)) ∧
     binds2 = MAP mk_lams binds ∧
     binds3 = MAP mk_seq_lams binds
     ⇒ find (Letrec binds2 e) c {} {} (Letrec binds3 e) NONE)
End

fun apply_to_first_n 0 tac = ALL_TAC
  | apply_to_first_n n tac = apply_to_first_n (n-1) tac >- tac;

Theorem concat_FOLDL_IsFree:
  ∀vL c1 c2. FOLDL (λc n. IsFree n c) (concat_ctxt c1 c2) vL = concat_ctxt (FOLDL (λc n. IsFree n c) c1 vL) c2
Proof
  Induct >> gvs [GSYM concat_ctxt_def]
QED

Theorem demands_boolList_soundness:
  ∀vL ds ds2 bL. demands_boolList ds vL = (bL, ds2)
                 ⇒ (∀h. MEM h vL ⇔ h ∈ ds2) ∧ LENGTH bL = LENGTH vL
                   ∧ ∀i. i < LENGTH vL ∧ EL i bL ⇒
                         (∃ps. (ps, EL i vL) ∈ ds)
                         ∧  ∀e ps c. e demands ((ps, EL i vL), FOLDL (λc n. IsFree n c) c vL)
                                     ⇒ Lams vL e fdemands ((ps, i), LENGTH vL, c)
Proof
  Induct >> gvs [demands_boolList_def, PAIR] >> rw [] >>
  rename1 ‘demands_boolList ds vL’ >>
  qabbrev_tac ‘p = demands_boolList ds vL’ >> PairCases_on ‘p’ >> gvs [] >>
  last_x_assum $ dxrule_then assume_tac >> gvs [Lams_def]
  >- (eq_tac >> rw [] >> gvs []) >>
  rename1 ‘i < SUC _’ >> Cases_on ‘i’
  >>~[‘0 < SUC _’]
  >- (gvs [] >> first_x_assum $ irule_at Any)
  >- (irule Lam_fdemands >> gvs [GSYM demands_when_applied_0] >>
      dxrule_then assume_tac demands_when_applied_Lams >>
      gvs [])
  >- gvs []
  >- (irule fdemands_Lam >> gvs [])
QED

Theorem find_soundness_lemma:
  ∀e c fdc ds e' fd. find e c fdc ds e' fd
    ⇒ (∀n l i c2. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l ⇒ (Var n) fdemands (([], i), LENGTH l, concat_ctxt c c2))
    ⇒ exp_eq_in_ctxt c e e' ∧ (∀d. d ∈ ds ⇒ e demands (d, c))
      ∧ (∀argDs ds2.
           fd = SOME (argDs, ds2)
           ⇒ (∀i c2. i < LENGTH argDs ∧ EL i argDs ⇒ e fdemands (([], i), LENGTH argDs, concat_ctxt c c2))
             ∧ ∀d2. d2 ∈ ds2 ⇒  e demands_when_applied (d2, LENGTH argDs, c))
Proof
  Induct_on ‘find’
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ gvs [exp_eq_in_ctxt_refl, demands_Var]
  >- (strip_tac \\ strip_tac \\ gs []
      \\ rw []
      >- (irule exp_eq_in_ctxt_trans
          \\ rpt $ first_x_assum $ irule_at Any)
      >- (irule demands_exp_eq
          \\ first_x_assum $ irule_at Any
          \\ gs [exp_eq_in_ctxt_sym])
      >- (irule fdemands_exp_eq
          \\ first_x_assum $ irule_at Any
          \\ gs [exp_eq_in_ctxt_sym]
          \\ irule exp_eq_concat_still_eq
          \\ gs [])
      >- (irule demands_when_applied_exp_eq
          \\ first_x_assum $ irule_at Any
          \\ gs [exp_eq_in_ctxt_sym]))
  >~[‘exp_eq_in_ctxt c e (Seq (Var v) e2)’] (* find_Seq *)
  >- (strip_tac
      \\ strip_tac
      \\ fs []
      \\ first_x_assum $ drule
      \\ strip_tac
      \\ dxrule_then assume_tac $ GEN_ALL demands_empty_Projs
      \\ gvs [demands_def, Projs_def]
      \\ irule exp_eq_in_ctxt_trans \\ pop_assum $ irule_at Any
      \\ gvs [exp_eq_in_ctxt_Prim, exp_eq_in_ctxt_refl])
  >~[‘exp_eq_in_ctxt c (Seq e e2) (Seq e' e2')’] (* find_Seq2 *)
  >- (rw []
      \\ gvs [exp_eq_in_ctxt_Prim, demands_Seq, demands_Seq2, fdemands_Seq,
             demands_when_applied_Seq])
  >~[‘exp_eq_in_ctxt c (If ec et ee) (If ec' et' ee')’]
  >- (rw [] \\ fs [exp_eq_in_ctxt_Prim, demands_If, demands_If2])
  >~[‘_ demands_when_applied (_, 0, _)’]
  >- (rw [] \\ gvs [demands_when_applied_0]
      \\ irule demands_exp_eq
      \\ metis_tac [exp_eq_in_ctxt_sym])
  >~[‘exp_eq_in_ctxt c (App f e) (App f' e')’] (* find_App *)
  >- (rw [] \\ fs [exp_eq_in_ctxt_App, demands_App])
  >>~[‘exp_eq_in_ctxt c (Apps e el') (Apps e' el'')’] (* find_Apps *)
  >- (rw []
      \\ fs [Apps_demands]
      \\ assume_tac exp_eq_in_ctxt_Apps
      \\ irule exp_eq_in_ctxt_Apps
      \\ fs [LIST_REL_EL_EQN] \\ rw []
      \\ rename1 ‘n < LENGTH _’
      \\ first_x_assum $ qspecl_then [‘n’] assume_tac
      \\ metis_tac [])
  >- (rw [] (* find_Apps_fd *)
      >- (irule exp_eq_in_ctxt_Apps
          \\ fs [LIST_REL_EL_EQN] \\ rw []
          \\ rename1 ‘n < LENGTH _’ \\ last_x_assum $ qspecl_then [‘n’] assume_tac
          \\ gvs [EL_ZIP])
      \\ first_x_assum $ dxrule_then assume_tac
      \\ gvs [Apps_demands, LIST_REL_EL_EQN, demands_when_applied_Apps]
      >- (irule fdemands_Apps \\ gvs [Once ADD_SYM]
          \\ first_x_assum irule
          \\ gvs [EL_APPEND_EQN])
      \\ irule demands_when_applied_Apps2
      \\ rename1 ‘i < LENGTH _’ \\ first_x_assum $ qspecl_then [‘i’, ‘Nil’] assume_tac
      \\ gvs [EL_ZIP, EL_APPEND_EQN, concat_Nil]
      \\ first_x_assum $ irule_at Any
      \\ last_x_assum $ drule_then assume_tac \\ gvs []
      \\ irule demands_exp_eq
      \\ rpt $ first_assum $ irule_at $ Pos last)
  >~[‘exp_eq_in_ctxt c (Proj n i e) (Proj n i e')’] (* find_Proj *)
  >- (strip_tac
      \\ fs [exp_eq_in_ctxt_Prim, demands_Proj])
  >~[‘exp_eq_in_ctxt c (IsEq n i _ e) (IsEq n i _ e')’] (* find_IsEq *)
  >- (rw []
      \\ fs [exp_eq_in_ctxt_Prim, demands_IsEq])
  >~[‘exp_eq_in_ctxt c (Prim (AtomOp op) el1) (Prim (AtomOp op) el2)’] (* find_Atom *)
  >- (rw []
      >- (irule exp_eq_in_ctxt_Prim
          \\ fs [LIST_REL_EL_EQN]
          \\ rw []
          \\ rename1 ‘n < LENGTH _’
          \\ first_x_assum $ qspecl_then [‘n’] assume_tac
          \\ gvs [EL_ZIP])
      \\ fs [LIST_REL_EL_EQN, MEM_EL]
      \\ rename1 ‘ds = EL n dsl’
      \\ first_x_assum $ qspecl_then [‘n’] assume_tac
      \\ irule demands_AtomOp
      \\ gvs [EL_ZIP, EXISTS_MEM]
      \\ first_x_assum $ irule_at Any
      \\ fs [EL_MEM])
  >>~[‘exp_eq_in_ctxt c (Prim ope el1) (Prim ope el2)’] (* find_Prim *)
  >- (rw []
      \\ irule exp_eq_in_ctxt_Prim
      \\ rw [LIST_REL_EL_EQN, EL_MAP]
      \\ rename1 ‘EL n _’
      \\ ‘n < LENGTH el1’ by fs []
      \\ first_x_assum drule
      \\ rw [])
  >- (rw [] (* find_Prim1 *)
      >- (irule exp_eq_in_ctxt_Prim
          \\ gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
          \\ rename1 ‘EL n _’
          \\ ‘n < LENGTH el1’ by fs []
          \\ first_x_assum drule
          \\ rw [])
      \\ last_x_assum dxrule
      \\ rw []
      \\ Cases_on ‘el1’
      \\ fs [demands_Prim])
  >~[‘exp_eq_in_ctxt c (Prim ope el1) Fail’] (* find_Prim_Fail *)
  >- (rw []
      \\ fs [exp_eq_IMP_exp_eq_in_ctxt, not_well_written_is_fail])
  >>~[‘exp_eq_in_ctxt c (Let v e e2) (Let v e' e2')’] (* find_Let *)
  >- (rw [exp_eq_in_ctxt_def]
      \\ rename1 ‘find _ (Bind _ _ _) fdc2 _ _ _’
      \\ ‘∀n l i c2.
            (n,l) ∈ fdc2 ∧ i < LENGTH l ∧ EL i l ⇒
            Var n fdemands (([],i),LENGTH l, concat_ctxt (Bind v e c) c2)’
        by (rw [] \\ first_x_assum $ dxrule_then assume_tac
            \\ gvs [fdemands_Bind, fdemands_def, concat_ctxt_def]
            \\ irule fdemands_exp_eq \\ last_x_assum $ irule_at Any
            \\ gvs []
            \\ irule exp_eq_IMP_exp_eq_in_ctxt
            \\ irule $ iffLR exp_eq_sym
            \\ gvs [GEN_ALL Let_Var])
      \\ gvs []
      >- (irule exp_eq_in_ctxt_trans \\ first_x_assum $ irule_at Any
          \\ gvs [exp_eq_in_ctxt_App, exp_eq_in_ctxt_refl])
      >~[‘Let _ _ _ demands (d, c)’]
      >- (PairCases_on ‘d’
          \\ irule demands_Let2
          \\ ‘d1 = v ∨ d1 ≠ v’ by fs []
          \\ gvs [])
      >~[‘Let _ _ _ fdemands _’]
      >- fs [concat_ctxt_def, fdemands_def]
      \\ first_x_assum $ drule_then assume_tac
      \\ rename1 ‘_ demands_when_applied (d2, _, _)’ \\ PairCases_on ‘d2’
      \\ gvs [demands_when_applied_def, eq_when_applied_def, dest_fd_SND_def]
      \\ irule eq_when_applied_trans \\ first_x_assum $ irule_at Any
      \\ irule exp_eq_IMP_eq_when_applied
      \\ irule exp_eq_trans \\ irule_at Any Let_Seq
      \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
      \\ irule Let_not_in_freevars \\ fs [freevars_Projs]
      \\ strip_tac \\ gvs [])
  >- (rw [exp_eq_in_ctxt_def]
      \\ rename1 ‘find _ (Bind _ _ _) fdc2 _ _ _’
      \\ ‘∀n l i c2.
            (n,l) ∈ fdc2 ∧ i < LENGTH l ∧ EL i l ⇒
            Var n fdemands (([],i),LENGTH l, concat_ctxt (Bind v e c) c2)’
        by (rw [] \\ first_x_assum $ dxrule_then assume_tac
            \\ gvs [fdemands_Bind, fdemands_def, concat_ctxt_def]
            \\ irule fdemands_exp_eq \\ last_x_assum $ irule_at Any
            \\ gvs []
            \\ irule exp_eq_IMP_exp_eq_in_ctxt
            \\ irule $ iffLR exp_eq_sym
            \\ gvs [GEN_ALL Let_Var])
      \\ gvs []
      >- (irule exp_eq_in_ctxt_trans
          \\ first_x_assum $ irule_at Any
          \\ fs [exp_eq_in_ctxt_App, exp_eq_in_ctxt_refl])
      >~[‘Let _ _ _ fdemands _’]
      >- fs [fdemands_def, concat_ctxt_def]
      >~[‘Let _ _ _ demands (d, c)’]
      >- (PairCases_on ‘d’
          \\ first_x_assum $ dxrule_then assume_tac
          \\ fs [demands_Let2]
          \\ irule demands_Let1
          \\ first_x_assum $ drule_then assume_tac
          \\ dxrule_then assume_tac demands_empty_Projs \\ fs [])
      \\ first_x_assum $ drule_then assume_tac
      \\ rename1 ‘_ demands_when_applied (d2, _, _)’ \\ PairCases_on ‘d2’
      \\ gvs [demands_when_applied_def, eq_when_applied_def, dest_fd_SND_def]
      \\ irule eq_when_applied_trans \\ first_x_assum $ irule_at Any
      \\ irule exp_eq_IMP_eq_when_applied
      \\ irule exp_eq_trans \\ irule_at Any Let_Seq
      \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
      \\ irule Let_not_in_freevars \\ fs [freevars_Projs]
      \\ strip_tac \\ gvs [])
  >~[‘SOME (T::argD, ds3)’]
  >- (rw [] \\ gvs [exp_eq_in_ctxt_App, demands_App, fdemands_App, demands_when_applied_App]
      >- (rw [Once $ GSYM concat_Nil]
          \\ irule fdemands_0_App_demands
          \\ last_assum $ irule_at Any \\ gvs [concat_Nil]
          \\ irule_at Any demands_exp_eq
          \\ first_x_assum $ dxrule_then assume_tac
          \\ pop_assum $ irule_at Any \\ gvs []))
  >~[‘SOME (b::argD, ds3)’]
  >- (rw [] \\ gvs [exp_eq_in_ctxt_App, demands_App, fdemands_App, demands_when_applied_App])
  >~[‘SOME (bL, fd)’]
  >- (rw [] \\ gvs [SUBSET_DEF])
  >~ [‘exp_eq_in_ctxt c e1 e2 ∧ find _ _ _ _ _ _ ∧ _’] (* find_Eq *)
  >- (rw [] >> gvs []
      >- (irule exp_eq_in_ctxt_trans >> rpt $ first_x_assum $ irule_at Any)
      >- (irule demands_exp_eq >>
          last_x_assum $ dxrule_then $ irule_at Any >>
          gvs [exp_eq_in_ctxt_sym])
      >- (irule fdemands_exp_eq >>
          last_x_assum $ dxrule_then $ irule_at Any >>
          gvs [exp_eq_in_ctxt_sym, exp_eq_concat_still_eq]) >>
      irule demands_when_applied_exp_eq >>
      last_x_assum $ dxrule_then $ irule_at Any >>
      gvs [exp_eq_in_ctxt_sym, exp_eq_concat_still_eq])
  >- (rw [] \\ dxrule_then (dxrule_then assume_tac) fdemands_subset (* find_Subset *)
      \\ gvs []
      \\ rename1 ‘e demands (d, c)’ \\ PairCases_on ‘d’
      \\ gvs []
      \\ first_x_assum $ drule_then assume_tac \\ fs []
      \\ first_x_assum $ drule_then assume_tac
      \\ drule demands_Projs_reduce
      \\ fs [])
  >- (rw [] \\ dxrule_then assume_tac fdemands_set_IsFree  (* find_Lam *)
      \\ pop_assum $ dxrule_then assume_tac
      \\ last_x_assum $ dxrule_then assume_tac
      \\ gvs [exp_eq_in_ctxt_Lam])
  >- (rw [] \\ dxrule_then (dxrule_then assume_tac) fdemands_set_FOLDL_IsFree
      \\ gvs [exp_eq_in_ctxt_Lams])
  >- (rw [] \\ dxrule_then (dxrule_then assume_tac) fdemands_set_FOLDL_IsFree
      \\ gvs [exp_eq_in_ctxt_Lams]
      \\ rename1 ‘demands_boolList ds vL’
      \\ qabbrev_tac ‘p = demands_boolList ds vL’ \\ PairCases_on ‘p’ \\ gvs []
      \\ dxrule_then assume_tac demands_boolList_soundness
      \\ gvs [] \\ first_x_assum $ drule_then $ dxrule_then assume_tac \\ gvs []
      \\ first_x_assum irule \\ irule demands_empty_Projs
      \\ gvs [concat_FOLDL_IsFree]
      \\ irule_at Any demands_concat
      \\ last_x_assum $ dxrule_then $ irule_at Any)
  >~[‘Fail demands _’]
  >- (gvs [demands_when_applied_def, FORALL_PROD, demands_Fail, fdemands_Fail] >> rw [] >>
      irule exp_eq_IMP_eq_when_applied >>
      irule no_err_eval_IMP_exp_eq >>
      rw [subst_def, no_err_eval_def, v_unfold, eval_wh_thm])
  >~[‘exp_eq_in_ctxt c (Letrec (MAP mk_lams binds) e1) (Letrec _ e2)’]
  >- (strip_tac
      \\ irule exp_eq_IMP_exp_eq_in_ctxt
      \\ irule Letrec_mk_seq_lams
      \\ gs [exp_eq_refl]
      \\ irule IMP_obligation_fixpoint
      \\ gs []
      \\ rpt gen_tac \\ strip_tac
      \\ last_x_assum $ dxrule_then irule)
  >~[‘exp_eq_in_ctxt c (Letrec b1 e1) (Letrec b2 e2)’]
  >- (strip_tac \\ strip_tac \\ gvs [EVERY_CONJ]
      \\ dxrule_then assume_tac fdemands_set_RecBind
      \\ first_assum   $ qspecl_then [‘b2’] assume_tac
      \\ first_x_assum $ qspecl_then [‘b1’] assume_tac
      \\ gvs [exp_eq_in_ctxt_def, fdemands_def, concat_ctxt_def]
      \\ ‘∀n l i c2. (n, l) ∈ fdc' ∧ i < LENGTH l ∧ EL i l
                            ⇒ Letrec b1 (Var n) fdemands (([], i), LENGTH l, concat_ctxt c c2)’
        by (rw [] \\ first_x_assum $ dxrule_then assume_tac
            \\ gvs [concat_ctxt_def, fdemands_def]
            \\ irule fdemands_exp_eq
            \\ irule_at Any exp_eq_IMP_exp_eq_in_ctxt
            \\ irule_at Any $ iffLR exp_eq_sym
            \\ rename1 ‘FST (EL i2 _)’
            \\ qexists_tac ‘Letrec b1 (SND (EL i2 b1))’
            \\ last_x_assum $ drule_then assume_tac
            \\ gvs [GSYM fdemands_def]
            \\ irule exp_eq_trans
            \\ irule_at Any Letrec_unfold
            \\ gvs [exp_eq_refl])
      \\ ‘MAP FST b1 = MAP FST b2’
        by (irule LIST_EQ >> rw [EL_MAP] >>
            last_x_assum $ drule_then assume_tac >>
            rename1 ‘FST p1 = FST p2’ >> PairCases_on ‘p1’ >> PairCases_on ‘p2’ >> gvs [])
      \\ conj_tac
      >- (irule exp_eq_in_ctxt_Letrec
          \\ gvs [LIST_REL_EL_EQN, exp_eq_in_ctxt_def, concat_ctxt_def, fdemands_def]
          \\ rw [] \\ last_x_assum $ drule_then assume_tac
          \\ rename1 ‘n < _’
          \\ qabbrev_tac ‘p1 = EL n b1’ \\ PairCases_on ‘p1’
          \\ qabbrev_tac ‘p2 = EL n b2’ \\ PairCases_on ‘p2’ \\ gvs [])
      \\ rw [] \\ gvs [fdemands_def, concat_ctxt_def]
      >~[‘Letrec _ _ demands (d, _)’]
      >- (PairCases_on ‘d’
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gvs [demands_Letrec]
          \\ irule demands_Letrec2 \\ gvs []
          \\ first_assum $ irule_at Any
          \\ last_x_assum $ drule_then assume_tac \\ gvs []
          \\ last_x_assum $ drule_then assume_tac
          \\ drule_then irule demands_empty_Projs)
      >- (irule demands_when_applied_Letrec >>
          gvs [EVERY_MEM, dest_fd_SND_def] >>
          strip_tac >> rpt $ last_x_assum $ drule_then assume_tac >>
          rename1 ‘d2 ∈ _’ >> PairCases_on ‘d2’ >> gvs []))
QED

Theorem find_soundness:
  find e Nil {} ds e' fd ⇒ e ≈ e'
Proof
  rw []
  \\ dxrule find_soundness_lemma
  \\ fs [exp_eq_in_ctxt_def]
QED

(*
  let foo = lam (a + 2) in
    lam x (foo x)
-->
  let foo = lam a (seq a (a + 2)) in
    lam x (foo x)
-->
  let foo = lam a (seq a (a + 2)) in
    lam x (seq x (foo x))

  Letrec [(f,x)] rest
*)

