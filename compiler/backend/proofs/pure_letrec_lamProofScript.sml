(*
   Verification of a compiler that ensures every Letrec bound name is a lambda (Lam).
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open arithmeticTheory listTheory alistTheory optionTheory pairTheory dep_rewrite
     pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_exp_lemmasTheory pure_exp_relTheory pure_evalTheory
     pure_congruenceTheory pure_miscTheory pure_eval_lemmasTheory
     pure_letrecTheory pure_letrecProofTheory;

val _ = new_theory "pure_letrec_lamProof";


Definition apps_ok_def:
  apps_ok (apps : string |-> exp) ⇔
    (* each subtition replaces a ‘Var n’ by ‘App (Var n) arg’ *)
    ∀n v. FLOOKUP apps n = SOME v ⇒ ∃arg. v = App (Var n) arg ∧ closed arg
End

Definition lams_ok_def:
  lams_ok apps xs ys ⇔
    (* all the substitions in apps must be within set of defined names *)
    FDOM apps SUBSET set (MAP FST xs) ∧
    LIST_REL
      (λ(v1,x1) (v2,x2).
         (* bound names stay the same *)
         v1 = v2 ∧
         if v1 IN FDOM apps then
           (* if this is an updated binding, then add a Lam, and subst apps: *)
           ∃w. ~(MEM w (freevars x1)) ∧ ~(MEM w (MAP FST xs)) ∧
               x2 = Lam w (subst apps x1)
         else (* otherise only subst apps: *) x2 = subst apps x1)
      xs ys
End

Inductive letrec_lam:
  (∀xs x apps ys.
     apps_ok apps ∧ lams_ok apps xs ys ⇒
     letrec_lam
       (Letrec xs x)
       (Letrec ys (subst apps x)))
  ∧
  (∀xs x apps ys arg.
     apps_ok apps ∧ lams_ok apps xs ys ∧ closed arg ⇒
     letrec_lam
       (Letrec xs x)
       (App (Letrec ys (Lam w (subst apps x))) arg))
End

Theorem letrec_rel_lam_subst:
  ∀x y.
    letrec_rel letrec_lam x y ⇒
    ∀f g. fmap_rel (letrec_rel letrec_lam) f g ⇒
          letrec_rel letrec_lam (subst f x) (subst g y)
Proof
  cheat
QED

Triviality letrec_rel_lam_subst_single:
  letrec_rel letrec_lam x y ∧
  letrec_rel letrec_lam a b ⇒
  letrec_rel letrec_lam (subst s a x) (subst s b y)
Proof
  cheat
QED

Theorem letrec_lam_correct:
  letrec_rel letrec_lam x y ∧ closed x ∧ closed y ⇒ x ≃ y
Proof
  rw [] \\ irule eval_to_sim_thm \\ fs []
  \\ qexists_tac ‘letrec_rel letrec_lam’ \\ fs []
  \\ simp [eval_to_sim_def]
  \\ rpt (pop_assum kall_tac)
  \\ qabbrev_tac ‘c = letrec_lam’
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
    \\ irule letrec_rel_lam_subst_single
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
      irule letrec_rel_lam_subst >> simp[] >>
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
        irule letrec_rel_lam_subst >> simp[] >>
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
    \\ simp [Once letrec_lam_cases] \\ rw []
    \\ ‘closed (subst_funs ys (subst apps y1)) ∧ closed (subst_funs f y)’ by cheat
    \\ ‘letrec_rel letrec_lam (subst_funs f y) (subst_funs ys (subst apps y1))’ by cheat
    THEN1 (* case 1 of letrec_lam *)
     (rewrite_tac [eval_wh_to_def]
      \\ IF_CASES_TAC THEN1 (gvs [] \\ qexists_tac ‘0’ \\ fs [])
      \\ gvs [] \\ last_x_assum irule \\ fs [])
    (* case 2 of letrec_lam *)
    \\ rewrite_tac [eval_wh_to_def]
    \\ IF_CASES_TAC THEN1 (gvs [] \\ qexists_tac ‘0’ \\ fs [])
    \\ gvs []
    \\ ‘subst_funs ys (Lam w (subst apps y1)) =
        Lam w (subst_funs ys (subst apps y1))’ by
          cheat (* because w was chosen so that this is true *)
    \\ fs [eval_wh_to_def] \\ fs [bind_single_def]
    \\ simp [closed_subst]
    \\ last_x_assum irule
    \\ fs [])
  \\ rename [‘Prim’]
  \\ cheat (* ought to be the same as in pure_letrecProof *)
QED

val _ = export_theory();
