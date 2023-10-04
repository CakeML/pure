(*
  Proof of correctness for the thunk_to_env compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pred_setTheory rich_listTheory thunkLang_primitivesTheory envLangTheory
     finite_mapTheory thunkLangTheory env_semanticsTheory thunk_semanticsTheory;
open thunk_to_envTheory thunk_to_env_1ProofTheory thunk_exp_ofTheory;
open pure_miscTheory thunkLangPropsTheory thunk_cexpTheory thunk_to_envTheory;

val _ = new_theory "thunk_to_envProof";

val _ = set_grammar_ancestry ["thunk_to_env", "thunk_to_env_1Proof", "thunk_exp_of"]

Triviality exp_rel_Disj:
  ∀xs x. exp_rel [] (Disj x xs) (Disj x xs)
Proof
  Induct \\ fs [Disj_def,FORALL_PROD,envLangTheory.Disj_def] \\ rw []
  \\ rpt (irule_at Any exp_rel_If \\ fs [])
  \\ rpt (irule_at Any exp_rel_Prim \\ fs [])
  \\ rpt (irule_at Any exp_rel_Var \\ fs [])
QED

Triviality op_of_op_to_env[simp]:
  op_of (op_to_env op) = op_of op
Proof
  Cases_on `op` >> rw[op_to_env_def, op_of_def]
QED

Theorem to_env_exp_of:
  ∀x. cexp_wf x ⇒ exp_rel [] (exp_of x) (exp_of (to_env x))
Proof
  ho_match_mp_tac to_env_ind \\ rw [cexp_wf_def] \\ fs []
  >~ [‘Var’] >-
   (fs [to_env_def]
    \\ irule exp_rel_Var \\ fs [])
  >~ [‘Let’] >-
   (fs [to_env_def]
    \\ Cases_on ‘opt’ \\ fs []
    >- (irule exp_rel_Let_NONE \\ fs [])
    \\ irule exp_rel_Let_SOME \\ fs [])
  >~ [‘Lam’] >-
   (last_x_assum mp_tac \\ fs [to_env_def]
    \\ qid_spec_tac ‘vs’ \\ Induct
    \\ fs [env_cexpTheory.Lams_def] \\ rw [] \\ fs []
    \\ irule exp_rel_Lam \\ fs [])
  >~ [‘App’] >-
   (fs [to_env_def]
    \\ qpat_x_assum ‘EVERY _ _’ mp_tac
    \\ last_x_assum mp_tac
    \\ last_x_assum mp_tac
    \\ last_x_assum mp_tac
    \\ qid_spec_tac ‘x’
    \\ qid_spec_tac ‘xs’
    \\ Induct
    \\ fs [env_cexpTheory.Apps_def] \\ rw [] \\ fs [SF DNF_ss]
    \\ ‘cexp_wf (App x [h])’ by fs [cexp_wf_def]
    \\ last_x_assum drule
    \\ fs [to_env_def,env_cexpTheory.Apps_def]
    \\ disch_then irule
    \\ irule exp_rel_App
    \\ gs [])
  >~ [‘Delay’] >-
   (fs [to_env_def] \\ irule exp_rel_Delay \\ fs [cexp_wf_def])
  >~ [‘Force’] >-
   (fs [to_env_def] \\ irule exp_rel_Force \\ fs [cexp_wf_def])
  >~ [‘Letrec’] >-
   (fs [to_env_def] \\ irule exp_rel_Letrec \\ fs [cexp_wf_def]
    \\ fs [GSYM MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF]
    \\ fs [LIST_REL_MAP_MAP,LAMBDA_PROD]
    \\ fs [FORALL_PROD,SF SFY_ss,EVERY_MEM])
  >~ [‘Case’] >-
   (fs [to_env_def]
    \\ qpat_x_assum ‘_ ≠ []’ kall_tac
    \\ qpat_x_assum ‘~(MEM _ _)’ kall_tac
    \\ Induct_on ‘rows’ \\ fs []
    >-
     (fs [rows_of_def,envLangTheory.rows_of_def]
      \\ Cases_on ‘d’ \\ fs []
      >- simp [Once exp_rel_cases]
      \\ pairarg_tac \\ fs []
      \\ strip_tac
      \\ irule_at Any exp_rel_If \\ gvs [exp_rel_Disj]
      \\ simp [Once exp_rel_cases])
    \\ PairCases \\ simp [SF DNF_ss, SF CONJ_ss, AND_IMP_INTRO]
    \\ rw [] \\ fs []
    \\ fs [rows_of_def,envLangTheory.rows_of_def]
    \\ irule exp_rel_If \\ fs []
    \\ conj_tac
    >-
     (irule_at Any exp_rel_Prim \\ fs []
      \\ irule_at Any exp_rel_Var \\ fs [])
    \\ reverse conj_tac
    >- (first_x_assum irule \\ fs [SF SFY_ss])
    \\ qspec_tac (‘LENGTH h1’,‘l’)
    \\ qspec_tac (‘(MAPi (λi v. (i,v)) (MAP explode h1))’,‘xs’)
    \\ Induct \\ fs [FORALL_PROD]
    \\ fs [lets_for_def,envLangTheory.lets_for_def]
    \\ rw []
    \\ irule exp_rel_Let_NONE
    \\ irule_at Any exp_rel_Let_SOME \\ fs []
    \\ irule_at Any exp_rel_Prim \\ fs []
    \\ irule_at Any exp_rel_Var \\ fs []
    \\ irule_at Any exp_rel_If \\ fs []
    \\ irule_at Any exp_rel_Prim \\ fs []
    \\ irule_at Any exp_rel_Var \\ fs []
    \\ rpt (irule_at Any exp_rel_Prim \\ fs []))
  >~ [`Prim`]
  >- (
    gvs[to_env_def] >> irule exp_rel_Prim >>
    gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EVERY_EL, EL_MAP]
    )
  >~ [`Monad`]
  >- (
    gvs[to_env_def] >> Cases_on `mop` >> gvs[exp_of_def] >>
    gvs[pure_configTheory.num_mop_args_def, LENGTH_EQ_NUM_compute, get_arg_def] >>
    simp[Once exp_rel_cases]
    )
QED

Theorem to_env_semantics:
  cexp_wf x ∧ closed (exp_of x) ⇒
  itree_of (exp_of x) =
  itree_of (exp_of (to_env x))
Proof
  rw [thunk_semanticsTheory.itree_of_def,env_semanticsTheory.itree_of_def]
  \\ imp_res_tac to_env_exp_of
  \\ drule_all exp_rel_semantics \\ fs []
QED

Theorem IMP_env_cexp_wf:
  thunk_exp_of$cexp_wf x ⇒
  envLang$cexp_wf (to_env x) ∧
  cns_arities (to_env x) ⊆ cns_arities x
Proof
  qid_spec_tac ‘x’
  \\ ho_match_mp_tac to_env_ind
  \\ rpt conj_tac \\ rpt gen_tac
  \\ fs [to_env_def,cexp_wf_def,
         thunk_cexpTheory.cns_arities_def,
         env_cexpTheory.cns_arities_def]
  >- (rw [] \\ gvs [SUBSET_DEF])
  >~ [‘Lams’] >-
   (strip_tac
    \\ strip_tac \\ pop_assum kall_tac
    \\ Induct_on ‘vs’ \\ fs [env_cexpTheory.Lams_def,cexp_wf_def]
    \\ fs [to_env_def,cexp_wf_def,
           thunk_cexpTheory.cns_arities_def,
           env_cexpTheory.cns_arities_def])
  >~ [‘Apps’] >-
   (strip_tac
    \\ strip_tac \\ pop_assum kall_tac \\ fs [SF ETA_ss]
    \\ rpt $ pop_assum mp_tac
    \\ qid_spec_tac ‘x’
    \\ Induct_on ‘xs’ \\ fs [env_cexpTheory.Apps_def,cexp_wf_def]
    \\ fs [to_env_def,cexp_wf_def,SF DNF_ss,
           thunk_cexpTheory.cns_arities_def,
           env_cexpTheory.cns_arities_def]
    \\ rw [] \\ fs []
    \\ rpt $ last_x_assum $ qspec_then ‘App x [h]’ mp_tac
    \\ fs [to_env_def,env_cexpTheory.Apps_def]
    \\ fs [to_env_def,cexp_wf_def,SF DNF_ss,
           thunk_cexpTheory.cns_arities_def,
           env_cexpTheory.cns_arities_def]
    \\ fs [SUBSET_DEF]
    \\ metis_tac [])
  >-
   (Cases_on ‘fs = []’ \\ fs []
    \\ pop_assum kall_tac
    \\ fs [MAP_REVERSE] \\ Induct_on ‘fs’ \\ fs [SF DNF_ss,FORALL_PROD]
    \\ rw [] \\ rpt $ first_x_assum irule
    \\ fs [] \\ fs [SUBSET_DEF]
    \\ fs [MEM_MAP,FORALL_PROD,EVERY_MEM,EXISTS_PROD]
    \\ gvs [SF SFY_ss,PULL_EXISTS]
    >-
     (rename [‘cexp_ok_bind pp’] \\ Cases_on ‘pp’ \\ fs [cexp_ok_bind_def]
      \\ fs [to_env_def]
      \\ fs [cexp_wf_def] \\ rename [‘Lams l’] \\ Cases_on ‘l’
      \\ fs [env_cexpTheory.Lams_def])
    >- metis_tac [])
  >- (strip_tac \\ strip_tac \\ fs []
      \\ rpt $ conj_tac
      >- (fs [EVERY_EL, EL_MAP, MEM_EL, PULL_EXISTS]
          \\ rw []
          \\ first_x_assum $ drule_then assume_tac
          \\ first_x_assum $ drule_then assume_tac
          \\ first_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs [])
      >- (CASE_TAC \\ fs []
          \\ CASE_TAC
          \\ fs [EVERY_MEM, DISJOINT_ALT, MEM_MAP, PULL_EXISTS, FORALL_PROD]
          \\ rw []
          \\ first_x_assum $ dxrule_then assume_tac
          \\ simp [])
      >- (gs [DISJOINT_ALT, MEM_MAP, PULL_EXISTS, FORALL_PROD]
          \\ rw []
          \\ first_x_assum $ drule_then assume_tac
          \\ fs [])
      >- (CASE_TAC
          >- fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
          \\ CASE_TAC
          \\ fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM])
      >- fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
      >- (CASE_TAC \\ fs []
          >- simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
          \\ CASE_TAC \\ fs []
          \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
          \\ irule SUBSET_TRANS
          \\ first_x_assum $ irule_at Any
          \\ simp [SUBSET_DEF])
      >- (fs [EVERY_MEM, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS]
          \\ rw []
          \\ last_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs []
          \\ last_x_assum $ drule_then assume_tac
          \\ gs []
          \\ irule SUBSET_TRANS
          \\ first_x_assum $ irule_at Any
          \\ rw [SUBSET_DEF, MEM_MAP]
          \\ disj2_tac
          \\ first_assum $ irule_at Any
          \\ first_assum $ irule_at Any
          \\ simp []))
  >~ [`op_to_env p`]
  >- (
    Cases_on `p` >> gvs[op_to_env_def, args_ok_def]
    >- (
      rw[] >- gvs[EVERY_MAP, EVERY_MEM] >>
      gvs[SUBSET_DEF, MEM_MAP, PULL_EXISTS] >> rw[] >> disj2_tac >>
      first_x_assum drule >> gvs[EVERY_MEM] >> rw[] >>
      pop_assum drule >> rw[SF SFY_ss]
      )
    >- (
      rw[] >> gvs[pure_configTheory.num_atomop_args_ok_def]
      >- gvs[EVERY_MAP, EVERY_MEM] >>
      gvs[SUBSET_DEF, MEM_MAP, PULL_EXISTS] >> rw[] >>
      first_x_assum drule >> gvs[EVERY_MEM] >> rw[] >>
      pop_assum drule >> rw[SF SFY_ss]
      )
    ) >>
  Cases_on `mop` >> gvs[] >>
  gvs[pure_configTheory.num_mop_args_def, LENGTH_EQ_NUM_compute] >>
  ntac 2 strip_tac >> gvs[get_arg_def, env_cexpTheory.cns_arities_def] >>
  gvs[SF DNF_ss, SUBSET_DEF]
QED

val _ = export_theory ();
