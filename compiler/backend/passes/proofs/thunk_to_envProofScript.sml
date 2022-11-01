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
    \\ fs [Lams_def] \\ rw [] \\ fs []
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
    \\ fs [Apps_def] \\ rw [] \\ fs [SF DNF_ss]
    \\ ‘cexp_wf (App x [h])’ by fs [cexp_wf_def]
    \\ last_x_assum drule
    \\ fs [to_env_def,Apps_def]
    \\ disch_then irule
    \\ irule exp_rel_App
    \\ gs [])
  >~ [‘Delay’] >-
   (fs [to_env_def] \\ irule exp_rel_Delay \\ fs [cexp_wf_def])
  >~ [‘Force’] >-
   (fs [to_env_def] \\ irule exp_rel_Force \\ fs [cexp_wf_def])
  >~ [‘Box’] >-
   (fs [to_env_def] \\ irule exp_rel_Box \\ fs [cexp_wf_def])
  >~ [‘Letrec’] >-
   (fs [to_env_def] \\ irule exp_rel_Letrec \\ fs [cexp_wf_def]
    \\ fs [GSYM MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF]
    \\ fs [LIST_REL_MAP_MAP,LAMBDA_PROD]
    \\ fs [FORALL_PROD,SF SFY_ss,EVERY_MEM])
  >~ [‘Case’] >-
   (fs [to_env_def]
    \\ qpat_x_assum ‘d = NONE ⇒ _’ kall_tac
    \\ qpat_x_assum ‘~(MEM _ _)’ kall_tac
    \\ Induct_on ‘rows’ \\ fs []
    >-
     (fs [rows_of_def,envLangTheory.rows_of_def]
      \\ Cases_on ‘d’ \\ fs []
      >- simp [Once exp_rel_cases]
      \\ rename [‘x = (_,_)’]
      \\ PairCases_on ‘x’ \\ fs []
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
  \\ rename [‘Prim’]
  \\ reverse (Cases_on ‘p’)
  >-
   (fs [to_env_def]
    \\ irule exp_rel_Prim
    \\ last_x_assum mp_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [])
  \\ fs [to_env_def,SF ETA_ss]
  \\ fs [args_ok_def]
  \\ rw [] \\ fs [get_arg_def,to_env_def,SF DNF_ss]
  \\ irule exp_rel_Prim \\ fs [] \\ gvs []
  \\ Induct_on ‘xs’ \\ fs []
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
    \\ Induct_on ‘vs’ \\ fs [Lams_def,cexp_wf_def]
    \\ fs [to_env_def,cexp_wf_def,
           thunk_cexpTheory.cns_arities_def,
           env_cexpTheory.cns_arities_def])
  >~ [‘Apps’] >-
   (strip_tac
    \\ strip_tac \\ pop_assum kall_tac \\ fs [SF ETA_ss]
    \\ rpt $ pop_assum mp_tac
    \\ qid_spec_tac ‘x’
    \\ Induct_on ‘xs’ \\ fs [Apps_def,cexp_wf_def]
    \\ fs [to_env_def,cexp_wf_def,SF DNF_ss,
           thunk_cexpTheory.cns_arities_def,
           env_cexpTheory.cns_arities_def]
    \\ rw [] \\ fs []
    \\ rpt $ last_x_assum $ qspec_then ‘App x [h]’ mp_tac
    \\ fs [to_env_def,Apps_def]
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
    \\ cheat (* cexp_wf needs ok_bind *))
  >- cheat
  \\ Cases_on ‘∃m. p = Cons m’
  >-
   (rw [] \\ fs [args_ok_def]
    \\ gvs [get_arg_def,remove_Delay_def,to_env_def,SF DNF_ss]
    \\ gvs [env_cexpTheory.cns_arities_def,SUBSET_DEF,cns_arities_def]
    \\ rw [] \\ fs [MEM_MAP,EVERY_MEM,PULL_EXISTS,get_arg_def,to_env_def,remove_Delay_def]
    \\ gvs [env_cexpTheory.cns_arities_def,SUBSET_DEF,cns_arities_def,SF DNF_ss,to_env_def]
    \\ gvs [EVAL “monad_cns”,MEM_MAP]
    \\ Cases_on ‘m’ \\ fs []
    \\ metis_tac [])
  \\ Cases_on ‘p’ \\ fs []
  \\ gvs [env_cexpTheory.cns_arities_def,SUBSET_DEF,cns_arities_def,MEM_MAP,PULL_EXISTS]
  \\ rewrite_tac [AND_IMP_INTRO]
  \\ strip_tac
  \\ Cases_on ‘∃m. a = Message m’ \\ fs []
  >- gvs [args_ok_def,pure_configTheory.num_atomop_args_ok_def,LENGTH_EQ_NUM_compute]
  \\ fs [args_ok_def]
  \\ qpat_x_assum ‘num_atomop_args_ok _ _’ kall_tac
  \\ Induct_on ‘xs’ \\ fs [SF DNF_ss]
  \\ rewrite_tac [AND_IMP_INTRO]
  \\ rpt gen_tac \\ strip_tac \\ gvs []
  \\ metis_tac []
QED

val _ = export_theory ();
