(*
  Correctness for compilation that inserts names for Lam NONE and
  replaces HandleApp by a Handle and an App.
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open state_names_1ProofTheory state_cexpTheory mlstringTheory state_namesTheory;

val _ = new_theory "state_namesProof";

val _ = set_grammar_ancestry ["state_names", "state_names_1Proof", "stateLang"];

Triviality LESS_EQ_list_max:
  ∀xs n. n ≤ list_max xs ⇔ n = 0 ∨ ∃x. MEM x xs ∧ n ≤ x
Proof
  Induct \\ fs [list_max_def]
  \\ metis_tac []
QED

Theorem give_names_freevars:
  ∀x e n.
    give_names x = (e,n) ⇒
    ∀v. v IN freevars (exp_of x) ⇒ max_name (implode v) ≤ n
Proof
  ho_match_mp_tac give_names_ind \\ rpt strip_tac
  >~ [‘Var’] >-
   (gvs [give_names_def])
  >~ [‘Raise’] >-
   (gvs [give_names_def] \\ pairarg_tac \\ fs [])
  >~ [‘Lam’] >-
   (gvs [give_names_def] \\ pairarg_tac \\ gvs [AllCaseEqs()])
  >~ [‘Let’] >-
   (gvs [give_names_def] \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()]))
  >~ [‘Handle’] >-
   (gvs [give_names_def] \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()]))
  >~ [‘HandleApp’] >-
   (gvs [give_names_def] \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()]))
  >~ [‘If’] >-
   (gvs [give_names_def] \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()]))
  >~ [‘App’] >-
   (gvs [give_names_def,MEM_MAP,LESS_EQ_list_max,PULL_EXISTS,EXISTS_PROD]
    \\ metis_tac [PAIR])
  >~ [‘Letrec’] >-
   (gvs [give_names_def,MEM_MAP,LESS_EQ_list_max,PULL_EXISTS,EXISTS_PROD]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ gvs [give_names_def,MEM_MAP,LESS_EQ_list_max,PULL_EXISTS,EXISTS_PROD]
    \\ res_tac \\ fs [] \\ metis_tac [PAIR])
  >~ [‘Case’] >-
   (gvs [give_names_def,MEM_MAP,LESS_EQ_list_max,PULL_EXISTS,EXISTS_PROD]
    \\ gvs [AllCaseEqs()]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ gvs [give_names_def,MEM_MAP,LESS_EQ_list_max,PULL_EXISTS,EXISTS_PROD]
    \\ metis_tac [LESS_EQ_REFL,PAIR])
QED

Triviality isStringThere_aux_lemma:
  ∀xs ts ys.
    LENGTH xs ≤ LENGTH ys ⇒
    (isStringThere_aux (strlit (ts ++ xs)) (strlit (ts ++ ys))
        (LENGTH ts) (LENGTH ts) (STRLEN xs) ⇔
     isStringThere_aux (strlit xs) (strlit ys) 0 0 (STRLEN xs))
Proof
  Induct \\ fs [isStringThere_aux_def]
  \\ gen_tac \\ gen_tac
  \\ Cases \\ fs []
  \\ strip_tac \\ fs [EL_LENGTH_APPEND]
  \\ rename [‘LENGTH xs ≤ LENGTH ys’]
  \\ last_x_assum drule \\ strip_tac
  \\ last_assum $ qspec_then ‘[h]’ mp_tac
  \\ last_x_assum $ qspec_then ‘ts ++ [h]’ mp_tac
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ fs [] \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ Cases_on ‘h = h'’ \\ fs []
QED

Theorem isPrefix_thm:
  isPrefix s t ⇔ isPREFIX (explode s) (explode t)
Proof
  fs [isPrefix_def]
  \\ Cases_on ‘s’ \\ Cases_on ‘t’ \\ fs []
  \\ rename [‘LENGTH xs ≤ LENGTH ys’]
  \\ Cases_on ‘LENGTH ys < LENGTH xs’ \\ fs []
  >-
   (CCONTR_TAC \\ fs []
    \\ imp_res_tac rich_listTheory.IS_PREFIX_LENGTH \\ fs [])
  \\ fs [NOT_LESS]
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘ys’
  \\ qid_spec_tac ‘xs’
  \\ Induct
  \\ fs [isStringThere_aux_def]
  \\ strip_tac \\ Cases \\ fs []
  \\ Cases_on ‘h = h'’ \\ fs []
  \\ gvs [] \\ rw []
  \\ last_x_assum $ drule_then $ rewrite_tac o single o GSYM
  \\ drule isStringThere_aux_lemma
  \\ disch_then $ qspec_then ‘[h]’ mp_tac
  \\ fs []
QED

Theorem max_name_make_name:
  n < max_name (make_name n)
Proof
  fs [make_name_def,max_name_def,isPrefix_thm]
  \\ fs [concat_def]
QED

Theorem compile_rel_give_names:
  ∀x e n.
    give_names x = (e,n) ⇒
    compile_rel (exp_of x) (exp_of e)
Proof
  ho_match_mp_tac give_names_ind \\ rpt strip_tac
  >~ [‘Var’] >-
   (gvs [give_names_def]
    \\ simp [Once compile_rel_cases])
  >~ [‘Let’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases]
    \\ CCONTR_TAC \\ fs []
    \\ drule_all give_names_freevars
    \\ fs [GSYM NOT_LESS,max_name_make_name])
  >~ [‘Lam’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases]
    \\ CCONTR_TAC \\ fs []
    \\ drule_all give_names_freevars
    \\ fs [GSYM NOT_LESS,max_name_make_name])
  >~ [‘Handle’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases])
  >~ [‘HandleApp’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases]
    \\ CCONTR_TAC \\ fs []
    \\ drule_all give_names_freevars
    \\ fs [GSYM NOT_LESS,max_name_make_name])
  >~ [‘If’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases])
  >~ [‘Raise’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases])
  >~ [‘App’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases,MAP_MAP_o]
    \\ simp [pure_miscTheory.LIST_REL_MAP_MAP]
    \\ simp [EVERY_MEM] \\ rw []
    \\ Cases_on ‘give_names x’ \\ fs [])
  >~ [‘Letrec’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases]
    \\ Induct_on ‘fs’ \\ fs [SF DNF_ss,FORALL_PROD]
    \\ rw [] \\ fs [UNCURRY]
    \\ rpt $ last_x_assum drule
    \\ fs [] \\ rw []
    \\ simp [Once compile_rel_cases,MAP_MAP_o]
    \\ Cases_on ‘give_names p_2’ \\ fs [])
  >~ [‘Case’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ gvs [AllCaseEqs()]
    \\ simp [Once compile_rel_cases]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ Induct_on ‘rows’ \\ fs [SF DNF_ss,FORALL_PROD]
    \\ rw [] \\ fs [UNCURRY]
    \\ rpt $ last_x_assum drule
    \\ fs [] \\ rw []
    \\ rename [‘give_names pp’]
    \\ Cases_on ‘give_names pp’ \\ fs [])
QED

Theorem itree_of_give_all_names:
  itree_of (exp_of e1) ---> itree_of (exp_of (give_all_names e1))
Proof
  fs [give_all_names_def]
  \\ Cases_on ‘give_names e1’
  \\ drule_then assume_tac compile_rel_give_names
  \\ drule compile_rel_itree_of \\ fs []
QED


Theorem give_all_names_cexp_wf:
  cexp_wf x ⇒
  cexp_wf (give_all_names x) ∧
  cns_arities (give_all_names x) ⊆ cns_arities x
Proof
  cheat
QED


val _ = export_theory ();
