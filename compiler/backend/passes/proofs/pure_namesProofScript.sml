(*
   Verification of functions in pure_namesTheory
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open listTheory pairTheory alistTheory pred_setTheory finite_mapTheory
     sptreeTheory arithmeticTheory combinTheory;
open pure_miscTheory pure_expTheory pure_cexpTheory pureLangTheory
     var_setTheory pure_exp_lemmasTheory pure_cexp_lemmasTheory
     pure_namesTheory;

val _ = set_grammar_ancestry
  ["pure_names", "pure_exp", "pure_cexp", "var_set", "pureLang"];

val _ = new_theory "pure_namesProof";

Theorem extract_names_thm:
  (∀s (x:'a cexp) t.
    extract_names s x = t ∧
    vars_ok s ⇒
    vars_ok t ∧ set_of t = allvars_of x UNION set_of s) ∧
  (∀s (xs: 'a cexp list) t.
    extract_names_list s xs = t ∧
    vars_ok s ⇒
    vars_ok t ∧ set_of t = BIGUNION (set (MAP allvars_of xs)) UNION set_of s)
Proof
  ho_match_mp_tac extract_names_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  >~ [‘Var’] >-
   (gvs [extract_names_def,exp_of_def] \\ fs [EXTENSION])
  >~ [‘Lam’] >-
   (gvs [extract_names_def,exp_of_def]
    \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ fs [])
  >~ [‘Let’] >-
   (gvs [extract_names_def,exp_of_def]
    \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ fs [])
  >~ [‘App’] >-
   (gvs [extract_names_def,exp_of_def,SF ETA_ss]
    \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
    \\ metis_tac [])
  >~ [‘Prim’] >-
   (gvs [extract_names_def,exp_of_def,SF ETA_ss]
    \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
    \\ metis_tac [])
  >~ [‘Letrec’] >-
   (gvs [extract_names_def,exp_of_def,SF ETA_ss]
    \\ strip_tac \\ gvs [MAP_MAP_o,o_DEF]
    \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
    \\ metis_tac [])
  >~ [‘Case _ _ _ _ opt’] >-
   (gen_tac \\ gvs [extract_names_def,exp_of_def,SF ETA_ss,AllCaseEqs()]
    \\ strip_tac \\ gvs []
    \\ gvs [MAP_MAP_o,o_DEF]
    \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
    \\ metis_tac [])
  >~ [‘NestedCase’] >-
   (gvs [extract_names_def,exp_of_def,SF ETA_ss]
    \\ strip_tac \\ gvs [MAP_MAP_o,o_DEF]
    \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
    \\ metis_tac [])
  >~ [‘extract_names_list s []’] >-
   gvs [extract_names_def,exp_of_def]
  >~ [‘extract_names_list s (x::xs)’]
  \\ gvs [extract_names_def,exp_of_def]
  \\ strip_tac \\ gvs []
  \\ fs [EXTENSION] \\ metis_tac []
QED

Theorem all_names_ok:
  vars_ok (all_names e)
Proof
  fs [all_names_def,SIMP_RULE std_ss [] extract_names_thm]
QED

Theorem all_names_eq_allvars:
  set_of (all_names e) = allvars (exp_of e)
Proof
  fs [all_names_def,SIMP_RULE std_ss [] extract_names_thm, allovars_of]
QED

val _ = export_theory();
