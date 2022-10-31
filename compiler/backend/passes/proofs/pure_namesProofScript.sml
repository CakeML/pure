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
    \\ ‘BIGUNION (set (MAP (λx. set (MAP explode (FST (SND x)))) ys)) =
        set (MAP explode (FLAT (MAP (λx. FST (SND x)) ys)))’ by
     (fs [EXTENSION,MEM_MAP,MEM_FLAT,FORALL_PROD,EXISTS_PROD,PULL_EXISTS]
      \\ rw [] \\ eq_tac \\ strip_tac
      \\ qpat_x_assum ‘MEM _ _’ $ irule_at Any
      >- metis_tac []
      \\ rw []
      \\ qexists_tac ‘IMAGE explode $ set l’ \\ fs [])
    \\ asm_rewrite_tac []
    \\ fs [EXTENSION,MEM_MAP,MEM_FLAT,PULL_EXISTS,EXISTS_PROD,FORALL_PROD]
    \\ rw [] \\ eq_tac \\ rw [] \\ fs []
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

Theorem pure_names_ok:
  vars_ok (pure_names e)
Proof
  fs [pure_names_def,SIMP_RULE std_ss [] extract_names_thm]
QED

Theorem pure_names_eq_allvars:
  set_of (pure_names e) = allvars_of e
Proof
  fs [pure_names_def,SIMP_RULE std_ss [] extract_names_thm]
QED

val _ = export_theory();
