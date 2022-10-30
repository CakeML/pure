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

Definition allvars_of_def[simp]:
  allvars_of (pure_cexp$Var c v) =
    {explode v} ∧
  allvars_of (Lam c ns x) =
    set (MAP explode ns) UNION allvars_of x ∧
  allvars_of (Letrec c xs y) =
    set (MAP (explode o FST) xs) UNION
    BIGUNION (set (MAP (allvars_of o SND) xs)) UNION
    allvars_of y ∧
  allvars_of (Prim c p xs) =
    BIGUNION (set (MAP allvars_of xs)) ∧
  allvars_of (App c x ys) =
    allvars_of x UNION
    BIGUNION (set (MAP allvars_of ys)) ∧
  allvars_of (Let c n x y) =
    {explode n} UNION allvars_of x UNION allvars_of y ∧
  allvars_of (Case c x n ys eopt) =
    {explode n} UNION
    BIGUNION (set (MAP (allvars_of o SND o SND) ys)) UNION
    allvars_of x UNION
      (case eopt of
       | NONE => {}
       | SOME (a,e) => allvars_of e) ∧
  allvars_of (NestedCase c g gv p e pes) =
    {explode gv} UNION
    BIGUNION (set (MAP (allvars_of o SND) pes)) UNION
    allvars_of e UNION allvars_of g
Termination
  WF_REL_TAC `measure $ cexp_size (K 0)`
End

Theorem allvars_Lams:
  ∀vs x. allvars (Lams vs x) = set vs UNION allvars x
Proof
  Induct \\ fs [Lams_def,EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
QED

Theorem allvars_Apps:
  ∀xs x. allvars (Apps x xs) = BIGUNION (set (MAP allvars xs)) UNION allvars x
Proof
  Induct \\ fs [Apps_def,EXTENSION] \\ metis_tac []
QED

Theorem allovars_of:
  ∀x. allvars_of x = allvars (exp_of x)
Proof
  ho_match_mp_tac allvars_of_ind
  \\ rw [exp_of_def,allvars_Lams,allvars_Apps]
  \\ fs [MAP_MAP_o,o_DEF,UNCURRY]
  >-
   (rename [‘MEM _ xs’] \\ Induct_on ‘xs’ \\ gvs [SF DNF_ss]
    \\ rw [] \\ gvs [] \\ gvs [EXTENSION] \\ metis_tac [])
  >-
   (rename [‘MEM _ xs’] \\ Induct_on ‘xs’ \\ gvs [SF DNF_ss]
    \\ rw [] \\ gvs [] \\ gvs [EXTENSION] \\ metis_tac [])
  >-
   (rename [‘MEM _ xs’] \\ Induct_on ‘xs’ \\ gvs [SF DNF_ss]
    \\ rw [] \\ gvs [] \\ gvs [EXTENSION] \\ metis_tac [])
  >- (rw [] \\ gvs [] \\ gvs [EXTENSION] \\ metis_tac [])
  \\ cheat
QED

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
