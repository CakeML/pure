(*
  Correctness for compilation that pushes applications to Unit as far in as possible,
  e.g. ‘(Let x = ... in foo) Unit’ becomes ‘Let x = ... in (foo Unit)’.
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory state_cexpTheory
     stateLangTheory state_app_unit_1ProofTheory state_app_unit_2ProofTheory
     state_app_unitTheory;
local open pure_semanticsTheory in end

val _ = new_theory "state_app_unitProof";

val _ = set_grammar_ancestry ["state_app_unit", "stateLang",
  "state_cexp", "state_app_unit_1Proof", "state_app_unit_2Proof"];

Inductive cexp1_rel:

[~App_Lam:]
  (cexp1_rel x y ⇒
   cexp1_rel (app (Lam NONE x) Unit) y)

[~App_Let:]
  (cexp1_rel x x1 ∧ cexp1_rel y y1 ⇒
   cexp1_rel (app (Let x_opt x y) Unit)
             (Let x_opt x1 (app y1 Unit)))

[~App_If:]
  (cexp1_rel x x1 ∧ cexp1_rel y y1 ∧ cexp1_rel z z1 ⇒
   cexp1_rel (app (If x y z) Unit)
             (If x1 (app y1 Unit) (app z1 Unit)))

[~App_Letrec:]
  (cexp1_rel y y1 ∧
   MAP FST tfns = MAP FST sfns ∧
   MAP (FST o SND) tfns = MAP (FST o SND) sfns ∧
   LIST_REL cexp1_rel (MAP (SND o SND) tfns) (MAP (SND o SND) sfns) ⇒
   cexp1_rel (app (Letrec tfns y) Unit)
             (Letrec sfns (app y1 Unit)))

[~Var:]
  cexp1_rel (state_cexp$Var v) (state_cexp$Var v)

[~Lam:]
  (cexp1_rel x y ⇒
  cexp1_rel (Lam ov x) (Lam ov y))

[~Raise:]
  (cexp1_rel x y ⇒
  cexp1_rel (Raise x) (Raise y))

[~Handle:]
  (cexp1_rel x1 y1 ∧ cexp1_rel x2 y2 ⇒
  cexp1_rel (Handle x1 v x2) (Handle y1 v y2))

[~HandleApp:]
  (cexp1_rel x1 y1 ∧ cexp1_rel x2 y2 ⇒
  cexp1_rel (HandleApp x1 x2) (HandleApp y1 y2))

[~App:]
  (LIST_REL (cexp1_rel) xs ys ⇒
  cexp1_rel (App op xs) (App op ys))

[~Letrec:]
  (∀tfns sfns te se.
    MAP FST tfns = MAP FST sfns ∧
    MAP (FST o SND) tfns = MAP (FST o SND) sfns ∧
    LIST_REL cexp1_rel (MAP (SND o SND) tfns) (MAP (SND o SND) sfns) ∧
    cexp1_rel te se ⇒
    cexp1_rel (Letrec tfns te) (Letrec sfns se))

[~Let:]
  (cexp1_rel te1 se1 ∧
   cexp1_rel te2 se2 ⇒
  cexp1_rel (Let x_opt te1 te2) (Let x_opt se1 se2))

[~If:]
  (cexp1_rel te se ∧
   cexp1_rel te1 se1 ∧
   cexp1_rel te2 se2 ⇒
  cexp1_rel (If te te1 te2) (If se se1 se2))

[~Case:]
  (∀v te se tes ses.
     OPTREL (λ(a,x) (b,y). a = b ∧ cexp1_rel x y) te se ∧
     MAP FST tes = MAP FST ses ∧
     MAP (FST o SND) tes = MAP (FST o SND) ses ∧
     LIST_REL cexp1_rel (MAP (SND o SND) tes) (MAP (SND o SND) ses) ⇒
  cexp1_rel (Case v tes te) (Case v ses se))

End

Overload rel1 = “state_app_unit_1Proof$compile_rel”
Overload rel2 = “state_app_unit_2Proof$compile_rel”

Triviality LIST_REL_rel2_rel1:
  ∀xs zs.
    LIST_REL (λx z. cexp1_rel x z ∧ ∃y. rel2 (exp_of x) y ∧ rel1 y (exp_of z)) xs zs ⇒
    ∃ys. LIST_REL rel2 (MAP exp_of xs) ys ∧ LIST_REL rel1 ys (MAP exp_of zs)
Proof
  Induct \\ Cases_on ‘zs’ \\ fs [PULL_EXISTS]
  \\ rw [] \\ res_tac \\ fs [] \\ metis_tac []
QED

Theorem cexp1_rel_thm:
  ∀x z. cexp1_rel x z ⇒ ∃y. rel2 (exp_of x) y ∧ rel1 y (exp_of z)
Proof
  Induct_on ‘cexp1_rel’ \\ rpt strip_tac \\ simp []
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_App_Lam \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_App \\ fs []
    \\ once_rewrite_tac [state_app_unit_2ProofTheory.compile_rel_cases] \\ simp []
    \\ first_x_assum $ irule_at Any \\ fs [])
  >-
   (irule_at Any state_app_unit_2ProofTheory.compile_rel_App_Let \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_Let \\ fs []
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_App \\ fs []
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_App \\ fs []
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_Let_Var \\ fs []
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_App_Lam \\ fs [])
  >-
   (irule_at Any state_app_unit_2ProofTheory.compile_rel_App_If \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs [])
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_If \\ fs []
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_Let_Var \\ fs []
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_App_Lam \\ fs []
    \\ rpt (irule_at Any state_app_unit_1ProofTheory.compile_rel_App \\ fs []))
  >-
   (irule_at Any state_app_unit_2ProofTheory.compile_rel_App_Letrec \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs [])
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_Letrec \\ fs []
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY,EVERY_MAP]
    \\ rpt (irule_at Any state_app_unit_1ProofTheory.compile_rel_App \\ fs [])
    \\ drule_all LIST_REL_rel2_rel1
    \\ strip_tac
    \\ qexists_tac ‘MAP2 (λ(n,v,_) y. (explode n,Lam (SOME (explode v)) y)) sfns ys’
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ rpt (pop_assum mp_tac)
    \\ qid_spec_tac ‘tfns’
    \\ qid_spec_tac ‘sfns’
    \\ qid_spec_tac ‘ys’
    \\ Induct \\ Cases_on ‘sfns’ \\ Cases_on ‘tfns’ \\ fs []
    \\ PairCases_on ‘h’ \\ PairCases_on ‘h'’ \\ fs []
    \\ strip_tac \\ rpt $ disch_then assume_tac \\ fs []
    \\ once_rewrite_tac [state_app_unit_2ProofTheory.compile_rel_cases] \\ simp []
    \\ once_rewrite_tac [state_app_unit_1ProofTheory.compile_rel_cases] \\ simp []
    \\ first_x_assum drule_all \\ fs [])
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_Var \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_Var \\ fs [])
  >-
   (qexists_tac ‘Lam (OPTION_MAP explode ov) y’
    \\ once_rewrite_tac [state_app_unit_2ProofTheory.compile_rel_cases] \\ simp []
    \\ once_rewrite_tac [state_app_unit_1ProofTheory.compile_rel_cases] \\ simp [])
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_Raise \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_Raise \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs []))
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_Handle \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_Handle \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs []))
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_HandleApp \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_HandleApp \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs []))
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_App \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_App \\ fs []
    \\ drule_all LIST_REL_rel2_rel1 \\ rpt strip_tac
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs []))
  >-
   (drule_all LIST_REL_rel2_rel1 \\ rpt strip_tac
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_Letrec \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_Letrec \\ fs []
    \\ rpt $ first_x_assum $ irule_at $ Any
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ qexists_tac ‘MAP (λ((x,y,_),z). (explode x,Lam (SOME (explode y)) z)) (ZIP (tfns,ys))’
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
    \\ rpt (pop_assum mp_tac)
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘tfns’
    \\ qid_spec_tac ‘sfns’
    \\ Induct \\ Cases_on ‘tfns’ \\ Cases_on ‘ys’ \\ gvs []
    \\ CONV_TAC $ DEPTH_CONV ETA_CONV \\ fs []
    \\ PairCases_on ‘h’ \\ PairCases \\ fs []
    \\ strip_tac \\ rpt $ disch_then assume_tac \\ fs []
    \\ once_rewrite_tac [state_app_unit_2ProofTheory.compile_rel_cases] \\ simp []
    \\ once_rewrite_tac [state_app_unit_1ProofTheory.compile_rel_cases] \\ simp []
    \\ first_x_assum drule_all \\ fs [])
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_Let \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_Let \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs []))
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_If \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_If \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs []))
  \\ drule_all LIST_REL_rel2_rel1 \\ rpt strip_tac
  \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_Case \\ fs []
  \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_Case \\ fs []
  \\ ‘∃tt. OPTREL (λ(a,x) (b,y). a = b ∧ rel2 x y)
             (OPTION_MAP (λ(alts,e). (MAP (explode ## I) alts,exp_of e)) te) tt ∧
           OPTREL (λ(a,x) (b,y). a = b ∧ rel1 x y) tt
             (OPTION_MAP (λ(alts,e). (MAP (explode ## I) alts,exp_of e)) se)’ by
   (Cases_on ‘te’ \\ Cases_on ‘se’ \\ gvs []
    \\ gvs [UNCURRY]
    \\ Q.REFINE_EXISTS_TAC ‘SOME (_,_)’
    \\ fs [] \\ rpt $ first_x_assum $ irule_at Any)
  \\ pop_assum $ irule_at Any
  \\ pop_assum $ irule_at Any
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
  \\ qexists_tac ‘MAP (λ((x,y,_),z). (explode x,MAP explode y,z)) (ZIP (tes,ys))’
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
  \\ rpt (pop_assum mp_tac)
  \\ qid_spec_tac ‘ys’
  \\ qid_spec_tac ‘tes’
  \\ qid_spec_tac ‘ses’
  \\ Induct \\ Cases_on ‘tes’ \\ Cases_on ‘ys’ \\ gvs []
  \\ CONV_TAC $ DEPTH_CONV ETA_CONV \\ fs []
  \\ rw []
  \\ qpat_x_assum ‘MAP FST t = MAP FST ses’ mp_tac
  \\ qpat_x_assum ‘MAP _ t = MAP _ ses’ mp_tac
  \\ qid_spec_tac ‘t’
  \\ qid_spec_tac ‘ses’
  \\ Induct \\ Cases_on ‘t’ \\ gvs [FORALL_PROD]
  \\ TRY (gen_tac \\ Cases \\ gvs [] \\ NO_TAC)
  \\ TRY (gen_tac \\ gen_tac \\ Cases \\ gvs [] \\ NO_TAC)
QED

Theorem cexp1_rel_correct:
  ∀x y. cexp1_rel x y ⇒ itree_of (exp_of x) = itree_of (exp_of y)
Proof
  rw [] \\ drule cexp1_rel_thm \\ rw []
  \\ imp_res_tac state_app_unit_2ProofTheory.compile_rel_itree_of
  \\ imp_res_tac state_app_unit_1ProofTheory.compile_rel_itree_of
  \\ simp []
QED

Theorem cexp1_rel_refl[simp]:
  ∀x. cexp1_rel x x
Proof
  ho_match_mp_tac exp_of_ind \\ rw []
  \\ simp [Once cexp1_rel_cases]
  \\ rpt disj2_tac
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac ‘funs’
  \\ qid_spec_tac ‘rows’
  \\ qid_spec_tac ‘xs’ \\ fs []
  >- (Induct \\ fs [FORALL_PROD] \\ metis_tac [])
  >- (Induct \\ fs [FORALL_PROD] \\ metis_tac [])
  \\ reverse Induct \\ fs [FORALL_PROD]
  >- metis_tac []
  \\ Cases_on ‘d’ \\ fs []
  \\ PairCases_on ‘x’ \\ fs []
QED

Triviality cexp1_rel_eq: (* TODO: delete *)
  x = y ⇒ cexp1_rel x y
Proof
  rw [] \\ fs []
QED

Theorem cexp1_rel_cexp_wwf:
  ∀x y. cexp1_rel x y ⇒ (cexp_wwf x ⇒ cexp_wwf y) ∧ cns_arities y ⊆ cns_arities x
Proof
  Induct_on ‘cexp1_rel’ \\ rpt strip_tac
  \\ gs [cexp_wwf_def, cns_arities_def]
  >- fs [SUBSET_DEF]
  >- fs [SUBSET_DEF]
  >- fs [SUBSET_DEF]
  >- (gs [EVERY_EL, LIST_REL_EL_EQN, EL_MAP]
      \\ rw []
      \\ first_x_assum $ drule_then assume_tac
      \\ first_x_assum $ drule_then assume_tac
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs [])
  >- (simp [BIGUNION_SUBSET, MEM_EL, EL_MAP, PULL_EXISTS]
      \\ reverse conj_tac
      >- gs [SUBSET_DEF]
      \\ gs [LIST_REL_EL_EQN]
      \\ rw []
      \\ first_x_assum $ drule_then assume_tac
      \\ gs [EL_MAP]
      \\ pairarg_tac \\ fs []
      \\ irule SUBSET_TRANS
      \\ first_x_assum $ irule_at Any
      \\ simp [SUBSET_DEF, MEM_EL]
      \\ rw []
      \\ disj1_tac
      \\ disj1_tac
      \\ first_assum $ irule_at Any
      \\ first_assum $ irule_at Any
      \\ simp [EL_MAP]
      \\ pairarg_tac \\ fs [])
  >- fs [SUBSET_DEF]
  >- fs [SUBSET_DEF]
  >- gs [EVERY_EL, LIST_REL_EL_EQN, EL_MAP]
  >- (conj_tac
      >- (drule_then assume_tac LIST_REL_LENGTH
          \\ CASE_TAC \\ simp [])
      \\ gs [LIST_REL_EL_EQN, SUBSET_DEF, MEM_EL, PULL_EXISTS, EL_MAP]
      \\ rw []
      \\ disj2_tac
      \\ first_assum $ irule_at Any
      \\ first_x_assum $ drule_then assume_tac
      \\ fs [EL_MAP])
  >- (gs [EVERY_EL, LIST_REL_EL_EQN, EL_MAP]
      \\ rw []
      \\ first_x_assum $ drule_then assume_tac
      \\ first_x_assum $ drule_then assume_tac
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs [])
  >- (reverse conj_tac
      >- fs [SUBSET_DEF]
      \\ gs [LIST_REL_EL_EQN, SUBSET_DEF, MEM_EL, PULL_EXISTS, EL_MAP]
      \\ rw []
      \\ disj1_tac
      \\ first_assum $ irule_at Any
      \\ first_x_assum $ drule_then assume_tac
      \\ fs [EL_MAP]
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs [])
  >- fs [SUBSET_DEF]
  >- fs [SUBSET_DEF]
  >- (conj_tac
      >- (strip_tac \\ fs [])
      \\ simp [CONJ_ASSOC]
      \\ conj_tac
      >- (rename1 ‘OPTREL _ te se’
          \\ Cases_on ‘te’ \\ fs [OPTREL_def]
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs []
          \\ gs [])
      \\ gs [EVERY_EL, LIST_REL_EL_EQN]
      \\ rw []
      \\ first_x_assum $ drule_then assume_tac
      \\ first_x_assum $ drule_then assume_tac
      \\ qpat_x_assum ‘MAP (FST o SND) _ = MAP _ _’ mp_tac
      \\ once_rewrite_tac [GSYM LIST_REL_eq]
      \\ strip_tac
      \\ dxrule_then assume_tac $ iffLR LIST_REL_EL_EQN
      \\ gs [EL_MAP]
      \\ pop_assum $ drule_then assume_tac
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs [])
  >- (conj_tac
      >- (CASE_TAC \\ fs [OPTREL_def]
          >- (disj1_tac
              \\ AP_TERM_TAC
              \\ irule LIST_EQ
              \\ qpat_x_assum ‘MAP FST _ = MAP _ _’ mp_tac
              \\ qpat_x_assum ‘MAP (FST o SND) _ = MAP _ _’ mp_tac
              \\ once_rewrite_tac [GSYM LIST_REL_eq]
              \\ strip_tac
              \\ dxrule_then assume_tac $ iffLR LIST_REL_EL_EQN
              \\ strip_tac
              \\ dxrule_then assume_tac $ iffLR LIST_REL_EL_EQN
              \\ gs [EL_MAP]
              \\ rw []
              \\ first_x_assum $ drule_then assume_tac
              \\ first_x_assum $ drule_then assume_tac
              \\ pairarg_tac \\ fs []
              \\ pairarg_tac \\ fs [])
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs []
          \\ conj_tac
          >- (disj1_tac \\ disj1_tac
              \\ AP_TERM_TAC \\ AP_TERM_TAC
              \\ irule LIST_EQ
              \\ qpat_x_assum ‘MAP FST _ = MAP _ _’ mp_tac
              \\ qpat_x_assum ‘MAP (FST o SND) _ = MAP _ _’ mp_tac
              \\ once_rewrite_tac [GSYM LIST_REL_eq]
              \\ strip_tac
              \\ dxrule_then assume_tac $ iffLR LIST_REL_EL_EQN
              \\ strip_tac
              \\ dxrule_then assume_tac $ iffLR LIST_REL_EL_EQN
              \\ gs [EL_MAP]
              \\ rw []
              \\ first_x_assum $ drule_then assume_tac
              \\ first_x_assum $ drule_then assume_tac
              \\ pairarg_tac \\ fs []
              \\ pairarg_tac \\ fs [])
          \\ fs [SUBSET_DEF])
      \\ fs [LIST_REL_EL_EQN, SUBSET_DEF, MEM_EL]
      \\ rw []
      \\ disj2_tac \\ gs []
      \\ first_x_assum $ drule_then assume_tac
      \\ first_assum $ irule_at Any
      \\ irule_at Any EQ_REFL
      \\ gs [EL_MAP]
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs [])
QED

Inductive cexp_rel:

[~refl:]
  (cexp_rel x x)

[~trans:]
  (cexp_rel x y ∧ cexp_rel y z ⇒ cexp_rel x z)

[~App_Lam:]
  (cexp_rel x y ⇒
   cexp_rel (app (Lam NONE x) Unit) y)

[~App_Let:]
  (cexp_rel x x1 ∧ cexp_rel y y1 ⇒
   cexp_rel (app (Let x_opt x y) Unit)
             (Let x_opt x1 (app y1 Unit)))

[~App_If:]
  (cexp_rel x x1 ∧ cexp_rel y y1 ∧ cexp_rel z z1 ⇒
   cexp_rel (app (If x y z) Unit)
             (If x1 (app y1 Unit) (app z1 Unit)))

[~App_Letrec:]
  (cexp_rel y y1 ∧
   MAP FST tfns = MAP FST sfns ∧
   MAP (FST o SND) tfns = MAP (FST o SND) sfns ∧
   LIST_REL cexp_rel (MAP (SND o SND) tfns) (MAP (SND o SND) sfns) ⇒
   cexp_rel (app (Letrec tfns y) Unit)
             (Letrec sfns (app y1 Unit)))

[~Var:]
  cexp_rel (state_cexp$Var v) (state_cexp$Var v)

[~Lam:]
  (cexp_rel x y ⇒
  cexp_rel (Lam ov x) (Lam ov y))

[~Raise:]
  (cexp_rel x y ⇒
  cexp_rel (Raise x) (Raise y))

[~Handle:]
  (cexp_rel x1 y1 ∧ cexp_rel x2 y2 ⇒
  cexp_rel (Handle x1 v x2) (Handle y1 v y2))

[~HandleApp:]
  (cexp_rel x1 y1 ∧ cexp_rel x2 y2 ⇒
  cexp_rel (HandleApp x1 x2) (HandleApp y1 y2))

[~App:]
  (LIST_REL (cexp_rel) xs ys ⇒
  cexp_rel (App op xs) (App op ys))

[~Letrec:]
  (∀tfns sfns te se.
    MAP FST tfns = MAP FST sfns ∧
    MAP (FST o SND) tfns = MAP (FST o SND) sfns ∧
    LIST_REL cexp_rel (MAP (SND o SND) tfns) (MAP (SND o SND) sfns) ∧
    cexp_rel te se ⇒
    cexp_rel (Letrec tfns te) (Letrec sfns se))

[~Let:]
  (cexp_rel te1 se1 ∧
   cexp_rel te2 se2 ⇒
  cexp_rel (Let x_opt te1 te2) (Let x_opt se1 se2))

[~If:]
  (cexp_rel te se ∧
   cexp_rel te1 se1 ∧
   cexp_rel te2 se2 ⇒
  cexp_rel (If te te1 te2) (If se se1 se2))

[~Case:]
  (∀v te se tes ses.
     OPTREL (λ(a,x) (b,y). a = b ∧ cexp_rel x y) te se ∧
     MAP FST tes = MAP FST ses ∧
     MAP (FST o SND) tes = MAP (FST o SND) ses ∧
     LIST_REL cexp_rel (MAP (SND o SND) tes) (MAP (SND o SND) ses) ⇒
  cexp_rel (Case v tes te) (Case v ses se))

End

Triviality NRC_refl:
  NRC cexp1_rel n x x
Proof
  Induct_on ‘n’ \\ fs [NRC]
  \\ irule_at Any cexp1_rel_eq \\ fs []
QED

Theorem LIST_REL_NRC_0:
  ∀xs ys. LIST_REL (NRC R 0) xs ys ⇔ xs = ys
Proof
  Induct \\ Cases_on ‘ys’ \\ fs []
QED

Theorem LIST_REL_NRC_SUC:
  ∀xs ys. LIST_REL (NRC R (SUC n)) xs ys ⇔
          ∃zs. LIST_REL R xs zs ∧ LIST_REL (NRC R n) zs ys
Proof
  Induct \\ Cases_on ‘ys’ \\ fs []
  \\ rw [] \\ eq_tac \\ rw []
  \\ fs [PULL_EXISTS,NRC]
  \\ metis_tac []
QED

Theorem LIST_REL_NRC:
  ∀n R. LIST_REL (NRC R n) = NRC (LIST_REL R) n
Proof
  simp [FUN_EQ_THM] \\ Induct
  \\ fs [LIST_REL_NRC_0,LIST_REL_NRC_SUC,NRC]
QED

Triviality NRC_Let:
  ∀k x x1 y y1.
    NRC cexp1_rel k x x1 ∧ NRC cexp1_rel k y y1 ⇒
    NRC cexp1_rel k (Let x_opt x y) (Let x_opt x1 y1)
Proof
  Induct \\ fs [NRC,PULL_EXISTS] \\ rw []
  \\ irule_at Any cexp1_rel_Let
  \\ rpt $ last_x_assum $ irule_at Any
QED

Triviality NRC_Handle:
  ∀k x x1 y y1.
    NRC cexp1_rel k x x1 ∧ NRC cexp1_rel k y y1 ⇒
    NRC cexp1_rel k (Handle x n y) (Handle x1 n y1)
Proof
  Induct \\ fs [NRC,PULL_EXISTS] \\ rw []
  \\ irule_at Any cexp1_rel_Handle
  \\ rpt $ last_x_assum $ irule_at Any
QED

Triviality NRC_HandleApp:
  ∀k x x1 y y1.
    NRC cexp1_rel k x x1 ∧ NRC cexp1_rel k y y1 ⇒
    NRC cexp1_rel k (HandleApp x y) (HandleApp x1 y1)
Proof
  Induct \\ fs [NRC,PULL_EXISTS] \\ rw []
  \\ irule_at Any cexp1_rel_HandleApp
  \\ rpt $ last_x_assum $ irule_at Any
QED

Triviality NRC_If:
  ∀k x x1 y y1 z z1.
    NRC cexp1_rel k x x1 ∧ NRC cexp1_rel k y y1 ∧ NRC cexp1_rel k z z1 ⇒
    NRC cexp1_rel k (If x y z) (If x1 y1 z1)
Proof
  Induct \\ fs [NRC,PULL_EXISTS] \\ rw []
  \\ irule_at Any cexp1_rel_If
  \\ rpt $ last_x_assum $ irule_at Any
QED

Triviality NRC_Lam:
  ∀k z z1.
    NRC cexp1_rel k z z1 ⇒
    NRC cexp1_rel k (Lam y z) (Lam y z1)
Proof
  Induct \\ fs [NRC,PULL_EXISTS] \\ rw []
  \\ irule_at Any cexp1_rel_Lam
  \\ rpt $ last_x_assum $ irule_at Any
QED

Triviality NRC_Raise:
  ∀k z z1.
    NRC cexp1_rel k z z1 ⇒
    NRC cexp1_rel k (Raise z) (Raise z1)
Proof
  Induct \\ fs [NRC,PULL_EXISTS] \\ rw []
  \\ irule_at Any cexp1_rel_Raise
  \\ rpt $ last_x_assum $ irule_at Any
QED

Triviality NRC_App:
  ∀k xs ys.
    LIST_REL (NRC cexp1_rel k) xs ys ⇒
    NRC cexp1_rel k (App f xs) (App f ys)
Proof
  Induct \\ fs [NRC,PULL_EXISTS]
  \\ rw [LIST_REL_NRC_0,LIST_REL_NRC_SUC]
  \\ last_x_assum $ irule_at Any
  \\ last_x_assum $ irule_at Any
  \\ irule cexp1_rel_App \\ fs []
QED

Triviality NRC_Letrec:
  ∀k xs ys x y.
    MAP FST xs = MAP FST ys ∧
    MAP (FST ∘ SND) xs = MAP (FST ∘ SND) ys ∧
    LIST_REL (NRC cexp1_rel k) (MAP (SND o SND) xs) (MAP (SND o SND) ys) ∧
    NRC cexp1_rel k x y ⇒
    NRC cexp1_rel k (Letrec xs x) (Letrec ys y)
Proof
  Induct \\ fs [NRC,PULL_EXISTS]
  \\ rw [LIST_REL_NRC_0,LIST_REL_NRC_SUC]
  >-
   (rpt $ pop_assum mp_tac
    \\ qid_spec_tac ‘xs’
    \\ qid_spec_tac ‘ys’
    \\ Induct \\ Cases_on ‘xs’ \\ fs [FORALL_PROD])
  \\ last_x_assum $ irule_at Any
  \\ irule_at Any cexp1_rel_Letrec \\ fs []
  \\ pop_assum $ irule_at Any \\ fs []
  \\ qexists_tac ‘MAP (λ((m,n,_),y).(m,n,y)) (ZIP (xs,zs))’
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac ‘xs’
  \\ qid_spec_tac ‘ys’
  \\ qid_spec_tac ‘zs’
  \\ Induct \\ Cases_on ‘xs’ \\ Cases_on ‘ys’ \\ fs [FORALL_PROD]
  \\ fs [UNCURRY]
  \\ metis_tac []
QED

Triviality NRC_Case:
  ∀k x x1 xs xs1.
    OPTREL (λ(a,x) (b,x1). a = b ∧ NRC cexp1_rel k x x1) x x1 ∧
    MAP FST xs = MAP FST xs1 ∧
    MAP (FST o SND) xs = MAP (FST o SND) xs1 ∧
    LIST_REL (NRC cexp1_rel k) (MAP (SND o SND) xs) (MAP (SND o SND) xs1) ⇒
    NRC cexp1_rel k (Case v xs x) (Case v xs1 x1)
Proof
  Induct \\ fs [NRC,PULL_EXISTS] \\ rw []
  >-
   (rpt $ pop_assum mp_tac
    \\ qid_spec_tac ‘xs’
    \\ qid_spec_tac ‘xs1’
    \\ Induct \\ Cases_on ‘xs’ \\ fs [FORALL_PROD])
  >-
   (Cases_on ‘x’ \\ Cases_on ‘x1’ \\ fs []
    \\ Cases_on ‘x’ \\ Cases_on ‘x'’ \\ fs [])
  \\ last_x_assum $ irule_at Any
  \\ irule_at Any cexp1_rel_Case
  \\ ‘∃tt. OPTREL (λ(a,x) (b,y). a = b ∧ cexp1_rel x y) x tt ∧
           OPTREL (λ(a,x) (b,x1). a = b ∧ NRC cexp1_rel k x x1) tt x1’ by
   (Cases_on ‘x’ \\ Cases_on ‘x1’ \\ fs []
    \\ Cases_on ‘x’ \\ Cases_on ‘x'’ \\ gvs []
    \\ Q.REFINE_EXISTS_TAC ‘SOME (_,_)’ \\ fs []
    \\ first_x_assum $ irule_at Any \\ fs [])
  \\ pop_assum $ irule_at Any
  \\ pop_assum $ irule_at Any
  \\ fs [LIST_REL_NRC_SUC]
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
  \\ qexists_tac ‘MAP (λ((n,m,_),z). (n,m,z)) (ZIP (xs,zs))’
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac ‘xs’
  \\ qid_spec_tac ‘xs1’
  \\ qid_spec_tac ‘zs’
  \\ Induct \\ Cases_on ‘xs’ \\ Cases_on ‘xs1’ \\ fs []
  \\ PairCases_on ‘h’ \\ PairCases_on ‘h'’
  \\ fs [] \\ rw [] \\ metis_tac []
QED

Theorem NRC_cexp_wwf:
  ∀n x y. NRC cexp1_rel n x y ⇒ (cexp_wwf x ⇒ cexp_wwf y) ∧ cns_arities y ⊆ cns_arities x
Proof
  Induct \\ fs [NRC, PULL_EXISTS] \\ rw []
  \\ dxrule_all_then assume_tac cexp1_rel_cexp_wwf
  \\ last_x_assum $ dxrule_all_then assume_tac
  \\ metis_tac [SUBSET_TRANS]
QED

Theorem LIST_REL_EXISTS_NRC:
  ∀xs ys.
    LIST_REL (λx y. cexp_rel x y ∧ ∃n. NRC cexp1_rel n x y) xs ys ⇒
    ∃k. LIST_REL (NRC cexp1_rel k) xs ys
Proof
  Induct \\ Cases_on ‘ys’ \\ fs [] \\ rw []
  \\ first_x_assum drule \\ strip_tac
  \\ qexists_tac ‘n+k’
  \\ fs [arithmeticTheory.NRC_ADD_EQN]
  \\ first_assum $ irule_at Any \\ fs [NRC_refl]
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘xs’
  \\ qid_spec_tac ‘t’
  \\ Induct \\ fs [PULL_EXISTS] \\ rw []
  \\ fs [arithmeticTheory.NRC_ADD_EQN]
  \\ first_assum $ irule_at Any \\ fs [NRC_refl]
QED

Triviality NRC_REFL:
  ∀n. R x x ⇒ NRC R n x x
Proof
  Induct \\ fs [NRC] \\ metis_tac []
QED

Theorem cexp_rel_imp_nrc:
  ∀x y. cexp_rel x y ⇒ ∃n. NRC cexp1_rel n x y
Proof
  Induct_on ‘cexp_rel’ \\ rw []
  >- (qexists_tac ‘0’ \\ fs [])
  >- (qexists_tac ‘n+n'’
      \\ fs [arithmeticTheory.NRC_ADD_EQN]
      \\ first_assum $ irule_at Any \\ fs [])
  >-
   (qexists_tac ‘1+n’
    \\ rewrite_tac [arithmeticTheory.NRC_ADD_EQN]
    \\ pop_assum $ irule_at Any
    \\ fs [] \\ irule cexp1_rel_App_Lam \\ fs [])
  >-
   (Q.REFINE_EXISTS_TAC ‘1+k’
    \\ rewrite_tac [arithmeticTheory.NRC_ADD_EQN] \\ fs []
    \\ irule_at Any cexp1_rel_App_Let
    \\ rpt $ irule_at Any cexp1_rel_eq \\ fs []
    \\ qexists_tac ‘n+n'’
    \\ irule NRC_Let
    \\ fs [arithmeticTheory.NRC_ADD_EQN]
    \\ first_assum $ irule_at Any \\ fs [NRC_refl]
    \\ qexists_tac ‘app x' Unit’ \\ fs [NRC_refl]
    \\ irule NRC_App \\ fs [NRC_refl])
  >-
   (Q.REFINE_EXISTS_TAC ‘1+k’
    \\ rewrite_tac [arithmeticTheory.NRC_ADD_EQN] \\ fs []
    \\ irule_at Any cexp1_rel_App_If
    \\ rpt $ irule_at Any cexp1_rel_eq \\ fs []
    \\ qexists_tac ‘n+n'+n''’
    \\ irule NRC_If
    \\ rpt conj_tac
    \\ rewrite_tac [arithmeticTheory.NRC_ADD_EQN] \\ fs [PULL_EXISTS]
    >-
     (first_x_assum $ irule_at $ Pos hd
      \\ qexists_tac ‘y’ \\ fs [NRC_refl])
    >-
     (qsuff_tac ‘NRC cexp1_rel n' (app x' Unit) (app y' Unit)’
      >- metis_tac [NRC_refl]
      \\ irule NRC_App \\ fs [NRC_refl])
    >-
     (qsuff_tac ‘NRC cexp1_rel n'' (app x'' Unit) (app y'' Unit)’
      >- metis_tac [NRC_refl]
      \\ irule NRC_App \\ fs [NRC_refl]))
  >-
   (Q.REFINE_EXISTS_TAC ‘1+k’
    \\ rewrite_tac [arithmeticTheory.NRC_ADD_EQN] \\ fs []
    \\ irule_at Any cexp1_rel_App_Letrec
    \\ qexists_tac ‘x’ \\ fs []
    \\ ‘LIST_REL (λx y. cexp_rel x y ∧ ∃n. NRC cexp1_rel n x y)
          (app x Unit::MAP (SND ∘ SND) tfns) (app y Unit::MAP (SND ∘ SND) sfns)’ by
     (fs [PULL_EXISTS] \\ qexists_tac ‘n’ \\ fs []
      \\ irule_at Any cexp_rel_App \\ fs [cexp_rel_refl]
      \\ irule_at Any NRC_App \\ fs [NRC_refl])
    \\ drule LIST_REL_EXISTS_NRC \\ strip_tac \\ fs []
    \\ irule_at Any NRC_Letrec
    \\ qexists_tac ‘tfns’ \\ fs []
    \\ pop_assum $ irule_at Any \\ fs []
    \\ qid_spec_tac ‘tfns’
    \\ Induct \\ fs [])
  >- (qexists_tac ‘0’ \\ fs [])
  >- (irule_at Any NRC_Lam \\ qexists_tac ‘n’ \\ fs [])
  >- (irule_at Any NRC_Raise \\ qexists_tac ‘n’ \\ fs [])
  >-
   (‘LIST_REL (λx y. cexp_rel x y ∧ ∃n. NRC cexp1_rel n x y) [x;x'] [y;y']’ by
        (fs [] \\ metis_tac [])
    \\ dxrule LIST_REL_EXISTS_NRC \\ strip_tac \\ fs []
    \\ qexists_tac ‘k’
    \\ irule_at Any NRC_Handle \\ fs [])
  >-
   (‘LIST_REL (λx y. cexp_rel x y ∧ ∃n. NRC cexp1_rel n x y) [x;x'] [y;y']’ by
        (fs [] \\ metis_tac [])
    \\ dxrule LIST_REL_EXISTS_NRC \\ strip_tac \\ fs []
    \\ qexists_tac ‘k’
    \\ irule_at Any NRC_HandleApp \\ fs [])
  >-
   (dxrule LIST_REL_EXISTS_NRC \\ strip_tac \\ fs []
    \\ qexists_tac ‘k’
    \\ irule_at Any NRC_App \\ fs [])
  >-
   (‘LIST_REL (λx y. cexp_rel x y ∧ ∃n. NRC cexp1_rel n x y)
          (x::MAP (SND ∘ SND) tfns) (y::MAP (SND ∘ SND) sfns)’
       by (fs [] \\ metis_tac [])
    \\ dxrule LIST_REL_EXISTS_NRC \\ rw []
    \\ irule_at Any NRC_Letrec \\ fs []
    \\ pop_assum $ irule_at Any \\ fs [])
  >-
   (‘LIST_REL (λx y. cexp_rel x y ∧ ∃n. NRC cexp1_rel n x y) [x;x'] [y;y']’ by
      (fs [] \\ metis_tac [])
    \\ dxrule LIST_REL_EXISTS_NRC \\ rw []
    \\ qexists_tac ‘k’
    \\ irule_at Any NRC_Let \\ fs [])
  >-
   (‘LIST_REL (λx y. cexp_rel x y ∧ ∃n. NRC cexp1_rel n x y) [x;x';x''] [y;y';y'']’ by
      (fs [] \\ metis_tac [])
    \\ dxrule LIST_REL_EXISTS_NRC \\ rw []
    \\ qexists_tac ‘k’
    \\ irule_at Any NRC_If \\ fs [])
  >-
   (irule_at Any NRC_Case \\ fs []
    \\ dxrule LIST_REL_EXISTS_NRC \\ rw []
    \\ ‘∃m. k ≤ m ∧ OPTREL (λ(a,x) (b,y). a = b ∧ NRC cexp1_rel m x y) te se’ by
      (Cases_on ‘te’ \\ Cases_on ‘se’ \\ gvs []
       >- irule_at Any LESS_EQ_REFL
       \\ fs [UNCURRY]
       \\ qexists_tac ‘k+n’ \\ fs []
       \\ fs [NRC_ADD_EQN]
       \\ last_x_assum $ irule_at Any
       \\ irule NRC_REFL \\ fs [])
    \\ pop_assum $ irule_at Any
    \\ fs [LIST_REL_NRC]
    \\ gvs [LESS_EQ_EXISTS]
    \\ fs [NRC_ADD_EQN]
    \\ first_x_assum $ irule_at Any
    \\ irule NRC_REFL
    \\ qid_spec_tac ‘ses’ \\ Induct \\ fs [])
QED

Theorem cexp_rel_itree:
  ∀x y. cexp_rel x y ⇒ itree_of (exp_of x) = itree_of (exp_of y)
Proof
  rw []
  \\ drule cexp_rel_imp_nrc
  \\ fs [PULL_EXISTS]
  \\ qid_spec_tac ‘x’
  \\ qid_spec_tac ‘y’
  \\ Induct_on ‘n’
  \\ fs [NRC,PULL_EXISTS]
  \\ rw [] \\ res_tac
  \\ imp_res_tac cexp1_rel_correct \\ fs []
QED

Theorem cexp_rel_cexp_wwf:
  ∀x y. cexp_rel x y ⇒ (cexp_wwf x ⇒ cexp_wwf y) ∧ cns_arities y ⊆ cns_arities x
Proof
  gen_tac \\ gen_tac \\ strip_tac
  \\ dxrule_then assume_tac cexp_rel_imp_nrc
  \\ fs []
  \\ dxrule_all_then irule NRC_cexp_wwf
QED

Theorem unit_apps_0[simp]:
  unit_apps 0 x = x
Proof
  EVAL_TAC
QED

Theorem cexp_rel_unit_apps:
  ∀l x y. cexp_rel x y ⇒ cexp_rel (unit_apps l x) (unit_apps l y)
Proof
  Induct \\ fs []
  \\ once_rewrite_tac [unit_apps_def] \\ fs []
  \\ rw [] \\ first_x_assum irule
  \\ irule cexp_rel_App
  \\ fs [cexp_rel_refl]
QED

Theorem cexp_rel_unit_apps_Letrec:
  ∀l x y.
    cexp_rel (Letrec funs (unit_apps l x)) y ⇒
    cexp_rel (unit_apps l (Letrec funs x)) y
Proof
  Induct \\ fs []
  \\ once_rewrite_tac [unit_apps_def] \\ fs []
  \\ rw [] \\ first_x_assum drule \\ rw []
  \\ irule cexp_rel_trans
  \\ pop_assum $ irule_at Any
  \\ irule cexp_rel_unit_apps
  \\ irule cexp_rel_App_Letrec \\ fs [cexp_rel_refl]
  \\ qid_spec_tac ‘funs’ \\ Induct
  \\ fs [cexp_rel_refl]
QED

Theorem cexp_rel_unit_apps_Let:
  ∀l x y.
    cexp_rel (Let n t (unit_apps l x)) y ⇒
    cexp_rel (unit_apps l (Let n t x)) y
Proof
  Induct \\ fs []
  \\ once_rewrite_tac [unit_apps_def] \\ fs []
  \\ rw [] \\ first_x_assum drule \\ rw []
  \\ irule cexp_rel_trans
  \\ pop_assum $ irule_at Any
  \\ irule cexp_rel_unit_apps
  \\ irule cexp_rel_App_Let \\ fs [cexp_rel_refl]
QED

Theorem cexp_rel_unit_apps_If:
  ∀l x x1 x2.
    cexp_rel (If x (unit_apps l x1) (unit_apps l x2)) y ⇒
    cexp_rel (unit_apps l (If x x1 x2)) y
Proof
  Induct \\ fs []
  \\ once_rewrite_tac [unit_apps_def] \\ fs []
  \\ rw [] \\ first_x_assum drule \\ rw []
  \\ irule cexp_rel_trans
  \\ pop_assum $ irule_at Any
  \\ irule cexp_rel_unit_apps
  \\ irule cexp_rel_App_If \\ fs [cexp_rel_refl]
QED

Theorem cexp_rel_pust_app_unit:
  ∀l x. cexp_rel (unit_apps l x) (push_app_unit l x)
Proof
  ho_match_mp_tac push_app_unit_ind \\ rpt strip_tac
  >- fs [push_app_unit_def,cexp_rel_refl]
  >-
   (reverse (Cases_on ‘op = AppOp ∧ LENGTH xs = 2 ∧ EL 1 xs = Unit’ \\ gvs [])
    \\ gvs [push_app_unit_def]
    >-
     (rw [] >- gvs [LENGTH_EQ_NUM_compute,any_el_def]
      \\ gvs []
      \\ irule cexp_rel_unit_apps
      \\ irule cexp_rel_App
      \\ qpat_x_assum ‘∀x. _’ mp_tac
      \\ qid_spec_tac ‘xs’ \\ Induct \\ fs []
      \\ metis_tac [])
    \\ gvs [LENGTH_EQ_NUM_compute,any_el_def]
    \\ pop_assum mp_tac
    \\ simp [Once unit_apps_def])
  >-
   (Cases_on ‘l = 0’ \\ gvs [push_app_unit_def]
    >- (irule cexp_rel_Lam \\ fs [])
    \\ reverse (Cases_on ‘vn’) \\ fs []
    >- (irule cexp_rel_unit_apps \\ irule cexp_rel_Lam \\ fs [])
    \\ irule cexp_rel_trans
    \\ first_x_assum $ irule_at Any
    \\ simp [Once unit_apps_def]
    \\ irule cexp_rel_unit_apps
    \\ irule cexp_rel_App_Lam \\ fs [cexp_rel_refl])
  >-
   (fs [push_app_unit_def]
    \\ irule_at Any cexp_rel_unit_apps_Letrec
    \\ irule cexp_rel_Letrec
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
    \\ last_x_assum mp_tac \\ qid_spec_tac ‘funs’
    \\ Induct \\ fs [FORALL_PROD] \\ metis_tac [])
  >-
   (fs [push_app_unit_def]
    \\ irule_at Any cexp_rel_unit_apps_Let
    \\ irule cexp_rel_Let \\ simp [])
  >-
   (fs [push_app_unit_def]
    \\ irule_at Any cexp_rel_unit_apps_If
    \\ irule cexp_rel_If \\ simp [])
  >-
   (fs [push_app_unit_def]
    \\ irule_at Any cexp_rel_unit_apps
    \\ irule cexp_rel_Case \\ fs []
    \\ Cases_on ‘d’ \\ fs []
    \\ TRY (PairCases_on ‘x’ \\ fs [])
    \\ rpt $ pop_assum mp_tac \\ qid_spec_tac ‘rows’
    \\ Induct \\ fs [FORALL_PROD] \\ rw []
    \\ metis_tac [])
  >-
   (fs [push_app_unit_def]
    \\ irule_at Any cexp_rel_unit_apps
    \\ irule cexp_rel_Raise \\ fs [])
  >-
   (fs [push_app_unit_def]
    \\ irule_at Any cexp_rel_unit_apps
    \\ irule cexp_rel_Handle \\ fs [])
  >-
   (fs [push_app_unit_def]
    \\ irule_at Any cexp_rel_unit_apps
    \\ irule cexp_rel_HandleApp \\ fs [])
QED

Theorem itree_of_push_app_unit:
  itree_of (exp_of (push_app_unit 0 x)) = itree_of (exp_of x)
Proof
  once_rewrite_tac [EQ_SYM_EQ]
  \\ simp_tac std_ss [Once $ GSYM unit_apps_0]
  \\ irule cexp_rel_itree
  \\ fs [cexp_rel_pust_app_unit]
QED

Theorem cexp_wwf_push_app_unit:
  (cexp_wwf x ⇒ cexp_wwf (push_app_unit 0 x)) ∧
  cns_arities (push_app_unit 0 x) ⊆ cns_arities x
Proof
  qspecl_then [‘unit_apps 0 x’, ‘push_app_unit 0 x’] mp_tac cexp_rel_cexp_wwf
  \\ reverse impl_tac
  >- simp [unit_apps_0]
  \\ fs [cexp_rel_pust_app_unit]
QED

Theorem itree_of_optimise_app_unit:
  itree_of (exp_of (optimise_app_unit b x)) = itree_of (exp_of x)
Proof
  rw [optimise_app_unit_def,itree_of_push_app_unit]
QED

Theorem cexp_wwf_optimise_app_unit:
  (cexp_wwf x ⇒ cexp_wwf (optimise_app_unit b x)) ∧
  cns_arities (optimise_app_unit b x) ⊆ cns_arities x
Proof
  rw [optimise_app_unit_def,cexp_wwf_push_app_unit]
QED

val _ = export_theory ();
