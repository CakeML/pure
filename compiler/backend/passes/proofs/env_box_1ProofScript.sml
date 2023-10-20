(*
  Correctness of compilation pass that introduces Box
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory intLib
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory combinTheory
     envLangTheory thunkLang_primitivesTheory env_cexpTheory env_semanticsTheory;
local open pure_semanticsTheory in end

val _ = new_theory "env_box_1Proof";

val _ = set_grammar_ancestry ["envLang", "env_semantics", "pure_config", "alist"];

(* -------------------- compile_rel, v_rel ---------------------- *)

Inductive can_box:

[~Delay:]
  can_box (Delay te) ∧

[~Box:]
  (can_box te ⇒
   can_box (Box te)) ∧

[~Var:]
  can_box (envLang$Var v) ∧

[~Monad:]
  can_box (Monad x xs) ∧

[~Cons:]
  (EVERY can_box xs ⇒
   can_box (Prim (Cons c) xs)) ∧

[~Lit:]
  (can_box (Prim (AtomOp (Lit l)) [])) ∧

[~Lam:]
  can_box (Lam v te)

End

Definition is_Delay_def:
  is_Delay (Delay t) = T ∧
  is_Delay _ = F
End

Inductive compile_rel:

[~Delay:]
  (∀te se.
    compile_rel te se ⇒
    compile_rel (Delay te) (Delay se)) ∧

[~Delay_Box:]
  (∀te se.
    compile_rel te se ∧ can_box se ⇒
    compile_rel (Delay te) (Box se)) ∧

[~Box:]
  (∀te se.
    compile_rel te se ⇒
    compile_rel (Box te) (Box se)) ∧

[~Force:]
  (∀te se.
    compile_rel te se ⇒
    compile_rel (Force te) (Force se)) ∧

[~Var:]
  compile_rel (envLang$Var v) (envLang$Var v) ∧

[~Monad:]
  (LIST_REL compile_rel xs ys ⇒
  compile_rel (Monad x xs) (Monad x ys)) ∧

[~Prim:]
  (LIST_REL compile_rel xs ys ⇒
  compile_rel (Prim p xs) (Prim p ys)) ∧

[~App:]
  (compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (App te1 te2) (App se1 se2)) ∧

[~Lam:]
  (∀x te se.
    compile_rel te se ⇒
    compile_rel (Lam x te) (Lam x se)) ∧

[~Letrec:]
  (∀tfns sfns te se.
    MAP FST tfns = MAP FST sfns ∧
    LIST_REL compile_rel (MAP SND tfns) (MAP SND sfns) ∧
    LIST_REL (λt s. is_Delay t ⇔ is_Delay s) (MAP SND tfns) (MAP SND sfns) ∧
    compile_rel te se ⇒
    compile_rel (Letrec tfns te) (Letrec sfns se)) ∧

[~Let:]
  (compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (Let x_opt te1 te2) (Let x_opt se1 se2)) ∧

[~If:]
  (compile_rel te se ∧
   compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (If te te1 te2) (If se se1 se2))

End

Inductive v_rel:

[~ThunkRL:]
  (∀te se tenv senv tv sv.
     compile_rel te se ∧ env_rel tenv senv ∧ v_rel tv sv ∧
     (∀k. eval_to k tenv te = INR tv) ∧
     (∀k. eval_to k senv se = INR sv) ⇒
     v_rel (Thunk $ INR (tenv, te)) (Thunk $ INL sv)) ∧

[~Constructor:]
  (∀tvs svs.
     LIST_REL v_rel tvs svs ⇒
     v_rel (envLang$Constructor s tvs) (envLang$Constructor s svs)) ∧

[~Closure:]
  (∀tenv senv te se.
     env_rel tenv senv ∧
     freevars te ⊆ {x} ∪ set (MAP FST tenv) ∧
     compile_rel te se ⇒
     v_rel (Closure x tenv te) (Closure x senv se)) ∧

[~Recclosure:]
  (∀tenv senv tfns sfns.
     env_rel tenv senv ∧
     LIST_REL ((=) ### compile_rel) tfns sfns ∧
     LIST_REL (λt s. is_Delay t ⇔ is_Delay s) (MAP SND tfns) (MAP SND sfns) ⇒
     v_rel (Recclosure tfns tenv n) (Recclosure sfns senv n)) ∧

[~ThunkL:]
  (∀tv sv.
     v_rel tv sv ⇒
     v_rel (Thunk $ INL tv) (Thunk $ INL sv)) ∧

[~ThunkR:]
  (∀tenv senv te se.
     env_rel tenv senv ∧ freevars te ⊆ set (MAP FST tenv) ∧
     compile_rel te se ⇒
     v_rel (Thunk $ INR (tenv, te)) (Thunk $ INR (senv, se))) ∧

[~Atom:]
  (∀a.
     v_rel (Atom a) (Atom a)) ∧

[~Monadic:]
  (∀te se tenv senv m.
     LIST_REL compile_rel te se ∧ env_rel tenv senv ∧
     BIGUNION (set (MAP freevars te)) ⊆ set (MAP FST tenv) ⇒
     v_rel (Monadic tenv m te)
           (Monadic senv m se)) ∧

[env_rel:]
  (∀tenv senv.
     LIST_REL (λ(n,tv) (m,sv). n = m ∧ v_rel tv sv) tenv senv ⇒
     env_rel tenv senv)

End

Theorem env_rel_def = v_rel_cases |> SPEC_ALL |> CONJUNCT2 |> GEN_ALL;

(* -------------------------- eval_to -------------------------- *)

Theorem can_box_eval_to:
  ∀te tenv se senv.
    can_box se ∧ compile_rel te se ∧ env_rel tenv senv ∧
    freevars te ⊆ set (MAP FST tenv) ⇒
    ∃tv sv.
      v_rel tv sv ∧
      ∀n. eval_to n tenv te = INR tv ∧
          eval_to n senv se = INR sv
Proof
  Induct_on ‘can_box’ \\ rpt strip_tac
  \\ qpat_x_assum ‘compile_rel _ _’ mp_tac
  >~ [‘Delay’] >-
   (simp [Once compile_rel_cases]
    \\ strip_tac \\ gvs [eval_to_def,freevars_def]
    \\ simp [Once v_rel_cases])
  >~ [‘Box’] >-
   (simp [Once compile_rel_cases]
    \\ strip_tac \\ gvs [eval_to_def,freevars_def]
    \\ last_x_assum $ drule_all \\ strip_tac \\ fs []
    \\ simp [Once v_rel_cases] \\ metis_tac [])
  >~ [‘Var’] >-
   (simp [Once compile_rel_cases]
    \\ strip_tac \\ gvs [eval_to_def,freevars_def]
    \\ rpt $ pop_assum mp_tac
    \\ qid_spec_tac ‘senv’
    \\ qid_spec_tac ‘tenv’
    \\ Induct \\ gvs [env_rel_def,PULL_EXISTS,FORALL_PROD]
    \\ rpt gen_tac \\ IF_CASES_TAC \\ gvs [])
  >~ [‘Monad’] >-
   (simp [Once compile_rel_cases]
    \\ strip_tac \\ gvs [eval_to_def,freevars_def,SF ETA_ss]
    \\ simp [Once v_rel_cases])
  >~ [‘Lam’] >-
   (simp [Once compile_rel_cases]
    \\ strip_tac \\ gvs [eval_to_def,freevars_def]
    \\ simp [Once v_rel_cases]
    \\ gvs [SUBSET_DEF] \\ metis_tac [])
  >~ [‘Lit’] >-
   (simp [Once compile_rel_cases]
    \\ strip_tac \\ gvs [eval_to_def,freevars_def]
    \\ gvs [result_map_def]
    \\ simp [Once v_rel_cases])
  >~ [‘Cons’] >-
   (simp [Once compile_rel_cases]
    \\ strip_tac \\ gvs [eval_to_def,freevars_def,SF ETA_ss]
    \\ rename [‘LIST_REL compile_rel xs ys’]
    \\ qsuff_tac
       ‘∃xs1 ys1.
          ∀n. result_map (eval_to n tenv) xs = INR xs1 ∧
              result_map (eval_to n senv) ys = INR ys1 ∧
              LIST_REL v_rel xs1 ys1’
    >- (strip_tac \\ gvs [] \\ simp [Once v_rel_cases])
    \\ rpt $ pop_assum mp_tac
    \\ qid_spec_tac ‘xs’
    \\ qid_spec_tac ‘ys’
    \\ Induct \\ gvs [PULL_EXISTS,result_map_def]
    \\ rpt strip_tac \\ gvs []
    \\ first_x_assum drule_all \\ strip_tac \\ gvs []
    \\ first_x_assum drule_all \\ strip_tac \\ gvs []
    \\ gvs [AllCaseEqs()]
    \\ qexists_tac ‘tv::xs1’ \\ fs []
    \\ qexists_tac ‘sv::ys1’ \\ fs [])
QED

Triviality list_rel_alookup_none:
  ∀tfns sfns.
    LIST_REL ($= ### compile_rel) tfns sfns ∧
    ALOOKUP tfns n = NONE ⇒
    ALOOKUP sfns n = NONE
Proof
  Induct \\ gvs [PULL_EXISTS,FORALL_PROD] \\ rw []
QED

Triviality list_rel_alookup_some:
  ∀tfns sfns.
    LIST_REL ($= ### compile_rel) tfns sfns ∧
    LIST_REL R (MAP SND tfns) (MAP SND sfns) ∧
    ALOOKUP tfns n = SOME te1 ⇒
    ∃se1. ALOOKUP sfns n = SOME se1 ∧ compile_rel te1 se1 ∧ R te1 se1
Proof
  Induct \\ gvs [PULL_EXISTS,FORALL_PROD] \\ rw [] \\ fs []
QED

Theorem result_map_Diverge[simp]:
  result_map (λx. INL Diverge) xs =
  if xs = [] then INR [] else INL Diverge
Proof
  Cases_on ‘xs’ \\ gvs [result_map_def,MEM_MAP]
QED

Triviality not_inl:
  x ≠ INL Type_error ∧ x ≠ INL Diverge ⇒ ∃y. x = INR y
Proof
  Cases_on ‘x’ \\ gvs []
  \\ rename [‘y = _’] \\ Cases_on ‘y’ \\ fs []
QED

Definition eval_to_atom_def:
  eval_to_atom f = (λx.
                     case f x of
                       INL err => INL err
                     | INR (Constructor v17 v18) => INL Type_error
                     | INR (Monadic v19 v20 v21) => INL Type_error
                     | INR (Closure v22 v23 v24) => INL Type_error
                     | INR (Recclosure v25 v26 v27) => INL Type_error
                     | INR (Thunk v28) => INL Type_error
                     | INR (Atom l) => INR l)
End

Theorem eval_to_thm:
  ∀n tenv te se senv st k.
    compile_rel te se ∧
    env_rel tenv senv ∧
    freevars te ⊆ set (MAP FST tenv)
    ⇒
    ((=) +++ v_rel) (eval_to n tenv te) (eval_to n senv se)
Proof
  ho_match_mp_tac eval_to_ind \\ rpt strip_tac \\ rpt var_eq_tac
  \\ qpat_x_assum ‘compile_rel _ _’ mp_tac \\ simp [Once compile_rel_cases]
  \\ strip_tac \\ rpt var_eq_tac
  >~ [‘Delay’,‘Box’,‘compile_rel te se’] >-
   (gvs [eval_to_def,freevars_def]
    \\ drule_all can_box_eval_to \\ strip_tac
    \\ gvs [] \\ simp [Once v_rel_cases]
    \\ rpt $ first_assum $ irule_at $ Pos hd \\ fs [])
  >~ [‘Force’,‘compile_rel te se’] >-
   (gvs [eval_to_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ first_x_assum $ drule_then drule
    \\ gvs [freevars_def]
    \\ Cases_on ‘eval_to n tenv te’
    \\ Cases_on ‘eval_to n senv se’ \\ gvs []
    \\ simp [Once v_rel_cases]
    \\ strip_tac \\ gvs [dest_anyThunk_def]
    >-
     (CASE_TAC \\ gvs []
      >- (drule_all list_rel_alookup_none \\ rw [] \\ fs [])
      \\ drule_all list_rel_alookup_some \\ rw [] \\ fs []
      \\ rename [‘is_Delay x = is_Delay y’]
      \\ pop_assum mp_tac
      \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ simp [is_Delay_def]
      \\ pop_assum mp_tac
      \\ simp [Once compile_rel_cases] \\ strip_tac
      \\ last_x_assum irule \\ fs []
      \\ fs [MAP_MAP_o,o_DEF]
      \\ simp [LAMBDA_PROD,FST_INTRO]
      \\ cheat)
    \\ last_x_assum drule
    \\ disch_then $ qspecl_then [‘tenv'’,‘[]’,‘senv'’] mp_tac \\ fs [])
  >~ [‘Delay d’] >-
   (gvs [eval_to_def,freevars_def] \\ simp [Once v_rel_cases])
  >~ [‘Box’,‘compile_rel te se’] >-
   (gvs [eval_to_def,freevars_def]
    \\ last_x_assum drule_all
    \\ Cases_on ‘eval_to n tenv te’
    \\ Cases_on ‘eval_to n senv se’ \\ gvs []
    \\ strip_tac \\ simp [Once v_rel_cases])
  >~ [‘Var’] >-
   (gvs [eval_to_def,freevars_def]
    \\ rpt $ pop_assum mp_tac
    \\ qid_spec_tac ‘senv’
    \\ qid_spec_tac ‘tenv’
    \\ Induct \\ gvs [env_rel_def,PULL_EXISTS,FORALL_PROD]
    \\ rpt gen_tac \\ IF_CASES_TAC \\ gvs [])
  >~ [‘Lam’] >-
   (gvs [freevars_def,eval_to_def]
    \\ simp [Once v_rel_cases]
    \\ gvs [SUBSET_DEF] \\ metis_tac [])
  >~ [‘Monad’] >-
   (gvs [freevars_def,eval_to_def,SF ETA_ss]
    \\ simp [Once v_rel_cases])
  >~ [‘Let NONE’] >-
   (gvs [freevars_def,eval_to_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ first_x_assum drule_all \\ strip_tac
    \\ first_x_assum drule_all \\ strip_tac
    \\ rename [‘($= +++ v_rel) (eval_to (n − 1) tenv te1)
                               (eval_to (n − 1) senv se1)’]
    \\ pop_assum mp_tac
    \\ rename [‘($= +++ v_rel) (eval_to (n − 1) tenv te2)
                               (eval_to (n − 1) senv se2)’]
    \\ Cases_on ‘eval_to (n − 1) tenv te1’
    \\ Cases_on ‘eval_to (n − 1) senv se1’
    \\ gvs [])
  >~ [‘Let (SOME v)’] >-
   (gvs [freevars_def,eval_to_def]
    \\ IF_CASES_TAC \\ gvs [env_rel_def,PULL_EXISTS,FORALL_PROD]
    \\ first_x_assum drule_all \\ strip_tac
    \\ rename [‘($= +++ v_rel) (eval_to (n − 1) tenv te1)
                               (eval_to (n − 1) senv se1)’]
    \\ Cases_on ‘eval_to (n − 1) tenv te1’
    \\ Cases_on ‘eval_to (n − 1) senv se1’
    \\ gvs [] \\ first_x_assum irule \\ gvs []
    \\ gvs [SUBSET_DEF] \\ metis_tac [])
  >~ [‘If’] >-
   (gvs [eval_to_def] \\ IF_CASES_TAC \\ gvs [freevars_def]
    \\ first_x_assum drule_all \\ strip_tac
    \\ rename [‘($= +++ v_rel) (eval_to (n − 1) tenv te1)
                               (eval_to (n − 1) senv se1)’]
    \\ Cases_on ‘eval_to (n − 1) tenv te1’
    \\ Cases_on ‘eval_to (n − 1) senv se1’
    \\ gvs []
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ Cases_on ‘tvs’ \\ gvs []
    \\ rw [] \\ gvs [])
  >~ [‘Letrec’] >-
   (gvs [eval_to_def] \\ IF_CASES_TAC \\ gvs []
    \\ last_x_assum irule
    \\ fs [MAP_MAP_o,o_DEF]
    \\ simp [LAMBDA_PROD,FST_INTRO]
    \\ cheat)
  >~ [‘App’] >-
   (gvs [freevars_def]
    \\ first_x_assum drule_all \\ strip_tac
    \\ first_x_assum drule_all \\ strip_tac
    \\ gvs [eval_to_def]
    \\ pop_assum mp_tac
    \\ rename [‘($= +++ v_rel) (eval_to n tenv te1)
                               (eval_to n senv se1)’]
    \\ Cases_on ‘eval_to n tenv te1’
    \\ Cases_on ‘eval_to n senv se1’
    \\ gvs []
    \\ rename [‘($= +++ v_rel) (eval_to n tenv te2)
                               (eval_to n senv se2)’]
    \\ Cases_on ‘eval_to n tenv te2’
    \\ Cases_on ‘eval_to n senv se2’
    \\ gvs []
    \\ simp [Once v_rel_cases]
    \\ strip_tac \\ gvs [dest_anyClosure_def]
    >-
     (IF_CASES_TAC \\ fs []
      \\ last_x_assum irule \\ fs [env_rel_def]
      \\ gvs [SUBSET_DEF])
    \\ cheat)
  \\ Cases_on ‘op’ \\ gvs [eval_to_def]
  >-
   (qsuff_tac
       ‘($= +++ LIST_REL v_rel) (result_map (eval_to n tenv) xs)
                                (result_map (eval_to n senv) ys)’
    >-
     (gvs [SF ETA_ss]
      \\ Cases_on ‘result_map (eval_to n tenv) xs’ \\ gvs []
      \\ Cases_on ‘result_map (eval_to n senv) ys’ \\ gvs []
      \\ simp [Once v_rel_cases])
    \\ gvs [freevars_def,SF ETA_ss]
    \\ rpt $ pop_assum mp_tac
    \\ qid_spec_tac ‘xs’
    \\ qid_spec_tac ‘ys’
    \\ Induct \\ gvs [PULL_EXISTS,result_map_def]
    \\ rpt strip_tac \\ gvs [SF DNF_ss]
    \\ last_x_assum $ drule_at $ Pos last \\ fs []
    \\ last_x_assum $ drule_at $ Pos hd \\ fs []
    \\ disch_then drule \\ rpt strip_tac
    \\ ‘eval_to n tenv x = INL Type_error ⇔
        eval_to n senv h = INL Type_error’ by
      (Cases_on ‘eval_to n tenv x’ \\ gvs []
       \\ Cases_on ‘eval_to n senv h’ \\ gvs [])
    \\ ‘MEM (INL Type_error) (MAP (eval_to n senv) ys) ⇔
        MEM (INL Type_error) (MAP (eval_to n tenv) xs')’ by
      (eq_tac \\ rw [] \\ gvs [] \\ CCONTR_TAC \\ gvs []
       \\ every_case_tac \\ gvs [])
    \\ gvs [] \\ IF_CASES_TAC \\ gvs []
    \\ ‘eval_to n tenv x = INL Diverge ⇔
        eval_to n senv h = INL Diverge’ by
      (Cases_on ‘eval_to n tenv x’ \\ gvs []
       \\ Cases_on ‘eval_to n senv h’ \\ gvs [])
    \\ ‘MEM (INL Diverge) (MAP (eval_to n senv) ys) ⇔
        MEM (INL Diverge) (MAP (eval_to n tenv) xs')’ by
      (every_case_tac \\ gvs [])
    \\ gvs [] \\ IF_CASES_TAC \\ gvs []
    \\ Cases_on ‘eval_to n tenv x’ >- (rename [‘INL y’] \\ Cases_on ‘y’ \\ gvs [])
    \\ Cases_on ‘eval_to n senv h’ >- (rename [‘INL y’] \\ Cases_on ‘y’ \\ gvs [])
    \\ gvs [])
  >-
   (imp_res_tac LIST_REL_LENGTH
    \\ IF_CASES_TAC \\ gvs []
    \\ IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute,freevars_def]
    \\ last_x_assum drule_all \\ strip_tac
    \\ rename [‘($= +++ v_rel) (eval_to n tenv te2) (eval_to n senv se2)’]
    \\ Cases_on ‘eval_to n tenv te2’ \\ Cases_on ‘eval_to n senv se2’
    \\ gvs []
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ IF_CASES_TAC \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ simp [Once v_rel_cases])
  >-
   (imp_res_tac LIST_REL_LENGTH
    \\ IF_CASES_TAC \\ gvs []
    \\ IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute,freevars_def]
    \\ last_x_assum drule_all \\ strip_tac
    \\ rename [‘($= +++ v_rel) (eval_to n tenv te2) (eval_to n senv se2)’]
    \\ Cases_on ‘eval_to n tenv te2’ \\ Cases_on ‘eval_to n senv se2’
    \\ gvs []
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ IF_CASES_TAC \\ gvs []
    \\ gvs [LIST_REL_EL_EQN])
  \\ Cases_on ‘n = 0’ \\ gvs []
  >-
   (gvs [result_map_def]
    \\ reverse IF_CASES_TAC \\ gvs []
    >- (IF_CASES_TAC \\ gvs [])
    \\ CASE_TAC \\ gvs []
    \\ CASE_TAC \\ gvs []
    \\ simp [Once v_rel_cases])
  \\ gvs [GSYM eval_to_atom_def,SF ETA_ss]
  \\ qsuff_tac ‘result_map (eval_to_atom (eval_to (n − 1) tenv)) xs =
                result_map (eval_to_atom (eval_to (n − 1) senv)) ys’
  >-
   (gvs []
    \\ Cases_on ‘result_map (eval_to_atom (eval_to (n − 1) senv)) ys’ \\ gvs []
    \\ Cases_on ‘eval_op a y’ \\ gvs []
    \\ Cases_on ‘x’ \\ gvs []
    \\ simp [Once v_rel_cases])
  \\ gvs [freevars_def,SF ETA_ss]
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac ‘ys’
  \\ qid_spec_tac ‘xs’
  \\ Induct \\ gvs [PULL_EXISTS,result_map_def]
  \\ rpt strip_tac
  \\ gvs [SF DNF_ss]
  \\ last_x_assum drule_all \\ strip_tac
  \\ last_x_assum drule_all \\ strip_tac
  \\ ‘(eval_to_atom (eval_to (n − 1) tenv) h = INL Type_error ⇔
       eval_to_atom (eval_to (n − 1) senv) y = INL Type_error) ∧
      (eval_to_atom (eval_to (n − 1) tenv) h = INL Diverge ⇔
       eval_to_atom (eval_to (n − 1) senv) y = INL Diverge)’ by
   (Cases_on ‘eval_to (n − 1) tenv h’
    \\ Cases_on ‘eval_to (n − 1) senv y’ \\ gvs [eval_to_atom_def]
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases]
    \\ strip_tac \\ gvs [])
  \\ ‘MEM (INL Type_error) (MAP (eval_to_atom (eval_to (n − 1) tenv)) xs) =
      MEM (INL Type_error) (MAP (eval_to_atom (eval_to (n − 1) senv)) ys')’ by
   (rpt strip_tac \\ eq_tac \\ rpt strip_tac \\ gvs [AllCaseEqs()])
  \\ gvs [] \\ IF_CASES_TAC \\ fs []
  \\ ‘MEM (INL Diverge) (MAP (eval_to_atom (eval_to (n − 1) tenv)) xs) =
      MEM (INL Diverge) (MAP (eval_to_atom (eval_to (n − 1) senv)) ys')’ by
   (rpt strip_tac \\ eq_tac \\ rpt strip_tac \\ gvs [AllCaseEqs()])
  \\ gvs [] \\ IF_CASES_TAC \\ fs []
  \\ dxrule_all not_inl
  \\ dxrule_all not_inl
  \\ rpt strip_tac \\ gvs []
  \\ gvs [eval_to_atom_def,AllCaseEqs()]
  \\ fs [Once v_rel_cases]
QED

(* -------------------------- eval -------------------------- *)

Theorem eval_exp_rel:
  compile_rel x y ∧ env_rel tenv senv ∧
  freevars x ⊆ set (MAP FST tenv)
  ⇒
  ($= +++ v_rel) (eval tenv x) (eval senv y)
Proof
  rw [envLangTheory.eval_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ simp [PULL_FORALL]
  \\ qx_gen_tac ‘i’
  \\ qx_gen_tac ‘j’
  \\ qx_gen_tac ‘k’
  \\ rw [] \\ gs []
  >-
   (drule_all_then (qspec_then ‘i + j’ assume_tac) eval_to_thm
    \\ dxrule_then (qspec_then ‘i + j’ assume_tac) eval_to_mono \\ gs []
    \\ dxrule_then (qspec_then ‘i + j’ assume_tac) eval_to_mono \\ gs [])
  >- (
    drule_all_then (qspec_then ‘i’ assume_tac) eval_to_thm
    \\ first_x_assum (qspec_then ‘i’ assume_tac) \\ gs [])
  >- (
    drule_all_then (qspec_then ‘k’ assume_tac) eval_to_thm
    \\ first_x_assum (qspec_then ‘k’ assume_tac) \\ gs [])
QED

(* ----------------------- next_action ---------------------- *)

Definition cont_rel_def[simp]:
  cont_rel env_semantics$Done env_semantics$Done = T ∧
  cont_rel (BC (tenv,te) c) (BC (senv,se) d) =
    (freevars te ⊆ set (MAP FST tenv) ∧
     env_rel tenv senv ∧ compile_rel te se ∧ cont_rel c d) ∧
  cont_rel (HC (tenv,te) c) (HC (senv,se) d) =
    (freevars te ⊆ set (MAP FST tenv) ∧
     env_rel tenv senv ∧ compile_rel te se ∧ cont_rel c d) ∧
  cont_rel _ _ = F
End

Definition next_rel_def[simp]:
  next_rel (env_semantics$Act a c s) (env_semantics$Act b d t) =
    (a = b ∧ cont_rel c d ∧ LIST_REL (LIST_REL v_rel) s t) ∧
  next_rel Ret Ret = T ∧
  next_rel Div Div = T ∧
  next_rel Err Err = T ∧
  next_rel _ _ = F
End

(*
Triviality LIST_REL_ALOOKUP_lemma:
  ∀f g s.
    LIST_REL (λ(fn,b) (gn,c). fn = gn ∧ exp_rel xs b c) f g ⇒
    ALOOKUP f s = NONE ∧ ALOOKUP g s = NONE ∨
    ∃b c.
      ALOOKUP f s = SOME b ∧
      ALOOKUP g s = SOME c ∧ exp_rel xs b c
Proof
  Induct \\ fs [PULL_EXISTS,FORALL_PROD]
  \\ rpt gen_tac \\ strip_tac
  \\ IF_CASES_TAC \\ fs []
QED

Theorem LIST_REL_MAP_MAP:
  ∀xs ys f g.
    LIST_REL P (MAP f xs) (MAP g ys) ⇔
    LIST_REL (λx y. P (f x) (g y)) xs ys
Proof
  Induct \\ fs [PULL_EXISTS]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on ‘ys’ \\ gvs []
QED
*)

Theorem apply_closure_thm:
  ∀v1 v2 env1 env2 f1 f2 y1 y2.
    v_rel v1 v2 ∧
    (∀v1 v2. ($= +++ v_rel) v1 v2 ⇒ next_rel (f1 v1) (f2 v2)) ⇒
    next_rel (apply_closure (env1,y1) v1 f1)
             (apply_closure (env2,y2) v2 f2)
Proof
  cheat (*
  fs [apply_closure_def,env_semanticsTheory.apply_closure_def]
  \\ fs [with_value_def,env_semanticsTheory.with_value_def]
  \\ fs [dest_anyClosure_def,envLangTheory.dest_anyClosure_def] >>
  rw[] >> drule eval_exp_rel >> BasicProvers.TOP_CASE_TAC >> gvs[]
  >- (Cases_on `eval env y1` >> gvs[] >> CASE_TAC >> rw[] >> gvs[]) >>
  rename1 `INR v1` >> Cases_on `eval env y1` >> gvs[] >>
  rename1 `INR w1` >> rw[Once v_rel_cases] >> gvs[]
  >-
   (first_x_assum irule
    \\ irule eval_exp_rel
    \\ once_rewrite_tac [GSYM (EVAL “[x:'a] ++ xs”)]
    \\ irule exp_rel_subst \\ fs []
    \\ fs [env_rel_def]
    \\ pop_assum mp_tac
    \\ simp [Once exp_rel_cases])
  \\ drule LIST_REL_ALOOKUP_lemma
  \\ disch_then $ qspec_then ‘n’ strip_assume_tac
  \\ fs []
  \\ pop_assum mp_tac
  \\ simp [Once exp_rel_cases]
  \\ strip_tac \\ gvs []
  \\ first_assum irule
  \\ irule eval_exp_rel
  \\ rewrite_tac [APPEND |> CONJUNCT2 |> GSYM]
  \\ irule exp_rel_subst
  \\ simp [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FILTER_FILTER]
  \\ fs [MEM_MAP,FORALL_PROD,FILTER_FILTER]
  \\ reverse conj_tac
  >-
   (pop_assum mp_tac
    \\ match_mp_tac (METIS_PROVE [] “x = y ⇒ (x ⇒ y)”)
    \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
    \\ fs [FUN_EQ_THM,FORALL_PROD]
    \\ rw [] \\ eq_tac \\ rw [])
  \\ fs [env_rel_def]
  \\ fs [GSYM MAP_REVERSE]
  \\ simp [LIST_REL_MAP_MAP,LAMBDA_PROD]
  \\ fs [LIST_REL_EL_EQN]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs []
  \\ rw [LAMBDA_PROD]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs []
  \\ first_assum drule
  \\ asm_rewrite_tac []
  \\ simp_tac std_ss []
  \\ fs [] \\ rw []
  \\ simp [Once v_rel_cases]
  \\ fs [LIST_REL_EL_EQN,MEM_MAP,FORALL_PROD] *)
QED

Theorem LIST_REL_LUPDATE:
  ∀xs ys x y n.
    LIST_REL R xs ys ∧ R x y ⇒
    LIST_REL R (LUPDATE x n xs) (LUPDATE y n ys)
Proof
  Induct \\ fs [PULL_EXISTS,LUPDATE_def] \\ rw []
  \\ Cases_on ‘n’ \\ fs [LUPDATE_def]
QED

Theorem LIST_REL_REPLICATE:
  LIST_REL R (REPLICATE n x) (REPLICATE n y) ⇔
  (0 < n ⇒ R x y)
Proof
  Induct_on ‘n’ \\ gvs [] \\ Cases_on ‘n’ \\ gvs []
QED

Triviality sum_map_simp[simp]:
  ((f +++ g) (INL x1) y1 ⇔ ∃z. y1 = INL z ∧ f x1 z) ∧
  ((f +++ g) (INR x2) y2 ⇔ ∃z. y2 = INR z ∧ g x2 z) ∧
  ((f +++ g) y3 (INL x3) ⇔ ∃z. y3 = INL z ∧ f z x3) ∧
  ((f +++ g) y4 (INR x4) ⇔ ∃z. y4 = INR z ∧ g z x4)
Proof
  rpt conj_tac
  >- (Cases_on ‘y1’ \\ gvs [])
  >- (Cases_on ‘y2’ \\ gvs [])
  >- (Cases_on ‘y3’ \\ gvs [])
  >- (Cases_on ‘y4’ \\ gvs [])
QED

Theorem next_thm:
  ∀k v c s w d t.
    ($= +++ v_rel) v w ∧
    cont_rel c d ∧
    LIST_REL (LIST_REL v_rel) s t
    ⇒
    next_rel (next k v c s) (next k w d t)
Proof
  ho_match_mp_tac next_ind \\ rw []
  \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs []
  >-
   (simp [env_semanticsTheory.next_def]
    \\ CASE_TAC \\ gs [])
  \\ rename1 ‘v_rel v w’
  \\ qpat_x_assum ‘v_rel _ _’ mp_tac
  \\ simp [Once v_rel_cases]
  \\ strip_tac \\ gvs []
  >- fs [next_def]
  >- fs [next_def]
  >- fs [next_def]
  >- fs [next_def]
  >- fs [next_def]
  >- fs [next_def]
  >- fs [next_def]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ Cases_on ‘m = Ret’ \\ fs [] >-
   (gvs []
    \\ once_rewrite_tac [next_def] \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘c’ \\ Cases_on ‘d’ \\ gvs []
    \\ gvs [with_value_def]
    >- (drule_all eval_exp_rel \\ every_case_tac \\ gvs [])
    >- (drule_all eval_exp_rel \\ every_case_tac \\ gvs []
        \\ rename [‘cont_rel (BC p1 c1) (BC p2 c2)’]
        \\ PairCases_on ‘p1’ \\ PairCases_on ‘p2’ \\ fs [] \\ strip_tac
        \\ last_x_assum $ drule_at_then Any $ drule_at Any \\ strip_tac
        \\ irule apply_closure_thm \\ fs [])
    >- (drule_all eval_exp_rel \\ every_case_tac \\ gvs [] \\ strip_tac
        \\ last_x_assum irule \\ fs []
        \\ simp [Once v_rel_cases]
        \\ rename [‘cont_rel (HC p1 c1) (HC p2 c2)’]
        \\ PairCases_on ‘p1’ \\ PairCases_on ‘p2’ \\ fs []))
  \\ Cases_on ‘m = Raise’ \\ fs [] >-
   (gvs []
    \\ once_rewrite_tac [next_def] \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘c’ \\ Cases_on ‘d’ \\ gvs []
    \\ gvs [with_value_def]
    >- (drule_all eval_exp_rel \\ every_case_tac \\ gvs [])
    >- (drule_all eval_exp_rel \\ every_case_tac \\ gvs [] \\ strip_tac
        \\ last_x_assum irule \\ fs []
        \\ simp [Once v_rel_cases]
        \\ rename [‘cont_rel (BC p1 c1) (BC p2 c2)’]
        \\ PairCases_on ‘p1’ \\ PairCases_on ‘p2’ \\ fs [])
    >- (drule_all eval_exp_rel \\ every_case_tac \\ gvs []
        \\ rename [‘cont_rel (HC p1 c1) (HC p2 c2)’]
        \\ PairCases_on ‘p1’ \\ PairCases_on ‘p2’ \\ fs [] \\ strip_tac
        \\ last_x_assum $ drule_at_then Any $ drule_at Any \\ strip_tac
        \\ irule apply_closure_thm \\ fs []))
  \\ Cases_on ‘m = Bind’ \\ fs [] >-
   (gvs []
    \\ once_rewrite_tac [next_def] \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ gvs []
    \\ last_x_assum irule \\ gvs []
    \\ irule eval_exp_rel \\ fs [])
  \\ Cases_on ‘m = Handle’ \\ fs [] >-
   (gvs []
    \\ once_rewrite_tac [next_def] \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ gvs []
    \\ last_x_assum irule \\ gvs []
    \\ irule eval_exp_rel \\ fs [])
  \\ Cases_on ‘m = Alloc’ \\ fs [] >-
   (gvs []
    \\ once_rewrite_tac [next_def] \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ gvs [LENGTH_EQ_NUM_compute,with_atoms_def,result_map_def]
    \\ drule_all eval_exp_rel
    \\ qpat_x_assum ‘compile_rel _ _’ kall_tac
    \\ dxrule_all eval_exp_rel
    \\ rpt strip_tac
    \\ gvs [AllCaseEqs()]
    \\ IF_CASES_TAC >- gvs [] \\ gvs []
    \\ qpat_abbrev_tac ‘p = next_rel rr’
    \\ IF_CASES_TAC >- gvs [Abbr‘p’] \\ gvs [Abbr‘p’]
    \\ IF_CASES_TAC >- gvs [] \\ gvs []
    \\ qpat_abbrev_tac ‘p = next_rel rr’
    \\ IF_CASES_TAC >- gvs [Abbr‘p’] \\ gvs [Abbr‘p’]
    \\ Cases_on ‘eval tenv h’ \\ gvs []
    >- (Cases_on ‘x’ \\ gvs [])
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases]
    \\ strip_tac \\ gvs [get_atoms_def]
    \\ Cases_on ‘a’ \\ gvs []
    \\ Cases_on ‘k=0’ \\ gvs [PULL_EXISTS]
    \\ last_x_assum irule \\ fs []
    \\ simp [Once v_rel_cases]
    \\ gvs [env_rel_def,freevars_def]
    \\ simp [Once compile_rel_cases,LIST_REL_REPLICATE]
    \\ rename [‘($= +++ v_rel) (eval tenv t1) (eval senv t2)’]
    \\ Cases_on ‘eval tenv t1’ \\ gvs []
    \\ Cases_on ‘x’ \\ gvs [])
  \\ Cases_on ‘m = Deref’ \\ fs [] >-
   (gvs []
    \\ once_rewrite_tac [next_def] \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ gvs [LENGTH_EQ_NUM_compute,with_atoms_def,result_map_def]
    \\ drule_all eval_exp_rel
    \\ qpat_x_assum ‘compile_rel _ _’ kall_tac
    \\ dxrule_all eval_exp_rel
    \\ rpt strip_tac
    \\ gvs [AllCaseEqs()]
    \\ IF_CASES_TAC >- gvs [] \\ gvs []
    \\ qpat_abbrev_tac ‘p = next_rel rr’
    \\ IF_CASES_TAC >- gvs [Abbr‘p’] \\ gvs [Abbr‘p’]
    \\ IF_CASES_TAC >- gvs [] \\ gvs []
    \\ qpat_abbrev_tac ‘p = next_rel rr’
    \\ IF_CASES_TAC >- gvs [Abbr‘p’] \\ gvs [Abbr‘p’]
    \\ Cases_on ‘eval tenv h’ \\ gvs []
    >- (Cases_on ‘x’ \\ gvs [])
    \\ Cases_on ‘eval tenv h'’ \\ gvs []
    >- (Cases_on ‘x’ \\ gvs [])
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases]
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases]
    \\ strip_tac \\ gvs [get_atoms_def]
    \\ strip_tac \\ gvs [get_atoms_def]
    \\ Cases_on ‘a’ \\ gvs []
    \\ Cases_on ‘a'’ \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ qpat_assum ‘LIST_REL (LIST_REL v_rel) s t’ mp_tac
    \\ simp_tac std_ss [Once LIST_REL_EL_EQN]
    \\ strip_tac
    \\ gvs [GSYM NOT_LESS]
    \\ pop_assum drule \\ strip_tac
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ reverse IF_CASES_TAC
    >-
     (fs [] \\ last_x_assum irule \\ fs []
      \\ simp [Once v_rel_cases]
      \\ simp [freevars_def,Once compile_rel_cases,env_rel_def]
      \\ Q.REFINE_EXISTS_TAC ‘_::_::[]’ \\ fs []
      \\ first_x_assum $ irule_at $ Pos hd \\ fs []
      \\ metis_tac [])
    \\ fs [] \\ last_x_assum irule \\ fs []
    \\ fs [PULL_EXISTS]
    \\ Q.REFINE_EXISTS_TAC ‘_::_::[]’ \\ fs []
    \\ simp [Once v_rel_cases]
    \\ simp [freevars_def,Once compile_rel_cases,env_rel_def]
    \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ gvs []
    \\ gvs [LIST_REL_EL_EQN])
  \\ Cases_on ‘m = Update’ \\ fs [] >-
   (gvs []
    \\ once_rewrite_tac [next_def] \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ gvs [LENGTH_EQ_NUM_compute,with_atoms_def,result_map_def]
    \\ drule_all eval_exp_rel
    \\ qpat_x_assum ‘compile_rel _ _’ kall_tac
    \\ drule_all eval_exp_rel
    \\ qpat_x_assum ‘compile_rel _ _’ kall_tac
    \\ drule_all eval_exp_rel
    \\ qpat_x_assum ‘compile_rel _ _’ kall_tac
    \\ rpt strip_tac
    \\ gvs [AllCaseEqs()]
    \\ IF_CASES_TAC >- gvs [] \\ gvs []
    \\ qpat_abbrev_tac ‘p = next_rel rr’
    \\ IF_CASES_TAC >- gvs [Abbr‘p’] \\ gvs [Abbr‘p’]
    \\ IF_CASES_TAC >- gvs [] \\ gvs []
    \\ qpat_abbrev_tac ‘p = next_rel rr’
    \\ IF_CASES_TAC >- gvs [Abbr‘p’] \\ gvs [Abbr‘p’]
    \\ Cases_on ‘eval tenv h’ \\ gvs []
    >- (Cases_on ‘x’ \\ gvs [])
    \\ Cases_on ‘eval tenv h'’ \\ gvs []
    >- (Cases_on ‘x’ \\ gvs [])
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases]
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases]
    \\ strip_tac \\ gvs [get_atoms_def]
    \\ strip_tac \\ gvs [get_atoms_def]
    \\ Cases_on ‘a’ \\ gvs []
    \\ Cases_on ‘a'’ \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ qpat_assum ‘LIST_REL (LIST_REL v_rel) s t’ mp_tac
    \\ simp_tac std_ss [Once LIST_REL_EL_EQN]
    \\ strip_tac
    \\ gvs [GSYM NOT_LESS]
    \\ pop_assum drule \\ strip_tac
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ reverse IF_CASES_TAC
    >-
     (fs [] \\ last_x_assum irule \\ fs []
      \\ simp [Once v_rel_cases]
      \\ simp [freevars_def,Once compile_rel_cases,env_rel_def]
      \\ Q.REFINE_EXISTS_TAC ‘_::_::[]’ \\ fs []
      \\ first_x_assum $ irule_at $ Pos hd \\ fs []
      \\ metis_tac [])
    \\ fs [] \\ last_x_assum irule \\ fs []
    \\ simp [Once v_rel_cases]
    \\ simp [freevars_def,Once compile_rel_cases,env_rel_def]
    \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ gvs []
    \\ rename [‘(OUTR (eval tenv h4))’]
    \\ Cases_on ‘eval tenv h4’ \\ gvs []
    >- (Cases_on ‘x’ \\ gvs [])
    \\ irule LIST_REL_LUPDATE \\ fs []
    \\ irule LIST_REL_LUPDATE \\ fs [])
  \\ Cases_on ‘m = Length’ \\ fs [] >-
   (gvs []
    \\ once_rewrite_tac [next_def] \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ gvs [LENGTH_EQ_NUM_compute,with_atoms_def,result_map_def]
    \\ drule_all eval_exp_rel
    \\ Cases_on ‘eval tenv h’ \\ Cases_on ‘eval senv h'’ \\ gvs []
    >-
     (strip_tac \\ gvs []
      \\ IF_CASES_TAC \\ gvs []
      \\ IF_CASES_TAC \\ gvs []
      \\ Cases_on ‘x’ \\ gvs [])
    \\ simp [Once v_rel_cases]
    \\ strip_tac \\ gvs [get_atoms_def]
    \\ TOP_CASE_TAC \\ gvs []
    \\ IF_CASES_TAC \\ gvs []
    \\ IF_CASES_TAC \\ gvs []
    \\ last_x_assum irule \\ fs []
    \\ simp [Once v_rel_cases] \\ fs []
    \\ gvs [freevars_def]
    \\ simp [Once compile_rel_cases]
    \\ gvs [env_rel_def]
    \\ gvs [GSYM NOT_LESS]
    \\ qpat_x_assum ‘LIST_REL (LIST_REL v_rel_) _ _’ mp_tac
    \\ simp [Once LIST_REL_EL_EQN]
    \\ disch_then drule
    \\ strip_tac \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ Q.REFINE_EXISTS_TAC ‘x::xs’ \\ fs [])
  \\ Cases_on ‘m = Act’ \\ fs [] >-
   (gvs []
    \\ once_rewrite_tac [next_def] \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ gvs [LENGTH_EQ_NUM_compute,with_atoms_def,result_map_def]
    \\ drule_all eval_exp_rel
    \\ Cases_on ‘eval tenv h’ \\ Cases_on ‘eval senv h'’ \\ gvs []
    >-
     (strip_tac \\ gvs []
      \\ IF_CASES_TAC \\ gvs []
      \\ IF_CASES_TAC \\ gvs []
      \\ Cases_on ‘x’ \\ gvs [])
    \\ simp [Once v_rel_cases]
    \\ strip_tac \\ gvs [get_atoms_def]
    \\ CASE_TAC \\ gvs [])
  \\ Cases_on ‘m’ \\ gvs []
QED

Theorem next_action_thm:
  ($= +++ v_rel) v w ∧
  cont_rel c d ∧
  LIST_REL (LIST_REL v_rel) s t ⇒
  next_rel (next_action v c s) (next_action w d t)
Proof
  strip_tac
  \\ rw [next_action_def,env_semanticsTheory.next_action_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ simp [PULL_FORALL]
  \\ qx_gen_tac ‘i’
  \\ qx_gen_tac ‘j’
  \\ qx_gen_tac ‘k’
  \\ rw []
  >-
   (drule_all next_thm
    \\ dxrule env_semanticsTheory.next_less_eq
    \\ disch_then $ qspec_then ‘i+j’ assume_tac
    \\ dxrule env_semanticsTheory.next_less_eq
    \\ disch_then $ qspec_then ‘i+j’ assume_tac
    \\ fs [])
  >-
   (last_x_assum (qspec_then ‘i’ assume_tac)
    \\ drule_all_then assume_tac next_thm
    \\ last_x_assum (qspec_then ‘i’ assume_tac)
    \\ gvs [])
  >-
   (last_x_assum (qspec_then ‘k’ assume_tac)
    \\ drule_all_then assume_tac next_thm
    \\ last_x_assum (qspec_then ‘k’ assume_tac)
    \\ gvs [])
QED

(* --------------------- interp and semantics ----------------------- *)

Theorem interp_eq:
  ($= +++ v_rel) v w ∧
  cont_rel c d ∧
  LIST_REL (LIST_REL v_rel) s t ⇒
  interp v c s = interp w d t
Proof
  strip_tac
  \\ rw [Once itreeTheory.itree_bisimulation]
  \\ qexists_tac `λt1 t2.
    (t1 = t2 ∨
     ∃v c s w d t.
       interp v c s = t1 ∧
       interp w d t = t2 ∧
       ($= +++ v_rel) v w ∧
       cont_rel c d ∧
       LIST_REL (LIST_REL v_rel) s t)`
  \\ rw []
  >~ [‘interp v c s = interp w d t’] >-
   (disj2_tac >> rpt $ irule_at Any EQ_REFL >> simp[])
  \\ drule_all next_action_thm \\ strip_tac
  \\ qpat_assum ‘interp _ _ _ = _’ mp_tac
  >~ [‘Ret’] >-
   (gvs []
    \\ qpat_x_assum ‘env_semantics$interp _ _ _ = _’ mp_tac
    \\ once_rewrite_tac [env_semanticsTheory.interp_def]
    \\ simp [AllCaseEqs()]
    \\ rw [] \\ gvs []
    \\ Cases_on `next_action w' d' t''` \\ gvs [])
  >~ [‘Div’] >-
   (gvs []
    \\ qpat_x_assum ‘env_semantics$interp _ _ _ = _’ mp_tac
    \\ once_rewrite_tac [env_semanticsTheory.interp_def]
    \\ simp [AllCaseEqs()]
    \\ rw [] \\ gvs []
    \\ Cases_on `next_action w' d' t''` \\ gvs [])
  \\ gvs []
  \\ qpat_x_assum ‘env_semantics$interp _ _ _ = _’ mp_tac
  \\ simp [Once env_semanticsTheory.interp_def]
  \\ simp [AllCaseEqs()]
  \\ rw [] \\ gvs []
  \\ Cases_on `next_action w' d' t''` \\ gvs[]
  \\ simp [Once env_semanticsTheory.interp_def]
  \\ rw []
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ disj2_tac
  \\ rpt (irule_at Any EQ_REFL)
  \\ rpt $ first_assum $ irule_at Any
  \\ fs []
  \\ simp [Once v_rel_cases]
  \\ gvs [freevars_def]
  \\ simp [Once compile_rel_cases]
  \\ gvs [env_rel_def]
  \\ simp [Once v_rel_cases]
QED

Theorem exp_rel_semantics:
  compile_rel x y ∧
  closed x
  ⇒
  env_semantics$semantics x [] Done [] =
  env_semantics$semantics y [] Done []
Proof
  strip_tac
  \\ rw [env_semanticsTheory.semantics_def]
  \\ irule interp_eq
  \\ irule_at Any eval_exp_rel
  \\ fs [closed_def,env_rel_def]
QED

val _ = export_theory ();
