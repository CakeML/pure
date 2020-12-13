(*
  Theorem beta_equivalence:
    App (Lam x body) arg ≅ CA_subst x arg body

  where CA_subst is the capture-avoiding substitution of the free variables "x"
  in the expression "body" with the expression "arg"

  the main theorem above state's that two beta-equivalent expressions
  belong to the same equivalence class under the eval function.
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_miscTheory
     pure_exp_relTheory pure_alpha_equivTheory pure_congruenceTheory;


val _ = new_theory "pure_beta_equiv";


Definition fresh_var_def:
  fresh_var v xs = if ¬MEM v xs
                   then v
                   else fresh_var (v ++ "'") xs
Termination
  WF_REL_TAC ‘measure (λ(v,xs). (LENGTH (FLAT xs) + 1) - LENGTH v)’ \\ rw[]
  \\ Induct_on ‘xs’ \\ fs[] \\ rpt strip_tac \\ fs[]
End

Theorem fresh_var_correctness:
  ∀v l. ¬ MEM (fresh_var v l) l
Proof
  recInduct fresh_var_ind \\ rw []
  \\ once_rewrite_tac [fresh_var_def]
  \\ IF_CASES_TAC \\ fs[]
QED

Definition fresh_var_list_def:
  fresh_var_list []      to_avoid = [] ∧
  fresh_var_list (x::xs) to_avoid = let fresh = fresh_var x to_avoid;
                                    in ((x,fresh)::fresh_var_list xs (fresh::to_avoid))
End

Theorem MAP_FST_fresh_var_list:
  ∀ v avoid. MAP FST (fresh_var_list v avoid) = v
Proof
  Induct \\ fs[fresh_var_list_def,MAP]
QED

Theorem fresh_var_list_correctness:
  ∀v l. DISJOINT (set (MAP SND (fresh_var_list v l))) (set l)
Proof
  Induct \\ fs[fresh_var_list_def]
  \\ rw[] \\ fs[fresh_var_correctness]
  \\ pop_assum (qspec_then ‘(fresh_var h l::l)’ assume_tac)
  \\ fs[EXTENSION,DISJOINT_DEF]
  \\ metis_tac[]
QED

Theorem fresh_var_list_distinctness:
  ∀vars avoids. ALL_DISTINCT (MAP SND (fresh_var_list vars avoids))
Proof
  Induct \\ fs[fresh_var_list_def]
  \\ rw[] \\ fs[]
  \\ CCONTR_TAC \\ fs[]
  \\ qspecl_then [‘vars’,‘(fresh_var h avoids::avoids)’]
                 assume_tac fresh_var_list_correctness
  \\ CCONTR_TAC
  \\ fs[]
QED

Theorem perm_exp_size_lemma:
 ∀ e. list_size char_size s = list_size char_size s'
      ⇒ exp_size (perm_exp s s' e) = exp_size e
Proof
  GEN_TAC
  \\ completeInduct_on ‘exp_size e’
  \\ fs[PULL_FORALL]
  \\ rw[]
  \\ Cases_on ‘e’
  THEN1(
   fs[perm_exp_def, perm1_def]
   \\ fs[exp_size_def]
   \\ IF_CASES_TAC \\ fs[]
   \\ IF_CASES_TAC \\ fs[]
  )
  THEN1(
   fs[perm_exp_def, perm1_def]
   \\ fs[exp_size_def]
   \\ Induct_on ‘l’ \\ fs[]
   \\ rw[] \\ fs[exp_size_def]
  )
  THEN1(
   fs[perm_exp_def, perm1_def]
   \\ fs[exp_size_def]
  )
  THEN1(
   fs[perm_exp_def, perm1_def]
   \\ fs[exp_size_def]
   \\ IF_CASES_TAC \\ fs[]
   \\ IF_CASES_TAC \\ fs[]
  )
  THEN1(
   fs[perm_exp_def,exp_size_def]
   \\ Induct_on ‘l’ \\ fs[]
   \\ strip_tac
   \\ fs[exp_size_def]
   \\ rw[] \\ fs[exp_size_def]
   \\ Cases_on ‘h’ \\ fs[] \\ fs[exp_size_def] \\ rw[]
   \\ fs[perm_exp_def,exp_size_def,perm1_def]
   \\ IF_CASES_TAC \\ fs[perm_exp_def,exp_size_def]
   \\ IF_CASES_TAC \\ fs[perm_exp_def,exp_size_def]
  )
QED

Definition exp_size'_def:
  exp_size' (Var        a) = 1                                   ∧
  exp_size' (Prim   a0 a1) = 1 + (op_size a0 + exp3_size' a1)    ∧
  exp_size' (App    a0 a1) = 1 + (exp_size' a0 + exp_size' a1)   ∧
  exp_size' (Lam    a0 a1) = 1 + (1 + exp_size' a1)              ∧
  exp_size' (Letrec a0 a1) = 1 + (exp1_size' a0 + exp_size' a1)  ∧
  exp1_size' [] = 0                                              ∧
  exp1_size' (a0::a1) = 1 + (exp2_size' a0 + exp1_size' a1)      ∧
  exp2_size' (a0, a1) = 1 + (1 + exp_size' a1)                   ∧
  exp3_size' [] = 0                                              ∧
  exp3_size' (a0::a1) = 1 + (exp_size' a0 + exp3_size' a1)
End

Theorem exp_size'_lemma:
  ∀ r. MEM (q,r) l' ⇒ exp_size' r < exp1_size' l'
Proof
  Induct_on ‘l'’ \\ fs[] \\ Cases \\ rw[] \\ fs[exp_size'_def]
  \\ res_tac \\ fs[]
QED

Theorem perm_exp_size'_mono:
  ∀ s s' e. exp_size' (perm_exp s s' e) = exp_size' e
Proof
  rw[]
  \\ completeInduct_on ‘exp_size' e’
  \\ rw[]
  \\ fs[PULL_FORALL]
  \\ Cases_on ‘e’
  \\ fs[exp_size'_def,perm_exp_def,perm1_def]
  THEN1 (
    Induct_on ‘l’ \\ fs[]
    \\ fs[exp_size'_def,perm_exp_def,perm1_def]
  )
  THEN1 (
    Induct_on ‘l’ \\ fs[]
    \\ Cases
    \\ fs[exp_size'_def,perm_exp_def,perm1_def]
  )
QED


(**************** perm_exp lemmas ******************)

Triviality perm1_MAP_set:
 ∀ l.  set l DELETE x DELETE y ⊆ set (MAP (perm1 x y) l)
Proof
  Induct \\ fs[]
  \\ strip_tac \\ rw[perm1_def]
  \\ fs [EXTENSION,SUBSET_DEF] \\ metis_tac []
QED

Triviality subset_union_weakening_gen1:
 A ⊆ x INSERT y INSERT B ⇒ A ⊆ x INSERT y INSERT (B ∪ C)
Proof
  fs [EXTENSION,SUBSET_DEF] \\ metis_tac []
QED

Triviality subset_union_weakening_gen2:
 A ⊆ x INSERT y INSERT C ⇒ A ⊆ x INSERT y INSERT (B ∪ C)
Proof
  fs [EXTENSION,SUBSET_DEF] \\ metis_tac []
QED

Triviality Letrec_SUBSET_INSERT_DIFF_DISTRIBUTIVITY:
  A ⊆ y INSERT x INSERT B ∪ D
  ∧ E DELETE x DELETE y ⊆ C
  ⇒
  A DIFF C ⊆ y INSERT x INSERT ((B ∪ D) DIFF E)
Proof
  fs [EXTENSION,SUBSET_DEF] \\ metis_tac []
QED

Triviality subset_union_weakening:
  A ⊆ B ⇒ (A ⊆ (B ∪ C))
Proof
  fs [EXTENSION,SUBSET_DEF] \\ metis_tac []
QED

Triviality DIFF_UNION_DISTRIBUTIVITY:
  (A ∪ B) DIFF C = (A DIFF C) ∪ (B DIFF C)
Proof
  fs [EXTENSION,SUBSET_DEF] \\ metis_tac []
QED

Triviality  perm1_MAP_set2:
 ∀ l. set (MAP (perm1 x y) l) DELETE x DELETE y ⊆ set l
Proof
  Induct \\ fs[]
  \\ strip_tac \\ rw[perm1_def]
  \\ fs [EXTENSION,SUBSET_DEF] \\ metis_tac []
QED

Theorem freevars_perm_exp_subset:
  ∀ e. freevars (perm_exp x y e) ⊆ y INSERT x INSERT freevars e
Proof
  ho_match_mp_tac freevars_ind \\ rw[]
  THEN1 (fs[perm_exp_def,perm1_def] \\ rw[])
  THEN1 (
    fs[perm_exp_def,perm1_def]
    \\fs[MAP_MAP_o,combinTheory.o_DEF,LIST_TO_SET_FLAT]
    \\ Induct_on ‘es’ \\ fs[]
    \\ strip_tac \\ strip_tac
    \\ fs[GSYM INSERT_UNION_EQ]
    \\ rw[]
    THEN1 (
      irule subset_union_weakening \\ fs[]
    )
    \\ simp[INSERT_UNION_EQ]
    \\ match_mp_tac (GEN_ALL subset_union_weakening_gen2) \\ fs[]
  )
  THEN1(
    fs[perm_exp_def,perm1_def]
    \\ conj_tac
    \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
  )
  THEN1(
    fs[perm_exp_def,perm1_def,freevars_def]
    \\ fs[] \\ rw[]
    \\ fs [EXTENSION,SUBSET_DEF,MEM_FILTER] \\ TRY( metis_tac [])
  )
  THEN1(
    fs[perm_exp_def]
    \\ fs[FILTER_FLAT,FILTER_APPEND_DISTRIB,MAP_MAP_o,combinTheory.o_DEF]
    \\ ‘(λx'. FST ((λ(x',z). (perm1 x y x',perm_exp x y z)) x')) =(perm1 x y) ∘ FST’ by (
       fs[FUN_EQ_THM]
       \\ Cases \\ fs[]
    )
    \\ fs[] \\ pop_assum kall_tac
    \\ conj_tac
    THEN1 (
      fs[GSYM list_to_set_diff]
      \\ match_mp_tac Letrec_SUBSET_INSERT_DIFF_DISTRIBUTIVITY \\ fs[]
      \\ conj_tac
      THEN1 ( match_mp_tac subset_union_weakening_gen1 \\ fs[])
      \\ fs[GSYM MAP_MAP_o]
      \\ fs[perm1_MAP_set]
    )
    \\ ‘(λx'. FILTER (λn. ¬MEM n (MAP (perm1 x y ∘ FST) lcs))
                       ((λ(fn,e'). freevars e')
                       ((λ(x',z). (perm1 x y x',perm_exp x y z)) x')))
        =
        FILTER (λn. ¬MEM n (MAP (perm1 x y ∘ FST) lcs))
        ∘ freevars
        ∘ (perm_exp x y)
        ∘ SND ’ by (
       fs[FUN_EQ_THM]
       \\ Cases \\ rw[]
    ) \\ fs[] \\ pop_assum kall_tac
    \\ fs[MAP_FILTER]
    \\ fs[GSYM MAP_MAP_o]
    \\ fs[GSYM FILTER_FLAT]
    \\ fs[GSYM list_to_set_diff]
    \\ match_mp_tac Letrec_SUBSET_INSERT_DIFF_DISTRIBUTIVITY  \\ fs[]
    \\ reverse (rw[]) THEN1 (fs[perm1_MAP_set])
    \\ match_mp_tac subset_union_weakening_gen2 \\ fs[]
    \\ fs[MAP_MAP_o,LIST_TO_SET_FLAT]
    \\ fs[BIGUNION_SUBSET]
    \\ fs[MEM_MAP]
    \\ strip_tac \\ rw[]
    \\ Cases_on ‘y'’ \\ fs[]
    \\ match_mp_tac SUBSET_TRANS
    \\ qexists_tac ‘ y INSERT x INSERT freevars r’
    \\ conj_tac THEN1 (res_tac \\ fs[])
    \\ fs[]
    \\ res_tac
    \\ ‘set (MAP (λ(fn,e). freevars e) lcs) = set (MAP set (MAP (freevars o SND) lcs))’by(
      ntac 4 (pop_assum kall_tac)
      \\ Induct_on ‘lcs’ \\ fs[]
      \\ Cases \\ fs[]
    )
    \\ fs[] \\ pop_assum kall_tac
    \\ fs[GSYM LIST_TO_SET_FLAT]
    \\ fs[SUBSET_INSERT_DELETE]
    \\ Induct_on ‘lcs’ \\ fs[MEM]
    \\ rw[]
    \\ res_tac \\ fs[]
    \\ TRY (Cases_on ‘h’) \\ rw[]
    \\ fs [EXTENSION,SUBSET_DEF] \\ metis_tac []
  )
QED

Theorem freevars_perm_exp_subset_inv:
  ∀e. freevars e ⊆ y INSERT x INSERT freevars (perm_exp x y e)
Proof
  ho_match_mp_tac freevars_ind \\ rw[]
  THEN1 (fs[perm_exp_def,perm1_def] \\ rw[])
  THEN1 (
    fs[perm_exp_def,perm1_def]
    \\fs[MAP_MAP_o,combinTheory.o_DEF,LIST_TO_SET_FLAT]
    \\ Induct_on ‘es’ \\ fs[]
    \\ strip_tac \\ strip_tac
    \\ fs[GSYM INSERT_UNION_EQ]
    \\ rw[]
    THEN1 (
      irule subset_union_weakening \\ fs[]
    )
    \\ simp[INSERT_UNION_EQ]
    \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
  )
  THEN1(
    fs[perm_exp_def,perm1_def]
    \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
  )
  THEN1(
    fs[perm_exp_def,perm1_def]
    \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
  )
  THEN1(
    fs[perm_exp_def,perm1_def,freevars_def]
    \\ fs[] \\ rw[]
    \\ fs [EXTENSION,SUBSET_DEF,MEM_FILTER] \\ TRY( metis_tac [])
  )
  THEN1(
    fs[perm_exp_def]
    \\ fs[FILTER_FLAT,FILTER_APPEND_DISTRIB,MAP_MAP_o,combinTheory.o_DEF]
    \\ ‘(λx'. FST ((λ(x',z). (perm1 x y x',perm_exp x y z)) x')) = (perm1 x y) ∘ FST’ by (
       fs[FUN_EQ_THM]
       \\ Cases \\ fs[]
    )
    \\ fs[] \\ pop_assum kall_tac
    \\ ‘(λx'. FILTER (λn. ¬MEM n (MAP (perm1 x y ∘ FST) lcs))
                       ((λ(fn,e'). freevars e')
                       ((λ(x',z). (perm1 x y x',perm_exp x y z)) x')))
        =
        FILTER (λn. ¬MEM n (MAP (perm1 x y ∘ FST) lcs))
        ∘ freevars
        ∘ (perm_exp x y)
        ∘ SND ’ by (
       fs[FUN_EQ_THM]
       \\ Cases \\ rw[]
    ) \\ fs[] \\ pop_assum kall_tac
    \\ fs[MAP_FILTER]
    \\ fs[GSYM MAP_MAP_o]
    \\ fs[GSYM FILTER_FLAT]
    \\ fs[GSYM list_to_set_diff]
    \\ fs[DIFF_UNION_DISTRIBUTIVITY]
    \\ conj_tac
    THEN1 (
      fs[GSYM DIFF_UNION_DISTRIBUTIVITY]
      \\ match_mp_tac Letrec_SUBSET_INSERT_DIFF_DISTRIBUTIVITY  \\ fs[]
      \\ conj_tac
      THEN1 (match_mp_tac subset_union_weakening_gen1 \\ fs[])
      \\ fs[perm1_MAP_set2]
    )
    \\ fs[GSYM DIFF_UNION_DISTRIBUTIVITY]
    \\ match_mp_tac Letrec_SUBSET_INSERT_DIFF_DISTRIBUTIVITY  \\ fs[]
    \\ reverse (rw[]) THEN1 (fs[perm1_MAP_set2])
    \\ match_mp_tac subset_union_weakening_gen2 \\ fs[]
    \\ fs[MAP_MAP_o] \\ fs[GSYM LIST_TO_SET_FLAT]
    \\ fs[BIGUNION_SUBSET]
    \\ fs[MEM_MAP]
    \\ fs[GSYM UNION_SUBSET]
    \\ strip_tac \\ rw[]
    \\ Cases_on ‘y'’ \\ fs[]
    \\ res_tac
    \\ match_mp_tac SUBSET_TRANS
    \\ qexists_tac ‘ y INSERT x INSERT freevars (perm_exp x y r)’
    \\ conj_tac THEN1 (fs [EXTENSION,SUBSET_DEF] \\ metis_tac[])
    \\ fs[GSYM LIST_TO_SET_FLAT]
    \\ fs[SUBSET_INSERT_DELETE]
    \\ Induct_on ‘lcs’ \\ fs[MEM]
    \\ rw[]
    \\ res_tac \\ fs[]
    \\ fs [EXTENSION,SUBSET_DEF] \\ metis_tac []
  )
QED

Theorem freevar_perm_exp_MEM:
 ∀ e. MEM x (freevars e) ⇒ MEM y (freevars (perm_exp x y e))
Proof
  ho_match_mp_tac freevars_ind
  \\ rpt conj_tac
  THEN1( fs[perm_exp_def,perm1_def] \\ rw[])
  THEN1(
     rw[] \\ fs[MEM_MAP] \\ rw[]
     \\ res_tac
     \\ fs[freevars_def,perm_exp_def,perm1_def]
     \\ fs[MEM_FLAT]
     \\ qexists_tac ‘(freevars (perm_exp x y e))’ \\ fs[]
     \\ fs[MAP_MAP_o,combinTheory.o_DEF]
     \\ fs[MEM_MAP]
     \\ qexists_tac ‘e’ \\ fs[]
  )
  THEN1(rw[] \\ fs[perm_exp_def,perm1_def])
  THEN1(
    fs[perm_exp_def,perm1_def]
    \\ rw[] \\ fs[MEM_FILTER]
  )
  THEN1(
    rpt strip_tac
    \\ fs[freevars_def,perm_exp_def,perm1_def]
    THEN1 (
      fs[MEM_FILTER]
      \\ fs[MAP_MAP_o,combinTheory.o_DEF]
      \\ CCONTR_TAC \\ fs[]
      \\ fs[MEM_MAP]
      \\ Cases_on ‘x'’ \\ fs[]
      \\ Cases_on ‘q = x’ \\ fs[]
      THEN1 (first_assum (qspec_then ‘(x,r)’ assume_tac) \\ fs[])
      \\ Cases_on ‘q = y’ \\ fs[]
   )
   \\ fs[MEM_FILTER]
   \\ fs[MAP_MAP_o,combinTheory.o_DEF]
   \\ fs[MEM_MAP]
   \\ CCONTR_TAC \\ fs[]
   THEN1 (
     Cases_on ‘x'’ \\ fs[]
     \\ Cases_on ‘q = x’ \\ rw[] \\ fs[]
     \\ first_assum (qspec_then ‘(q,r)’ assume_tac) \\ rw[] \\ fs[]
     \\ Cases_on ‘q = y’ \\ fs[]
   )
   \\ rw[]
   \\ fs[MEM_MAP]
   \\ fs[MEM_FLAT]
   \\ fs[MEM_MAP]
   \\ Cases_on ‘y'’ \\ res_tac \\ fs[] \\ res_tac \\ fs[]
   \\ first_x_assum (qspec_then ‘freevars (perm_exp x y r)’ assume_tac) \\ rw[] \\ fs[]
   \\ first_x_assum (qspec_then ‘(q,r)’ assume_tac) \\ rw[] \\ fs[]
  )
QED

Theorem freevar_perm_exp_not_MEM:
 ∀ e. ¬MEM x (freevars e) ⇒ ¬ MEM y (freevars (perm_exp x y e))
Proof
  ho_match_mp_tac freevars_ind
  \\ rpt conj_tac
  THEN1( fs[perm_exp_def,perm1_def] \\ rw[])
  THEN1(
    rw[]
    \\ fs[MEM_MAP]
    \\ fs[freevars_def,perm_exp_def,perm1_def]
    \\ fs[MEM_FLAT]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[MEM_MAP]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ res_tac
    \\ first_assum (qspec_then ‘set (freevars a)’ assume_tac)
    \\ fs[] \\ fs[]
    \\ pop_assum (qspec_then ‘a’ assume_tac) \\ fs[]
  )
  THEN1(rw[] \\ fs[perm_exp_def,perm1_def])
  THEN1(
    fs[perm_exp_def,perm1_def]
    \\ rw[] \\ fs[MEM_FILTER]
  )
  THEN1(
    fs[freevars_def,perm_exp_def,perm1_def]
    \\ rw[]
    THEN1 (
      fs[MEM_FILTER,MEM_FLAT,MEM_MAP,MAP_MAP_o,combinTheory.o_DEF]
      \\ CCONTR_TAC \\ fs[] \\ rw[] \\ fs[]
      \\ Cases_on ‘y''’ \\ rw[] \\ fs[]
      \\ res_tac
      \\ Cases_on ‘MEM x (freevars r)’ \\ fs[]
      \\ last_x_assum (qspec_then ‘freevars r’ assume_tac) \\ rw[] \\ fs[]
      \\ pop_assum (qspec_then ‘(q,r)’ assume_tac) \\ rw[] \\ fs[]
    )
    \\ fs[GSYM perm1_def]
    \\ fs[MEM_FILTER]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF] \\ rw[]
    \\ disj1_tac
    \\ ‘(λx'. FST ((λ(x',z). (perm1 x y x',perm_exp x y z)) x')) = (perm1 x y) o FST’ by (
       fs[FUN_EQ_THM]
       \\ Cases \\ rw[]
    )
    \\ fs[] \\ pop_assum kall_tac
    \\ fs[MEM_MAP]
    \\ qexists_tac ‘y'’ \\ fs[]
    \\ Cases_on ‘y'’ \\ fs[perm1_def]
  )
QED

Theorem freevars_perm_exp:
  freevars (perm_exp x y e) =
     freevars e
     DIFF (if x ∉ freevars e then {y} else ∅)
     DIFF (if y ∉ freevars e then {x} else ∅)
     ∪ (if x ∈ freevars e then {y} else ∅)
     ∪ (if y ∈ freevars e then {x} else ∅)
Proof
  rw[]
  \\ assume_tac (GEN_ALL freevars_perm_exp_subset)
  \\ assume_tac (GEN_ALL freevars_perm_exp_subset_inv)
  \\ assume_tac (GEN_ALL freevar_perm_exp_MEM)
  \\ assume_tac (GEN_ALL freevar_perm_exp_not_MEM)
  \\ TRY (fs [EXTENSION,SUBSET_DEF] \\ metis_tac [perm_exp_sym])
QED

Theorem boundvars_perm_exp_subset:
  ∀ e.
  boundvars (perm_exp x y e) ⊆ x INSERT y INSERT (boundvars e)
Proof
  recInduct boundvars_ind
  \\ rw[]
  THEN1 (fs[perm_exp_def])
  THEN1 (
    fs[perm_exp_def]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[LIST_TO_SET_FLAT]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[MEM_MAP]
    \\ fs[BIGUNION_SUBSET]
    \\ rw[]
    \\ fs[MEM_MAP]
    \\ last_assum (qspec_then ‘a’ assume_tac)
    \\ res_tac \\ fs[]
    \\ irule SUBSET_TRANS
    \\ qexists_tac ‘ x INSERT y INSERT boundvars a’
    \\ fs[]
    \\ irule SUBSET_INSERT_RIGHT
    \\ irule SUBSET_INSERT_RIGHT
    \\ irule SUBSET_BIGUNION_I
    \\ fs[MEM_MAP]
    \\ qexists_tac ‘a’ \\ fs[]
  )
  THEN1 (
    fs[perm_exp_def]
    \\ fs[DISJOINT_SYM]
    \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
  )
  THEN1 (
    fs[perm_exp_def,boundvars_def,perm1_def]
    \\ rw[]
    \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
  )
  \\ fs[perm_exp_def]
  \\ reverse conj_tac
  THEN1 (fs[EXTENSION,SUBSET_DEF] \\ metis_tac[])
  \\ fs[MAP_MAP_o,combinTheory.o_DEF]
  \\ fs[LIST_TO_SET_FLAT]
  \\ fs[MAP_MAP_o,combinTheory.o_DEF]
  \\ fs[MEM_MAP]
  \\ fs[BIGUNION_SUBSET]
  \\ rw[]
  \\ fs[MEM_MAP]
  \\ Cases_on ‘x'’
  \\ fs[perm1_def]
  \\ reverse conj_tac
  THEN1 (
     rw[]
     \\ res_tac
     \\ irule SUBSET_TRANS
     \\ qexists_tac ‘x INSERT y INSERT
                     BIGUNION (set (MAP (λ(fn,e). fn INSERT boundvars e) lcs))’
     \\ reverse conj_tac
     THEN1 (fs[EXTENSION,SUBSET_DEF,UNION_DEF] \\ metis_tac[])
     \\ fs[SUBSET_INSERT_DELETE]
     \\ irule SUBSET_TRANS
     \\ qexists_tac ‘q INSERT boundvars r’
     \\ conj_tac
     THEN1 (fs[EXTENSION,SUBSET_DEF,UNION_DEF] \\ metis_tac[])
     \\ irule SUBSET_BIGUNION_I
     \\ fs[MEM_MAP]
     \\ qexists_tac ‘(q,r)’ \\ fs[]
  )
  \\ rw[]
  \\ disj2_tac
  \\ qexists_tac ‘q INSERT boundvars r’
  \\ fs[]
  \\ fs[MEM_MAP]
  \\ qexists_tac ‘(q,r)’ \\ fs[]
QED

Theorem boundvars_perm_exp_subset_inv:
  ∀e. boundvars e ⊆ x INSERT y INSERT boundvars (perm_exp x y e)
Proof
  recInduct boundvars_ind
  \\ rw[]
  THEN1 (
    fs[perm_exp_def]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[LIST_TO_SET_FLAT]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[MEM_MAP]
    \\ fs[BIGUNION_SUBSET]
    \\ rw[]
    \\ fs[MEM_MAP]
    \\ res_tac
    \\ irule SUBSET_TRANS
    \\ qexists_tac ‘ x INSERT y INSERT boundvars (perm_exp x y e)’
    \\ fs[]
    \\ irule SUBSET_INSERT_RIGHT
    \\ irule SUBSET_INSERT_RIGHT
    \\ irule SUBSET_BIGUNION_I
    \\ fs[MEM_MAP]
    \\ qexists_tac ‘e’ \\ fs[]
  )
  THEN1 (
    fs[perm_exp_def]
    \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
  )
  THEN1 (
    fs[perm_exp_def]
    \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
  )
  THEN1 (
    fs[perm_exp_def]
    \\ fs[perm1_def]
    \\ rw[]
  )
  THEN1 (
    fs[perm_exp_def]
    \\ fs[perm1_def]
    \\ rw[]
    \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
  )
  THEN1 (
    fs[perm_exp_def]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[LIST_TO_SET_FLAT]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[EXTENSION,UNION_DEF,SUBSET_DEF] \\ metis_tac[]
  )
  \\ fs[perm_exp_def]
  \\ fs[MAP_MAP_o,combinTheory.o_DEF]
  \\ fs[LIST_TO_SET_FLAT]
  \\ fs[MAP_MAP_o,combinTheory.o_DEF]
  \\ fs[BIGUNION_SUBSET]
  \\ rw[]
  \\ fs[MEM_MAP]
  \\ Cases_on ‘y'’
  \\ fs[perm1_def]
  \\ rw[]
  THEN1 (
    CCONTR_TAC \\ fs[] \\ res_tac \\ fs[MEM_MAP]
    \\ first_assum (qspec_then ‘q INSERT (boundvars (perm_exp x y r))’ assume_tac) \\ fs[]
    \\ first_assum (qspec_then ‘(q,r)’ assume_tac) \\ fs[]
    \\ pop_assum mp_tac \\ rw[]
  )
  \\ res_tac
  \\ fs[SUBSET_INSERT_DELETE]
  \\ irule SUBSET_TRANS
  \\ qexists_tac ‘perm1 x y q INSERT boundvars (perm_exp x y r)’
  \\ conj_tac THEN1 (fs[EXTENSION,SUBSET_DEF] \\ metis_tac[])
  \\ irule subset_union_weakening
  \\ irule SUBSET_BIGUNION_I
  \\ fs[MEM_MAP]
  \\ qexists_tac ‘(q,r)’ \\ fs[perm1_def] \\ rw[]
QED

Theorem boundvar_perm_exp_MEM:
 ∀ e. MEM x (boundvars e) ⇒ MEM y (boundvars (perm_exp x y e))
Proof
  ho_match_mp_tac boundvars_ind
  \\ rw[]
  \\ fs[perm_exp_def]
  \\ fs[perm1_def]
  THEN1 (
    fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[MEM_FLAT]
    \\ fs[MEM_MAP]
    \\ rw[]
    \\ res_tac
    \\ qexists_tac ‘boundvars (perm_exp x y e)’
    \\ rw[]
    \\ qexists_tac ‘e’
    \\ fs[]
  )
  \\ fs[GSYM perm1_def]
  \\ fs[MAP_MAP_o,combinTheory.o_DEF]
  \\ fs[MEM_FLAT]
  \\ fs[MEM_MAP]
  \\ rw[]
  \\ Cases_on ‘y'’
  \\ res_tac \\ fs[] \\ rw[]
  THEN1 (
    disj1_tac
    \\ qexists_tac ‘y::(boundvars (perm_exp q y r))’
    \\ fs[] \\ rw[]
    \\ qexists_tac ‘(q,r)’
    \\ fs[] \\ rw[]
    \\ fs[perm1_def]
  )
  \\ res_tac \\ fs[] \\ rw[]
  \\ disj1_tac
  \\ Cases_on ‘MEM y (boundvars (perm_exp x y e))’ \\ fs[]
  \\ qexists_tac ‘perm1 x y q::(boundvars (perm_exp x y r))’
  \\ fs[] \\ rw[]
  \\ qexists_tac ‘(q,r)’
  \\ fs[] \\ rw[]
QED

Theorem boundvar_perm_exp_not_MEM:
 ∀ e. ¬MEM x (boundvars e) ⇒ ¬ MEM y (boundvars (perm_exp x y e))
Proof
  ho_match_mp_tac boundvars_ind
  \\ rw[]
  \\ fs[perm_exp_def]
  \\ fs[perm1_def]
  THEN1 (
    fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[MEM_FLAT]
    \\ fs[MEM_MAP]
    \\ CCONTR_TAC \\ fs[]
    \\ res_tac \\ rw[]
    \\ Cases_on ‘MEM x (boundvars a)’ \\ fs[]
    \\ first_assum (qspec_then ‘boundvars a’ assume_tac) \\ fs[] \\ fs[]
    \\ metis_tac[]
  )
  THEN1 (
    IF_CASES_TAC \\ fs[]
  )
  \\ fs[GSYM perm1_def]
  \\ fs[MAP_MAP_o,combinTheory.o_DEF]
  \\ fs[MEM_FLAT]
  \\ fs[MEM_MAP]
  \\ rw[]
  \\ CCONTR_TAC \\ fs[]
  \\ Cases_on ‘x'’ \\ fs[] \\ rw[]
  \\ res_tac \\ fs[] \\ rw[]
  THEN1 (
    fs[perm1_def]
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ IF_CASES_TAC \\ fs[]
    \\ rw[] \\ res_tac \\ fs[]
    \\ first_assum (qspec_then ‘q INSERT boundvars r’ assume_tac) \\ fs[]
    \\ first_assum (qspec_then ‘(q,r)’ assume_tac) \\ fs[]
  )
  \\ Cases_on ‘MEM x (boundvars r)’ \\ fs[]
  \\ first_assum (qspec_then ‘q INSERT boundvars r’ assume_tac) \\ fs[]
  \\ fs[] \\ rw[]
  \\ first_assum (qspec_then ‘(q,r)’ assume_tac) \\ fs[]
QED

Theorem boundvars_perm_exp:
  boundvars (perm_exp x y e) =
     boundvars e
     DIFF (if x ∉ boundvars e then {y} else ∅)
     DIFF (if y ∉ boundvars e then {x} else ∅)
     ∪ (if x ∈ boundvars e then {y} else ∅)
     ∪ (if y ∈ boundvars e then {x} else ∅)
Proof
  rw[]
  \\ assume_tac (GEN_ALL boundvars_perm_exp_subset)
  \\ assume_tac (GEN_ALL boundvars_perm_exp_subset_inv)
  \\ assume_tac (GEN_ALL boundvar_perm_exp_MEM)
  \\ assume_tac (GEN_ALL boundvar_perm_exp_not_MEM)
  \\ fs [EXTENSION,SUBSET_DEF] \\ metis_tac [perm_exp_sym]
QED


(*******************)



Definition perm_exp_list_def:
  perm_exp_list [] e = e ∧
  perm_exp_list ((old,new)::binds) e = perm_exp_list binds (perm_exp old new e)
End

Theorem perm_exp_list_size'_mono:
  ∀ binds e. exp_size' (perm_exp_list binds e) = exp_size' e
Proof
  recInduct perm_exp_list_ind
  \\ rw[] \\ fs[perm_exp_list_def,perm_exp_size'_mono]
QED

Theorem exp_alpha_perm_exp_list:
  ∀ binds e.
      (DISJOINT (set (MAP FST binds)) (freevars e))
    ∧ (DISJOINT (set (MAP SND binds)) (freevars e))
    ⇒ exp_alpha e (perm_exp_list binds e)
Proof
  recInduct perm_exp_list_ind
  \\ conj_tac
  THEN1 (
    rw[]
    \\ fs[perm_exp_list_def]
    \\ fs[exp_alpha_refl]
  )
  \\ rw[]
  \\ fs[perm_exp_list_def]
  \\ irule exp_alpha_Trans
  \\ qexists_tac  ‘(perm_exp old new e)’
  \\ conj_tac
  THEN1 (irule exp_alpha_perm_irrel \\ fs[])
  \\ last_assum irule
  \\ fs[freevars_perm_exp]
  \\ fs[EXTENSION,DISJOINT_DEF] \\  metis_tac[]
QED

Theorem exp_alpha_perm_exp_list_trans:
  ∀ binds e e'.
      (DISJOINT (set (MAP FST binds)) (freevars e'))
    ∧ (DISJOINT (set (MAP SND binds)) (freevars e'))
    ∧ exp_alpha e e'
    ⇒ exp_alpha e (perm_exp_list binds e')
Proof
  recInduct perm_exp_list_ind
  \\ conj_tac
  THEN1 (fs[perm_exp_list_def])
  \\ rw[]
  \\ fs[perm_exp_list_def]
  \\ irule exp_alpha_Trans
  \\ qexists_tac ‘(perm_exp old new e')’
  \\ conj_tac
  THEN1 (
    irule exp_alpha_Trans
    \\ qexists_tac ‘e'’
    \\ fs[]
    \\ irule exp_alpha_perm_irrel \\ fs[]
  )
  \\ irule exp_alpha_perm_exp_list \\ fs[]
  \\ fs[freevars_perm_exp]
  \\ fs[EXTENSION,DISJOINT_DEF] \\  metis_tac[]
QED

Triviality FILTER_MEM_INTERSECTION:
  ∀ l1 l2. set (FILTER (λx. MEM x l2) l1) = set l1 ∩ set l2
Proof
  Induct \\ fs[]
  \\ rw[]
  \\ fs[EXTENSION,INTER_DEF] \\ metis_tac[]
QED

Triviality DISJOINT_UNION_DIFF:
   DISJOINT A (B DIFF D)
 ∧ DISJOINT A (C DIFF D) ⇒ DISJOINT A (B ∪ C DIFF D)
Proof
 fs[EXTENSION,DISJOINT_DEF] \\ metis_tac[]
QED

Triviality DIFF_SUBSET_UNION:
  A DIFF B ⊆ C ⇒ A ⊆ C ∪ B
Proof
  fs[EXTENSION,DISJOINT_DEF,SUBSET_DEF] \\ metis_tac[]
QED

Triviality UNION_SYM:
  ∀ A B. A ∪ B = B ∪ A
Proof
  fs[EXTENSION,UNION_DEF] \\ metis_tac[]
QED

Definition avoid_vars_def:
  avoid_vars avoid (Var x) = (Var x) ∧
  avoid_vars avoid (Prim op es) = Prim op (MAP (avoid_vars avoid) es) ∧
  avoid_vars avoid (Lam x e) = (
                 let fresh = fresh_var x avoid in
                 let e'    = avoid_vars (x::fresh::avoid) e
                 in (if MEM x avoid
                      then Lam fresh (perm_exp x fresh e')
                      else Lam x e'))                                ∧
  avoid_vars avoid (App e1 e2) = App (avoid_vars avoid e1)
                                     (avoid_vars avoid e2)           ∧
  avoid_vars avoid (Letrec lcs e) =
     let clashes     = nub (FILTER (λx. MEM x avoid) (MAP FST lcs))  in
     let freshes     = fresh_var_list clashes (MAP FST lcs ++ avoid) in
     let new_avoids  = MAP FST lcs ++ avoid ++ MAP SND freshes       in
     let lcs_bodies' = MAP (\x. avoid_vars new_avoids (SND x)) lcs   in
     (* let lcs_bodies' = MAP ((avoid_vars new_avoids) o SND) lcs       in *)
     let lcs'        = ZIP (MAP FST lcs,lcs_bodies')                 in
     let body'       = avoid_vars new_avoids e
     in  perm_exp_list freshes (Letrec lcs' body')
Termination
  WF_REL_TAC ‘measure (exp_size' o SND)’ \\ fs[exp_size'_def]
  \\ reverse (rpt conj_tac)
  THEN1 (
    rw[]
    \\ Induct_on ‘es’ \\ fs[]
    \\ rw[] \\ fs[exp_size'_def]
  )
  \\ rw[]
  \\ imp_res_tac exp_size'_lemma \\ fs[]
End

Theorem exp_alpha_avoid_vars:
  ∀ avoid e. freevars e ⊆ (set avoid) ⇒ exp_alpha e (avoid_vars avoid e)
Proof
  recInduct avoid_vars_ind
  \\ rw[]
  THEN1 (
    fs[avoid_vars_def]
    \\ fs[exp_alpha_refl]
  )
  THEN1 (
    fs[avoid_vars_def]
    \\ irule exp_alpha_Prim
    \\ fs[EVERY2_EVERY]
    \\ fs[ZIP_MAP]
    \\ fs[EVERY_MEM]
    \\ Cases
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[MEM_MAP] \\ rw[]
    \\ res_tac \\ fs[]
    \\ pop_assum irule
    \\ irule SUBSET_TRANS
    \\ qexists_tac ‘BIGUNION (set (MAP (λe. freevars e) es))’
    \\ fs[]
    \\ fs[EXTENSION,BIGUNION,SUBSET_DEF] \\ rw[]
    \\ qexists_tac ‘freevars q’ \\ fs[]
    \\ fs[MEM_MAP]
    \\ qexists_tac ‘q’ \\ fs[]
  )
  THEN1 (
    fs[avoid_vars_def]
    \\ IF_CASES_TAC
    THEN1 (
      ‘freevars e ⊆ set avoid’ by (fs[EXTENSION,SUBSET_DEF] \\ metis_tac[])
      \\ res_tac \\ fs[]
      \\ irule exp_alpha_Trans
      \\ qexists_tac ‘Lam (fresh_var x avoid) (perm_exp x (fresh_var x avoid) e)’
      \\ conj_tac
      THEN1 (
        irule exp_alpha_Alpha
        \\ qspecl_then [‘x’,‘avoid’] assume_tac fresh_var_correctness
        \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
      )
      \\ irule exp_alpha_Lam
      \\ irule exp_alpha_perm_closed
      \\ last_x_assum irule
      \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
    )
    \\ irule exp_alpha_Lam
    \\ last_x_assum irule
    \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
  )
  THEN1 (
    fs[avoid_vars_def]
    \\ irule exp_alpha_App \\ fs[]
  )
  \\ fs[avoid_vars_def]
  \\ ‘freevars e ⊆ set (MAP FST lcs) ∪ set avoid
      ∪ set (MAP SND
             (fresh_var_list (nub (FILTER (λx. MEM x avoid) (MAP FST lcs)))
               (MAP FST lcs ++ avoid)))’ by (
     fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
  )
  \\ res_tac \\ fs[] \\ rw[]
  \\ irule exp_alpha_perm_exp_list_trans
  \\ conj_tac
  THEN1 (
    fs[ZIP_MAP]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[freevars_perm_exp]
    \\ fs[MAP_FST_fresh_var_list]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[FILTER_MEM_INTERSECTION]
    \\ fs[EXTENSION,DISJOINT_DEF,freevars_perm_exp] \\ metis_tac[]
  )
  \\ conj_tac
  THEN1 (
    fs [ZIP_MAP]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ drule (GSYM exp_alpha_freevars)
    \\ disch_tac \\ fs[]
    \\ irule DISJOINT_UNION_DIFF
    \\ conj_tac
    THEN1 (
      irule DISJOINT_SUBSET
      \\ qexists_tac ‘set (MAP FST lcs ++ avoid)’
      \\ conj_tac THEN1 (fs[fresh_var_list_correctness])
      \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
    )
    \\ irule DISJOINT_SUBSET
    \\ qexists_tac
       ‘freevars e
       ∪ BIGUNION (set (MAP
           (λx.freevars (avoid_vars (MAP FST lcs
                                     ++ avoid
                                     ++  MAP SND
                                          (fresh_var_list
                                           (nub (FILTER (λx. MEM x avoid) (MAP FST lcs)))
                                           (MAP FST lcs ++ avoid))) (SND x)))
           lcs))’
    \\ reverse conj_tac THEN1 (fs[EXTENSION,SUBSET_DEF] \\ metis_tac[])
    \\ fs[DISJOINT_BIGUNION]
    \\ conj_tac
    THEN1 (
      once_rewrite_tac[DISJOINT_SYM]
      \\ irule DISJOINT_SUBSET
      \\ qexists_tac ‘set (MAP FST lcs ++ avoid)’
      \\ conj_tac THEN1 (fs[fresh_var_list_correctness])
      \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
    )
    \\ fs[MEM_MAP] \\ rw[]
    \\ last_x_assum (qspec_then ‘x’ assume_tac)
    \\ Cases_on ‘x’ \\ fs[]
    \\ pop_assum mp_tac
    \\ impl_tac \\ fs[]
    \\ impl_tac
    THEN1 (
      irule SUBSET_TRANS
      \\ qexists_tac ‘BIGUNION (set (MAP (λ(fn,e). freevars e) lcs))’
      \\ reverse conj_tac THEN1 (fs[EXTENSION,SUBSET_DEF] \\ metis_tac[])
      \\ irule SUBSET_BIGUNION_I
      \\ fs[MEM_MAP]
      \\ qexists_tac ‘(q,r)’ \\ fs[]
    )
    \\ disch_tac
    \\ drule (GSYM exp_alpha_freevars)
    \\ disch_tac \\ fs[]
    \\ once_rewrite_tac[DISJOINT_SYM]
    \\ irule DISJOINT_SUBSET
    \\ qexists_tac ‘set (MAP FST lcs ++ avoid)’
    \\ conj_tac THEN1 (fs[fresh_var_list_correctness])
    \\ fs[]
    \\ once_rewrite_tac[UNION_SYM]
    \\ irule DIFF_SUBSET_UNION
    \\ irule SUBSET_TRANS
    \\ qexists_tac ‘BIGUNION (set (MAP (λ(fn,e). freevars e) lcs)) DIFF
                    set (MAP FST lcs)’
    \\ reverse conj_tac THEN1 (fs[EXTENSION,SUBSET_DEF] \\ metis_tac[])
    \\ qsuff_tac ‘freevars r ⊆ BIGUNION (set (MAP (λ(fn,e). freevars e) lcs))’
    THEN1 (fs[EXTENSION,SUBSET_DEF] \\ metis_tac[])
    \\ irule SUBSET_BIGUNION_I
    \\ fs[MEM_MAP]
    \\ qexists_tac ‘(q,r)’ \\ fs[]
  )
  \\ fs[ZIP_MAP]
  \\ fs[MAP_MAP_o,combinTheory.o_DEF]
  \\ irule exp_alpha_Letrec
  \\ rw[]
  THEN1 (fs[MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f])
  \\ fs[MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f]
  \\ fs[EVERY2_EVERY]
  \\ fs[ZIP_MAP]
  \\ fs[MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f]
  \\ fs[EVERY_MEM]
  \\ Cases
  \\ fs[MEM_MAP]
  \\ rw[]
  \\ Cases_on ‘x’ \\ fs[]
  \\ res_tac \\ fs[]
  \\ pop_assum irule
  \\ irule SUBSET_TRANS
  \\ qexists_tac ‘BIGUNION (set (MAP (λ(fn,e). freevars e) lcs))’
  \\ reverse conj_tac THEN1 (fs[EXTENSION,SUBSET_DEF] \\ metis_tac[])
  \\ irule SUBSET_BIGUNION_I
  \\ fs[MEM_MAP]
  \\ qexists_tac ‘(q,r)’ \\ fs[]
QED




(********Capture avoiding substitution**********)



Definition CA_subst_def:
   CA_subst x arg body =
       subst x arg (avoid_vars (freevars arg ++ freevars body) body)
End

Theorem App_Lam_bisim:
  closed (Lam x body) ∧ closed arg ⇒
  App (Lam x body) arg ≃ subst x arg body
Proof
  rw [] \\ match_mp_tac eval_IMP_app_bisimilarity
  \\ fs [eval_Let,bind_single_def]
  \\ match_mp_tac IMP_closed_subst
  \\ fs [] \\ fs [closed_def,FILTER_EQ_NIL,EVERY_MEM,SUBSET_DEF]
QED

Triviality app_bisimilarity_trans:
  ∀x y z. x ≃ y ∧ y ≃ z ⇒ x ≃ z
Proof
  rw[]
  \\ assume_tac transitive_app_bisimilarity
  \\ fs[transitive_def]
  \\ res_tac \\ fs[]
QED

Triviality app_bisimilarity_sym:
  ∀x y. x ≃ y ⇒ y ≃ x
Proof
  rw[]
  \\ assume_tac symmetric_app_bisimilarity
  \\ fs[symmetric_def]
QED

Theorem freevars_avoid_vars_mono:
  ∀ avoid e . freevars e ⊆ set avoid
  ⇒ freevars (avoid_vars avoid e) = freevars e
Proof
  rw[]
  \\ drule exp_alpha_avoid_vars
  \\ disch_tac
  \\ imp_res_tac exp_alpha_freevars
  \\ fs[]
QED

Theorem boundvars_perm_exp_list:
  ∀ binds e.
     ALL_DISTINCT (MAP FST binds)
  ∧  ALL_DISTINCT (MAP SND binds)
  ∧  DISJOINT (set (MAP SND binds)) (boundvars e)
  ⇒  boundvars (perm_exp_list binds e) ⊆
     boundvars e DIFF (set (MAP FST binds)) ∪ set (MAP SND binds)
Proof
  recInduct perm_exp_list_ind
  \\ conj_tac THEN1 (fs[perm_exp_list_def])
  \\ rw[]
  \\ fs[perm_exp_list_def]
  \\ fs[boundvars_perm_exp]
  \\ last_x_assum mp_tac
  \\ reverse impl_tac
  \\ rw[]
  \\ fs[EXTENSION,SUBSET_DEF,DISJOINT_DEF] \\ metis_tac[MEM]
QED

Triviality DISJOINT_UNION_DIFF_DISTRIB:
  DISJOINT (A ∪ B DIFF C) D ⇔ DISJOINT (A DIFF C) D ∧ DISJOINT (B DIFF C) D
Proof
  fs[EXTENSION,DISJOINT_DEF,SUBSET_DEF] \\ metis_tac[]
QED

Triviality DISJOINT_DIFF_WEAKENING:
  DISJOINT A B ⇒ DISJOINT (A DIFF C) B
Proof
  fs[EXTENSION,DISJOINT_DEF,SUBSET_DEF] \\ metis_tac[]
QED

Triviality FILTER_MAP_MEM:
  ∀ l1 l2. MEM x l1 ∧ MEM x l2 ⇒ MEM x (nub (FILTER (λx. MEM x l1) l2))
Proof
  Induct_on ‘l1’ \\ fs[]
  \\ rw[] \\ res_tac \\ fs[]
  \\ Induct_on ‘l2’ \\ fs[]
  \\ rw[] \\ res_tac \\ fs[]
QED

Triviality MEM_PAIR_MAP:
  MEM (q,r) lcs ⇒ MEM q (MAP FST lcs)
Proof
  Induct_on ‘lcs’ \\ fs[]
  \\ Cases \\ fs[] \\ rw[]
  \\ res_tac \\ fs[]
QED

Triviality NOT_MEM_PAIR:
 (∀y. q ≠ FST y ∨ ¬MEM y l) ⇒ ¬MEM q (MAP FST l)
Proof
  Induct_on ‘l’ \\ fs[]
  \\ Cases \\ fs[] \\ rw[]
  THEN1 (
    CCONTR_TAC \\ fs[] \\ rw[]
    \\ last_x_assum mp_tac
    \\ impl_tac THEN1 (metis_tac[MEM])
    \\ fs[]
    \\ pop_assum (qspec_then ‘(q,r)’ assume_tac) \\ fs[]
  )
  \\ last_x_assum irule
  \\ rw[]
  \\ pop_assum (qspec_then ‘y’ assume_tac) \\ fs[]
QED

Triviality NOT_MEM_DISJOINT:
  ¬MEM x l ⇔ DISJOINT {x} (set l)
Proof
  fs[EXTENSION,DISJOINT_DEF] \\ metis_tac[MEM]
QED

Theorem avoid_vars_safe_renaming:
  ∀ avoid e . freevars e ⊆ set avoid
  ⇒ DISJOINT (boundvars (avoid_vars avoid e)) (set avoid)
Proof
  recInduct avoid_vars_ind
  \\ rw[]
  THEN1 (fs[avoid_vars_def])
  THEN1 (
    fs[avoid_vars_def]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[LIST_TO_SET_FLAT]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[MEM_MAP]
    \\ fs[BIGUNION_SUBSET]
    \\ rw[]
    \\ last_x_assum irule
    \\ fs[]
    \\ first_x_assum (qspec_then ‘freevars a’ assume_tac)
    \\ pop_assum irule
    \\ fs[MEM_MAP]
    \\ qexists_tac ‘a’ \\ fs[]
  )
  THEN1 (
    ‘freevars e ⊆ x INSERT fresh_var x avoid INSERT set avoid’ by (
      fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
    )
    \\ fs[] \\ pop_assum kall_tac
    \\ fs[avoid_vars_def]
    \\ rw[] \\ fs[fresh_var_correctness]
    \\ simp[boundvars_perm_exp]
    \\ rw[]
    \\ fs[EXTENSION,DISJOINT_DEF,SUBSET_DEF] \\ metis_tac[fresh_var_correctness]
  )
  THEN1 (fs[avoid_vars_def])
  \\ ‘freevars e ⊆
        set (MAP FST lcs) ∪ set avoid ∪
        set (MAP SND
             (fresh_var_list (nub (FILTER (λx. MEM x avoid) (MAP FST lcs)))
                (MAP FST lcs ++ avoid)))’ by (
     fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
  )
  \\ fs[] \\ pop_assum kall_tac
  \\ qspecl_then [‘(nub (FILTER (λx. MEM x avoid) (MAP FST lcs)))’
                 ,‘(MAP FST lcs ++ avoid)’] assume_tac fresh_var_list_correctness
  \\ fs[avoid_vars_def]
  \\ fs[ZIP_MAP]
  \\ fs[MAP_MAP_o,combinTheory.o_DEF]
  \\ once_rewrite_tac[DISJOINT_SYM]
  \\ irule DISJOINT_SUBSET
  \\ qspecl_then
     [‘(fresh_var_list
                   (nub (FILTER (λx. MEM x avoid) (MAP FST lcs)))
                   (MAP FST lcs ++ avoid))’
     ,‘(Letrec
                   (MAP
                      (λx.
                           (FST x,
                            avoid_vars
                              (MAP FST lcs ++ avoid ++
                               MAP SND
                                 (fresh_var_list
                                    (nub
                                       (FILTER (λx. MEM x avoid)
                                          (MAP FST lcs)))
                                    (MAP FST lcs ++ avoid))) (SND x))) lcs)
                   (avoid_vars
                      (MAP FST lcs ++ avoid ++
                       MAP SND
                         (fresh_var_list
                            (nub (FILTER (λx. MEM x avoid) (MAP FST lcs)))
                            (MAP FST lcs ++ avoid))) e))’]
     mp_tac boundvars_perm_exp_list
  \\ impl_tac
  THEN1 (
    fs[MAP_FST_fresh_var_list]
    \\ conj_tac THEN1 (irule fresh_var_list_distinctness)
    \\ conj_tac
    THEN1 (fs[EXTENSION,DISJOINT_DEF,SUBSET_DEF] \\ metis_tac[])
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[MEM_MAP]
    \\ rw[]
    \\ Cases_on ‘x’ \\ fs[]
    \\ reverse conj_tac
    THEN1 (
      once_rewrite_tac[NOT_MEM_DISJOINT]
      \\ once_rewrite_tac[DISJOINT_SYM]
      \\ irule DISJOINT_SUBSET
      \\ qexists_tac ‘set (MAP FST lcs ++ avoid)’
      \\ fs[fresh_var_list_correctness]
      \\ metis_tac[MEM_PAIR_MAP,MEM]
    )
    \\ res_tac \\ fs[]
    \\ once_rewrite_tac[DISJOINT_SYM]
    \\ first_assum irule
    \\ irule SUBSET_TRANS
    \\ qexists_tac ‘BIGUNION (set (MAP (λ(fn,e). freevars e) lcs))’
    \\ reverse conj_tac THEN1 (fs[EXTENSION,SUBSET_DEF] \\ metis_tac[])
    \\ irule SUBSET_BIGUNION_I
    \\ fs[MEM_MAP]
    \\ qexists_tac ‘(q,r)’ \\ fs[]
  )
  \\ strip_tac
  \\ qexists_tac ‘ boundvars
          (Letrec
             (MAP
                (λx.
                     (FST x,
                      avoid_vars
                        (MAP FST lcs ++ avoid ++
                         MAP SND
                           (fresh_var_list
                              (nub (FILTER (λx. MEM x avoid) (MAP FST lcs)))
                              (MAP FST lcs ++ avoid))) (SND x))) lcs)
             (avoid_vars
                (MAP FST lcs ++ avoid ++
                 MAP SND
                   (fresh_var_list
                      (nub (FILTER (λx. MEM x avoid) (MAP FST lcs)))
                      (MAP FST lcs ++ avoid))) e)) DIFF
        set
          (MAP FST
             (fresh_var_list (nub (FILTER (λx. MEM x avoid) (MAP FST lcs)))
                (MAP FST lcs ++ avoid))) ∪
        set
          (MAP SND
             (fresh_var_list (nub (FILTER (λx. MEM x avoid) (MAP FST lcs)))
                (MAP FST lcs ++ avoid)))’
  \\ fs[]
  \\ reverse conj_tac THEN1 (
    irule DISJOINT_SUBSET
    \\ qexists_tac ‘set (MAP FST lcs ++ avoid)’
    \\ fs[fresh_var_list_correctness]
  )
  \\ fs[DISJOINT_UNION_DIFF_DISTRIB]
  \\ conj_tac THEN1 (fs[EXTENSION,DISJOINT_DEF,DIFF_DEF] \\ metis_tac[])
  \\ fs[MAP_MAP_o,combinTheory.o_DEF]
  \\ fs[pure_miscTheory.BIGUNION_DIFF]
  \\ GEN_TAC
  \\ rw[]
  \\ fs[MEM_MAP]
  \\ Cases_on ‘x’ \\ fs[] \\ rw[]
  THEN1 (
    res_tac \\ fs[]
    \\ irule DISJOINT_DIFF_WEAKENING
    \\ once_rewrite_tac[DISJOINT_SYM]
    \\ first_assum irule
    \\ irule SUBSET_TRANS
    \\ qexists_tac ‘ BIGUNION (set (MAP (λ(fn,e). freevars e) lcs))’
    \\ reverse conj_tac
    THEN1 (fs[EXTENSION,DISJOINT_DEF,SUBSET_DEF] \\ metis_tac[])
    \\ irule SUBSET_BIGUNION_I
    \\ fs[MEM_MAP]
    \\ qexists_tac ‘(FST y,r)’ \\ fs[]
  )
  THEN1 (
    fs[MAP_FST_fresh_var_list]
    \\ irule DISJOINT_DIFF_WEAKENING
    \\ res_tac \\ fs[]
    \\ once_rewrite_tac[DISJOINT_SYM]
    \\ first_assum irule
    \\ irule SUBSET_TRANS
    \\ qexists_tac ‘BIGUNION (set (MAP (λ(fn,e). freevars e) lcs))’
    \\ reverse conj_tac THEN1 (fs[EXTENSION,SUBSET_DEF] \\ metis_tac[])
    \\ irule SUBSET_BIGUNION_I
    \\ fs[MEM_MAP]
    \\ qexists_tac ‘(q,r)’ \\ fs[]
  )
  \\ fs[]
  \\ ‘¬MEM q (MAP FST (fresh_var_list (nub (FILTER (λx. MEM x avoid) (MAP FST lcs)))
                      (MAP FST lcs ++ avoid)))’ by (
     irule NOT_MEM_PAIR \\ fs[]
  )
  \\ CCONTR_TAC \\ fs[]
  \\ ‘MEM q (nub (FILTER (λx. MEM x avoid) (MAP FST lcs)))’ by (
    irule FILTER_MAP_MEM
    \\ fs[]
    \\ drule MEM_PAIR_MAP \\ fs[]
  )
  \\ ‘MEM q (MAP FST (fresh_var_list (nub (FILTER (λx. MEM x avoid) (MAP FST lcs)))
                     (MAP FST lcs ++ avoid)))’ by (
       qspecl_then [‘(nub (FILTER (λx. MEM x avoid) (MAP FST lcs)))’
                   ,‘(MAP FST lcs ++ avoid)’] assume_tac MAP_FST_fresh_var_list
       \\ metis_tac[MEM]
     )
  \\ fs[]
QED

Theorem boundvars_avoid_vars:
∀l x. freevars body ⊆ set l ∧
      MEM x (boundvars (avoid_vars l body)) ⇒
        ¬MEM x l
Proof
  rw[]
  \\ qspecl_then [‘l’,‘body’] assume_tac avoid_vars_safe_renaming
  \\ res_tac
  \\ fs[EXTENSION,DISJOINT_DEF] \\ metis_tac[MEM]
QED

Theorem subst_NOT_MEM:
 ∀ f arg.  ¬MEM n (freevars arg) ⇒ subst (f \\ n) arg = subst f arg
Proof
  recInduct subst_ind
  \\ rw[]
  THEN1 (fs[subst_def,DOMSUB_FLOOKUP_NEQ])
  THEN1 (
    fs[subst_def]
    \\ fs[MAP_EQ_f]
    \\ rw[] \\ res_tac \\ fs[]
    \\ pop_assum irule
    \\ fs[MEM_MAP] \\ metis_tac[MEM]
  )
  THEN1 (
    fs[subst_def] \\ res_tac \\ fs[]
  )
  THEN1 (
    fs[subst_def]
    \\ fs[DOMSUB_COMMUTES]
  )
  THEN1 (
    fs[subst_def]
  )
  THEN1 (
    res_tac \\ fs[] \\ rw[]
    \\ fs[subst_def]
    \\ reverse conj_tac THEN1 (fs[fdiff_fdomsub_commute])
    \\ fs[MEM_MAP]
    \\ fs[MAP_EQ_f] \\ rw[]
    \\ Cases_on ‘e’ \\ fs[]
    \\ res_tac
    \\ fs[fdiff_fdomsub_commute]
    \\ pop_assum irule
    \\ first_assum (qspec_then ‘freevars r’ assume_tac) \\ fs[]
    \\ pop_assum (qspec_then ‘(q,r)’ assume_tac) \\ fs[]
  )
  \\ fs[subst_def]
  \\ fs[fdiff_fdomsub_INSERT]
  \\ ‘n INSERT set (MAP FST f) = set (MAP FST f)’ by (
    fs[EXTENSION] \\ metis_tac[MEM]
  )
  \\ fs[]
QED

Triviality MAP_FST_list_mono:
  ∀ g l. MAP (λx. FST ((λ(f,e).(f,g e)) x)) l = MAP FST l
Proof
  rw[] \\ fs[MAP_EQ_f] \\ Cases \\ fs[]
QED

Triviality MAP_FST_MEM_pair_companion:
  ∀x. MEM x (MAP FST lcs) ⇒ ∃ y. MEM (x,y) lcs
Proof
  rw[]
  \\ Induct_on ‘lcs’ \\ fs[]
  \\ Cases \\ fs[]
  \\ Cases_on ‘x = q’ \\ fs[] \\ rw[]
  \\ qexists_tac ‘r’ \\ fs[]
QED

Triviality INSERT_absorption:
  MEM x l ⇒ x INSERT (set l) = set l
Proof
  fs[EXTENSION] \\ metis_tac[]
QED

Theorem subst_distrib:
  ∀ body f v arg.
    (∀n v. FLOOKUP f n = SOME v ⇒ closed v)
  ∧ EVERY (λ x. x ∉ freevars arg) (boundvars body)
   ⇒
  subst f (subst v arg body)
  = subst v (subst f arg) (subst (f \\ v) body)
Proof
  ho_match_mp_tac freevars_ind
  \\ rpt strip_tac
  THEN1(
    fs[subst_def]
    \\ fs[FLOOKUP_UPDATE] \\ fs[DOMSUB_FLOOKUP_THM]
    \\ rw[] \\ fs[subst_single_def]
    \\ Cases_on ‘FLOOKUP f n’ \\ fs[subst_single_def] \\ fs[subst_def]
    \\ res_tac \\ fs[closed_subst])
  THEN1(
    fs[subst_def]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ fs[MAP_EQ_f]
    \\ fs[EVERY_FLAT,EVERY_MAP,EVERY_MEM]
    \\ rw[] \\ res_tac \\ fs[]
  )
  THEN1(
    fs[subst_def]
    \\ res_tac \\ fs[]
  )
  THEN1(
    fs[subst_single_def]
    \\ IF_CASES_TAC \\ fs[subst_def]
    \\ ‘∀m v. FLOOKUP (f \\ n) m = SOME v ⇒ closed v’ by (
       fs[DOMSUB_FLOOKUP_THM]
       \\ metis_tac[]
    )
    \\ last_x_assum drule
    \\ disch_then (qspecl_then [‘v’,‘arg’] mp_tac)
    \\ impl_tac
    \\ rw[]
    \\ fs[DOMSUB_FUPDATE_NEQ]
    \\ fs[subst_NOT_MEM]
    \\ metis_tac[DOMSUB_COMMUTES]
  )
  \\ fs[MAP_MAP_o,combinTheory.o_DEF]
  \\ fs[EVERY_FLAT,EVERY_MAP,EVERY_MEM]
  \\ ‘∀ x. MEM x (MAP FST lcs) ⇒ ¬ MEM x (freevars arg)’ by (
      rw[]
      \\ last_assum irule
      \\ imp_res_tac MAP_FST_MEM_pair_companion
      \\ res_tac
      \\ qexists_tac ‘(x,y)’ \\ fs[]
  )
  \\ fs[subst_def]
  \\ fs[MAP_MAP_o,combinTheory.o_DEF]
  \\ fs[MAP_FST_list_mono]
  \\ fs[MAP_EQ_f]
  \\ rw[]
  \\ TRY (Cases_on ‘x’ \\ fs[])
  \\ ‘(FDIFF (f \\ v) (set (MAP FST lcs))) = (FDIFF f (set (MAP FST lcs))) \\ v’ by (
     simp[Once fdiff_fdomsub_commute]
  ) \\ fs[] \\ pop_assum kall_tac
  \\ ‘subst f arg = subst (FDIFF f (set (MAP FST lcs))) arg’ by (
     irule subst_FDIFF'' \\ fs[]
  ) \\ fs[] \\ pop_assum kall_tac
  THEN1 (
    last_x_assum (qspecl_then [‘q’,‘r’] mp_tac) \\ fs[]
    \\ disch_tac
    \\ simp[FDIFF_def]
    \\ rw[]
    \\ simp[GSYM FDIFF_def]
    THEN1 (
      first_assum irule
      \\ rw[]
      THEN1 (
        first_assum irule
        \\ qexists_tac ‘n’
        \\ irule FLOOKUP_SUBMAP
        \\ qexists_tac ‘(FDIFF f (set (MAP FST lcs)))’ \\ fs[]
        \\ fs[FDIFF_def,DRESTRICT_SUBMAP]
      )
      \\ last_assum irule
      \\ qexists_tac ‘(q,r)’ \\ fs[]
    )
    \\ once_rewrite_tac[GSYM fdiff_fdomsub_commute]
    \\ fs[fdiff_fdomsub_INSERT]
    \\ fs[INSERT_absorption]
  )
  \\ simp[FDIFF_def]
  \\ rw[]
  \\ simp[GSYM FDIFF_def]
  THEN1 (
    first_assum irule
    \\ rw[]
    \\ first_assum irule
    \\ qexists_tac ‘n’
    \\ irule FLOOKUP_SUBMAP
    \\ qexists_tac ‘(FDIFF f (set (MAP FST lcs)))’ \\ fs[]
    \\ fs[FDIFF_def,DRESTRICT_SUBMAP]
  )
  \\ once_rewrite_tac[GSYM fdiff_fdomsub_commute]
  \\ fs[fdiff_fdomsub_INSERT]
  \\ fs[INSERT_absorption]
QED

Theorem beta_equivalence:
  App (Lam x body) arg ≅ CA_subst x arg body
Proof
  fs[CA_subst_def]
  \\ fs[exp_eq_def]
  \\ rpt strip_tac
  \\ fs[bind_def]
  \\ rw[]
  \\ fs[subst_def]
  \\ match_mp_tac app_bisimilarity_trans
  \\ qexists_tac ‘ subst x (subst f arg) (subst (f \\ x) body)’
  \\ conj_tac
  THEN1 (
    irule App_Lam_bisim
    \\ conj_tac THEN1 (
      irule IMP_closed_subst \\ fs[FRANGE_DEF]
      \\ fs[FLOOKUP_DEF,PULL_EXISTS]
    )
    \\ qsuff_tac ‘closed (subst f (Lam x body))’ THEN1 (fs[subst_def])
    \\ irule IMP_closed_subst \\ fs[FRANGE_DEF]
    \\ fs[FLOOKUP_DEF,PULL_EXISTS]
  )
  \\ drule subst_distrib
  \\ disch_then (qspecl_then [‘(avoid_vars (freevars arg ++ freevars body) body)’
                             ,‘x’,‘arg’] mp_tac)
  \\ impl_tac
  THEN1 (
    fs[EVERY_MEM]
    \\ rw[]
    \\ imp_res_tac boundvars_avoid_vars \\ fs[]
  )
  \\ rw[]
  \\ ‘(∀v. v ∈ FRANGE (f \\ x) ⇒ closed v)’ by (
    rw[]
    \\ first_assum irule
    \\ fs[GSYM IN_FRANGE_FLOOKUP]
    \\ fs[EXTENSION,FRANGE_DEF,IN_DEF] \\ rw[]
    \\ fs[DOMSUB_FAPPLY_THM] \\ rw[]
    \\ metis_tac[]
  )
  \\ fs[subst_subst_FUNION]
  \\ irule app_bisimilarity_sym
  \\ irule exp_alpha_app_bisimilarity
  \\ reverse (rpt conj_tac)
  THEN1 (
    irule exp_alpha_subst_all_closed''
    \\ rw[]
    THEN1 (
      qspecl_then [‘FEMPTY |+ (x,subst f arg)’,‘f \\ x’] mp_tac (GEN_ALL FRANGE_FUNION)
      \\ impl_tac THEN1 (fs[FDOM_DOMSUB])
      \\ disch_tac \\ fs[] \\ pop_assum kall_tac
      \\ rw[]
      \\ irule IMP_closed_subst \\ fs[]
      \\ rw[]
      \\ last_assum irule
      \\ fs[GSYM IN_FRANGE_FLOOKUP]
    )
    \\ fs[exp_alpha_sym,exp_alpha_avoid_vars]
  )
  \\ irule IMP_closed_subst \\ fs[]
  \\ rw[]
  \\ TRY (
    qspecl_then [‘FEMPTY |+ (x,subst f arg)’,‘f \\ x’] mp_tac (GEN_ALL FRANGE_FUNION)
    \\ impl_tac THEN1 (fs[FDOM_DOMSUB])
    \\ disch_tac \\ fs[] \\ pop_assum kall_tac
    \\ rw[]
    \\ irule IMP_closed_subst \\ fs[]
    \\ rw[]
    \\ last_assum irule
    \\ fs[GSYM IN_FRANGE_FLOOKUP]
  )
  \\ fs[freevars_avoid_vars_mono]
  \\ fs[EXTENSION,SUBSET_DEF] \\ metis_tac[]
QED


val _ = export_theory();
