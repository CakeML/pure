(*
   Proves lemmas that follow from the definitions in pure_presTheory
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     combinTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_exp_relTheory
     pure_alpha_equivTheory pure_miscTheory pure_congruenceTheory
     pure_demandTheory pure_letrec_delargTheory
     pure_cexpTheory pure_cexp_lemmasTheory pureLangTheory pure_presTheory;

val _ = new_theory "pure_pres_lemmas";

Theorem bidir_letrec_eta:
  MEM (f,Lam a vs x) l ∧ ALL_DISTINCT (MAP FST l) ∧ vs ≠ [] ∧
  EVERY (λ(v,e).
           DISJOINT (IMAGE explode (set vs)) (freevars (exp_of e)) ∧
           ~MEM v vs) l ∧
  DISJOINT (set (MAP FST l)) (set vs)
  ⇒
  (Letrec a l (Var a f))
  <-->
  (Letrec a l (Lam a vs (App a (Var a f) (MAP (Var a) vs))))
Proof
  rw []
  \\ irule_at Any bidir_trans
  \\ irule_at (Pos hd) bidir_Letrec_unroll
  \\ first_assum $ irule_at $ Pos hd \\ fs []
  \\ irule_at Any bidir_trans
  \\ qexists_tac ‘Letrec a l (Lam a vs (App a (Lam a vs x) (MAP (Var a) vs)))’
  \\ conj_tac
  >-
   (irule bidir_Letrec \\ fs [LIST_REL_same]
    \\ simp [Once bidir_sym]
    \\ irule bidir_App_Lam \\ fs [])
  \\ irule_at Any bidir_trans
  \\ irule_at (Pos hd) bidir_Letrec_Lam \\ fs []
  \\ simp [Once bidir_sym]
  \\ irule_at Any bidir_trans
  \\ irule_at (Pos hd) bidir_Letrec_Lam \\ fs []
  \\ irule_at Any bidir_Lam
  \\ irule_at Any bidir_trans
  \\ irule_at (Pos hd) bidir_Letrec_App_forget \\ fs []
  \\ simp [Once bidir_sym]
  \\ irule_at Any bidir_trans
  \\ irule_at (Pos hd) bidir_Letrec_App_forget \\ fs []
  \\ irule_at (Pos hd) bidir_App \\ fs [LIST_REL_same]
  \\ simp [Once bidir_sym]
  \\ irule_at (Pos hd) bidir_Letrec_unroll \\ fs []
  \\ gvs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS]
  \\ res_tac \\ rw [] \\ gvs [exp_of_def]
  \\ gvs [IN_DISJOINT] \\ metis_tac []
QED

Theorem bidir_letrec_eta_1:
  ¬MEM f vs ∧ vs ≠ []
  ⇒
  (Letrec a [(f,Lam a vs x)] (Var a f))
  <-->
  (Letrec a [(f,Lam a vs x)] (Lam a vs (App a (Var a f) (MAP (Var a) vs))))
Proof
  rw [] \\ irule bidir_letrec_eta \\ fs []
  \\ gvs [IN_DISJOINT,exp_of_def,MEM_MAP]
  \\ metis_tac []
QED

Theorem bidir_letrec_expand_1:
  ¬MEM f vs ∧ vs ≠ []
  ⇒
  (Letrec a [(f,Lam a vs x)] x)
  <-->
  (Let a f (Lam a vs
             (Letrec a [(f,Lam a vs x)]
               (App a (Var a f) (MAP (Var a) vs))))
     x)
Proof
  rw []
  \\ irule bidir_trans
  \\ irule_at Any bidir_Letrec_eq_Let_Letrec
  \\ irule_at Any bidir_Let \\ fs []
  \\ simp [Once bidir_sym]
  \\ irule_at Any bidir_trans
  \\ simp [Once bidir_sym]
  \\ irule_at (Pos hd) bidir_Letrec_Lam \\ gvs []
  \\ simp [Once bidir_sym]
  \\ irule_at Any bidir_letrec_eta_1
  \\ fs [exp_of_def,IN_DISJOINT,MEM_MAP]
  \\ metis_tac []
QED

Theorem bidir_contract_1:
  ~MEM f ps ∧ ~MEM f ws ∧ vs ≠ [] ∧ ws ≠ [] ∧ set ws ⊆ set vs
  ⇒
  (Lam a (vs ++ ps)
     (Letrec a [(f,Lam a (ws ++ ps) x)]
        (App a (Var a f) (MAP (Var a) (ws ++ ps)))))
  <-->
  (Lam a vs
     (Letrec a [(f,Lam a (ws ++ ps) x)]
        (App a (Var a f) (MAP (Var a) ws))))
Proof
  Cases_on ‘ps = []’ >- fs []
  \\ rw []
  \\ qabbrev_tac ‘z = Letrec a [(f,Lam a (ws ++ ps) x)] x’
  \\ ‘Letrec a [(f,Lam a (ws ++ ps) x)] (Var a f) <--> Lam a (ws ++ ps) z’ by
   (irule bidir_trans
    \\ irule_at (Pos hd) bidir_Letrec_unroll \\ fs []
    \\ unabbrev_all_tac
    \\ irule_at (Pos hd) bidir_Letrec_Lam \\ gvs []
    \\ gvs [exp_of_def,IN_DISJOINT,MEM_MAP]
    \\ metis_tac [])
  \\ qsuff_tac ‘
      Lam a (vs ++ ps)
        (App a (Lam a (ws ++ ps) z) (MAP (Var a) ws ++ MAP (Var a) ps)) <-->
      Lam a vs
        (App a (Lam a (ws ++ ps) z) (MAP (Var a) ws))’
  >-
   (strip_tac
    \\ irule_at (Pos hd) bidir_trans
    \\ irule_at (Pos last) bidir_trans
    \\ pop_assum $ irule_at $ Pos hd
    \\ irule_at Any bidir_Lam
    \\ irule_at Any bidir_Lam
    \\ unabbrev_all_tac
    \\ irule_at (Pos hd) bidir_trans
    \\ irule_at Any bidir_Letrec_App_forget
    \\ gvs [EVERY_MAP,exp_of_def] \\ gvs [EVERY_MEM]
    \\ irule_at (Pos hd) bidir_App
    \\ gvs [LIST_REL_same]
    \\ simp [Once bidir_sym]
    \\ irule_at (Pos hd) bidir_trans
    \\ irule_at Any bidir_Letrec_App_forget
    \\ gvs [EVERY_MAP,exp_of_def] \\ gvs [EVERY_MEM]
    \\ irule_at (Pos hd) bidir_App
    \\ gvs [LIST_REL_same])
  \\ irule_at Any bidir_trans
  \\ qexists_tac ‘Lam a (vs ++ ps) z’
  \\ conj_tac >-
   (rewrite_tac [GSYM MAP_APPEND]
    \\ irule bidir_App_Lam \\ fs []
    \\ gvs [SUBSET_DEF])
  \\ qsuff_tac ‘
      Lam a vs (Lam a ps z) <-->
      Lam a vs (App a (Lam a ws (Lam a ps z)) (MAP (Var a) ws))’
  >-
   (strip_tac
    \\ irule bidir_trans
    \\ irule_at (Pos hd) bidir_Lam_append \\ fs []
    \\ irule bidir_trans
    \\ pop_assum $ irule_at $ Pos hd
    \\ irule bidir_Lam
    \\ irule bidir_App
    \\ gvs [LIST_REL_same]
    \\ simp [Once bidir_sym]
    \\ irule_at (Pos hd) bidir_Lam_append \\ fs [])
  \\ simp [Once bidir_sym]
  \\ irule bidir_App_Lam \\ fs []
QED

val _ = export_theory ();
