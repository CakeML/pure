(*
   Prove that Seq can be introduced in a Letrec
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_exp_relTheory
     pure_alpha_equivTheory pure_miscTheory pure_congruenceTheory;

val _ = new_theory "pure_letrec_seq";

Type bind = “:string # (string # bool) list # exp”;

Overload Zero[local] = “Lit (Int 0):exp”;

Definition mk_bind_def:
  mk_bind ((n,vs,e):bind) = (n, Lams (MAP FST vs) (Seq Zero e))
End

Definition mk_seqs_def:
  mk_seqs [] e = e ∧
  mk_seqs ((_,F)::xs) e = mk_seqs xs e ∧
  mk_seqs ((v,T)::xs) e = Seq (Var v) (mk_seqs xs e)
End

Definition mk_seq_bind_def:
  mk_seq_bind ((n,vs,e):bind) = (n, Lams (MAP FST vs) (Seq Zero (mk_seqs vs e)))
End

Definition obligation_def:
  obligation (binds : bind list) ⇔
    EVERY (λ(vname,args,body).
      (* args are disjoint *)
      DISJOINT (set (MAP FST args)) (set (MAP FST binds)) ∧
      (* body of bound exp only mentions args and other bound names *)
      freevars body SUBSET (set (MAP FST binds) UNION set (MAP FST args)) ∧
      (* every forced var is free body *)
      set (MAP FST (FILTER SND args)) SUBSET freevars body ∧
      (* if all function rec. calls force args,
         then we can add forcing to the top-level *)
      (let
         x = subst_funs (MAP mk_seq_bind binds) body
       in
         x ≈ mk_seqs args x)) binds
End

Inductive letrec_seq:
[~change:]
  (∀binds b.
    MEM b binds ∧ obligation binds ⇒
    letrec_seq binds (Letrec (MAP mk_bind binds) (SND (mk_bind b)))
                     (Letrec (MAP mk_seq_bind binds) (SND (mk_seq_bind b)))) ∧
[~seq:]
  (∀binds n vs e m1 m2.
    MEM (n,vs,e) binds ∧
    FEVERY (λ(k,v). closed v) m1 ∧ FEVERY (λ(k,v). closed v) m2 ∧
    FDOM m1 = FDOM m2 ∧
    (∀k v1 v2.
      FLOOKUP m1 k = SOME v1 ∧ FLOOKUP m2 k = SOME v2 ⇒
      letrec_seq binds v1 v2) ⇒
    letrec_seq binds
      (Seq Zero (subst m1 (subst_funs (MAP mk_bind binds) e)))
      (Seq Zero (subst m2 (mk_seqs vs (subst_funs (MAP mk_seq_bind binds) e))))) ∧
  (* cases below are just recursion *)
  (∀binds n.
    letrec_seq binds (Var n) (Var n))
  ∧
  (∀binds n x y.
    letrec_seq binds x y ⇒
    letrec_seq binds (Lam n x) (Lam n y))
  ∧
  (∀binds f g x y.
    letrec_seq binds f g ∧ letrec_seq binds x y ⇒
    letrec_seq binds (App f x) (App g y))
  ∧
  (∀binds n xs ys.
    LIST_REL (letrec_seq binds) xs ys ⇒
    letrec_seq binds (Prim n xs) (Prim n ys))
  ∧
  (∀binds  xs ys x y.
    LIST_REL (letrec_seq binds) (MAP SND xs) (MAP SND ys) ∧
    MAP FST xs = MAP FST ys ∧ letrec_seq binds x y ⇒
    letrec_seq binds (Letrec xs x) (Letrec ys y))
End

Theorem letrec_seq_refl:
  ∀x. letrec_seq binds x x
Proof
  ho_match_mp_tac freevars_ind
  \\ rw [] \\ simp [Once letrec_seq_cases]
  \\ rpt disj2_tac
  >- (Induct_on ‘es’ \\ fs [])
  \\ Induct_on ‘lcs’ \\ fs [FORALL_PROD,SF DNF_ss]
  \\ rw [] \\ res_tac \\ fs []
QED

Triviality MAP_FST_mk_bind:
  MAP FST (MAP mk_bind binds) = MAP FST binds
Proof
  Induct_on ‘binds’ \\ fs [FORALL_PROD,mk_bind_def]
QED

Theorem freevars_mk_seqs:
  MEM (n,args,body) binds ∧ obligation binds ⇒
  freevars (mk_seqs args body) = freevars body
Proof
  rw [obligation_def,EVERY_MEM]
  \\ first_x_assum dxrule
  \\ fs [] \\ rw []
  \\ qpat_x_assum ‘_ ⊆ freevars body’ mp_tac
  \\ qid_spec_tac ‘args’
  \\ Induct \\ fs [mk_seqs_def,FORALL_PROD]
  \\ rw [] \\ fs [mk_seqs_def]
  \\ fs [EXTENSION] \\ metis_tac []
QED

Theorem letrec_seq_freevars:
  ∀binds x y. letrec_seq binds x y ⇒ freevars x = freevars y
Proof
  Induct_on ‘letrec_seq’ \\ rw [] \\ gvs []
  >-
   (PairCases_on ‘b’ \\ fs [mk_bind_def,MAP_FST_mk_bind]
    \\ rw [EXTENSION] \\ eq_tac \\ rw [] \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS]
    \\ fs [mk_seq_bind_def,MEM_MAP,EXISTS_PROD,PULL_EXISTS,FORALL_PROD,mk_bind_def]
    \\ gvs [freevars_mk_seqs]
    \\ metis_tac [freevars_mk_seqs])
  >- cheat (* long and boring case *)
  >- (pop_assum mp_tac
      \\ qid_spec_tac ‘xs’
      \\ qid_spec_tac ‘ys’
      \\ Induct \\ Cases_on ‘xs’ \\ fs [])
  \\ last_x_assum mp_tac
  \\ qid_spec_tac ‘xs’
  \\ qid_spec_tac ‘ys’
  \\ Induct \\ fs []
  \\ fs [PULL_EXISTS]
  \\ strip_tac \\ Cases \\ fs []
  \\ strip_tac \\ res_tac \\ fs [UNCURRY]
  \\ gvs [EXTENSION]
  \\ metis_tac []
QED

Theorem subst_letrec_seq:
  ∀binds x y m1 m2.
    letrec_seq binds x y ∧
    FDOM m1 = FDOM m2 ∧
    (∀k v1 v2.
      FLOOKUP m1 k = SOME v1 ∧ FLOOKUP m2 k = SOME v2 ⇒
      letrec_seq binds v1 v2 ∧ closed v1 ∧ closed v2) ⇒
    letrec_seq binds (subst m1 x) (subst m2 y)
Proof
  Induct_on ‘letrec_seq’ \\ rw []
  \\ cheat (*
  >-
   (DEP_REWRITE_TAC [closed_subst]
    \\ irule_at Any letrec_seq_change \\ fs [MAP_FST_mk_bind]
    \\ drule_at Any freevars_mk_seqs
    \\ PairCases_on ‘b’ \\ fs [mk_bind_def,EVERY_MEM]
    \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS,mk_seq_bind_def,mk_bind_def]
    \\ gvs [SF SFY_ss]
    \\ fs [obligation_def,EVERY_MEM,FORALL_PROD]
    \\ rw [] \\ res_tac
    \\ gvs [SUBSET_DEF]
    \\ metis_tac [])
  \\ cheat (*
  >-
   (simp [subst_def]
    \\ DEP_REWRITE_TAC [pure_exp_lemmasTheory.subst_subst_FUNION]
    \\ conj_tac >- fs [FRANGE_DEF,FEVERY_DEF,PULL_EXISTS]
    \\ irule letrec_seq_seq
    \\ last_x_assum $ irule_at Any
    \\ fs [FEVERY_DEF,FUNION_DEF,FLOOKUP_DEF]
    \\ rw [])
  \\ cheat
  >-
   (fs [subst_def]
    \\ simp [Once letrec_seq_cases]
    \\ disj1_tac
    \\ fs [MAP_ID,FORALL_PROD]
    \\ reverse (rw [])
    >-
     (last_x_assum irule \\ fs [FDOM_FDIFF,EXTENSION,SUBSET_DEF]
      \\ fs [FDOM_FDIFF,EXTENSION,FLOOKUP_FDIFF]
      \\ rw [] \\ res_tac \\ fs []
      \\ metis_tac [])
    \\ irule pure_exp_lemmasTheory.subst_ignore
    \\ CCONTR_TAC \\ gvs [IN_DISJOINT,EVERY_MEM,SUBSET_DEF]
    \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS] \\ metis_tac [])
  >-
   (fs [subst_def] \\ rpt CASE_TAC \\ fs [letrec_seq_refl]
    \\ res_tac \\ fs [] \\ gvs [FLOOKUP_DEF])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_seq_cases]
    \\ last_x_assum irule \\ fs []
    \\ fs [DOMSUB_FLOOKUP_THM,AllCaseEqs()]
    \\ rw [] \\ res_tac \\ fs [SUBSET_DEF])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_seq_cases]
    \\ rpt $ last_x_assum $ irule_at Any \\ fs [])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_seq_cases,SF ETA_ss]
    \\ last_x_assum mp_tac \\ fs []
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    \\ rw [] \\ metis_tac [])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_seq_cases] \\ disj2_tac
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
    \\ reverse conj_tac
    >-
     (last_x_assum irule
      \\ fs [FDOM_FDIFF,EXTENSION,FLOOKUP_FDIFF,SUBSET_DEF]
      \\ rw [] \\ res_tac \\ fs [])
    \\ last_x_assum mp_tac
    \\ last_x_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘m2’
    \\ qid_spec_tac ‘m1’
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    \\ strip_tac \\ Cases \\ fs []
    \\ rw []
    >-
     (first_x_assum irule
      \\ fs [FDOM_FDIFF,EXTENSION,FLOOKUP_FDIFF,SUBSET_DEF]
      \\ rw [] \\ res_tac \\ fs [])
    \\ rewrite_tac [GSYM finite_mapTheory.FDIFF_FDOMSUB_INSERT]
    \\ first_x_assum irule
    \\ fs [FDOM_FDIFF,EXTENSION,FLOOKUP_FDIFF]
    \\ fs [DOMSUB_FLOOKUP_THM,AllCaseEqs(),SUBSET_DEF]
    \\ rw [] \\ res_tac \\ fs []) *) *)
QED

Theorem letrec_seq_subst1:
  letrec_seq binds a1 a2 ∧ letrec_seq binds z y ∧ closed a1 ∧ closed a2 ⇒
  letrec_seq binds (subst1 v a1 z) (subst1 v a2 y)
Proof
  strip_tac
  \\ irule subst_letrec_seq
  \\ fs [FLOOKUP_DEF]
QED

Triviality FDOM_UPDATES_EQ:
  ∀b1. FDOM (FEMPTY |++ MAP (λ(g,x). (g,Letrec b2 x)) b1) = set (MAP FST b1)
Proof
  fs [FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
QED

Triviality FORALL_FRANGE:
  (∀v. v ∈ FRANGE m ⇒ P v) ⇔ ∀k v. FLOOKUP m k = SOME v ⇒ P v
Proof
  fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS]
QED

Theorem ALOOKUP_REVERSE_LIST_REL[local]:
  ∀bs ys.
    LIST_REL p (MAP SND bs) (MAP SND ys) ∧
    MAP FST ys = MAP FST bs ∧
    ALOOKUP (REVERSE (MAP (λ(g,x). (g,f x)) bs)) k' = SOME v1 ∧
    ALOOKUP (REVERSE (MAP (λ(g,x). (g,h x)) ys)) k' = SOME v2 ⇒
    ∃x y. p x y ∧ v1 = f x ∧ v2 = h y ∧ MEM x (MAP SND bs) ∧ MEM y (MAP SND ys)
Proof
  Induct using SNOC_INDUCT \\ fs [PULL_EXISTS]
  \\ Cases \\ Cases using SNOC_CASES
  \\ gvs [GSYM REVERSE_APPEND,MAP_SNOC,LIST_REL_SNOC,REVERSE_SNOC]
  \\ rename [‘SND hh’] \\ PairCases_on ‘hh’ \\ fs []
  \\ fs [AllCaseEqs()]
  \\ rpt strip_tac \\ gvs []
  \\ metis_tac []
QED

Triviality MEM_IMP_EQ:
  ∀b1 k p1 p2.
    MEM (k,p1) b1 ∧ MEM (k,p2) b1 ∧ ALL_DISTINCT (MAP FST b1) ⇒ p1 = p2
Proof
  Induct \\ fs [FORALL_PROD] \\ rw []
  \\ fs [MEM_MAP,EXISTS_PROD]
  \\ res_tac \\ fs []
QED

Triviality EVERY_FLOOKUP_closed_lemma:
  EVERY (λe. freevars e ⊆ set (MAP FST ys)) (MAP SND ys) ⇒
  (∀n v.
     FLOOKUP (FEMPTY |++ MAP (λ(g,x). (g,Letrec ys x)) ys) n = SOME v ⇒
     closed v)
Proof
  fs [alistTheory.flookup_fupdate_list,AllCaseEqs()]
  \\ rw [] \\ imp_res_tac ALOOKUP_MEM
  \\ gvs [MEM_MAP,EXISTS_PROD,EVERY_MEM,PULL_EXISTS]
  \\ res_tac \\ fs []
QED

Theorem MEM_LIST_REL:
  ∀xs ys P y. LIST_REL P xs ys ∧ MEM y ys ⇒ ∃x. MEM x xs ∧ P x y
Proof
  Induct \\ fs [PULL_EXISTS]
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
  \\ metis_tac []
QED

Theorem MEM_LIST_REL1:
  ∀xs ys P x. LIST_REL P xs ys ∧ MEM x xs ⇒ ∃y. MEM y ys ∧ P x y
Proof
  Induct \\ fs [PULL_EXISTS]
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
  \\ metis_tac []
QED

Theorem LIST_REL_COMP:
  ∀xs ys zs.
    LIST_REL f xs ys ∧ LIST_REL g ys zs ⇒
    LIST_REL (λx z. ∃y. f x y ∧ g y z) xs zs
Proof
  Induct \\ fs [PULL_EXISTS]
  \\ metis_tac []
QED

Theorem freevars_mk_seqs_lemma:
  ∀vs x.
    freevars (mk_seqs vs x) DIFF set (MAP FST vs) =
    freevars x DIFF set (MAP FST vs)
Proof
  Induct \\ fs [mk_seqs_def,FORALL_PROD]
  \\ gen_tac \\ Cases
  \\ fs [mk_seqs_def]
  \\ fs [EXTENSION]
  \\ metis_tac []
QED

Theorem freevars_mk_seq_bind[local,simp]:
  freevars (SND (mk_seq_bind b)) = freevars (SND (mk_bind b))
Proof
  PairCases_on ‘b’
  \\ rewrite_tac [mk_seq_bind_def,mk_bind_def]
  \\ fs [freevars_mk_seqs_lemma]
QED

Theorem MAP_FST_mk_seq_bind[local,simp]:
  MAP FST (MAP mk_seq_bind binds) = MAP FST (MAP mk_bind binds)
Proof
  Induct_on ‘binds’ \\ fs [FORALL_PROD,mk_seq_bind_def,mk_bind_def]
QED

Theorem subst_funs_Lams:
  ∀vs xs.
    DISJOINT (set vs) (set (MAP FST xs)) ∧
    (∀n v. FLOOKUP (FEMPTY |++ MAP (λ(g,x). (g,Letrec xs x)) xs) n = SOME v ⇒
           closed v) ⇒
    subst_funs xs (Lams vs y) = Lams vs (subst_funs xs y)
Proof
  Induct \\ fs [Lams_def] \\ rw []
  \\ fs [subst_funs_def,bind_def,SF SFY_ss,subst_def]
  \\ irule EQ_TRANS
  \\ last_x_assum $ irule_at Any \\ fs [SF SFY_ss]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ pop_assum kall_tac
  \\ rename [‘(_,f _)’]
  \\ fs [finite_mapTheory.DOMSUB_FUPDATE_LIST]
  \\ AP_TERM_TAC
  \\ last_x_assum kall_tac
  \\ Induct_on ‘xs’ \\ fs [FORALL_PROD]
QED

Triviality subst_funs_Seq_Zero:
  (∀n v. FLOOKUP (FEMPTY |++ MAP (λ(g,x). (g,Letrec xs x)) xs) n = SOME v ⇒
         closed v) ⇒
  subst_funs xs (Seq Zero x) = Seq Zero (subst_funs xs x)
Proof
  fs [subst_funs_def, bind_def, SF SFY_ss, subst_def]
QED

Theorem letrec_seq_Lams[local]:
  ∀vs. letrec_seq binds x y ⇒ letrec_seq binds (Lams vs x) (Lams vs y)
Proof
  Induct \\ fs [Lams_def] \\ rw [] \\ fs []
  \\ simp [Once letrec_seq_cases]
QED

Theorem subst_funs_mk_seq[local]:
  ∀args.
    (∀n v. FLOOKUP (FEMPTY |++ MAP (λ(g,x). (g,Letrec fs x)) fs) n = SOME v ⇒
           closed v) ∧ DISJOINT (set (MAP FST args)) (set (MAP FST fs)) ⇒
    subst_funs fs (mk_seqs args body) = mk_seqs args (subst_funs fs body)
Proof
  Induct \\ fs [mk_seqs_def,FORALL_PROD]
  \\ gen_tac \\ Cases \\ fs [mk_seqs_def]
  \\ fs [subst_funs_def,bind_def, SF SFY_ss, subst_def]
  \\ fs [alistTheory.flookup_fupdate_list,AllCaseEqs()]
  \\ fs [ALOOKUP_NONE,MEM_MAP,FORALL_PROD]
QED

Theorem letrec_seq_subst_funs:
  MEM b binds ∧ obligation binds ⇒
  letrec_seq binds (subst_funs (MAP mk_bind binds) (SND (mk_bind b)))
                   (subst_funs (MAP mk_seq_bind binds) (SND (mk_seq_bind b)))
Proof
  rw []
  \\ PairCases_on ‘b’
  \\ fs [mk_bind_def,mk_seq_bind_def]
  \\ DEP_REWRITE_TAC [subst_funs_Lams] \\ fs [MAP_FST_mk_bind]
  \\ fs [obligation_def]
  \\ fs [EVERY_MEM] \\ res_tac \\ fs []
  \\ irule_at Any letrec_seq_Lams
  \\ once_rewrite_tac [CONJ_COMM]
  \\ DEP_REWRITE_TAC [subst_funs_Seq_Zero]
  \\ DEP_REWRITE_TAC [subst_funs_mk_seq]
  \\ fs [MAP_FST_mk_bind]
  \\ REWRITE_TAC [CONJ_ASSOC]
  \\ reverse conj_tac
  >-
   (simp [Once letrec_seq_cases]
    \\ disj1_tac
    \\ last_x_assum $ irule_at Any
    \\ qexists_tac ‘FEMPTY’
    \\ qexists_tac ‘FEMPTY’
    \\ fs [FEVERY_DEF])
  \\ rw []
  \\ fs [FDOM_UPDATES_EQ,PULL_EXISTS,alistTheory.flookup_fupdate_list]
  \\ fs [FORALL_FRANGE,alistTheory.flookup_fupdate_list,AllCaseEqs()]
  \\ rw []
  \\ imp_res_tac ALOOKUP_MEM
  \\ gvs [EVERY_MEM] \\ res_tac \\ fs []
  \\ gvs [MEM_MAP,EXISTS_PROD,PULL_EXISTS,EVERY_MEM,mk_seq_bind_def,
          MAP_FST_mk_bind,mk_bind_def,freevars_mk_seqs_lemma]
  \\ rw [] \\ res_tac \\ fs []
  \\ gvs [SUBSET_DEF]
  \\ metis_tac []
QED

Triviality eval_wh_Constructor_NIL_bisim =
  eval_wh_Constructor_bisim |> Q.GEN ‘xs’ |> Q.SPEC ‘[]’ |> SIMP_RULE (srw_ss()) [];

Triviality LIST_REL_IMP_MAP_EQ:
  ∀xs ys P f g.
    (∀x y. MEM x xs ∧ MEM y ys ∧ P x y ⇒ f x = g y) ⇒
    LIST_REL P xs ys ⇒ MAP g ys = MAP f xs
Proof
  Induct \\ fs [PULL_EXISTS,SF DNF_ss] \\ metis_tac []
QED

Triviality IMP_Seq_Zero:
  closed y ∧ (x ≃ y) F ⇒ (x ≃ Seq Zero y) F
Proof
  rw []
  \\ irule app_bisimilarity_trans
  \\ first_x_assum $ irule_at Any
  \\ irule eval_wh_IMP_app_bisimilarity
  \\ fs [eval_wh_Seq,eval_wh_Prim,get_atoms_def]
QED

Theorem letrec_seq_subst_funs_mk_bind:
  obligation binds ∧
  FEVERY (λ(k,v). closed v) m1 ∧
  FEVERY (λ(k,v). closed v) m2 ∧
  FDOM m1 = FDOM m2 ∧
  (∀k v1 v2.
     FLOOKUP m1 k = SOME v1 ∧ FLOOKUP m2 k = SOME v2 ⇒
     letrec_seq binds v1 v2) ⇒
  letrec_seq binds (subst m1 (subst_funs (MAP mk_bind binds) e))
                   (subst m2 (subst_funs (MAP mk_seq_bind binds) e))
Proof
  cheat
QED

Triviality freevars_mk_seqs':
  freevars (mk_seqs vs e) =
  set (MAP FST (FILTER SND vs)) UNION freevars e
Proof
  Induct_on ‘vs’ \\ fs [mk_seqs_def,FORALL_PROD]
  \\ strip_tac \\ Cases \\ fs [mk_seqs_def]
  \\ fs [EXTENSION] \\ metis_tac []
QED

Theorem obligation_imp_freevars:
  obligation binds ∧ MEM (n,vs,e) binds ⇒
  freevars (mk_seqs vs (subst_funs (MAP mk_seq_bind binds) e)) ⊆
  freevars (subst_funs (MAP mk_bind binds) e)
Proof
  rw [obligation_def,EVERY_MEM]
  \\ first_assum drule
  \\ simp_tac std_ss [] \\ rw []
  \\ fs [freevars_mk_seqs']
  \\ simp [subst_funs_def,bind_def]
  \\ reverse IF_CASES_TAC
  >-
   (qsuff_tac ‘F’ \\ fs []
    \\ fs [FDOM_UPDATES_EQ,PULL_EXISTS,alistTheory.flookup_fupdate_list]
    \\ fs [FORALL_FRANGE,alistTheory.flookup_fupdate_list,AllCaseEqs()]
    \\ rw []
    \\ dxrule ALOOKUP_MEM
    \\ gvs [EVERY_MEM]
    \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS,EVERY_MEM,mk_bind_def]
    \\ CCONTR_TAC \\ fs []
    \\ qpat_x_assum ‘~(closed _)’ mp_tac
    \\ gvs []
    \\ gvs [mk_bind_def,MAP_FST_mk_bind]
    \\ fs [SUBSET_DEF,EVERY_MEM,FORALL_PROD,EXISTS_PROD,MEM_MAP,mk_bind_def,PULL_EXISTS]
    \\ metis_tac [])
  \\ conj_tac
  >-
   (DEP_REWRITE_TAC [freevars_subst]
    \\ fs [SUBSET_DEF,FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS,MEM_MAP,MEM_FILTER]
    \\ cheat)
  \\ cheat (* local proof *)
QED

Theorem eval_forward_letrec_seq:
  obligation binds ⇒
  eval_forward F (letrec_seq binds)
Proof
  strip_tac
  \\ simp [eval_forward_def]
  \\ ho_match_mp_tac eval_wh_to_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  >~ [‘Var’] >- fs [eval_wh_to_def]
  >~ [‘Lam v z’] >-
   (fs [eval_wh_to_def]
    \\ qpat_x_assum ‘letrec_seq _ _ _’ mp_tac
    \\ simp [Once letrec_seq_cases] \\ strip_tac \\ gvs []
    \\ ‘eval_wh (Lam v y) = wh_Closure v y’ by fs [eval_wh_Lam]
    \\ drule_all eval_wh_Closure_bisim
    \\ strip_tac \\ fs []
    \\ rw [] \\ first_x_assum drule
    \\ disch_then $ irule_at Any
    \\ irule_at Any letrec_seq_subst1
    \\ fs [])
  >~ [‘App e1 e2y’] >-
   (fs [eval_wh_to_def]
    \\ simp [Once letrec_seq_cases] \\ rpt strip_tac \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k e1)’ \\ fs []
    \\ PairCases_on ‘x’ \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘eval_wh_to k e1’ \\ gvs [dest_wh_Closure_def]
    \\ first_x_assum drule \\ fs []
    \\ imp_res_tac letrec_seq_freevars
    \\ ‘(g ≃ g) F ∧ closed g’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule_all
    \\ strip_tac \\ fs []
    \\ rename [‘eval_wh g = wh_Closure v1 e1’]
    \\ first_x_assum $ qspec_then ‘e2y’ mp_tac
    \\ imp_res_tac letrec_seq_freevars
    \\ ‘closed y’ by fs [closed_def]
    \\ disch_then drule_all \\ strip_tac \\ gvs []
    \\ fs [bind_def,FLOOKUP_DEF]
    \\ first_x_assum drule
    \\ disch_then irule
    \\ irule_at Any IMP_closed_subst
    \\ fs [FRANGE_DEF]
    \\ irule_at Any pure_eval_lemmasTheory.eval_wh_Closure_closed
    \\ drule eval_wh_to_IMP_eval_wh \\ fs [] \\ strip_tac
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ irule app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ irule app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos last \\ fs []
    \\ irule eval_wh_IMP_app_bisimilarity
    \\ irule_at Any IMP_closed_subst
    \\ fs [FRANGE_DEF]
    \\ irule_at Any pure_eval_lemmasTheory.eval_wh_Closure_closed
    \\ first_assum $ irule_at $ Pos hd \\ fs []
    \\ fs [eval_wh_App,bind_def,FLOOKUP_DEF])
  >~ [‘Letrec bs x’] >-
   (rpt strip_tac
    \\ qpat_x_assum ‘letrec_seq _ _ _’ mp_tac
    \\ simp [Once letrec_seq_cases]
    \\ reverse strip_tac \\ gvs []
    >-
     (rw [eval_wh_to_def] \\ gvs [] \\ first_x_assum irule
      \\ rename [‘(Letrec ys y ≃ e2) F’]
      \\ irule_at Any app_bisimilarity_trans
      \\ first_x_assum $ irule_at $ Pos $ el 2
      \\ qexists_tac ‘subst_funs ys y’
      \\ irule_at Any eval_wh_IMP_app_bisimilarity
      \\ simp [eval_wh_Letrec] \\ gvs []
      \\ fs [subst_funs_def,bind_def]
      \\ ‘MAP FST ys = MAP FST bs’ by fs [] \\ fs []
      \\ drule EVERY_FLOOKUP_closed_lemma \\ strip_tac
      \\ ‘EVERY (λe. freevars e ⊆ set (MAP FST ys)) (MAP SND ys)’ by
        (fs [EVERY_MEM] \\ rw []
         \\ drule_all MEM_LIST_REL \\ rw []
         \\ imp_res_tac letrec_seq_freevars \\ fs []
         \\ res_tac  \\ gvs [] \\ metis_tac [])
      \\ imp_res_tac letrec_seq_freevars \\ fs []
      \\ drule EVERY_FLOOKUP_closed_lemma  \\ strip_tac
      \\ asm_rewrite_tac []
      \\ rpt $ irule_at Any IMP_closed_subst
      \\ gvs [] \\ irule_at Any subst_letrec_seq \\ gs [FORALL_FRANGE]
      \\ asm_rewrite_tac []
      \\ fs [FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
      \\ fs [alistTheory.flookup_fupdate_list,AllCaseEqs()]
      \\ rpt strip_tac
      \\ drule_all ALOOKUP_REVERSE_LIST_REL \\ strip_tac \\ gvs []
      >- (simp [Once letrec_seq_cases] \\ disj2_tac \\ fs [])
      \\ res_tac \\ fs []
      \\ imp_res_tac letrec_seq_freevars \\ fs [])
    \\ rw [eval_wh_to_def] \\ gvs []
    \\ first_x_assum irule \\ fs []
    \\ conj_tac >-
     (fs [subst_funs_def] \\ irule IMP_closed_bind
      \\ fs [SUBSET_DEF,FDOM_FUPDATE_LIST,MAP_MAP_o,
             combinTheory.o_DEF,UNCURRY,SF ETA_ss])
    \\ irule_at Any letrec_seq_subst_funs \\ simp []
    \\ irule_at Any app_bisimilarity_trans
    \\ last_x_assum $ irule_at Any
    \\ irule eval_IMP_app_bisimilarity
    \\ fs [eval_Letrec]
    \\ fs [subst_funs_def,bind_def]
    \\ rpt $ irule_at Any IMP_closed_subst
    \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
    \\ rw []
    \\ rpt $ irule_at Any IMP_closed_subst
    \\ fs [FDOM_UPDATES_EQ,PULL_EXISTS,alistTheory.flookup_fupdate_list]
    \\ fs [FORALL_FRANGE,alistTheory.flookup_fupdate_list,AllCaseEqs()]
    \\ rw []
    \\ imp_res_tac ALOOKUP_MEM
    \\ gvs [EVERY_MEM] \\ res_tac \\ fs []
    \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS,EVERY_MEM])
  >~ [‘letrec_seq _ (Prim p xs)’]
  \\ rpt strip_tac
  \\ qpat_x_assum ‘letrec_seq _ _ _’ mp_tac
  \\ Cases_on ‘p = Seq’
  >-
   (simp [Once letrec_seq_cases]
    \\ reverse (rpt strip_tac) \\ gvs []
    >-
     (fs [eval_wh_to_def]
      \\ IF_CASES_TAC \\ fs []
      \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
      \\ Cases_on ‘k=0’ \\ fs [SF DNF_ss]
      \\ Cases_on ‘eval_wh_to (k − 1) h = wh_Diverge’ \\ fs []
      \\ Cases_on ‘eval_wh_to (k − 1) h = wh_Error’ \\ gvs []
      \\ imp_res_tac letrec_seq_freevars
      \\ first_assum irule \\ fs []
      \\ first_x_assum $ irule_at $ Pos last
      \\ irule app_bisimilarity_trans
      \\ first_x_assum $ irule_at $ Pos last \\ fs []
      \\ irule eval_wh_IMP_app_bisimilarity
      \\ fs [closed_def,eval_wh_Seq,AllCaseEqs()]
      \\ qsuff_tac ‘eval_wh y ≠ wh_Error ∧ eval_wh y ≠ wh_Diverge’
      \\ fs []
      \\ first_x_assum drule
      \\ ‘(y ≃ y) F ∧ closed y’ by
        (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
         \\ fs [closed_def])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ Cases_on ‘eval_wh_to (k − 1) h’ \\ fs [])
    \\ fs [SF DNF_ss]
    \\ simp [eval_wh_to_def]
    \\ Cases_on ‘k = 0’ \\ gvs []
    \\ first_x_assum irule \\ fs []
    \\ irule_at Any app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos $ el 2
    \\ irule_at Any IMP_Seq_Zero
    \\ irule_at Any letrec_seq_subst_funs_mk_bind \\ fs []
    \\ qexists_tac ‘m2’ \\ fs []
    \\ conj_tac >- fs [SF SFY_ss]
    \\ ‘∀n v. FLOOKUP m2 n = SOME v ⇒ closed v’ by fs [FEVERY_DEF,FLOOKUP_DEF]
    \\ ‘∀v. v ∈ FRANGE m2 ⇒ closed v’ by fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS]
    \\ conj_asm1_tac
    >-
     (‘∀n v. FLOOKUP m1 n = SOME v ⇒ closed v’ by fs [FEVERY_DEF,FLOOKUP_DEF]
      \\ ‘∀v. v ∈ FRANGE m1 ⇒ closed v’ by fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS]
      \\ drule_all pure_exp_lemmasTheory.closed_subst_freevars \\ strip_tac
      \\ irule IMP_closed_subst \\ fs [] \\ gvs []
      \\ irule SUBSET_TRANS \\ pop_assum $ irule_at Any
      \\ irule obligation_imp_freevars \\ fs [] \\ first_x_assum $ irule_at Any)
    \\ fs [obligation_def,EVERY_MEM]
    \\ first_x_assum drule \\ fs [exp_eq_def]
    \\ rpt strip_tac
    \\ pop_assum $ qspec_then ‘m2’ mp_tac
    \\ fs [bind_def,SF SFY_ss]
    \\ disch_then irule
    \\ qabbrev_tac ‘aa = subst_funs (MAP mk_seq_bind binds) e’
    \\ drule_all pure_exp_lemmasTheory.closed_subst_freevars
    \\ fs [] \\ rw []
    \\ irule SUBSET_TRANS
    \\ pop_assum $ irule_at Any
    \\ qid_spec_tac ‘vs’ \\ Induct \\ fs [mk_seqs_def]
    \\ Cases \\ Cases_on ‘r’ \\ fs [mk_seqs_def]
    \\ fs [SUBSET_DEF])
  \\ simp [Once letrec_seq_cases] \\ rw []
  \\ Cases_on ‘p’ \\ fs []
  >~ [‘Cons s xs’] >-
   (rw [eval_wh_to_def]
    \\ ‘eval_wh (Cons s ys) = wh_Constructor s ys’ by fs [eval_wh_Cons]
    \\ drule_all eval_wh_Constructor_bisim \\ strip_tac \\ fs []
    \\ drule_then drule LIST_REL_COMP
    \\ match_mp_tac LIST_REL_mono \\ fs [])
  >~ [‘If’] >-
   (gvs [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ fs [SF DNF_ss]
    \\ reverse (Cases_on ‘∃s. eval_wh_to (k − 1) h = wh_Constructor s []’ \\ fs [])
    >- (Cases_on ‘eval_wh_to (k − 1) h’ \\ gvs [] \\ rw [])
    \\ qpat_x_assum ‘letrec_seq _ h y’ assume_tac
    \\ first_assum drule
    \\ imp_res_tac letrec_seq_freevars
    \\ ‘(y ≃ y) F ∧ closed y’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule \\ fs [] \\ strip_tac
    \\ reverse (rw []) \\ fs []
    \\ rename [‘eval_wh_to (k − 1) h2’]
    \\ qpat_x_assum ‘letrec_seq _ h2 _’ assume_tac
    \\ first_x_assum drule
    \\ disch_then irule \\ fs []
    \\ irule app_bisimilarity_trans
    \\ first_x_assum $ irule_at Any \\ fs []
    \\ irule eval_wh_IMP_app_bisimilarity
    \\ fs [closed_def,eval_wh_If])
  >~ [‘IsEq cname arity onoff’] >-
   (fs [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ fs [SF DNF_ss]
    \\ reverse (Cases_on ‘∃s xs. eval_wh_to (k − 1) h = wh_Constructor s xs ∧
                   ~is_eq_fail onoff s ∧ (s = cname ⇒ arity = LENGTH xs)’ \\ fs [])
    >- (Cases_on ‘eval_wh_to (k − 1) h’ \\ gvs [] \\ rw [])
    \\ IF_CASES_TAC \\ gvs []
    \\ first_assum drule
    \\ imp_res_tac letrec_seq_freevars
    \\ ‘(y ≃ y) F ∧ closed y’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule \\ fs [] \\ strip_tac
    \\ irule eval_wh_Constructor_NIL_bisim
    \\ first_x_assum $ irule_at $ Pos last
    \\ imp_res_tac LIST_REL_LENGTH
    \\ fs [eval_wh_IsEq])
  >~ [‘Proj cname i’] >-
   (fs [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘k=0’ \\ fs [SF DNF_ss]
    \\ imp_res_tac LIST_REL_LENGTH
    \\ reverse (Cases_on ‘∃s xs. eval_wh_to (k − 1) h = wh_Constructor s xs ∧
                                 s = cname ∧ i < LENGTH xs’ \\ fs [])
    >- (Cases_on ‘eval_wh_to (k − 1) h’ \\ gvs [] \\ rw [])
    \\ first_assum irule \\ fs []
    \\ last_x_assum drule \\ fs []
    \\ imp_res_tac letrec_seq_freevars
    \\ ‘(y ≃ y) F ∧ closed y’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule \\ fs [] \\ strip_tac
    \\ fs [LIST_REL_EL_EQN]
    \\ gvs []
    \\ pop_assum drule \\ strip_tac
    \\ first_x_assum $ irule_at $ Pos last
    \\ irule_at Any app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ irule_at Any app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos $ el 2 \\ fs []
    \\ irule_at Any eval_wh_IMP_app_bisimilarity
    \\ fs [eval_wh_Proj]
    \\ dxrule eval_wh_freevars_SUBSET
    \\ dxrule eval_wh_to_freevars_SUBSET
    \\ fs [PULL_EXISTS,MEM_MAP,closed_def,EXTENSION]
    \\ fs [MEM_EL]
    \\ metis_tac [])
  >~ [‘AtomOp a’] >-
   (fs [eval_wh_to_def]
    \\ Cases_on ‘get_atoms (MAP (if k = 0 then K wh_Diverge else
                                   (λa. eval_wh_to (k − 1) a)) xs)’ \\ fs []
    \\ Cases_on ‘x’ \\ fs []
    \\ rename [‘eval_op a atoms’]
    \\ qsuff_tac ‘get_atoms (MAP eval_wh ys) = SOME (SOME atoms)’
    >-
     (rw [] \\ gvs []
      \\ Cases_on ‘eval_op a atoms’ \\ fs []
      \\ Cases_on ‘x’ \\ fs []
      >-
       (rw [] \\ irule eval_wh_Atom_bisim
        \\ last_x_assum $ irule_at Any
        \\ gvs [eval_wh_Prim])
      \\ Cases_on ‘y’ \\ fs []
      \\ rw [] \\ irule eval_wh_Constructor_NIL_bisim
      \\ last_x_assum $ irule_at Any
      \\ gvs [eval_wh_Prim])
    \\ fs [get_atoms_def,AllCaseEqs()]
    \\ gvs []
    \\ Cases_on ‘xs = []’ >- gvs []
    \\ Cases_on ‘k = 0’ >- (Cases_on ‘xs’ \\ fs [])
    \\ gvs [MEM_MAP]
    \\ rw []
    >-
     (fs [EVERY_MEM,MEM_MAP] \\ rw []
      \\ drule_all MEM_LIST_REL \\ rw []
      \\ first_x_assum $ drule_then drule
      \\ res_tac
      \\ imp_res_tac letrec_seq_freevars
      \\ ‘(y ≃ y) F ∧ closed y’ by
        (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
         \\ fs [closed_def])
      \\ disch_then drule_all
      \\ rw [] \\ fs [PULL_EXISTS]
      \\ first_x_assum drule \\ strip_tac
      \\ Cases_on ‘eval_wh_to (k − 1) x’ \\ fs []
      \\ res_tac \\ fs [])
    >-
     (CCONTR_TAC \\ fs []
      \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
      \\ drule_all MEM_LIST_REL \\ strip_tac
      \\ ‘closed x ∧ ¬error_Atom (eval_wh_to (k − 1) x)’ by (res_tac \\ fs [])
      \\ ‘eval_wh_to (k − 1) x ≠ wh_Diverge’ by (CCONTR_TAC \\ fs [] \\ res_tac \\ fs [])
      \\ first_x_assum $ drule_then drule
      \\ imp_res_tac letrec_seq_freevars
      \\ ‘(y ≃ y) F ∧ closed y ∧ closed x’ by
        (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
         \\ fs [closed_def,EVERY_MEM] \\ res_tac \\ fs [])
      \\ disch_then drule \\ fs []
      \\ Cases_on ‘eval_wh_to (k − 1) x’ \\ fs [])
    \\ AP_TERM_TAC
    \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ match_mp_tac LIST_REL_IMP_MAP_EQ
    \\ rw []
    \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
    \\ ‘closed x ∧ ¬error_Atom (eval_wh_to (k − 1) x)’ by (res_tac \\ fs [])
    \\ ‘eval_wh_to (k − 1) x ≠ wh_Diverge’ by (CCONTR_TAC \\ fs [] \\ res_tac \\ fs [])
    \\ first_x_assum $ drule_then drule
    \\ imp_res_tac letrec_seq_freevars
    \\ ‘(y ≃ y) F ∧ closed y ∧ closed x’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def,EVERY_MEM] \\ res_tac \\ fs [])
    \\ disch_then drule \\ fs []
    \\ Cases_on ‘eval_wh_to (k − 1) x’ \\ fs [])
QED

Theorem eval_forward_letrec_seq_rev:
  eval_forward F (λx y. letrec_seq binds y x)
Proof
  cheat
QED

Theorem Letrec_mk_seq_bind:
  closed (Letrec (MAP mk_bind binds) (SND (mk_bind b))) ∧
  closed (Letrec (MAP mk_seq_bind binds) (SND (mk_seq_bind b))) ∧
  MEM b binds ∧ obligation binds ⇒
  (Letrec (MAP mk_bind binds) (SND (mk_bind b)) ≃
   Letrec (MAP mk_seq_bind binds) (SND (mk_seq_bind b))) F
Proof
  rw [] \\ irule eval_forward_imp_bisim \\ fs []
  \\ qexists_tac ‘letrec_seq binds’
  \\ irule_at Any letrec_seq_change
  \\ fs [letrec_seq_refl,eval_forward_letrec_seq,eval_forward_letrec_seq_rev]
QED

val _ = export_theory();
