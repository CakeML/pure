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

Definition mk_lams_def:
  mk_lams ((n,vs,e):bind) = (n, Lams (MAP FST vs) e)
End

Definition mk_seqs_def:
  mk_seqs [] e = e ∧
  mk_seqs ((_,F)::xs) e = mk_seqs xs e ∧
  mk_seqs ((v,T)::xs) e = Seq (Var v) (mk_seqs xs e)
End

Definition mk_seq_lams_def:
  mk_seq_lams ((n,vs,e):bind) = (n, Lams (MAP FST vs) (mk_seqs vs e))
End

Overload Zero[local] = “Lit (Int 0):exp”;

Definition mk_bind_def: (* same as mk_lams but with Seq Zero marker *)
  mk_bind ((n,vs,e):bind) = (n, Lams (MAP FST vs) (Seq Zero e))
End

Definition mk_seq_bind_def: (* same as mk_seq_lams but with Seq Zero marker *)
  mk_seq_bind ((n,vs,e):bind) = (n, Lams (MAP FST vs) (Seq Zero (mk_seqs vs e)))
End

Definition obligation_def:
  obligation (binds : bind list) ⇔
    ALL_DISTINCT (MAP FST binds) ∧
    EVERY (λ(vname,args,body).
      (* args are disjoint *)
      ALL_DISTINCT (MAP FST args) ∧
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
    MEM (n,vs,e) binds ∧ obligation binds ∧
    FEVERY (λ(k,v). closed v) m1 ∧ FEVERY (λ(k,v). closed v) m2 ∧
    FDOM m1 = FDOM m2 ∧
    (∀k v1 v2.
      FLOOKUP m1 k = SOME v1 ∧ FLOOKUP m2 k = SOME v2 ⇒
      letrec_seq binds v1 v2) ⇒
    letrec_seq binds
      (Seq Zero (subst m1 (subst_funs (MAP mk_bind binds) e)))
      (Seq Zero (subst m2 (mk_seqs vs (subst_funs (MAP mk_seq_bind binds) e))))) ∧
   (* cases below are just recursion *)
[~Var:]
  (∀binds n.
    letrec_seq binds (Var n) (Var n)) ∧
[~Lam:]
  (∀binds n x y.
    letrec_seq binds x y ⇒
    letrec_seq binds (Lam n x) (Lam n y)) ∧
[~App:]
  (∀binds f g x y.
    letrec_seq binds f g ∧ letrec_seq binds x y ⇒
    letrec_seq binds (App f x) (App g y)) ∧
[~Prim:]
  (∀binds n xs ys.
    LIST_REL (letrec_seq binds) xs ys ⇒
    letrec_seq binds (Prim n xs) (Prim n ys)) ∧
[~Letrec:]
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

Triviality MAP_FST_mk_bind:
  MAP FST (MAP mk_bind binds) = MAP FST binds
Proof
  Induct_on ‘binds’ \\ fs [FORALL_PROD,mk_bind_def]
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

Definition obl_syntax_def:
  obl_syntax binds ⇔
    ALL_DISTINCT (MAP FST binds) ∧
    EVERY (λ(vname,args,body).
      ALL_DISTINCT (MAP FST args) ∧
      DISJOINT (set (MAP FST args)) (set (MAP FST binds)) ∧
      freevars body ⊆ set (MAP FST binds) ∪ set (MAP FST args) ∧
      set (MAP FST (FILTER SND args)) ⊆ freevars body) binds
End

Triviality IMP_obl_syntax[simp]:
  obligation binds ⇒ obl_syntax binds
Proof
  fs [obligation_def,obl_syntax_def,EVERY_MEM,FORALL_PROD,SF SFY_ss]
QED

Theorem freevars_mk_seqs_syntax:
  MEM (n,args,body) binds ∧ obl_syntax binds ⇒
  freevars (mk_seqs args body) = freevars body
Proof
  rw [obl_syntax_def,EVERY_MEM]
  \\ first_x_assum dxrule
  \\ fs [] \\ rw []
  \\ qpat_x_assum ‘_ ⊆ freevars body’ mp_tac
  \\ qid_spec_tac ‘args’
  \\ Induct \\ fs [mk_seqs_def,FORALL_PROD]
  \\ rw [] \\ fs [mk_seqs_def]
  \\ fs [EXTENSION] \\ metis_tac []
QED

Theorem freevars_mk_seqs:
  MEM (n,args,body) binds ∧ obligation binds ⇒
  freevars (mk_seqs args body) = freevars body
Proof
  metis_tac [freevars_mk_seqs_syntax,IMP_obl_syntax]
QED

Triviality FDOM_UPDATES_EQ:
  ∀b1. FDOM (FEMPTY |++ MAP (λ(g,x). (g,Letrec b2 x)) b1) = set (MAP FST b1)
Proof
  fs [FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
QED

Theorem mk_bind_closed:
  obligation binds ⇒
  (∀v. v ∈ FRANGE
             (FEMPTY |++
                MAP (λ(g,x). (g,Letrec (MAP mk_bind binds) x))
                  (MAP mk_bind binds)) ⇒
       closed v)
Proof
  rw [obligation_def,FRANGE_FLOOKUP]
  \\ fs [FDOM_UPDATES_EQ,PULL_EXISTS,alistTheory.flookup_fupdate_list]
  \\ fs [FORALL_FRANGE,alistTheory.flookup_fupdate_list,AllCaseEqs()]
  \\ rw []
  \\ dxrule ALOOKUP_MEM
  \\ gvs [EVERY_MEM]
  \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS,EVERY_MEM,mk_bind_def]
  \\ CCONTR_TAC \\ fs [] \\ gvs []
  \\ gvs [mk_bind_def,MAP_FST_mk_bind]
  \\ fs [SUBSET_DEF,EVERY_MEM,FORALL_PROD,EXISTS_PROD,MEM_MAP,mk_bind_def,PULL_EXISTS]
  \\ metis_tac []
QED

Theorem mk_seq_bind_closed_syntax':
  obl_syntax binds ∧ set bs SUBSET set binds ⇒
  (∀v. v ∈ FRANGE
             (FEMPTY |++
                MAP (λ(g,x). (g,Letrec (MAP mk_seq_bind binds) x))
                  (MAP mk_seq_bind bs)) ⇒
       closed v)
Proof
  rw []
  \\ drule_at Any freevars_mk_seqs_syntax \\ strip_tac
  \\ fs [obl_syntax_def,FRANGE_FLOOKUP]
  \\ fs [FDOM_UPDATES_EQ,PULL_EXISTS,alistTheory.flookup_fupdate_list]
  \\ fs [FORALL_FRANGE,alistTheory.flookup_fupdate_list,AllCaseEqs()]
  \\ rw []
  \\ dxrule ALOOKUP_MEM
  \\ gvs [EVERY_MEM]
  \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS,EVERY_MEM,mk_bind_def]
  \\ CCONTR_TAC \\ fs []
  \\ gvs [SUBSET_DEF]
  \\ res_tac
  \\ gvs []
  \\ gvs [mk_seq_bind_def,MAP_FST_mk_seq_bind,mk_bind_def]
  \\ fs [SUBSET_DEF,EVERY_MEM,FORALL_PROD,EXISTS_PROD,MEM_MAP,mk_seq_bind_def,PULL_EXISTS]
  \\ gvs [mk_seq_bind_def,MAP_FST_mk_seq_bind,mk_bind_def]
  \\ metis_tac []
QED

Theorem mk_seq_bind_closed_syntax:
  obl_syntax binds ⇒
  (∀v. v ∈ FRANGE
             (FEMPTY |++
                MAP (λ(g,x). (g,Letrec (MAP mk_seq_bind binds) x))
                  (MAP mk_seq_bind binds)) ⇒
       closed v)
Proof
  strip_tac \\ match_mp_tac mk_seq_bind_closed_syntax' \\ fs []
QED

Theorem mk_seq_bind_closed:
  obligation binds ⇒
  (∀v. v ∈ FRANGE
             (FEMPTY |++
                MAP (λ(g,x). (g,Letrec (MAP mk_seq_bind binds) x))
                  (MAP mk_seq_bind binds)) ⇒
       closed v)
Proof
  strip_tac \\ match_mp_tac mk_seq_bind_closed_syntax \\ fs []
QED

Theorem subset_funs_mk_bind:
  obligation binds ⇒
  subst_funs (MAP mk_bind binds) e =
  subst
    (FEMPTY |++
       MAP (λ(g,x). (g,Letrec (MAP mk_bind binds) x))
         (MAP mk_bind binds)) e
Proof
  rw [subst_funs_def,bind_def]
  \\ qsuff_tac ‘F’ \\ fs []
  \\ drule mk_bind_closed
  \\ fs [FLOOKUP_DEF,FRANGE_DEF]
  \\ metis_tac []
QED

Theorem subset_funs_mk_seq_bind_syntax:
  obl_syntax binds ⇒
  subst_funs (MAP mk_seq_bind binds) e =
  subst
    (FEMPTY |++
       MAP (λ(g,x). (g,Letrec (MAP mk_seq_bind binds) x))
         (MAP mk_seq_bind binds)) e
Proof
  rw [subst_funs_def,bind_def]
  \\ qsuff_tac ‘F’ \\ fs []
  \\ drule mk_seq_bind_closed_syntax
  \\ fs [FLOOKUP_DEF,FRANGE_DEF]
  \\ metis_tac []
QED

Theorem subset_funs_mk_seq_bind:
  obligation binds ⇒
  subst_funs (MAP mk_seq_bind binds) e =
  subst
    (FEMPTY |++
       MAP (λ(g,x). (g,Letrec (MAP mk_seq_bind binds) x))
         (MAP mk_seq_bind binds)) e
Proof
  rw [subst_funs_def,bind_def]
  \\ qsuff_tac ‘F’ \\ fs []
  \\ drule mk_seq_bind_closed
  \\ fs [FLOOKUP_DEF,FRANGE_DEF]
  \\ metis_tac []
QED

Theorem mk_seqs_subst:
  ∀vs m e.
    DISJOINT (set (MAP FST vs)) (FDOM m) ⇒
    mk_seqs vs (subst m e) = subst m (mk_seqs vs e)
Proof
  Induct \\ fs [mk_seqs_def]
  \\ PairCases \\ fs [mk_seqs_def]
  \\ Cases_on ‘h1’ \\ fs [mk_seqs_def]
  \\ fs [subst_def,FLOOKUP_DEF]
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
  >-
   (simp [subset_funs_mk_bind,subset_funs_mk_seq_bind]
    \\ DEP_REWRITE_TAC [mk_seqs_subst]
    \\ DEP_REWRITE_TAC [pure_exp_lemmasTheory.subst_subst_FUNION]
    \\ DEP_REWRITE_TAC [freevars_subst]
    \\ fs [FDOM_FUPDATE_LIST]
    \\ drule_at Any freevars_mk_seqs \\ strip_tac
    \\ drule mk_bind_closed
    \\ drule mk_seq_bind_closed
    \\ fs [SF SFY_ss]
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,mk_bind_def,mk_seq_bind_def]
    \\ fs [FRANGE_FLOOKUP,PULL_EXISTS,FLOOKUP_FUNION,AllCaseEqs()]
    \\ fs [SF SFY_ss, SF DNF_ss]
    \\ rw []
    \\ imp_res_tac FEVERY_FLOOKUP
    \\ fs []
    \\ fs [obligation_def,IN_DISJOINT,EVERY_MEM]
    \\ res_tac \\ fs []
    \\ fs [SUBSET_DEF,EXTENSION,MEM_MAP,EXISTS_PROD,FORALL_PROD,MEM_FILTER])
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
  >-
   (simp [subst_def]
    \\ DEP_REWRITE_TAC [pure_exp_lemmasTheory.subst_subst_FUNION]
    \\ conj_tac >- fs [FRANGE_DEF,FEVERY_DEF,PULL_EXISTS]
    \\ irule letrec_seq_seq
    \\ last_x_assum $ irule_at Any
    \\ fs [FEVERY_DEF,FUNION_DEF,FLOOKUP_DEF]
    \\ rw [])
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
    \\ disj2_tac
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
    \\ rw [] \\ res_tac \\ fs [])
QED

Theorem letrec_seq_subst1:
  letrec_seq binds a1 a2 ∧ letrec_seq binds z y ∧ closed a1 ∧ closed a2 ⇒
  letrec_seq binds (subst1 v a1 z) (subst1 v a2 y)
Proof
  strip_tac
  \\ irule subst_letrec_seq
  \\ fs [FLOOKUP_DEF]
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
  \\ first_assum mp_tac
  \\ simp_tac std_ss [obligation_def] \\ strip_tac
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
  simp [subset_funs_mk_bind,subset_funs_mk_seq_bind]
  \\ strip_tac
  \\ irule subst_letrec_seq \\ fs []
  \\ conj_tac >- (rw [] \\ imp_res_tac FEVERY_FLOOKUP \\ fs [] \\ res_tac)
  \\ irule subst_letrec_seq \\ fs []
  \\ fs [letrec_seq_refl]
  \\ reverse conj_tac
  >- fs [FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss,
         LAMBDA_PROD,mk_bind_def,mk_seq_bind_def]
  \\ reverse (rpt strip_tac)
  >- (drule mk_seq_bind_closed \\ disch_then irule
      \\ fs [FRANGE_FLOOKUP] \\ first_x_assum $ irule_at Any)
  >- (drule mk_bind_closed \\ disch_then irule
      \\ fs [FRANGE_FLOOKUP] \\ first_x_assum $ irule_at Any)
  \\ fs [FDOM_UPDATES_EQ,PULL_EXISTS,alistTheory.flookup_fupdate_list]
  \\ fs [FORALL_FRANGE,alistTheory.flookup_fupdate_list,AllCaseEqs()]
  \\ simp [Once letrec_seq_cases]
  \\ disj1_tac
  \\ fs [EXISTS_PROD]
  \\ fs [FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss,
         LAMBDA_PROD,mk_bind_def,mk_seq_bind_def]
  \\ qabbrev_tac ‘xs = MAP mk_bind binds’ \\ pop_assum kall_tac
  \\ qabbrev_tac ‘ys = MAP mk_seq_bind binds’ \\ pop_assum kall_tac
  \\ pop_assum mp_tac \\ pop_assum mp_tac
  \\ rpt $ pop_assum kall_tac
  \\ qid_spec_tac ‘k’
  \\ qid_spec_tac ‘v1’
  \\ qid_spec_tac ‘v2’
  \\ qid_spec_tac ‘binds’
  \\ Induct \\ fs [FORALL_PROD]
  \\ fs [ALOOKUP_APPEND,AllCaseEqs(),ALOOKUP_NONE,MAP_REVERSE]
  \\ fs [MEM_MAP,FORALL_PROD]
  \\ rw []
  >- metis_tac []
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [MEM_MAP,EXISTS_PROD] \\ gvs []
  \\ res_tac \\ fs []
  \\ metis_tac []
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
  rw [subset_funs_mk_bind,subset_funs_mk_seq_bind]
  \\ fs [freevars_mk_seqs']
  \\ DEP_REWRITE_TAC [freevars_subst]
  \\ fs [FDOM_FUPDATE_LIST]
  \\ drule mk_bind_closed
  \\ drule mk_seq_bind_closed
  \\ simp [SF SFY_ss] \\ strip_tac \\ strip_tac
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,mk_bind_def,mk_seq_bind_def]
  \\ fs [obligation_def,EVERY_MEM]
  \\ res_tac
  \\ fs [SUBSET_DEF,MEM_FILTER,MEM_MAP,EXISTS_PROD,FORALL_PROD,IN_DISJOINT]
  \\ metis_tac []
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
         \\ drule_all LIST_REL_MEM_ALT \\ rw []
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
      \\ drule_all LIST_REL_MEM_ALT \\ rw []
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
      \\ drule_all LIST_REL_MEM_ALT \\ strip_tac
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

Theorem eval_wh_mk_seqs_skip:
  ∀vs ee k.
    eval_wh_to k (subst m2 (mk_seqs vs ee)) ≠ wh_Error ∧
    eval_wh_to k (subst m2 (mk_seqs vs ee)) ≠ wh_Diverge ⇒
    ∃k1. eval_wh_to k (subst m2 (mk_seqs vs ee)) =
         eval_wh_to k1 (subst m2 ee) ∧ k1 ≤ k
Proof
  Induct \\ fs [mk_seqs_def]
  >- (rw [] \\ qexists_tac ‘k’ \\ fs [])
  \\ fs [FORALL_PROD] \\ gen_tac \\ Cases \\ rw []
  \\ fs [mk_seqs_def,subst_def]
  \\ fs [eval_wh_to_def]
  \\ Cases_on ‘k = 0’ \\ fs []
  \\ IF_CASES_TAC \\ fs [] \\ gvs []
  \\ FULL_CASE_TAC \\ fs [eval_wh_to_def]
  \\ rpt strip_tac
  \\ first_x_assum drule_all \\ rw [] \\ fs []
  \\ qexists_tac ‘k1’ \\ fs []
QED

Theorem eval_forward_letrec_seq_rev:
  obligation binds ⇒
  eval_forward F (λx y. letrec_seq binds y x)
Proof
  strip_tac
  \\ simp [eval_forward_def]
  \\ completeInduct_on ‘k’ \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ completeInduct_on ‘exp_size x’ \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ rpt gen_tac
  \\ strip_tac \\ gvs []
  \\ Cases_on ‘x’ \\ gvs []
  >~ [‘Lam v z’] >-
   (fs [eval_wh_to_def]
    \\ qpat_x_assum ‘letrec_seq _ _ _’ mp_tac
    \\ simp [Once letrec_seq_cases] \\ strip_tac \\ gvs []
    \\ ‘eval_wh (Lam v x) = wh_Closure v x’ by fs [eval_wh_Lam]
    \\ drule_all eval_wh_Closure_bisim
    \\ strip_tac \\ fs []
    \\ qexists_tac ‘m’
    \\ qexists_tac ‘y1’ \\ fs []
    \\ rw [] \\ first_x_assum drule
    \\ disch_then $ irule_at Any
    \\ irule_at Any letrec_seq_subst1
    \\ fs [])
  >~ [‘App e1 e2y’] >-
   (fs [eval_wh_to_def]
    \\ qpat_x_assum ‘letrec_seq _ _ _’ mp_tac
    \\ simp [Once letrec_seq_cases] \\ rpt strip_tac \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k e1)’ \\ fs []
    \\ PairCases_on ‘x'’ \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘eval_wh_to k e1’ \\ gvs [dest_wh_Closure_def]
    \\ first_x_assum $ qspecl_then [‘e1’] mp_tac
    \\ simp [exp_size_def]
    \\ imp_res_tac letrec_seq_freevars
    \\ ‘(f ≃ f) F ∧ closed f’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule_all
    \\ strip_tac \\ fs [GSYM PULL_FORALL]
    \\ rename [‘eval_wh f = wh_Closure v1 e1’]
    \\ first_x_assum $ qspec_then ‘e2y’ mp_tac
    \\ imp_res_tac letrec_seq_freevars
    \\ ‘closed x’ by fs [closed_def]
    \\ disch_then drule_all \\ strip_tac \\ gvs []
    \\ fs [bind_def,FLOOKUP_DEF]
    \\ first_x_assum $ drule_at $ Pos $ el 2
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
         \\ drule_all LIST_REL_MEM \\ rw []
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
      \\ ‘MAP FST bs = MAP FST ys’ by fs []
      \\ drule_all ALOOKUP_REVERSE_LIST_REL
      \\ pop_assum kall_tac
      \\ strip_tac \\ gvs []
      >- (simp [Once letrec_seq_cases] \\ disj2_tac \\ fs [])
      \\ res_tac \\ fs []
      \\ imp_res_tac letrec_seq_freevars \\ fs [])
    \\ rw [eval_wh_to_def] \\ gvs []
    \\ first_x_assum irule \\ fs []
    \\ conj_tac >-
     (fs [subset_funs_mk_seq_bind,closed_def]
      \\ DEP_REWRITE_TAC [freevars_subst]
      \\ conj_tac
      >- (drule mk_seq_bind_closed \\ fs [SF SFY_ss])
      \\ fs [EXTENSION]
      \\ fs [SUBSET_DEF,FDOM_FUPDATE_LIST,MAP_MAP_o,
             combinTheory.o_DEF,UNCURRY,SF ETA_ss]
      \\ fs [LAMBDA_PROD,mk_seq_bind_def,mk_bind_def]
      \\ CCONTR_TAC \\ fs [] \\ res_tac \\ fs [])
    \\ irule_at Any letrec_seq_subst_funs \\ simp []
    \\ irule_at Any app_bisimilarity_trans
    \\ last_x_assum $ irule_at Any
    \\ irule eval_IMP_app_bisimilarity
    \\ fs [eval_Letrec]
    \\ fs [subst_funs_def,bind_def]
    \\ drule mk_bind_closed \\ fs [SF SFY_ss]
    \\ fs [FRANGE_FLOOKUP,PULL_EXISTS,SF SFY_ss]
    \\ rpt $ irule_at Any IMP_closed_subst
    \\ strip_tac
    \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
    \\ drule mk_bind_closed \\ fs [SF SFY_ss]
    \\ strip_tac
    \\ rpt $ irule_at Any IMP_closed_subst
    \\ fs [FDOM_UPDATES_EQ,PULL_EXISTS,alistTheory.flookup_fupdate_list]
    \\ fs [FORALL_FRANGE,alistTheory.flookup_fupdate_list,AllCaseEqs()])
  >~ [‘letrec_seq _ _ (Prim p xs)’]
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
      \\ qsuff_tac ‘eval_wh x ≠ wh_Error ∧ eval_wh x ≠ wh_Diverge’
      \\ fs []
      \\ last_x_assum $ drule_at $ Pos $ el 2
      \\ disch_then $ qspec_then ‘k-1’ mp_tac \\ fs []
      \\ ‘(x ≃ x) F ∧ closed x’ by
        (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
         \\ fs [closed_def])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ Cases_on ‘eval_wh_to (k − 1) h’ \\ fs [])
    \\ fs [SF DNF_ss]
    \\ simp [eval_wh_to_def]
    \\ Cases_on ‘k = 0’ \\ gvs []
    \\ qabbrev_tac ‘ee = (subst_funs (MAP mk_seq_bind binds) e)’
    \\ Cases_on ‘eval_wh_to (k − 1) (subst m2 (mk_seqs vs ee)) = wh_Error ∨
                 eval_wh_to (k − 1) (subst m2 (mk_seqs vs ee)) = wh_Diverge’
    >- fs [] \\ fs []
    \\ drule_all eval_wh_mk_seqs_skip
    \\ strip_tac \\ fs []
    \\ fs [Abbr‘ee’]
    \\ last_x_assum irule \\ fs []
    \\ fs [PULL_EXISTS]
    \\ irule_at Any app_bisimilarity_trans
    \\ qpat_assum ‘(_ ≃ e2) F’ $ irule_at $ Pos $ el 2
    \\ irule_at Any IMP_Seq_Zero
    \\ irule_at Any reflexive_app_bisimilarity
    \\ irule_at Any letrec_seq_subst_funs_mk_bind \\ fs []
    \\ conj_tac >- fs [SF SFY_ss]
    \\ ‘∀n v. FLOOKUP m1 n = SOME v ⇒ closed v’ by fs [FEVERY_DEF,FLOOKUP_DEF]
    \\ ‘∀n v. FLOOKUP m2 n = SOME v ⇒ closed v’ by fs [FEVERY_DEF,FLOOKUP_DEF]
    \\ fs [closed_def]
    \\ DEP_REWRITE_TAC [freevars_subst]
    \\ fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS,closed_def,freevars_subst,freevars_mk_seqs']
    \\ gvs [subset_funs_mk_bind,subset_funs_mk_seq_bind]
    \\ qpat_x_assum ‘(set _ ∪ _) DIFF _ = {}’ mp_tac
    \\ DEP_REWRITE_TAC [freevars_subst]
    \\ drule mk_bind_closed
    \\ drule mk_seq_bind_closed \\ fs []
    \\ fs [FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
    \\ fs [LAMBDA_PROD,mk_bind_def,mk_seq_bind_def]
    \\ fs [EXTENSION]
    \\ metis_tac [])
  \\ simp [Once letrec_seq_cases] \\ rw []
  \\ Cases_on ‘p’ \\ fs []
  >~ [‘Cons s xs’] >-
   (rw [eval_wh_to_def]
    \\ ‘eval_wh (Cons s xs') = wh_Constructor s xs'’ by fs [eval_wh_Cons]
    \\ drule_all eval_wh_Constructor_bisim \\ strip_tac \\ fs []
    \\ pop_assum mp_tac
    \\ simp [Once LIST_REL_SWAP] \\ rpt strip_tac
    \\ drule_then drule LIST_REL_COMP
    \\ simp [Once LIST_REL_SWAP]
    \\ match_mp_tac LIST_REL_mono \\ fs []
    \\ metis_tac [])
  >~ [‘If’] >-
   (gvs [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ fs [SF DNF_ss]
    \\ reverse (Cases_on ‘∃s. eval_wh_to (k − 1) h = wh_Constructor s []’ \\ fs [])
    >- (Cases_on ‘eval_wh_to (k − 1) h’ \\ gvs [] \\ rw [])
    \\ qpat_x_assum ‘letrec_seq _ y h’ assume_tac
    \\ last_assum $ drule_at $ Pos $ el 2
    \\ imp_res_tac letrec_seq_freevars
    \\ ‘(x ≃ x) F ∧ closed x’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then $ qspec_then ‘k-1’ mp_tac \\ fs []
    \\ disch_then $ drule \\ fs [] \\ strip_tac
    \\ reverse (rw []) \\ fs []
    \\ rename [‘eval_wh_to (k − 1) h2’]
    \\ qpat_x_assum ‘letrec_seq _ _ h2’ assume_tac
    \\ last_x_assum $ drule_at $ Pos $ el 2
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
    \\ last_assum $ drule_at $ Pos $ el 2
    \\ imp_res_tac letrec_seq_freevars
    \\ ‘(x ≃ x) F ∧ closed x’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then $ drule_at $ Pos $ el 2 \\ fs [] \\ strip_tac
    \\ pop_assum $ qspec_then ‘k-1’ assume_tac \\ gvs []
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
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ fs []
    \\ disch_then $ qspec_then ‘k-1’ mp_tac \\ fs []
    \\ imp_res_tac letrec_seq_freevars
    \\ ‘(x ≃ x) F ∧ closed x’ by
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
    \\ qsuff_tac ‘get_atoms (MAP eval_wh xs') = SOME (SOME atoms)’
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
      \\ drule_all LIST_REL_MEM \\ rw []
      \\ last_x_assum $ drule_at $ Pos $ el 2
      \\ disch_then $ qspec_then ‘k-1’ mp_tac \\ fs []
      \\ res_tac
      \\ imp_res_tac letrec_seq_freevars
      \\ ‘(y ≃ y) F ∧ closed y’ by
        (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
         \\ fs [closed_def])
      \\ disch_then drule_all
      \\ rw [] \\ fs [PULL_EXISTS]
      \\ first_x_assum drule \\ strip_tac
      \\ Cases_on ‘eval_wh_to (k − 1) y'’ \\ fs []
      \\ res_tac \\ fs [])
    >-
     (CCONTR_TAC \\ fs []
      \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
      \\ drule_all LIST_REL_MEM \\ strip_tac
      \\ ‘closed y' ∧ ¬error_Atom (eval_wh_to (k − 1) y')’ by (res_tac \\ fs [])
      \\ ‘eval_wh_to (k − 1) y' ≠ wh_Diverge’ by (CCONTR_TAC \\ fs [] \\ res_tac \\ fs [])
      \\ last_x_assum $ drule_at $ Pos $ el 2
      \\ disch_then $ qspec_then ‘k-1’ mp_tac
      \\ imp_res_tac letrec_seq_freevars
      \\ ‘(y ≃ y) F ∧ closed y ∧ closed y'’ by
        (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
         \\ fs [closed_def,EVERY_MEM] \\ res_tac \\ fs [])
      \\ disch_then $ drule_at $ Pos $ el 2 \\ fs []
      \\ Cases_on ‘eval_wh_to (k − 1) y'’ \\ fs [])
    \\ AP_TERM_TAC
    \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ match_mp_tac (GSYM LIST_REL_IMP_MAP_EQ)
    \\ rw []
    \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
    \\ ‘closed y ∧ ¬error_Atom (eval_wh_to (k − 1) y)’ by (res_tac \\ fs [])
    \\ ‘eval_wh_to (k − 1) y ≠ wh_Diverge’ by (CCONTR_TAC \\ fs [] \\ res_tac \\ fs [])
    \\ last_x_assum $ drule_at $ Pos $ el 2
    \\ disch_then $ qspec_then ‘k-1’ mp_tac
    \\ imp_res_tac letrec_seq_freevars
    \\ ‘(x ≃ x) F ∧ closed y ∧ closed x’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def,EVERY_MEM] \\ res_tac \\ fs [])
    \\ simp []
    \\ disch_then drule \\ fs []
    \\ Cases_on ‘eval_wh_to (k − 1) y’ \\ fs [])
QED

Theorem Letrec_mk_seq_bind_lemma:
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

Theorem Letrec_mk_seq_bind:
  MEM b binds ∧ obligation binds ⇒
  (Letrec (MAP mk_bind binds) (SND (mk_bind b)) ≈
   Letrec (MAP mk_seq_bind binds) (SND (mk_seq_bind b)))
Proof
  PairCases_on ‘b’
  \\ fs [exp_eq_def]
  \\ rw [bind_def] \\ rw []
  \\ DEP_REWRITE_TAC [closed_subst]
  \\ irule_at Any Letrec_mk_seq_bind_lemma
  \\ fs []
  \\ drule_at (Pos last) freevars_mk_seqs
  \\ strip_tac
  \\ fs [obligation_def,EVERY_MEM]
  \\ res_tac \\ fs [MAP_FST_mk_bind]
  \\ fs [mk_bind_def,SUBSET_DEF,SF SFY_ss]
  \\ fs [MEM_MAP,FORALL_PROD,PULL_EXISTS,mk_bind_def]
  \\ fs [MEM_MAP,FORALL_PROD,PULL_EXISTS,mk_bind_def,MEM_FILTER,EXISTS_PROD]
  \\ metis_tac []
QED

Triviality FLOOKUP_FLOOKUP_IMP_LIST_REL:
  EVERY (λb. FST (f b) = FST (g b) ∧ P (SND (f b)) (SND (g b))) binds ⇒
  (∀k v1 v2.
     FLOOKUP (FEMPTY |++ MAP f binds) k = SOME v1 ∧
     FLOOKUP (FEMPTY |++ MAP g binds) k = SOME v2 ⇒
     P v1 v2)
Proof
  Induct_on ‘binds’ using SNOC_INDUCT
  \\ fs [FUPDATE_LIST]
  \\ fs [EVERY_SNOC,MAP_SNOC,FOLDL_SNOC] \\ rw []
  \\ Cases_on ‘f x’
  \\ Cases_on ‘g x’
  \\ fs [FLOOKUP_UPDATE] \\ gvs []
  \\ Cases_on ‘q = k’ \\ gvs []
  \\ res_tac \\ fs []
QED

Theorem Letrec_mk_seq_bind_same:
  obligation binds ⇒
  (Letrec (MAP mk_bind binds) x ≈
   Letrec (MAP mk_seq_bind binds) x)
Proof
  strip_tac
  \\ irule_at Any exp_eq_trans
  \\ irule_at Any (beta_equality_Letrec |> GEN_ALL |> Q.SPEC ‘F’)
  \\ simp [Once exp_eq_sym]
  \\ irule_at Any exp_eq_trans
  \\ irule_at Any (beta_equality_Letrec |> GEN_ALL |> Q.SPEC ‘F’)
  \\ fs [AC CONJ_ASSOC CONJ_COMM,MAP_FST_mk_bind]
  \\ reverse conj_tac
  >-
   (fs [obligation_def,EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS]
    \\ fs [mk_bind_def] \\ rw [] \\ res_tac
    \\ fs [SUBSET_DEF] \\ metis_tac [])
  \\ fs [subset_funs_mk_bind,subset_funs_mk_seq_bind]
  \\ irule exp_eq_subst_all
  \\ fs [FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
  \\ fs [LAMBDA_PROD,mk_bind_def,mk_seq_bind_def]
  \\ ho_match_mp_tac FLOOKUP_FLOOKUP_IMP_LIST_REL
  \\ fs [EVERY_MEM,FORALL_PROD]
  \\ rpt gen_tac \\ strip_tac
  \\ drule_all Letrec_mk_seq_bind
  \\ fs [mk_bind_def,mk_seq_bind_def]
  \\ simp [Once exp_eq_sym]
  \\ strip_tac
  \\ fs [MEM_MAP,PULL_EXISTS,FORALL_PROD]
  \\ fs [freevars_mk_seqs, SF SFY_ss, MAP_FST_mk_bind]
  \\ pop_assum kall_tac
  \\ fs [mk_bind_def]
  \\ fs [obligation_def,SUBSET_DEF,EVERY_MEM]
  \\ res_tac \\ fs []
  \\ fs [MEM_MAP,PULL_EXISTS,FORALL_PROD,MEM_FILTER,EXISTS_PROD]
  \\ metis_tac []
QED

Triviality Seq_Zero:
  ∀x y. x ≈ y ⇒ Seq Zero x ≈ y
Proof
  rw [] \\ irule exp_eq_trans
  \\ pop_assum $ irule_at Any
  \\ irule eval_wh_IMP_exp_eq
  \\ fs [subst_def,eval_wh_Seq] \\ rw [] \\ fs []
  \\ fs [eval_wh_Prim,get_atoms_def]
QED

Inductive reformulate:
[~full:]
  (∀(binds:bind list) f es seqs bs.
    ALOOKUP binds f = SOME (bs,body) ∧ LENGTH bs = LENGTH es ∧
    seqs = MAP SND (FILTER (SND o FST) (ZIP (bs,es))) ⇒
    reformulate binds
      (Apps (Var f) es)
      (Seqs seqs (Apps (Var f) es)))
  ∧
[~partial:]
  (∀binds f bs body.
    ALOOKUP binds f = SOME (bs,body) ⇒
    reformulate binds
      (Var f)
      (SND (mk_seq_lams (f,bs,Apps (Var f) (MAP (Var o FST) bs)))))
  ∧
  (* cases below are just recursion *)
[~Var:]
  (∀binds n.
     reformulate binds (Var n) (Var n)) ∧
[~Lam:]
  (∀binds n x y.
    reformulate (FILTER (λ(m,x). m ≠ n) binds) x y ⇒
    reformulate binds (Lam n x) (Lam n y)) ∧
[~App:]
  (∀binds f g x y.
    reformulate binds f g ∧ reformulate binds x y ⇒
    reformulate binds (App f x) (App g y)) ∧
[~Prim:]
  (∀binds n xs ys.
    LIST_REL (reformulate binds) xs ys ⇒
    reformulate binds (Prim n xs) (Prim n ys)) ∧
[~Letrec:]
  (∀binds bs xs ys x y.
    bs = FILTER (λ(m,x). ~MEM m (MAP FST xs)) binds ∧
    LIST_REL (reformulate bs) (MAP SND xs) (MAP SND ys) ∧
    MAP FST xs = MAP FST ys ∧ reformulate bs x y ⇒
    reformulate binds (Letrec xs x) (Letrec ys y))
End

Theorem reformulate_refl:
  ∀e binds. reformulate binds e e
Proof
  Induct using freevars_ind
  >- irule reformulate_Var
  >- (gen_tac \\ irule reformulate_Prim
      \\ gvs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN])
  >- (gen_tac \\ irule reformulate_App
      \\ gs [])
  >- (gen_tac \\ irule reformulate_Lam
      \\ gs [])
  >- (gen_tac \\ irule reformulate_Letrec
      \\ gs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN, EL_MAP]
      \\ rw []
      \\ last_x_assum $ dxrule_then assume_tac
      \\ first_x_assum irule
      \\ irule_at Any PAIR)
QED

Theorem reformulate_filtered_bind:
  ∀binds f e1 e2.
    reformulate (FILTER (λ(v, _). f v) binds) e1 e2  ⇒
    reformulate binds e1 e2
Proof
  Induct_on ‘reformulate’ \\ rw []
  >- (gs [ALOOKUP_FILTER]
      \\ irule reformulate_full
      \\ metis_tac [])
  >- (gs [ALOOKUP_FILTER]
      \\ irule reformulate_partial
      \\ metis_tac [])
  >- simp [reformulate_Var]
  >- (irule reformulate_Lam
      \\ first_x_assum irule
      \\ simp [FILTER_FILTER, CONJ_COMM]
      \\ irule_at Any EQ_REFL)
  >- (irule_at Any reformulate_App
      \\ rpt $ first_x_assum $ irule_at Any
      \\ rpt $ irule_at Any EQ_REFL)
  >- (irule_at Any reformulate_Prim
      \\ gs [LIST_REL_EL_EQN] \\ rw []
      \\ first_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ irule_at Any EQ_REFL)
  >- (irule_at Any reformulate_Letrec
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ simp [FILTER_FILTER, CONJ_COMM]
      \\ irule_at Any EQ_REFL
      \\ gs [LIST_REL_EL_EQN] \\ rw []
      \\ first_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ first_x_assum $ irule_at Any
      \\ simp [FILTER_FILTER, CONJ_COMM]
      \\ irule_at Any EQ_REFL)
QED

Triviality FDIFF_LIST_FUPDATE:
  FDIFF (FEMPTY |++ ys) P = FEMPTY |++ (FILTER (λ(x,y). ~P x) ys)
Proof
  fs [fmap_eq_flookup,FLOOKUP_FDIFF,GSYM FILTER_REVERSE,
      alistTheory.flookup_fupdate_list,ALOOKUP_FILTER]
  \\ rw [] \\ fs [IN_DEF]
QED

Triviality subst_mk_seqs:
  ∀args m.
    DISJOINT (FDOM m) (set (MAP FST args)) ⇒
    subst m (mk_seqs args e) = mk_seqs args (subst m e)
Proof
  Induct \\ fs [mk_seqs_def]
  \\ PairCases \\ Cases_on ‘h1’ \\ fs [mk_seqs_def,subst_def]
  \\ fs [FLOOKUP_DEF]
QED

Theorem subst_Lams_mk_seqs_lemma[local]:
  ~MEM f (MAP FST args) ⇒
  subst m (Lams (MAP FST args) (mk_seqs args (Apps (Var f) (MAP (Var ∘ FST) args)))) =
  Lams (MAP FST args) (mk_seqs args (Apps (subst m (Var f)) (MAP (Var ∘ FST) args)))
Proof
  strip_tac
  \\ fs [subst_Lams]
  \\ DEP_REWRITE_TAC [subst_mk_seqs]
  \\ fs [subst_Apps]
  \\ fs [subst_def,FLOOKUP_FDIFF]
  \\ fs [IN_DISJOINT]
  \\ conj_tac >- metis_tac []
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ fs [MAP_MAP_o,MAP_EQ_f]
  \\ fs [FORALL_PROD]
  \\ fs [subst_def,FLOOKUP_FDIFF,MEM_MAP,EXISTS_PROD,AllCaseEqs()]
  \\ metis_tac []
QED

Triviality Apps_cong1:
  ∀xs f g. f ≈ g ⇒ Apps f xs ≈ Apps g xs
Proof
  Induct \\ fs [Apps_def]
  \\ rw [] \\ gvs []
  \\ first_x_assum irule
  \\ irule exp_eq_App_cong \\ fs [exp_eq_refl]
QED

Theorem Letrec_mk_seqs_swap:
  DISJOINT (set (MAP FST vs)) (set (MAP FST xs)) ∧
  EVERY (λ(v,x). freevars x SUBSET set (MAP FST xs)) xs ⇒
  Letrec xs (mk_seqs vs x) ≈ mk_seqs vs (Letrec xs x)
Proof
  Induct_on ‘vs’ \\ fs [mk_seqs_def,exp_eq_refl]
  \\ PairCases \\ Cases_on ‘h1’ \\ fs [mk_seqs_def]
  \\ rw [] \\ fs []
  \\ irule_at Any exp_eq_trans
  \\ irule_at Any Letrec_Prim \\ fs []
  \\ irule exp_eq_Prim_cong \\ fs []
  \\ irule_at Any exp_eq_trans
  \\ irule_at Any beta_equality_Letrec_alt
  \\ fs [boundvars_def,subst_def]
  \\ CASE_TAC \\ fs [exp_eq_refl]
  \\ fs [FLOOKUP_DEF,FDOM_FUPDATE_LIST]
  \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS]
QED

Theorem mk_seqs_APPEND:
  ∀xs ys e. mk_seqs (xs ++ ys) e = mk_seqs xs (mk_seqs ys e)
Proof
  Induct \\ fs [mk_seqs_def]
  \\ PairCases \\ Cases_on ‘h1’ \\ fs [mk_seqs_def]
QED

Triviality mk_seqs_cong:
  ∀args x y. x ≈ y ⇒ mk_seqs args x ≈ mk_seqs args y
Proof
  Induct
  \\ fs [mk_seqs_def,FORALL_PROD]
  \\ gen_tac \\ Cases \\ fs [mk_seqs_def] \\ rw []
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
QED

Theorem Seq_commute[local]:
  Seq x (Seq y z) ≈ Seq y (Seq x z)
Proof
  irule no_err_eval_wh_IMP_exp_eq
  \\ rw [subst_def, no_err_eval_wh_def, eval_wh_Seq]
  \\ fs []
  \\ Cases_on ‘eval_wh (subst f x)’
  \\ Cases_on ‘eval_wh (subst f y)’
  \\ fs []
QED

Theorem Seq_idem[local]:
  Seq x (Seq x y) ≈ Seq x y
Proof
  irule no_err_eval_wh_IMP_exp_eq
  \\ rw [subst_def, no_err_eval_wh_def, eval_wh_Seq]
QED

Theorem mk_seqs_mk_seqs:
  ∀xs ys.
    set xs SUBSET set ys ⇒
    mk_seqs xs (mk_seqs ys body) ≈ mk_seqs ys body
Proof
  Induct using SNOC_INDUCT \\ fs [mk_seqs_def,exp_eq_refl]
  \\ PairCases \\ Cases_on ‘x1’ \\ fs [mk_seqs_def,exp_eq_refl]
  \\ fs [mk_seqs_APPEND,SNOC_APPEND,mk_seqs_def]
  \\ rw [] \\ res_tac
  \\ irule_at Any exp_eq_trans
  \\ pop_assum $ irule_at Any
  \\ irule_at Any mk_seqs_cong
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘ys’ \\ Induct \\ fs []
  \\ rw [] \\ fs [mk_seqs_def]
  >- irule_at Any Seq_idem
  \\ PairCases_on ‘h’ \\ Cases_on ‘h1’ \\ fs [mk_seqs_def]
  \\ irule_at Any exp_eq_trans
  \\ irule_at Any Seq_commute
  \\ irule_at Any exp_eq_Prim_cong \\ fs [exp_eq_refl]
QED

Theorem ETA_lemma[local]:
  obl_syntax binds ∧ MEM (f,args,body) binds ⇒
  Letrec (MAP mk_seq_bind binds)
    (Lams (MAP FST args) (Seq Zero (mk_seqs args body))) ≈
  Lams (MAP FST args)
    (mk_seqs args
      (Apps
        (Letrec (MAP mk_seq_bind binds)
           (Lams (MAP FST args) (Seq Zero (mk_seqs args body))))
        (MAP (Var ∘ FST) args)))
Proof
  rpt strip_tac
  \\ simp [Once exp_eq_sym]
  \\ irule_at Any exp_eq_trans
  \\ irule_at Any Lams_cong
  \\ irule_at Any mk_seqs_cong
  \\ irule_at Any Apps_cong1
  \\ irule_at Any Letrec_Lams_swap
  \\ conj_asm1_tac
  >-
   (fs [obl_syntax_def,EVERY_MEM] \\ res_tac \\ fs [MAP_FST_mk_bind])
  \\ conj_asm1_tac
  >-
   (fs [obl_syntax_def,EVERY_MEM] \\ res_tac \\ fs [MAP_FST_mk_bind]
    \\ fs [MEM_MAP,PULL_EXISTS,FORALL_PROD]
    \\ rw [] \\ res_tac \\ fs [mk_seq_bind_def,freevars_mk_seqs_lemma]
    \\ fs [SUBSET_DEF] \\ metis_tac [])
  \\ irule_at Any exp_eq_trans
  \\ irule_at Any Lams_cong
  \\ irule_at Any mk_seqs_cong
  \\ fs [GSYM MAP_MAP_o]
  \\ irule_at Any exp_eq_Apps_Lams
  \\ irule_at Any exp_eq_trans
  \\ irule_at Any Lams_cong
  \\ simp [Once exp_eq_sym]
  \\ irule_at Any Letrec_mk_seqs_swap
  \\ simp []
  \\ irule_at Any exp_eq_trans
  \\ simp [Once exp_eq_sym]
  \\ irule_at Any Letrec_Lams_swap
  \\ simp []
  \\ irule_at Any exp_eq_Letrec_cong1
  \\ irule_at Any Lams_cong
  \\ simp [Once exp_eq_sym]
  \\ irule Seq_Zero
  \\ simp [Once exp_eq_sym]
  \\ irule_at Any exp_eq_trans
  \\ irule_at Any mk_seqs_cong
  \\ irule_at Any Seq_Zero
  \\ irule_at Any exp_eq_refl
  \\ irule mk_seqs_mk_seqs
  \\ fs []
QED

Triviality ALOOKUP_IMP_FLOOKUP:
  ALOOKUP bs f = SOME (args,body) ∧ obl_syntax binds ∧
  set bs ⊆ set binds ⇒
  FLOOKUP (FEMPTY |++
            MAP (λ(g,x). (g,Letrec (MAP mk_seq_bind binds) x))
            (MAP mk_seq_bind bs)) f =
  SOME (Letrec (MAP mk_seq_bind binds) (SND (mk_seq_bind (f,args,body))))
Proof
  fs [subst_def,alistTheory.flookup_fupdate_list,AllCaseEqs()]
  \\ Induct_on ‘bs’ \\ fs []
  \\ PairCases \\ fs []
  \\ fs [ALOOKUP_APPEND]
  \\ fs [AllCaseEqs(),mk_seq_bind_def]
  \\ reverse (Cases_on ‘h0 = f’) >- fs []
  \\ fs []
  \\ rw [] \\ fs []
  \\ fs [ALOOKUP_NONE,MAP_REVERSE,MEM_MAP,FORALL_PROD,mk_seq_bind_def]
  \\ CCONTR_TAC \\ fs []
  \\ fs [SUBSET_DEF]
  \\ Cases_on ‘ALOOKUP
          (REVERSE
             (MAP (λ(g,x). (g,Letrec (MAP mk_seq_bind binds) x))
                (MAP mk_seq_bind bs))) f’
  >- fs [ALOOKUP_NONE,MEM_MAP,EXISTS_PROD,mk_seq_bind_def]
  \\ fs [] \\ imp_res_tac ALOOKUP_MEM
  \\ fs [MEM_MAP,PULL_EXISTS,EXISTS_PROD]
  \\ gvs [mk_seq_bind_def]
  \\ rename [‘MEM (f,args1,body1) bs’]
  \\ fs [obl_syntax_def]
  \\ qsuff_tac ‘(args,body) = (args1,body1)’
  >- (strip_tac \\ fs [])
  \\ drule_then irule ALL_DISTINCT_MEM_MEM
  \\ qexists_tac ‘f’ \\ fs []
QED

Triviality mk_seqs_eq_Seqs:
  ∀args e. mk_seqs args e = Seqs (MAP (Var o FST) (FILTER SND args)) e
Proof
  Induct \\ fs [mk_seqs_def]
  \\ PairCases \\ Cases_on ‘h1’ \\ fs [mk_seqs_def]
QED

Theorem Apps_Lams_eq_Seqs[local]:
  closed ll ∧ LENGTH vals = LENGTH args ∧ ALL_DISTINCT (MAP FST args) ⇒
  Apps
    (Lams (MAP FST args)
       (mk_seqs args (Apps ll (MAP (Var ∘ FST) args)))) vals ≈
  Seqs (MAP SND (FILTER (SND ∘ FST) (ZIP (args,vals)))) (Apps ll vals)
Proof
  rw [] \\ irule eval_wh_IMP_exp_eq \\ rw []
  \\ fs [subst_Apps,subst_Seqs]
  \\ DEP_REWRITE_TAC [closed_subst]
  \\ conj_tac >-
   (fs [closed_Lams,freevars_mk_seqs',closed_def]
    \\ fs [SUBSET_DEF,MEM_MAP,PULL_EXISTS,MEM_FILTER,FORALL_PROD,EXISTS_PROD]
    \\ metis_tac [])
  \\ DEP_REWRITE_TAC [eval_wh_Apps_Lams]
  \\ fs []
  \\ conj_tac >-
   (fs [EVERY_MAP,SUBSET_DEF,EVERY_MEM,PULL_EXISTS,MEM_MAP,closed_def]
    \\ gen_tac \\ DEP_REWRITE_TAC [freevars_subst]
    \\ fs [EXTENSION,closed_def,FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS]
    \\ metis_tac [])
  \\ AP_TERM_TAC
  \\ fs [mk_seqs_eq_Seqs,subst_Seqs,subst_Apps]
  \\ match_mp_tac (METIS_PROVE [] “x1 = x2 ∧ y1 = y2 ⇒ Seqs x1 (f y1) = Seqs x2 (f y2)”)
  \\ fs [GSYM MAP_MAP_o]
  \\ conj_asm2_tac
  >-
   (pop_assum mp_tac
    \\ rename [‘subst m’]
    \\ qpat_x_assum ‘LENGTH _ = LENGTH _’ mp_tac
    \\ qid_spec_tac ‘vals’
    \\ qid_spec_tac ‘args’
    \\ Induct \\ fs [] \\ strip_tac \\ Cases \\ fs []
    \\ rw [])
  \\ rename [‘subst (m |++ _)’]
  \\ qpat_x_assum ‘LENGTH _ = LENGTH _’ mp_tac
  \\ qpat_x_assum ‘ALL_DISTINCT _’ mp_tac
  \\ qid_spec_tac ‘m’
  \\ qid_spec_tac ‘vals’
  \\ qid_spec_tac ‘args’
  \\ Induct \\ fs [] \\ gen_tac \\ Cases \\ fs []
  \\ rw [] \\ TRY (fs [FUPDATE_LIST] \\ NO_TAC)
  \\ fs [subst_def,alistTheory.flookup_fupdate_list]
  \\ fs [ALOOKUP_APPEND]
  \\ fs [AllCaseEqs()]
  \\ fs [ALOOKUP_NONE]
  \\ disj1_tac
  \\ fs [MEM_MAP,MEM_ZIP,FORALL_PROD]
  \\ fs [MEM_EL]
  \\ CCONTR_TAC \\ gvs []
  \\ gvs [EL_MAP]
  \\ rename [‘k < LENGTH aa’]
  \\ first_x_assum $ qspecl_then [‘SND (EL k aa)’,‘k’] mp_tac
  \\ fs []
QED

Theorem reformulate_thm:
  reformulate binds body e ∧ obl_syntax binds ⇒
  subst_funs (MAP mk_seq_bind binds) body ≈
  subst_funs (MAP mk_seq_bind binds) e
Proof
  simp [subset_funs_mk_seq_bind_syntax]
  \\ qsuff_tac ‘
    ∀bs e1 e2.
      reformulate bs e1 e2 ∧ obl_syntax binds ∧
      set bs SUBSET set binds ⇒
      subst
       (FEMPTY |++
        MAP (λ(g,x). (g,Letrec (MAP mk_seq_bind binds) x))
          (MAP mk_seq_bind bs)) e1 ≈
      subst
       (FEMPTY |++
        MAP (λ(g,x). (g,Letrec (MAP mk_seq_bind binds) x))
          (MAP mk_seq_bind bs)) e2’
  >- (disch_then (fn th => rw [] \\ drule th) \\ fs [])
  \\ Induct_on ‘reformulate’ \\ rpt strip_tac
  >-
   (gvs [subst_Seqs,subst_Apps]
    \\ rename [‘_ = SOME (args,body)’]
    \\ qpat_abbrev_tac ‘ss = subst _’
    \\ ‘(MAP ss (MAP SND (FILTER (SND ∘ FST) (ZIP (args,es))))) =
        MAP SND (FILTER (SND ∘ FST) (ZIP (args,MAP ss es)))’ by
      (qpat_x_assum ‘LENGTH _ = LENGTH _’ mp_tac
       \\ qid_spec_tac ‘args’
       \\ qid_spec_tac ‘es’
       \\ Induct \\ fs []
       \\ gen_tac \\ Cases \\ fs []  \\ rw [])
    \\ simp []
    \\ qabbrev_tac ‘vals = MAP ss es’
    \\ simp [Abbr‘ss’]
    \\ drule_all ALOOKUP_IMP_FLOOKUP \\ strip_tac
    \\ fs [subst_def] \\ fs [mk_seq_bind_def]
    \\ irule_at Any exp_eq_trans
    \\ irule_at Any Apps_cong1
    \\ irule_at Any ETA_lemma \\ fs []
    \\ qexists_tac ‘f’ \\ conj_tac
    >- (imp_res_tac ALOOKUP_MEM \\ fs [SUBSET_DEF])
    \\ qpat_abbrev_tac ‘ll = Letrec _ _’
    \\ irule Apps_Lams_eq_Seqs
    \\ qsuff_tac ‘closed ll’
    >-
     (fs [Abbr‘vals’]
      \\ imp_res_tac ALOOKUP_MEM \\ fs [obl_syntax_def,EVERY_MEM]
      \\ fs [SUBSET_DEF] \\ res_tac \\ fs []
      \\ fs [SUBSET_DEF] \\ res_tac \\ fs [])
    \\ drule mk_seq_bind_closed_syntax'
    \\ disch_then drule
    \\ disch_then irule \\ fs []
    \\ gvs [FLOOKUP_DEF,FRANGE_DEF,PULL_EXISTS]
    \\ metis_tac [])
  >-
   (fs [subst_def,mk_seq_lams_def]
    \\ rename [‘_ = SOME (args,body)’]
    \\ drule_all ALOOKUP_IMP_FLOOKUP \\ strip_tac
    \\ fs [] \\ DEP_REWRITE_TAC [subst_Lams_mk_seqs_lemma]
    \\ fs [subst_def,mk_seq_lams_def]
    \\ conj_tac
    >-
     (fs [FDOM_FUPDATE_LIST,MEM_MAP,EXISTS_PROD,mk_seq_bind_def,obl_syntax_def]
      \\ imp_res_tac ALOOKUP_MEM
      \\ fs [EVERY_MEM,SUBSET_DEF]
      \\ fs [IN_DISJOINT,MEM_MAP,EXISTS_PROD]
      \\ res_tac \\ fs []
      \\ res_tac \\ fs []
      \\ metis_tac [])
    \\ fs [mk_seq_bind_def]
    \\ irule ETA_lemma \\ fs []
    \\ imp_res_tac ALOOKUP_MEM
    \\ fs [SUBSET_DEF] \\ res_tac
    \\ first_x_assum $ irule_at Any)
  >~ [‘Var’] >- simp [exp_eq_refl]
  >~ [‘App’] >- (gvs [subst_def] \\ irule_at Any exp_eq_App_cong \\ fs [])
  >~ [‘Prim’] >-
   (gvs [subst_def] \\ irule_at Any exp_eq_Prim_cong \\ fs []
    \\ last_x_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS])
  >~ [‘Lam’] >-
   (gvs [subst_def] \\ irule_at Any exp_eq_Lam_cong
    \\ gs [SUBSET_DEF,MEM_FILTER]
    \\ qpat_x_assum ‘_ ≈ _’ mp_tac
    \\ fs [DOMSUB_FUPDATE_LIST]
    \\ qpat_abbrev_tac ‘xs1 = MAP _ (MAP _ (FILTER _ _))’
    \\ qpat_abbrev_tac ‘xs2 = FILTER _ (MAP _ (MAP _ _))’
    \\ qsuff_tac ‘xs1 = xs2’ >- fs []
    \\ unabbrev_all_tac
    \\ qid_spec_tac ‘bs’ \\ Induct \\ fs [FORALL_PROD,mk_seq_bind_def]
    \\ rw [mk_seq_bind_def])
  \\ rename [‘Letrec’]
  \\ gvs [subst_def] \\ irule_at Any exp_eq_Letrec_cong
  \\ gs [SUBSET_DEF,MEM_FILTER]
  \\ conj_tac
  >- (fs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_INTRO])
  \\ fs [LIST_REL_MAP,LAMBDA_PROD,FDIFF_LIST_FUPDATE]
  \\ rpt $ pop_assum mp_tac
  \\ qpat_abbrev_tac ‘xs1 = MAP _ (MAP _ (FILTER _ _))’
  \\ qpat_abbrev_tac ‘xs2 = FILTER _ (MAP _ (MAP _ _))’
  \\ rpt $ disch_then assume_tac
  \\ qsuff_tac ‘xs1 = xs2’
  >-
   (strip_tac \\ gvs []
    \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
    \\ gvs [FORALL_PROD])
  \\ unabbrev_all_tac
  \\ qid_spec_tac ‘bs’
  \\ Induct \\ fs [FORALL_PROD,mk_seq_bind_def]
  \\ fs [IN_DEF] \\ rw [mk_seq_bind_def]
QED

Theorem IMP_obligation:
  ALL_DISTINCT (MAP FST binds) ∧
  (∀vname args body.
     MEM (vname,args,body) binds
     ⇒
     (* args are distinct *)
     ALL_DISTINCT (MAP FST args) ∧
     (* args are disjoint *)
     DISJOINT (set (MAP FST args)) (set (MAP FST binds)) ∧
     (* body of bound exp only mentions args and other bound names *)
     freevars body SUBSET (set (MAP FST binds) UNION set (MAP FST args)) ∧
     (* every forced var is free in body *)
     set (MAP FST (FILTER SND args)) SUBSET freevars body ∧
     (* there is a reformulation of body, called e, such that 'e ≈ mk_seqs args e' *)
     ∃e.
       reformulate binds body e ∧
       e ≈ mk_seqs args e)
  ⇒
  obligation binds
Proof
  rw [EVERY_MEM,obligation_def,FORALL_PROD]
  \\ rename [‘MEM (vname,args,body) binds’]
  \\ first_assum $ drule_then strip_assume_tac
  \\ ‘obl_syntax binds’ by
    (fs [obl_syntax_def,EVERY_MEM,FORALL_PROD] \\ rw [] \\ res_tac)
  \\ drule_all reformulate_thm \\ strip_tac
  \\ irule_at Any exp_eq_trans
  \\ first_assum $ irule_at Any
  \\ irule_at Any exp_eq_trans
  \\ irule_at Any mk_seqs_cong
  \\ simp [Once exp_eq_sym]
  \\ first_x_assum $ irule_at Any
  \\ fs [subset_funs_mk_seq_bind_syntax]
  \\ DEP_REWRITE_TAC [mk_seqs_subst]
  \\ conj_tac >-
   (fs [FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,mk_seq_bind_def]
    \\ fs [IN_DISJOINT,MEM_MAP,FORALL_PROD])
  \\ irule exp_eq_forall_subst_all \\ fs []
  \\ drule mk_seq_bind_closed_syntax
  \\ fs [FEVERY_DEF,FRANGE_DEF,PULL_EXISTS]
QED

Theorem Letrec_mk_seq_lams:
  obligation binds ∧ x ≈ y ⇒
  (Letrec (MAP mk_lams binds) x ≈
   Letrec (MAP mk_seq_lams binds) y)
Proof
  rw []
  \\ irule_at Any exp_eq_trans
  \\ irule_at Any exp_eq_trans
  \\ irule_at Any Letrec_mk_seq_bind_same
  \\ last_assum $ irule_at Any
  \\ qexists_tac ‘x’
  \\ irule_at Any exp_eq_Letrec_cong \\ fs []
  \\ irule_at Any exp_eq_Letrec_cong \\ fs []
  \\ fs [AC CONJ_COMM CONJ_ASSOC]
  \\ fs [exp_eq_refl]
  \\ qid_spec_tac ‘binds’ \\ Induct
  \\ fs [mk_lams_def,mk_seq_lams_def,mk_bind_def,mk_seq_bind_def,FORALL_PROD]
  \\ rpt gen_tac
  \\ rpt $ irule_at Any Lams_cong
  \\ irule_at Any Seq_Zero \\ fs [exp_eq_refl]
  \\ simp [Once exp_eq_sym]
  \\ irule_at Any Seq_Zero \\ fs [exp_eq_refl]
QED

(*

  fac n i = if n = 0 then i else fac (i-1) (n * i)

  if n = 0 then i else seq (i-1) (seq (n*i) (fac (i-1) (n * i)))
  ~
  seq n (seq i (if n = 0 then i else seq (i-1) (seq (n*i) (fac (i-1) (n * i))))

*)

val _ = export_theory();
