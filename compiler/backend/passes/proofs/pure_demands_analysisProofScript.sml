(*
   Proof of the demands analysis pass
*)

open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory dep_rewrite
     optionTheory pairTheory ltreeTheory llistTheory bagTheory mlmapTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory
     finite_mapTheory mlstringTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_miscTheory pure_exp_relTheory pure_congruenceTheory
     pure_cexpTheory pure_demandTheory pure_demands_analysisTheory pureLangTheory;
open pure_letrec_seqTheory pure_letrecProofTheory;
open pure_typingPropsTheory

val _ = new_theory "pure_demands_analysisProof";

val _ = set_grammar_ancestry [
          "pure_letrecProof",
          "pureLang",
          "pure_demand",
          "pure_demands_analysis"
        ]

(** Proof **)

Definition update_ctxt_def:
  (update_ctxt id n c [] = c) ∧
  (update_ctxt id n c ((i,p)::tl) =
   update_ctxt id n (Bind (explode p) (Proj (explode id) i (Var (explode n))) c) tl)
End

Definition ctxt_trans_def:
  ctxt_trans (Nil: α da_ctxt) = Nil ∧
  ctxt_trans (IsFree l ctxt) = FOLDL (λc n. IsFree (explode n) (c:ctxt)) (ctxt_trans ctxt) l ∧
  ctxt_trans (Bind n e ctxt) = Bind (explode n) (exp_of e) (ctxt_trans ctxt) ∧
  ctxt_trans ((RecBind (binds: (mlstring # α cexp) list) ctxt): α da_ctxt) =
             (RecBind (MAP (λ(n,e). (explode n, exp_of e)) binds) (ctxt_trans ctxt) : ctxt) ∧
  ctxt_trans (Unfold id n names c) = update_ctxt id n (ctxt_trans c) (MAPi (λi v. (i, v)) names)
End

Definition demands_map_to_set_def:
  demands_map_to_set m = IMAGE (λx. (([]: (string # num) list), explode x)) (FDOM (to_fmap m))
End

Definition fd_to_set_def:
  fd_to_set NONE = NONE ∧
  fd_to_set (SOME (bL, m)) = SOME (bL, demands_map_to_set m)
End

Definition fdemands_map_to_set_def:
  fdemands_map_to_set fds = IMAGE (λx. (explode x, (to_fmap fds) ' x)) (FDOM (to_fmap fds))
End

Theorem demands_map_union:
  map_ok m1 ∧ map_ok m2 ∧ cmp_of m1 = cmp_of m2
  ⇒ demands_map_to_set (union m1 m2) = demands_map_to_set m1 ∪ demands_map_to_set m2
Proof
  rw [union_thm, demands_map_to_set_def]
QED

Theorem demands_map_empty:
  demands_map_to_set (empty cmp) = {}
Proof
  rw [empty_thm, demands_map_to_set_def]
QED

Theorem demands_map_insert:
  map_ok m ⇒ demands_map_to_set (insert m n ()) = demands_map_to_set m ∪ {[], explode n}
Proof
  rw [insert_thm, demands_map_to_set_def, Once INSERT_SING_UNION, UNION_COMM]
QED

Theorem demands_map_FOLDL:
  ∀l cmp m2. TotOrd cmp ∧ EVERY (λm. map_ok m ∧ cmp_of m = cmp) l ∧ map_ok m2 ∧ cmp_of m2 = cmp
             ⇒ demands_map_to_set (FOLDL union m2 l)
               = demands_map_to_set m2 ∪ BIGUNION (set (MAP demands_map_to_set l))
Proof
  Induct >> rw [] >>
  rename1 ‘union m2 h’ >>
  last_x_assum $ qspecl_then [‘cmp_of m2’, ‘union m2 h’] assume_tac >>
  gvs [union_thm, demands_map_union, UNION_ASSOC]
QED

Theorem FOLDL_delete_ok:
  ∀m v. map_ok m
        ⇒ map_ok (FOLDL (λm2 w. delete m2 w) m vL)
          ∧ cmp_of (FOLDL (λm2 w. delete m2 (w : mlstring)) m vL) = cmp_of m
Proof
  Induct_on ‘LENGTH vL’ >> rw [] >>
  rename1 ‘SUC _ = LENGTH vL’ >>
  qspecl_then [‘vL’] assume_tac last_exists >> gvs [FOLDL_APPEND, delete_thm]
QED

Theorem FOLDL_delete_soundness:
  ∀m v. map_ok m
        ⇒ map_ok (FOLDL (λm2 w. delete m2 w) m vL)
          ∧ cmp_of (FOLDL (λm2 w. delete m2 (w : mlstring)) m vL) = cmp_of m ∧
          FDOM (to_fmap (FOLDL (λm2 w. delete m2 w) m vL)) = (FDOM $ to_fmap m) DIFF set vL
Proof
  Induct_on ‘LENGTH vL’ >> rw [] >>
  rename1 ‘SUC _ = LENGTH vL’ >>
  qspecl_then [‘vL’] assume_tac last_exists >>
  gvs [FOLDL_APPEND, delete_thm] >>
  simp [SET_EQ_SUBSET, SUBSET_DEF]
QED

Theorem demands_map_delete:
  ∀m v. map_ok m ⇒ ∀ps. (ps, explode v) ∉ demands_map_to_set (delete m v)
Proof
  rw [demands_map_to_set_def, delete_thm]
QED

Theorem demands_map_delete_subset:
  ∀m v. map_ok m ⇒
        demands_map_to_set (delete m v) ⊆ demands_map_to_set m
Proof
  rw [demands_map_to_set_def, delete_thm]
QED

Theorem demands_map_FOLDL_delete_subset:
  ∀vL m. map_ok m ⇒
        demands_map_to_set (FOLDL (λf k. delete f k) m vL) ⊆ demands_map_to_set m
Proof
  Induct >> rw [] >>
  irule SUBSET_TRANS >>
  last_x_assum $ irule_at (Pos hd) >>
  gvs [demands_map_delete_subset, delete_thm]
QED

Theorem demands_map_delete2:
  ∀m v w ps. map_ok m ∧ (ps, v) ∉ demands_map_to_set m
           ⇒ (ps, v) ∉ demands_map_to_set (delete m w)
Proof
  rw [demands_map_to_set_def, delete_thm]
QED

Theorem demands_map_FOLDL_delete:
  ∀m v.
    map_ok m ∧ MEM v vL
    ⇒ ∀ps. (ps, explode v) ∉ demands_map_to_set (FOLDL (λm2 w. delete m2 w) m vL)
Proof
  Induct_on ‘LENGTH vL’ >> rw [] >>
  rename1 ‘SUC _ = LENGTH vL’ >>
  qspecl_then [‘vL’] assume_tac last_exists >> gvs [FOLDL_APPEND]
  >- (irule demands_map_delete2 >>
      gvs [FOLDL_delete_ok]) >>
  irule demands_map_delete >>
  gvs [FOLDL_delete_ok]
QED

Theorem fdemands_map_to_set_soundness:
  ∀fds n x. map_ok fds ⇒
            (lookup fds n = SOME x ⇔ (explode n, x) ∈ fdemands_map_to_set fds)
Proof
  rw [lookup_thm, FLOOKUP_DEF, fdemands_map_to_set_def] >>
  eq_tac >> rw [] >> gvs [implode_explode] >>
  pop_assum $ irule_at Any >> gvs [explode_implode]
QED

Theorem fdemands_map_delete_subset:
  ∀v fds. map_ok fds
           ⇒ fdemands_map_to_set (delete fds v)
                                 ⊆ fdemands_map_to_set fds
Proof
  Induct >> gvs [fdemands_map_to_set_def, SUBSET_DEF, delete_thm] >>
  rw [DOMSUB_FAPPLY_NEQ]
QED

Theorem fdemands_map_FOLDL_delete_subset:
  ∀vL fds. map_ok fds
           ⇒ fdemands_map_to_set (FOLDL (λf k. delete f k) fds vL)
                                 ⊆ fdemands_map_to_set fds
Proof
  Induct >> rw [] >>
  irule SUBSET_TRANS >> last_x_assum $ irule_at $ Pos hd >>
  gvs [delete_thm, fdemands_map_delete_subset]
QED

Theorem fdemands_map_delete:
  ∀m v. map_ok m ⇒ ∀ps. (explode v, ps) ∉ fdemands_map_to_set (delete m v)
Proof
  rw [fdemands_map_to_set_def, delete_thm]
QED

Theorem fdemands_map_insert:
  ∀m v bL d. d ∈ fdemands_map_to_set (insert m v bL) ∧ map_ok m
             ⇒ (d = (explode v, bL) ∨ (FST d ≠ explode v ∧ d ∈ fdemands_map_to_set m))
Proof
  rw [] >> gvs [fdemands_map_to_set_def, insert_thm] >>
  gvs [FAPPLY_FUPDATE_THM, SF CONJ_ss]
QED

Theorem fdemands_map_delete2:
  ∀m w d. map_ok m ∧ d ∉ fdemands_map_to_set m
           ⇒ d ∉ fdemands_map_to_set (delete m w)
Proof
  gvs [FORALL_PROD] >>
  rw [fdemands_map_to_set_def, delete_thm] >>
  rename1 ‘x ∉ FDOM _ ∨ x = w’ >> pop_assum $ qspecl_then [‘x’] assume_tac >>
  Cases_on ‘x = w’ >>
  gvs [DOMSUB_FAPPLY_NEQ]
QED

Theorem fdemands_map_FOLDL_delete2:
  ∀vL fds v bL bL2. map_ok fds ⇒
                      ((explode v, bL) ∈ fdemands_map_to_set (FOLDL (λf k. delete f k) fds vL)
                       ⇔ ((explode v, bL) ∈ fdemands_map_to_set fds ∧ ¬MEM v vL))
Proof
  Induct >> rw [] >> eq_tac >> strip_tac >>
  rename1 ‘delete fds h’ >>
  last_x_assum $ qspecl_then [‘delete fds h’] assume_tac >>
  gvs [delete_thm] >>
  pop_assum kall_tac >>
  gvs [fdemands_map_to_set_def, delete_thm, DOMSUB_FAPPLY_NEQ]
QED

Theorem fdemands_map_FOLDL_delete:
  ∀m v.
    map_ok m ∧ MEM v vL
    ⇒ ∀ps. (explode v, ps) ∉ fdemands_map_to_set (FOLDL (λm2 w. delete m2 w) m vL)
Proof
  Induct_on ‘LENGTH vL’ >> rw [] >>
  rename1 ‘SUC _ = LENGTH vL’ >>
  qspecl_then [‘vL’] assume_tac last_exists >> gvs [FOLDL_APPEND]
  >- (irule fdemands_map_delete2 >>
      gvs [FOLDL_delete_ok]) >>
  irule fdemands_map_delete >>
  gvs [FOLDL_delete_ok]
QED

Theorem fdemands_map_delete_soundness:
  ∀v fds n ps. map_ok fds
               ∧ (n, ps) ∈ fdemands_map_to_set (delete fds v)
               ⇒ n ≠ explode v ∧ (n, ps) ∈ fdemands_map_to_set fds
Proof
  rw [fdemands_map_to_set_def] >>
  gvs [delete_thm, DOMSUB_FAPPLY_NEQ]
QED

Theorem demands_map_delete_soundness:
  ∀v m n ps. map_ok m
               ∧ (ps, n) ∈ demands_map_to_set (delete m v)
               ⇒ n ≠ explode v ∧ (ps, n) ∈ demands_map_to_set m
Proof
  rw [demands_map_to_set_def] >>
  gvs [delete_thm, DOMSUB_FAPPLY_NEQ]
QED

Theorem demands_map_FOLDL_delete_soundness:
  ∀vL m n ps. (ps, n) ∈ demands_map_to_set (FOLDL (λm v. delete m v) m vL) ∧ map_ok m
               ⇒ ¬MEM (implode n) vL ∧ (ps, n) ∈ demands_map_to_set m
Proof
  Induct >> rw [] >>
  last_x_assum $ dxrule_then assume_tac >>
  gvs [delete_thm] >>
  dxrule_then (dxrule_then assume_tac) demands_map_delete_soundness >> gvs [] >>
  strip_tac >> gvs []
QED

Theorem compute_ALL_DISTINCT_soundness_lemma:
  ∀l m. compute_ALL_DISTINCT l m ∧ map_ok m ⇒
        ALL_DISTINCT (MAP explode l) ∧ (∀v. MEM v l ⇒ lookup m v = NONE)
Proof
  Induct >> rw [compute_ALL_DISTINCT_def] >>
  last_x_assum $ dxrule_then assume_tac >>
  gvs [insert_thm, lookup_thm, FLOOKUP_UPDATE]
  >- (strip_tac >> first_x_assum $ dxrule_then assume_tac >>
      gvs []) >>
  first_x_assum $ dxrule_then assume_tac >>
  FULL_CASE_TAC >> fs []
QED

Theorem compute_ALL_DISTINCT_soundness:
  ∀l. compute_ALL_DISTINCT l (empty compare) ⇒ ALL_DISTINCT (MAP explode l)
Proof
  rw [] >> dxrule_then assume_tac compute_ALL_DISTINCT_soundness_lemma >>
  gvs [empty_thm, TotOrd_compare]
QED

Theorem FOLDL_union_map_ok:
  ∀l cmp m. TotOrd cmp ∧ EVERY (λm. map_ok m ∧ cmp_of m = cmp) l ∧ map_ok m ∧ cmp_of m = cmp ⇒
          map_ok (FOLDL union m l)
Proof
  Induct
  \\ fs [empty_thm]
  \\ rw [union_thm]
QED

Theorem FOLDL_union_cmp_of:
  ∀l cmp m. TotOrd cmp ∧ EVERY (λm. map_ok m ∧ cmp_of m = cmp) l ∧ map_ok m ∧ cmp_of m = cmp ⇒
          cmp_of (FOLDL union m l) = cmp
Proof
  Induct
  \\ fs [empty_thm]
  \\ rw [union_thm]
QED

Theorem FOLDL_union:
  ∀l cmp (m:('a,unit) map).
    TotOrd cmp ∧
    EVERY (λm. map_ok m ∧ cmp_of m = cmp) l ∧
    map_ok m ∧ cmp_of m = cmp
  ⇒ map_ok (FOLDL union m l) ∧ cmp_of (FOLDL union m l) = cmp_of m ∧
    FDOM (to_fmap (FOLDL union m l)) =
    FDOM (to_fmap m) ∪ BIGUNION { FDOM (to_fmap m') | MEM m' l }
Proof
  Induct >> rw[union_thm] >>
  rw[EXTENSION] >> eq_tac >> rw[] >> gvs[PULL_EXISTS] >> metis_tac[]
QED


Theorem adds_demands_soundness:
  ∀vl e e' m ds c ds a fds fd fd2.
    map_ok m ∧ find (exp_of e) c fds (demands_map_to_set m) (exp_of e') fd
    ⇒ find (exp_of e) c fds (demands_map_to_set m)
                             (exp_of (adds_demands a (m, e', fd2) vl)) fd
Proof
  Induct
  \\ rw [adds_demands_def]
  \\ rename1 ‘lookup m h’
  \\ Cases_on ‘lookup m h’
  \\ fs []
  \\ rw [exp_of_def, op_of_def]
  \\ irule find_Seq
  \\ gvs [demands_map_to_set_def, lookup_thm, FLOOKUP_DEF]
  \\ rpt $ first_x_assum $ irule_at Any
QED

Theorem handle_Letrec_fdemands_soundness:
  ∀vL (mL : (bool list # (mlstring, unit) map) option list) fds.
    LENGTH vL = LENGTH mL ∧ map_ok fds ∧ cmp_of fds = compare
    ⇒ map_ok (handle_Letrec_fdemands fds vL mL)
      ∧ cmp_of (handle_Letrec_fdemands fds vL mL) = compare
      ∧ ∀v argDs. (explode v, argDs) ∈ fdemands_map_to_set (handle_Letrec_fdemands fds vL mL)
                  ⇒ (explode v, argDs) ∈ fdemands_map_to_set (FOLDL (λf v. delete f v) fds vL)
                    ∨ ∃i fdMap. i < LENGTH vL ∧ EL i vL = v ∧ EL i mL = SOME (argDs, fdMap)
Proof
  Induct >> gvs [handle_Letrec_fdemands_def] >>
  gen_tac >> Cases >> fs [] >>
  rename1 ‘handle_Letrec_fdemands _ _ (h2::_)’ >>
  Cases_on ‘h2’ >> gvs [handle_Letrec_fdemands_def] >> rw [] >>
  last_x_assum $ dxrule_then assume_tac
  >>~[‘FST x’]
  >- (pop_assum $ qspecl_then [‘insert fds h (FST x)’] assume_tac >> gvs [insert_thm])
  >- (pop_assum $ qspecl_then [‘insert fds h (FST x)’] assume_tac >> gvs [insert_thm])
  >- (pop_assum $ qspecl_then [‘insert fds h (FST x)’] assume_tac >> gvs [insert_thm] >>
      first_x_assum $ dxrule_then assume_tac >> gvs []
      >- (rename1 ‘FOLDL _ (insert fds h (FST x)) vL’ >>
          qspecl_then [‘vL’, ‘insert fds h (FST x)’] assume_tac fdemands_map_FOLDL_delete2 >>
          gvs [insert_thm] >> pop_assum kall_tac >>
          dxrule_then assume_tac fdemands_map_insert >> gvs []
          >- (disj2_tac >> qexists_tac ‘0’ >> qexists_tac ‘SND x’ >> gvs [])
          >- (qspecl_then [‘vL’, ‘delete fds h’] assume_tac $ iffRL fdemands_map_FOLDL_delete2 >>
              disj1_tac >> gvs [delete_thm] >> pop_assum irule >>
              gvs [fdemands_map_to_set_def, delete_thm, DOMSUB_FAPPLY_NEQ]))
      >- (rename1 ‘i < _’ >> disj2_tac >>
          qexists_tac ‘SUC i’ >> gvs [] >> first_x_assum $ irule_at Any))
  >>~[‘delete fds h’]
  >- (pop_assum $ qspecl_then [‘delete fds h’] assume_tac >> gvs [delete_thm])
  >- (pop_assum $ qspecl_then [‘delete fds h’] assume_tac >> gvs [delete_thm])
  >- (pop_assum $ qspecl_then [‘delete fds h’] assume_tac >> gvs [delete_thm] >>
      first_x_assum $ dxrule_then assume_tac >> gvs [] >>
      disj2_tac >> rename1 ‘EL i _’ >> qexists_tac ‘SUC i’ >> gvs [])
QED

Theorem add_all_demands_soundness_lemma:
  ∀m s cmp a e e' fds fd fd2 c.
    TotOrd cmp ∧
    find (exp_of e) c fds (s ∪ IMAGE (λx. ([], explode x)) (FDOM (to_fmap (Map cmp m)))) (exp_of e') fd
    ⇒ find (exp_of e) c fds (s ∪ IMAGE (λx. ([], explode x)) (FDOM (to_fmap (Map cmp m))))
           (exp_of (add_all_demands a (Map cmp m, e', fd2))) fd
Proof
  Induct
  \\ fs [add_all_demands_def, foldrWithKey_def, balanced_mapTheory.foldrWithKey_def, to_fmap_def]
  \\ rw [Once INSERT_SING_UNION]
  \\ rw [Once INSERT_SING_UNION]
  \\ rename1 ‘s ∪ ({([], explode k)} ∪ _)’
  \\ last_x_assum $ qspecl_then [‘s ∪ {([], explode k)} ∪ (IMAGE (λx. ([],explode x)) (FDOM (to_fmap (Map cmp m'))))’, ‘cmp’] assume_tac
  \\ qabbrev_tac ‘set1=IMAGE (λx. ([]:(string#num) list,explode x)) (FDOM (to_fmap (Map cmp m)))’
  \\ qabbrev_tac ‘set2=IMAGE (λx. ([]:(string#num) list,explode x)) (FDOM (to_fmap (Map cmp m')))’
  \\ ‘s ∪ ({([], explode k)} ∪ (set1 ∪ set2)) = (s ∪ {([], explode k)} ∪ set2) ∪ set1’
    by metis_tac [UNION_ASSOC, UNION_COMM]
  \\ rw []
  \\ first_x_assum irule
  \\ fs []
  \\ pop_assum kall_tac
  \\ ‘(s ∪ {([], explode k)} ∪ set2) ∪ set1 = (s ∪ {([], explode k)} ∪ set1) ∪ set2’
    by metis_tac [UNION_ASSOC, UNION_COMM]
  \\ rw [exp_of_def, op_of_def]
  \\ irule find_Seq
  \\ unabbrev_all_tac
  \\ first_x_assum $ irule_at Any
  \\ fs []
  \\ qexists_tac ‘[]’
  \\ fs []
QED

Theorem add_all_demands_soundness:
  ∀m a e e' fds fd fd2 c.
    TotOrd (cmp_of m) ∧
    find (exp_of e) c fds (demands_map_to_set m) (exp_of e') fd
    ⇒ find (exp_of e) c fds (demands_map_to_set m)
           (exp_of (add_all_demands a (m, e', fd2))) fd
Proof
  Cases >> rw [] >> rename1 ‘Map f b’ >>
  dxrule_then (qspecl_then [‘b’, ‘{}’] assume_tac) add_all_demands_soundness_lemma >>
  gvs [demands_map_to_set_def, cmp_of_def]
QED

(* ------------------------------ *)
(* - Proof of fixpoint analysis - *)
(* ------------------------------ *)

Theorem ALL_DISTINCT_IMP:
  ∀l. ALL_DISTINCT (MAP FST l) ⇒ ALL_DISTINCT (MAP (λ(p1, p2). explode p1) l)
Proof
  Induct >> gvs [] >> rw [] >>
  strip_tac >> first_x_assum irule >>
  gvs [MEM_EL] >>
  first_assum $ irule_at $ Pos hd >> gvs [EL_MAP] >>
  pairarg_tac >> gs [] >> pairarg_tac >> gs []
QED

Theorem ALL_DISTINCT_IMP2:
  ∀l. ALL_DISTINCT (MAP (λ(p1, p2). explode p1) l) ⇒ ALL_DISTINCT (MAP FST l)
Proof
  Induct >> gvs [] >> rw [] >>
  strip_tac >> first_x_assum irule >>
  gvs [MEM_EL] >>
  first_assum $ irule_at $ Pos hd >> gvs [EL_MAP] >>
  pairarg_tac >> gs [] >> pairarg_tac >> gs []
QED

Theorem split_body_soundness:
  ∀e l bL body label. LENGTH l = LENGTH bL ⇒
                  split_body e = (l, body, label) ⇒
                  (∀v. (v, (exp_of e)) = mk_lams (v, ZIP(MAP explode l, bL), (exp_of body))) ∧
                  (NestedCase_free e ⇒ NestedCase_free body) ∧
                  (cexp_wf e ⇒ cexp_wf body)
Proof
  Cases \\ gs [split_body_def, Lams_def, mk_lams_def, NestedCase_free_def, cexp_wf_def]
  \\ gs [MAP_ZIP, exp_of_def]
QED

Theorem compute_freevars_soundness_lemma:
  ∀(l : α cexp list). (∀v. v < cexp10_size (K 0) l ⇒
       ∀(e : α cexp). cexp_size (K 0) e = v ⇒ NestedCase_free e ⇒
                      map_ok (compute_freevars e) ∧
                      cmp_of (compute_freevars e) = compare ∧
                      (FDOM (to_fmap (compute_freevars e))) = IMAGE implode (freevars (exp_of e)))
                      ⇒ ∀m1 m2. FOLDR (λe m. union m (compute_freevars e)) m1 l = m2 ∧
                                EVERY (λa. NestedCase_free a) l ∧
                                map_ok m1 ∧ cmp_of m1 = compare ⇒
                                map_ok m2 ∧ cmp_of m2 = compare ∧
                                (FDOM (to_fmap m2))
                                = IMAGE implode (freevars (Apps Fail (MAP exp_of l))) ∪ (FDOM (to_fmap m1))
Proof
  Induct \\ gs []
  \\ gen_tac \\ strip_tac
  \\ last_x_assum mp_tac
  \\ impl_tac
  >- (gen_tac \\ strip_tac
      \\ rename1 ‘v < _’
      \\ last_x_assum $ qspec_then ‘v’ assume_tac
      \\ gs [cexp_size_def])
  \\ strip_tac
  \\ gen_tac \\ strip_tac
  \\ first_x_assum $ dxrule_then $ dxrule_then assume_tac \\ gs []
  \\ rename1 ‘h::_’
  \\ last_x_assum $ qspec_then ‘cexp_size (K 0) h’ assume_tac
  \\ gs [cexp_size_def]
  \\ pop_assum $ qspec_then ‘h’ assume_tac
  \\ gs [union_thm]
  \\ rpt $ pop_assum kall_tac
  \\ simp [SET_EQ_SUBSET, SUBSET_DEF]
QED

Theorem compute_freevars_soundness_lemma2:
  ∀l (m : (mlstring, unit) map). map_ok m ∧ cmp_of m = compare ⇒
        ∀m2. FOLDR (λv m. delete m v) m l = m2 ⇒
             map_ok m2 ∧ cmp_of m2 = compare ∧
             (FDOM (to_fmap m2)) = (FDOM (to_fmap m)) DIFF (set l)
Proof
  Induct \\ gs []
  \\ rpt $ gen_tac \\ strip_tac
  \\ last_x_assum $ dxrule_then assume_tac
  \\ gs [delete_thm]
  \\ gvs [SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
QED

Theorem compute_freevars_soundness_lemma3:
  ∀(rows : (mlstring # mlstring list # α cexp) list).
    (∀v. v < cexp2_size (K 0) rows ⇒
         ∀(e : α cexp).
           cexp_size (K 0) e = v ⇒ NestedCase_free e ⇒
           map_ok (compute_freevars e) ∧
           cmp_of (compute_freevars e) = compare ∧
           FDOM (to_fmap (compute_freevars e)) = IMAGE implode (freevars (exp_of e)))
    ⇒ ∀m1 m2. FOLDR (λ(_, vL, e') m. union (FOLDR (λv m. delete m v) (compute_freevars e') vL)
                                           m) m1 rows = m2 ∧
              EVERY (λa. NestedCase_free a) (MAP (SND o SND) rows) ∧
              map_ok m1 ∧ cmp_of m1 = compare ⇒
              map_ok m2 ∧ cmp_of m2 = compare ∧
              (FDOM (to_fmap m2))
              = IMAGE implode (BIGUNION (set (MAP (λ(_, vL, e). freevars (exp_of e)
                                                                         DIFF (set (MAP explode vL))) rows)))
                         ∪ (FDOM (to_fmap m1))
Proof
  Induct \\ gs []
  \\ gen_tac \\ strip_tac
  \\ last_x_assum mp_tac
  \\ impl_tac
  >- (gen_tac \\ strip_tac
      \\ rename1 ‘v < _’
      \\ last_x_assum $ qspec_then ‘v’ assume_tac
      \\ gs [cexp_size_def])
  \\ strip_tac
  \\ gen_tac \\ strip_tac
  \\ first_x_assum $ dxrule_then $ dxrule_then assume_tac \\ gs []
  \\ rename1 ‘h::_’
  \\ PairCases_on ‘h’
  \\ rename1 ‘(_, h1, h2)::_’
  \\ last_x_assum $ qspec_then ‘cexp_size (K 0) h2’ assume_tac
  \\ gs [cexp_size_def]
  \\ pop_assum $ qspec_then ‘h2’ assume_tac
  \\ qspecl_then [‘h1’, ‘compute_freevars h2’] assume_tac compute_freevars_soundness_lemma2
  \\ gs [union_thm]
  \\ rpt $ pop_assum kall_tac
  \\ simp [SET_EQ_SUBSET]
  \\ gvs [SUBSET_DEF, PULL_EXISTS]
  \\ rw []
  >- (disj1_tac \\ disj1_tac
      \\  irule_at Any EQ_REFL \\ simp []
      \\ strip_tac \\ gs [MEM_MAP])
  >- (disj1_tac
      \\  irule_at Any EQ_REFL \\ simp []
      \\ strip_tac \\ gs [MEM_MAP])
QED

Theorem compute_freevars_soundness_lemma4:
  ∀(l : (mlstring # α cexp) list). (∀v. v < cexp7_size (K 0) l ⇒
       ∀(e : α cexp). cexp_size (K 0) e = v ⇒ NestedCase_free e ⇒
                      map_ok (compute_freevars e) ∧
                      cmp_of (compute_freevars e) = compare ∧
                      (FDOM (to_fmap (compute_freevars e))) = IMAGE implode (freevars (exp_of e)))
                      ⇒ ∀m1 m2. FOLDR (λ(v, e) m. union m (compute_freevars e)) m1 l = m2 ∧
                                EVERY (λ(fn, a). NestedCase_free a) l ∧
                                map_ok m1 ∧ cmp_of m1 = compare ⇒
                                map_ok m2 ∧ cmp_of m2 = compare ∧
                                (FDOM (to_fmap m2))
                                = IMAGE implode (BIGUNION (set (MAP (λ(fn, e'). freevars (exp_of e')) l)))
                                        ∪ (FDOM (to_fmap m1))
Proof
  Induct \\ gs []
  \\ gen_tac \\ strip_tac
  \\ last_x_assum mp_tac
  \\ impl_tac
  >- (gen_tac \\ strip_tac
      \\ rename1 ‘v < _’
      \\ last_x_assum $ qspec_then ‘v’ assume_tac
      \\ gs [cexp_size_def])
  \\ strip_tac
  \\ gen_tac \\ strip_tac
  \\ first_x_assum $ dxrule_then $ dxrule_then assume_tac \\ gs []
  \\ rename1 ‘h::_’
  \\ last_x_assum $ qspec_then ‘cexp_size (K 0) (SND h)’ assume_tac
  \\ PairCases_on ‘h’ \\ gs []
  \\ rename1 ‘(h0, h1)::_’
  \\ gs [cexp_size_def]
  \\ pop_assum $ qspec_then ‘h1’ assume_tac
  \\ gs [union_thm]
  \\ rpt $ pop_assum kall_tac
  \\ simp [SET_EQ_SUBSET, SUBSET_DEF]
QED

Theorem IMAGE_implode_DIFF:
  ∀(s1 : string -> bool) s2. IMAGE implode (s1 DIFF s2) = (IMAGE implode s1) DIFF (IMAGE implode s2)
Proof
  rw [SET_EQ_SUBSET] \\ gs [SUBSET_DEF, PULL_EXISTS]
  \\ rw []
  \\ irule_at Any EQ_REFL \\ gs []
  \\ assume_tac implode_BIJ
  \\ gs [BIJ_DEF, INJ_DEF]
  \\ rw [] \\ gvs []
  \\ first_x_assum $ dxrule_then assume_tac
  \\ gs []
QED

Theorem IMAGE_implode_DELETE:
  ∀(s1 : string -> bool) var. IMAGE implode (s1 DELETE var) = (IMAGE implode s1) DELETE (implode var)
Proof
  rw [SET_EQ_SUBSET] \\ gs [SUBSET_DEF, PULL_EXISTS]
  \\ rw []
  \\ irule_at Any EQ_REFL \\ gs []
  \\ assume_tac implode_BIJ
  \\ gs [BIJ_DEF, INJ_DEF]
  \\ strip_tac \\ gs []
QED

Theorem IMAGE_implode_MAP_explode:
  ∀(l : mlstring list). IMAGE implode (set (MAP explode l)) = set l
Proof
  Induct \\ gs [implode_explode]
QED

Theorem freevars_lets_for:
  ∀l e m1 m2. freevars (lets_for m1 m2 l e) DELETE m2 = freevars e DIFF set (MAP SND l) DELETE m2
Proof
  Induct
  \\ gs [FORALL_PROD, lets_for_def, SING_DELETE, UNION_DELETE, DELETE_COMM]
  \\ pop_assum kall_tac
  \\ rw [SET_EQ_SUBSET] \\ gs [SUBSET_DEF]
QED

Theorem freevars_rows_of:
  ∀rows m expr.
    (freevars (rows_of (explode m) expr (MAP (λ(c, vs, e). (explode c, MAP explode vs, exp_of e)) rows)))
    DELETE (explode m)
    = (BIGUNION (set (MAP (λ(_, vL, x'). freevars (exp_of x') DIFF set (MAP explode vL)) rows))
       ∪ freevars expr) DELETE (explode m)
Proof
  Induct
  \\ gs [rows_of_def, FORALL_PROD, freevars_def, UNION_DELETE, freevars_lets_for]
  \\ rw [GSYM UNION_ASSOC]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
QED

Theorem freevars_Disj:
  ∀l m. freevars (Disj m l) DELETE m = ∅
Proof
  Induct \\ gs [Disj_def, FORALL_PROD]
  \\ gen_tac \\ rename1 ‘Disj m _’
  \\ last_x_assum $ qspec_then ‘m’ assume_tac
  \\ dxrule_then assume_tac $ iffLR SET_EQ_SUBSET
  \\ pop_assum mp_tac
  \\ strip_tac
  \\ dxrule_then assume_tac $ iffLR DELETE_SUBSET_INSERT
  \\ simp [SET_EQ_SUBSET]
  \\ gs [SUBSET_DEF]
QED

Theorem compute_freevars_soundness:
  ∀m. compute_freevars e = m ∧ NestedCase_free e ⇒
        map_ok m ∧ cmp_of m = compare ∧
        (FDOM (to_fmap m)) = IMAGE implode (freevars (exp_of e))
Proof
  completeInduct_on ‘cexp_size (K 0) e’
  \\ Cases \\ gs [compute_freevars_def]
  >- gs [empty_thm, insert_thm, TotOrd_compare, exp_of_def, freevars_def, NestedCase_free_def]
  >~[‘cexp_size _ (Prim _ _ l)’]
  >- (strip_tac \\ gs []
      \\ qspec_then ‘l’ mp_tac compute_freevars_soundness_lemma
      \\ impl_tac
      >- (gen_tac \\ strip_tac
          \\ rename1 ‘v2 < _’
          \\ last_x_assum $ qspec_then ‘v2’ assume_tac
          \\ gs [cexp_size_def])
      \\ disch_then $ qspec_then ‘empty compare’ assume_tac
      \\ gvs [empty_thm, TotOrd_compare, exp_of_def, freevars_def]
      \\ simp [SF ETA_ss])
  >~[‘cexp_size _ (App _ f eL)’]
  >- (strip_tac \\ gs []
      \\ qspec_then ‘eL’ mp_tac compute_freevars_soundness_lemma
      \\ impl_tac
      >- (gen_tac \\ strip_tac
          \\ rename1 ‘v2 < _’
          \\ last_x_assum $ qspec_then ‘v2’ assume_tac
          \\ gs [cexp_size_def])
      \\ last_x_assum $ qspec_then ‘cexp_size (K 0) f’ assume_tac
      \\ gs [cexp_size_def]
      \\ pop_assum $ qspec_then ‘f’ assume_tac
      \\ gs []
      \\ strip_tac \\ gs [exp_of_def, freevars_def]
      \\ simp [SF ETA_ss, UNION_COMM])
  >~[‘cexp_size _ (Lam _ l e)’]
  >- (strip_tac \\ gs []
      \\ last_x_assum $ qspec_then ‘cexp_size (K 0) e’ assume_tac
      \\ gs [cexp_size_def]
      \\ pop_assum $ qspec_then ‘e’ assume_tac
      \\ strip_tac
      \\ gs []
      \\ dxrule_then (qspec_then ‘l’ assume_tac) compute_freevars_soundness_lemma2
      \\ gs [exp_of_def, freevars_def, IMAGE_implode_DIFF, IMAGE_implode_MAP_explode])
  >~[‘cexp_size _ (Let _ w e1 e2)’]
  >- (strip_tac \\ strip_tac \\ gs []
      \\ last_assum $ qspec_then ‘cexp_size (K 0) e1’ assume_tac
      \\ last_x_assum $ qspec_then ‘cexp_size (K 0) e2’ assume_tac
      \\ gs [cexp_size_def]
      \\ last_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
      \\ last_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
      \\ gs [union_thm, delete_thm]
      \\ gs [exp_of_def, freevars_def, IMAGE_implode_DELETE]
      \\ simp [UNION_COMM])
  >~[‘cexp_size _ (Letrec _ l e)’]
  >- (strip_tac \\ strip_tac \\ gs []
      \\ qspec_then ‘l’ mp_tac compute_freevars_soundness_lemma4
      \\ impl_tac
      >- (gen_tac \\ strip_tac
          \\ rename1 ‘var < _’
          \\ last_x_assum $ qspec_then ‘var’ assume_tac
          \\ gs [cexp_size_def])
      \\ disch_then $ qspec_then ‘compute_freevars e’ assume_tac
      \\ last_x_assum $ qspec_then ‘cexp_size (K 0) e’ assume_tac
      \\ gs [cexp_size_def]
      \\ pop_assum $ qspec_then ‘e’ assume_tac
      \\ gs []
      \\ qmatch_goalsub_abbrev_tac ‘map_ok (FOLDR _ big_set l)’
      \\ qspecl_then [‘MAP FST l’, ‘big_set’]
                     assume_tac compute_freevars_soundness_lemma2
      \\ gvs [FOLDR_MAP, LAMBDA_PROD, EVERY_MAP]
      \\ gs [freevars_def, exp_of_def, IMAGE_UNION]
      \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
               GSYM FST_THM, IMAGE_implode_DIFF, GSYM LIST_TO_SET_MAP]
      \\ simp [UNION_COMM])
  >~[‘cexp_size _ (Case _ exp m rows fall)’]
  >- (strip_tac \\ strip_tac \\ gs []
      \\ qspec_then ‘rows’ mp_tac compute_freevars_soundness_lemma3
      \\ impl_tac
      >- (gen_tac \\ strip_tac
          \\ rename1 ‘var < _’
          \\ last_x_assum $ qspec_then ‘var’ assume_tac
          \\ gs [cexp_size_def])
      \\ strip_tac
      \\ Cases_on ‘fall’
      \\ gs [empty_thm, TotOrd_compare, union_thm, delete_thm]
      >- (last_x_assum $ qspec_then ‘cexp_size (K 0) exp’ assume_tac
          \\ gs [cexp_size_def]
          \\ first_x_assum $ qspec_then ‘exp’ assume_tac
          \\ first_x_assum $ qspec_then ‘empty compare’ assume_tac
          \\ gs [union_thm, TotOrd_compare, empty_thm, delete_thm]
          \\ gs [exp_of_def, freevars_def]
          \\ qmatch_goalsub_abbrev_tac ‘Seq Fail expr’
          \\ ‘freevars (if MEM m (FLAT (MAP (FST o SND) rows)) then (Seq Fail expr) else expr) = freevars expr’
            by (IF_CASES_TAC \\ gs [freevars_def])
          \\ gs [] \\ pop_assum kall_tac
          \\ gs [Abbr ‘expr’]
          \\ simp [freevars_rows_of]
          \\ simp [IMAGE_implode_DELETE, implode_explode]
          \\ gs [UNION_COMM])
      \\ CASE_TAC \\ gs []
      \\ rename1 ‘SOME (disjs, fall)’
      \\ last_assum $ qspec_then ‘cexp_size (K 0) fall’ assume_tac
      \\ last_x_assum $ qspec_then ‘cexp_size (K 0) exp’ assume_tac
      \\ gs [cexp_size_def]
      \\ first_x_assum $ qspec_then ‘exp’ assume_tac
      \\ first_x_assum $ qspec_then ‘fall’ assume_tac
      \\ last_x_assum $ qspec_then ‘compute_freevars fall’ assume_tac
      \\ gs [union_thm, delete_thm]
      \\ gs [exp_of_def, freevars_def]
      \\ qmatch_goalsub_abbrev_tac ‘Seq Fail expr’
      \\ ‘freevars (if MEM m (FLAT (MAP (FST o SND) rows)) then (Seq Fail expr) else expr) = freevars expr’
        by (IF_CASES_TAC \\ gs [freevars_def])
      \\ gs [] \\ pop_assum kall_tac
      \\ gs [Abbr ‘expr’]
      \\ simp [freevars_rows_of]
      \\ simp [IMAGE_UNION, UNION_DELETE]
      \\ simp [IfDisj_def, freevars_Disj, freevars_def, UNION_DELETE]
      \\ simp [IMAGE_implode_DELETE, implode_explode]
      \\ simp [GSYM UNION_ASSOC, UNION_COMM]
      \\ rpt $ pop_assum kall_tac
      \\ gvs [SET_EQ_SUBSET, SUBSET_DEF])
QED

Theorem compute_is_subset_lemma_F:
  ∀m m2.
    ¬foldrWithKey (λid (() : unit) b. case lookup m2 id of
                            | NONE => F
                            | SOME () => b) F (Map mlstring$compare m)
Proof
  Induct \\ gs [to_fmap_def, foldrWithKey_def, balanced_mapTheory.foldrWithKey_def]
  \\ rw []
  \\ CASE_TAC \\ gs []
QED

Theorem compute_is_subset_lemma_T:
  ∀m m2.
    map_ok m2 ∧
    foldrWithKey (λid (() : unit) b. case lookup m2 id of
                            | NONE => F
                            | SOME () => b) T (Map mlstring$compare m) ⇒
    FDOM (to_fmap (Map mlstring$compare m)) ⊆ FDOM $ to_fmap m2
Proof
  Induct \\ gs [to_fmap_def, foldrWithKey_def, balanced_mapTheory.foldrWithKey_def]
  \\ rpt $ gen_tac
  \\ CASE_TAC
  >- (strip_tac
      \\ assume_tac compute_is_subset_lemma_F
      \\ gs [foldrWithKey_def])
  \\ rename1 ‘foldrWithKey _ (foldrWithKey _ T m')’
  \\ Cases_on ‘foldrWithKey (λid () b. case lookup m2 id of
                                       | NONE => F
                                       | SOME () => b) T m'’
  \\ strip_tac \\ gs []
  >- gs [lookup_thm, FLOOKUP_DEF]
  \\ assume_tac compute_is_subset_lemma_F
  \\ gs [foldrWithKey_def]
QED

Theorem compute_is_subset_soundness:
  ∀m1 m2. compute_is_subset m1 m2 ∧ map_ok m2 ∧ cmp_of m1 = mlstring$compare ⇒
          (FDOM $ to_fmap m1) ⊆ (FDOM $ to_fmap m2)
Proof
  Cases \\ rw [cmp_of_def]
  \\ irule compute_is_subset_lemma_T
  \\ gs [compute_is_subset_def]
QED

Theorem compute_is_disjoint_lemma_F:
  ∀m m2.
    ¬foldrWithKey (λid (() : unit) b. case lookup m2 id of
                            | NONE => b
                            | SOME () => F) F (Map mlstring$compare m)
Proof
  Induct \\ gs [to_fmap_def, foldrWithKey_def, balanced_mapTheory.foldrWithKey_def]
  \\ rw []
  \\ CASE_TAC \\ gs []
QED

Theorem compute_is_disjoint_lemma_T:
  ∀m m2.
    map_ok m2 ∧
    foldrWithKey (λid (() : unit) b. case lookup m2 id of
                            | NONE => b
                            | SOME () => F) T (Map mlstring$compare m) ⇒
    DISJOINT (FDOM (to_fmap (Map mlstring$compare m))) (FDOM $ to_fmap m2)
Proof
  Induct \\ gs [to_fmap_def, foldrWithKey_def, balanced_mapTheory.foldrWithKey_def]
  \\ rpt $ gen_tac
  \\ CASE_TAC
  >~[‘lookup _ _ = SOME _’]
  >- (strip_tac
      \\ assume_tac compute_is_disjoint_lemma_F
      \\ gs [foldrWithKey_def])
  \\ rename1 ‘foldrWithKey _ (foldrWithKey _ T m')’
  \\ Cases_on ‘foldrWithKey (λid () b. case lookup m2 id of
                                       | NONE => b
                                       | SOME () => F) T m'’
  \\ strip_tac \\ gs []
  >- gs [lookup_thm, FLOOKUP_DEF]
  \\ assume_tac compute_is_disjoint_lemma_F
  \\ gs [foldrWithKey_def]
QED

Theorem compute_is_disjoint_soundness:
  ∀m1 m2. compute_is_disjoint m1 m2 ∧ map_ok m2 ∧ cmp_of m1 = mlstring$compare ⇒
          DISJOINT (FDOM $ to_fmap m1) (FDOM $ to_fmap m2)
Proof
  Cases \\ rw [cmp_of_def]
  \\ irule compute_is_disjoint_lemma_T
  \\ gs [compute_is_disjoint_def]
QED

Theorem are_valid_soundness_lemma:
  ∀(l : mlstring list) m. m = FOLDR (λv m. insert m v ()) (empty compare) l ⇒
                     map_ok m ∧ cmp_of m = compare ∧ FDOM (to_fmap m) = set l
Proof
  Induct \\ gs [empty_thm, TotOrd_compare]
  \\ gs [insert_thm]
QED

Theorem are_valid_soundness:
  ∀m args body.
    are_valid m args body ∧ map_ok m ∧ cmp_of m = compare ∧ NestedCase_free body ⇒
    DISJOINT (set args) (FDOM $ to_fmap m) ∧
    freevars (exp_of body) ⊆ (IMAGE explode (set args)) ∪ IMAGE explode (FDOM $ to_fmap m)
Proof
  gs [are_valid_def]
  \\ rpt $ gen_tac \\ strip_tac
  \\ dxrule_then assume_tac compute_is_disjoint_soundness
  \\ dxrule_then assume_tac compute_is_subset_soundness
  \\ assume_tac are_valid_soundness_lemma
  \\ qspec_then ‘body’ assume_tac $ GEN_ALL compute_freevars_soundness
  \\ gs [DISJOINT_SYM]
  \\ first_x_assum $ qspec_then ‘args’ assume_tac
  \\ gs [union_thm]
  \\ gs [SUBSET_DEF, PULL_EXISTS]
  \\ rw []
  \\ last_x_assum $ drule_then assume_tac
  \\ gs []
  >- (disj2_tac \\ first_x_assum $ irule_at Any
      \\ gs [explode_implode])
  >- (disj1_tac \\ first_x_assum $ irule_at Any
      \\ gs [explode_implode])
QED

Theorem can_compute_fixpoint_lemma:
  ∀binds m.
    FOLDR (λ(v, p1, p2) m. insert m v ()) (empty compare) (MAP (λ(v, body). (v, split_body body)) binds) = m ⇒
    FDOM (to_fmap m) = set (MAP FST binds) ∧ map_ok m ∧ cmp_of m = compare
Proof
  Induct \\ gs [empty_thm, TotOrd_compare, FORALL_PROD]
  \\ rpt $ gen_tac
  \\ pairarg_tac \\ gs [insert_thm]
QED

Theorem can_compute_fixpoint_soundness:
  ∀binds1 binds2.
    can_compute_fixpoint binds1 = (T, binds2) ∧ EVERY (λ(v, e). NestedCase_free e) binds1 ∧
    ALL_DISTINCT (MAP FST binds1) ⇒
    ∀binds1b binds2b bLfull.
      LIST_REL (λbL (_, args, _). LENGTH bL = LENGTH args) bLfull binds2 ∧
      binds1b = MAP (λ(v, e). (explode v, exp_of e)) binds1 ∧
      binds2b = MAP2 (λbL (v, args, e, label). (explode v, ZIP (MAP explode args, bL), exp_of e)) bLfull binds2
      ⇒ binds1b = MAP mk_lams binds2b ∧
        ∀v args body.
          MEM (v, args, body) binds2b ⇒
          ALL_DISTINCT (MAP FST args) ∧
          DISJOINT (set (MAP FST args)) (set (MAP FST binds2b)) ∧
          freevars body ⊆ set (MAP FST binds2b) ∪ set (MAP FST args)
Proof
  gs [can_compute_fixpoint_def]
  \\ gen_tac \\ gen_tac
  \\ IF_CASES_TAC \\ gs []
  \\ strip_tac
  \\ gen_tac \\ strip_tac
  \\ conj_tac
  >- (irule LIST_EQ
      \\ gs [EL_MAP, LIST_REL_EL_EQN]
      \\ rw [] \\ pairarg_tac \\ gs [EL_MAP2, EL_MAP]
      \\ pairarg_tac \\ gs []
      \\ rename1 ‘split_body e’
      \\ qspec_then ‘e’ assume_tac split_body_soundness
      \\ first_x_assum $ dxrule_then assume_tac
      \\ gs [])
  \\ rpt $ gen_tac \\ strip_tac
  \\ gs []
  \\ gs [EVERY_EL, MEM_EL, EL_MAP2, LIST_REL_EL_EQN]
  \\ rpt $ last_x_assum $ drule_then assume_tac
  \\ gs [EL_MAP]
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ dxrule_then assume_tac are_valid_soundness
  \\ dxrule_then assume_tac compute_ALL_DISTINCT_soundness
  \\ gvs [MAP_ZIP, MAP2_ZIP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
  \\ ‘(λ(p1 : bool list, p1', p1'' : mlstring list, p2 : α cexp). explode p1') = explode o FST o SND’
    by (gvs [combinTheory.o_DEF, LAMBDA_PROD])
  \\ gs [GSYM MAP_MAP_o, MAP_ZIP]
  \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
  \\ rename1 ‘FOLDR _ (empty compare) (MAP _ binds1)’
  \\ last_x_assum $ drule_then assume_tac
  \\ pairarg_tac \\ gvs [EL_MAP]
  \\ qspec_then ‘binds1’ assume_tac can_compute_fixpoint_lemma
  \\ rename1 ‘split_body body = (args', body2, label)’
  \\ rename1 ‘LENGTH (EL n bLfull) = LENGTH _’
  \\ qspecl_then [‘body’, ‘args'’, ‘EL n bLfull’] assume_tac split_body_soundness
  \\ gvs []
  \\ conj_tac
  >- (gs [DISJOINT_ALT, PULL_EXISTS, MEM_MAP, FORALL_PROD, GSYM LAMBDA_PROD]
      \\ rw []
      \\ last_x_assum $ dxrule_then assume_tac
      \\ strip_tac
      \\ first_x_assum irule
      \\ gvs [MEM_EL, EL_MAP, EL_ZIP]
      \\ first_assum $ irule_at Any
      \\ pairarg_tac \\ gs [])
  \\ gvs [SUBSET_DEF, PULL_EXISTS, MEM_MAP, EXISTS_PROD, GSYM LAMBDA_PROD]
  \\ rw [] \\ last_x_assum $ dxrule_then assume_tac
  \\ gs []
  \\ disj1_tac \\ gs [MEM_EL]
  \\ first_assum $ irule_at Any
  \\ rw [EL_ZIP, EL_MAP]
  \\ pairarg_tac \\ gs []
  \\ rename1 ‘split_body body'’
  \\ Cases_on ‘body'’
  \\ gs [split_body_def]
QED

Theorem fixpoint1_App_lemma1:
  ∀l binds e c ds.
    find_fixpoint binds e c ds {} [] ⇒ find_fixpoint binds (Apps e l) c ds {} []
Proof
  Induct \\ gs [Apps_def]
  \\ rw [] \\ last_x_assum irule
  \\ irule find_fixpoint_App
  \\ first_x_assum $ irule_at Any
  \\ irule_at Any find_fixpoint_refl
QED

Theorem cexp10_size_SNOC:
  ∀l x f. cexp10_size f (SNOC x l) = 1 + cexp10_size f l + cexp_size f x
Proof
  Induct \\ gs [cexp_size_def]
QED

Theorem fixpoint1_App_lemma2:
  ∀(l : α cexp list).
    (∀m. m < cexp10_size (K 0) l ⇒
         ∀(e : α cexp). m = cexp_size (K 0) e ⇒
             ∀fds c ds fd binds.
               fixpoint1 c e fds = (ds,fd) ∧ map_ok fds ∧
               cmp_of fds = compare ∧ cexp_wf e ∧
               (∀v. v ∈ FDOM (to_fmap fds) ⇒
                    ∃args body.
                      LENGTH args = LENGTH (to_fmap fds ' v) ∧
                      MEM (explode v,ZIP (args,to_fmap fds ' v),body) binds) ⇒
               map_ok ds ∧ cmp_of ds = compare ∧
               ∀l dwas. (case fd of
                           NONE => l = [] ∧ dwas = empty compare
                         | SOME (l',dwas') =>
                             l = l' ∧ dwas = dwas') ⇒
                        find_fixpoint binds (exp_of e) (ctxt_trans c)
                                      (IMAGE explode (FDOM (to_fmap ds)))
                                      (IMAGE explode (FDOM (to_fmap dwas))) l ∧
                        map_ok dwas ∧ cmp_of dwas = compare) ⇒
    ∀bL c fds bL2 ds2 binds.
      fixpoint_demands_App bL (MAP (λe. fixpoint1 c e fds) l) = (bL2, ds2) ∧
      EVERY (λa. cexp_wf a) l ∧
      (∀v. v ∈ FDOM (to_fmap fds) ⇒
           ∃args body. LENGTH args = LENGTH (to_fmap fds ' v) ∧
                       MEM (explode v, ZIP (args, to_fmap fds ' v), body) binds) ∧
      map_ok fds ∧ cmp_of fds = compare ⇒
      map_ok ds2 ∧ cmp_of ds2 = compare ∧
      ∀e ds1 ads ds3 ads2.
        find_fixpoint binds e (ctxt_trans c) ds1 ads bL ∧
        (if bL2 = [] then (ads ∪ IMAGE explode (FDOM (to_fmap ds2)), {})
         else ({}, ads ∪ IMAGE explode (FDOM (to_fmap ds2)))) = (ds3, ads2) ⇒
        find_fixpoint binds (Apps e (MAP exp_of l)) (ctxt_trans c)
                      (ds1 ∪ ds3) ads2 bL2
Proof
  Induct \\ gs [Apps_def]
  >- (strip_tac \\ Cases
      \\ gs [fixpoint_demands_App_def, empty_thm, TotOrd_compare]
      \\ rw []
      \\ gs [find_fixpoint_App_empty])
  \\ gen_tac \\ strip_tac
  \\ last_x_assum mp_tac
  \\ impl_tac
  >- (gen_tac \\ strip_tac
      \\ rename1 ‘val < _’
      \\ first_x_assum $ qspec_then ‘val’ assume_tac
      \\ gs [cexp_size_def])
  \\ rename1 ‘x::l’
  \\ last_x_assum $ qspec_then ‘cexp_size (K 0) x’ assume_tac
  \\ gs [cexp_size_def]
  \\ first_x_assum $ qspec_then ‘x’ assume_tac
  \\ gs []
  \\ strip_tac \\ rpt $ gen_tac \\ strip_tac
  \\ rename1 ‘fixpoint_demands_App bL’
  \\ Cases_on ‘bL’ \\ gs [fixpoint_demands_App_def]
  >- (gs [empty_thm, TotOrd_compare]
      \\ rw []
      \\ irule fixpoint1_App_lemma1
      \\ irule find_fixpoint_App
      \\ irule_at Any find_fixpoint_refl
      \\ irule_at Any find_fixpoint_App_empty
      \\ first_x_assum $ irule_at Any)
  \\ rename1 ‘fixpoint_demands_App (b::bL) (fixpoint1 c x fds::_)’
  \\ Cases_on ‘fixpoint1 c x fds’ \\ gs []
  \\ Cases_on ‘b’
  \\ gs [fixpoint_demands_App_def]
  >- (pairarg_tac \\ gs []
      \\ rename1 ‘fixpoint1 _ _ _ = (map1, opt)’
      \\ last_x_assum $ dxrule_then assume_tac
      \\ last_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ last_x_assum $ drule_then assume_tac
      \\ last_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ qpat_x_assum ‘union _ _ = _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM
      \\ Cases_on ‘opt’ \\ gs [union_thm]
      >- (rw []
          \\ dxrule_then (dxrule_then assume_tac) find_fixpoint_App_T
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gvs [GSYM UNION_ASSOC])
      \\ qpat_x_assum ‘∀l dwas. _ ⇒ _’ mp_tac
      \\ CASE_TAC \\ gs []
      \\ strip_tac
      \\ gs [union_thm]
      \\ rw []
      \\ dxrule_then (dxrule_then assume_tac) find_fixpoint_App_T
      \\ first_x_assum $ dxrule_then assume_tac
      \\ gvs [GSYM UNION_ASSOC])
  \\ first_x_assum $ dxrule_then assume_tac
  \\ first_x_assum $ dxrule_then assume_tac
  \\ gs []
  \\ rw []
  >- (first_x_assum irule
      \\ irule find_fixpoint_App_F
      \\ simp []
      \\ irule_at Any find_fixpoint_refl)
  \\ gs []
  \\ first_x_assum irule
  \\ irule find_fixpoint_App_F
  \\ simp []
  \\ irule_at Any find_fixpoint_refl
QED

Theorem fixpoint1_AtomOp_lemma:
  ∀eL.
    (∀(e : α cexp). MEM e eL ⇒
              ∀fds c ds fd binds.
                fixpoint1 c e fds = (ds,fd) ∧ map_ok fds ∧
                cmp_of fds = compare ∧ cexp_wf e ∧
                (∀v. v ∈ FDOM (to_fmap fds) ⇒
                     ∃args body.
                       LENGTH args = LENGTH (to_fmap fds ' v) ∧
                       MEM (explode v,ZIP (args,to_fmap fds ' v),body) binds) ⇒
                map_ok ds ∧ cmp_of ds = compare ∧
                ∀l dwas.
                  (case fd of
                     NONE => l = [] ∧ dwas = empty compare
                   | SOME (l',dwas') => l = l' ∧ dwas = dwas') ⇒
                  find_fixpoint binds (exp_of e) (ctxt_trans c)
                                (IMAGE explode (FDOM (to_fmap ds)))
                                (IMAGE explode (FDOM (to_fmap dwas))) l ∧
                  map_ok dwas ∧ cmp_of dwas = compare) ⇒
    ∀c fds binds l m.
      (∀v. v ∈ FDOM (to_fmap fds) ⇒
           ∃args body.
             LENGTH args = LENGTH (to_fmap fds ' v) ∧
             MEM (explode v,ZIP (args,to_fmap fds ' v),body) binds) ∧
      EVERY (λa. cexp_wf a) eL ∧
      map_ok fds ∧ cmp_of fds = compare ∧
      l = MAP (λe. fixpoint1 c e fds) eL ∧
      m = FOLDR (λ(ds, _) m. union ds m) (empty compare) l ⇒
      EVERY (λ(ds, _). map_ok ds ∧ cmp_of ds = compare) l ∧
      LIST_REL (λe ds. find_fixpoint binds e (ctxt_trans c) ds {} [])
               (MAP exp_of eL) (MAP (λ(ds, _). IMAGE explode (FDOM $ to_fmap ds)) l) ∧
      map_ok m ∧ cmp_of m = compare ∧
      FDOM (to_fmap m) = BIGUNION (set (MAP (λ(ds, _). FDOM $ to_fmap ds) l))
Proof
  Induct \\ gs [empty_thm, TotOrd_compare]
  \\ gen_tac \\ strip_tac
  \\ last_x_assum mp_tac
  \\ impl_tac
  >- (gen_tac \\ strip_tac
      \\ rename1 ‘MEM e _’
      \\ first_x_assum $ qspec_then ‘e’ assume_tac
      \\ gs [])
  \\ strip_tac
  \\ rename1 ‘_ = h ∨ MEM _ eL’
  \\ first_x_assum $ qspec_then ‘h’ assume_tac
  \\ rpt gen_tac \\ strip_tac
  \\ gs []
  \\ pairarg_tac \\ gs []
  \\ first_x_assum $ dxrule_then assume_tac
  \\ last_x_assum $ drule_then assume_tac
  \\ gs []
  \\ first_x_assum $ dxrule_then mp_tac
  \\ gs []
  \\ CASE_TAC \\ gs [union_thm, empty_thm, TotOrd_compare]
  \\ CASE_TAC \\ gs [union_thm]
  \\ strip_tac
  \\ irule find_fixpoint_drop_fd
  \\ first_x_assum $ irule_at Any
QED

Theorem FOLDR_delete:
  ∀vs m. map_ok m ∧ cmp_of m = compare ⇒
         map_ok (FOLDR (λv m. delete m v) m vs) ∧
         cmp_of (FOLDR (λv m. delete m v) m vs) = mlstring$compare ∧
         FDOM (to_fmap (FOLDR (λv m. delete m v) m vs)) = (FDOM $ to_fmap m) ∩ COMPL (set vs) ∧
         (∀v. ¬MEM v vs ⇒ to_fmap (FOLDR (λv m. delete m v) m vs) ' v = to_fmap m ' v)
Proof
  Induct \\ gvs [delete_thm]
  \\ rw []
  \\ gvs [SET_EQ_SUBSET, SUBSET_DEF]
  \\ gs [DOMSUB_FAPPLY_THM]
QED

Theorem find_fixpoint_lets_for:
  ∀(vs : (num # string) list) binds e cn v c ds.
    find_fixpoint binds e (FOLDL (λc (_, n). (IsFree n (c : ctxt) : ctxt)) c vs) ds {} [] ∧
    (∀v. MEM v (MAP SND vs) ⇒ ¬MEM v (MAP FST binds)) ⇒
    find_fixpoint binds (lets_for cn v vs e) c (ds ∩ COMPL (set (MAP SND vs))) {} []
Proof
  Induct \\ gs [lets_for_def, FORALL_PROD]
  \\ rw []
  \\ irule find_fixpoint_Let
  \\ gs []
  \\ irule_at Any find_fixpoint_refl
  \\ irule find_fixpoint_Subset
  \\ rename [‘FILTER _ binds’, ‘_ = p_2 ∨ MEM _ _’]
  \\ ‘FILTER (λ(v, _). v ≠ p_2) binds = binds’
    by (gs [FILTER_EQ_ID]
        \\ gvs [EVERY_MEM, FORALL_PROD]
        \\ first_x_assum $ qspec_then ‘p_2’ assume_tac
        \\ gs [MEM_MAP])
  \\ gvs []
  \\ last_x_assum $ irule_at Any
  \\ first_x_assum $ irule_at Any
  \\ gs [SUBSET_DEF]
QED

Theorem FOLDL_IsFree_MAPi:
  ∀vs c. FOLDL (λc (_, n). (IsFree n c : ctxt)) c (MAPi (λi v. (i, explode v)) vs)
         = FOLDL (λc n. IsFree (explode n) c) c vs
Proof
  Induct using SNOC_INDUCT \\ gs [FOLDL_APPEND, SNOC_APPEND, indexedListsTheory.MAPi_APPEND]
QED

Theorem IMAGE_explode_DIFF:
  ∀s1 s2. IMAGE explode (s1 DIFF s2) = (IMAGE explode s1) DIFF (IMAGE explode s2)
Proof
  gs [SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
QED

Theorem fixpoint1_Case_lemma:
  ∀rows.
    (∀v vL (e : α cexp). MEM (v, vL, e) rows ⇒
              ∀fds c ds fd binds.
                fixpoint1 c e fds = (ds,fd) ∧ map_ok fds ∧
                cmp_of fds = compare ∧ cexp_wf e ∧
                (∀v. v ∈ FDOM (to_fmap fds) ⇒
                     ∃args body.
                       LENGTH args = LENGTH (to_fmap fds ' v) ∧
                       MEM (explode v,ZIP (args,to_fmap fds ' v),body) binds) ⇒
                map_ok ds ∧ cmp_of ds = compare ∧
                ∀l dwas.
                  (case fd of
                     NONE => l = [] ∧ dwas = empty compare
                   | SOME (l',dwas') => l = l' ∧ dwas = dwas') ⇒
                  find_fixpoint binds (exp_of e) (ctxt_trans c)
                                (IMAGE explode (FDOM (to_fmap ds)))
                                (IMAGE explode (FDOM (to_fmap dwas))) l ∧
                  map_ok dwas ∧ cmp_of dwas = compare) ⇒
    ∀binds fds c l v.
      (∀v. v ∈ FDOM (to_fmap fds) ⇒
           ∃args body.
             LENGTH args = LENGTH (to_fmap fds ' v) ∧
             MEM (explode v,ZIP (args,to_fmap fds ' v),body) binds) ∧
      map_ok fds ∧ cmp_of fds = compare ∧
      EVERY (λa. cexp_wf a) (MAP (SND o SND) rows) ∧
      l = MAP (λ(cons, vL, (e : α cexp)).
                 FOLDR (λv m. delete m v)
                       (FST (fixpoint1 (IsFree vL c) e
                             (FOLDR (λv m. delete m v) fds vL))) vL) rows ⇒
      LIST_REL (λ(cn, vs, e) ds.
                  map_ok ds ∧ cmp_of ds = compare ∧
                  find_fixpoint binds (lets_for (explode cn) (explode v)
                                       (MAPi (λi v. (i, explode v)) vs) (exp_of e))
                                (ctxt_trans c)
                                (IMAGE explode (FDOM $ to_fmap ds)) {} []) rows l
Proof
  Induct \\ gs []
  \\ rw []
  >- (pairarg_tac \\ gs []
      \\ rename1 ‘lets_for (explode cn) (explode v) (MAPi _ vs) (exp_of e)’
      \\ first_x_assum $ qspecl_then [‘cn’, ‘vs’, ‘e’] assume_tac
      \\ gs []
      \\ qmatch_goalsub_abbrev_tac ‘map_ok (FOLDR _ (FST m1) _)’
      \\ PairCases_on ‘m1’ \\ gs []
      \\ first_x_assum $ drule_then assume_tac
      \\ gs [delete_thm, FOLDR_delete]
      \\ rename1 ‘fixpoint1 _ _ _ = (_, opt)’
      \\ Cases_on ‘opt’ \\ gs []
      >- (pop_assum $ qspec_then ‘FILTER (λ(v, _). ¬MEM v (MAP explode vs)) binds’
          mp_tac
          \\ impl_tac
          >- (rw []
              \\ first_x_assum $ dxrule_then assume_tac
              \\ gs [MEM_FILTER, MEM_MAP, DOMSUB_FAPPLY_THM]
              \\ first_x_assum $ irule_at Any
              \\ simp [])
          \\ strip_tac
          \\ gs [FOLDR_delete, ctxt_trans_def]
          \\ rename1 ‘find_fixpoint binds (lets_for (explode cn) (explode v) (MAPi _ vs) (exp_of e))
                      (ctxt_trans c)’
          \\ qspecl_then [‘MAPi (λi v. (i, explode v)) vs’,
                          ‘FILTER (λ(v, _). ¬MEM v (MAP explode vs)) binds’,
                          ‘exp_of e’, ‘explode cn’, ‘explode v’,
                          ‘ctxt_trans c’] assume_tac find_fixpoint_lets_for
          \\ gs [FOLDL_IsFree_MAPi, empty_thm, TotOrd_compare]
          \\ first_x_assum $ dxrule_then mp_tac
          \\ impl_tac
          >- (rw []
              \\ dxrule_then assume_tac $ iffLR MEM_EL
              \\ gs [EL_MAP, indexedListsTheory.EL_MAPi]
              \\ strip_tac
              \\ gs [MEM_MAP, MEM_FILTER]
              \\ pairarg_tac \\ gs []
              \\ rw []
              \\ first_x_assum $ resolve_then Any assume_tac EQ_REFL
              \\ gvs [EL_MEM])
          \\ gs [combinTheory.o_DEF, LAMBDA_PROD]
          \\ strip_tac \\ gs []
          \\ irule find_fixpoint_smaller_binds
          \\ qexists_tac ‘λv. ¬MEM v (MAP explode vs)’
          \\ gs [LIST_TO_SET_MAP, IMAGE_explode_DIFF, GSYM DIFF_INTER_COMPL]
          \\ simp [LAMBDA_PROD])
      \\ pop_assum mp_tac
      \\ CASE_TAC \\ gs []
      \\ disch_then $ qspec_then ‘FILTER (λ(v, _). ¬MEM v (MAP explode vs)) binds’
                    mp_tac
      \\ impl_tac
      >- (rw []
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gs [MEM_FILTER, MEM_MAP, DOMSUB_FAPPLY_THM]
          \\ first_x_assum $ irule_at Any
          \\ simp [])
      \\ strip_tac
      \\ gs [FOLDR_delete, ctxt_trans_def]
      \\ rename1 ‘find_fixpoint binds (lets_for (explode cn) (explode v) (MAPi _ vs) (exp_of e))
                  (ctxt_trans c)’
      \\ qspecl_then [‘MAPi (λi v. (i, explode v)) vs’,
                      ‘FILTER (λ(v, _).  ¬MEM v (MAP explode vs)) binds’,
                      ‘exp_of e’, ‘explode cn’, ‘explode v’,
                      ‘ctxt_trans c’] assume_tac find_fixpoint_lets_for
      \\ gs [FOLDL_IsFree_MAPi, empty_thm, TotOrd_compare]
      \\ gs [combinTheory.o_DEF, LAMBDA_PROD]
      \\ irule find_fixpoint_smaller_binds
      \\ qexists_tac ‘λv. ¬MEM v (MAP explode vs)’
      \\ gs [LIST_TO_SET_MAP, IMAGE_explode_DIFF, GSYM DIFF_INTER_COMPL]
      \\ simp [LAMBDA_PROD]
      \\ first_x_assum irule
      \\ rw []
      >- (gs [MEM_FILTER]
          \\ pairarg_tac \\ gs [])
      \\ irule find_fixpoint_drop_fd
      \\ first_x_assum $ irule_at Any)
  \\ last_x_assum irule
  \\ simp []
  \\ rpt gen_tac \\ strip_tac
  \\ rename1 ‘MEM (v, vL, e) _’
  \\ last_x_assum $ qspecl_then [‘v’, ‘vL’, ‘e’] assume_tac
  \\ gvs []
QED

Theorem fixpoint1_Case_rows_of_Fail:
  ∀rows dsL n binds c v.
    rows ≠ [] ∧
    LIST_REL (λ(cn, vs, e) ds. find_fixpoint binds (lets_for cn v (MAPi (λi v. (i, v)) vs) e)
                                             c ds {} []) rows dsL
    ⇒ find_fixpoint binds (rows_of v Fail rows) c ({v} ∪ BIGINTER (set dsL)) {} []
Proof
  Induct \\ gs [FORALL_PROD, rows_of_def]
  \\ rw []
  \\ rename1 ‘rows ≠ []’
  \\ Cases_on ‘rows = []’ \\ gs [rows_of_def]
  >- (irule_at Any find_fixpoint_If_Fail
      \\ first_x_assum $ irule_at Any
      \\ irule_at Any find_fixpoint_IsEq
      \\ irule_at Any find_fixpoint_Var)
  \\ irule_at Any find_fixpoint_If
  \\ last_x_assum $ irule_at Any
  \\ irule_at Any find_fixpoint_IsEq
  \\ irule_at Any find_fixpoint_Var
  \\ last_x_assum $ dxrule_then assume_tac
  \\ irule_at Any find_fixpoint_Subset
  \\ first_x_assum $ irule_at Any
  \\ gs []
QED

Theorem fixpoint1_Case_rows_of_expr:
  ∀rows dsL n binds c v e ds.
    rows ≠ [] ∧
    LIST_REL (λ(cn, vs, e) ds. find_fixpoint binds (lets_for cn v (MAPi (λi v. (i, v)) vs) e)
                                             c ds {} []) rows dsL ∧
    find_fixpoint binds e c ds {} []
    ⇒ find_fixpoint binds (rows_of v e rows) c ({v} ∪ BIGINTER (set dsL) ∩ ds) {} []
Proof
  Induct \\ gs [FORALL_PROD, rows_of_def]
  \\ rw []
  \\ rename1 ‘rows ≠ []’
  \\ Cases_on ‘rows = []’ \\ gs [rows_of_def]
  >- (irule_at Any find_fixpoint_If
      \\ first_x_assum $ irule_at Any
      \\ first_x_assum $ irule_at Any
      \\ irule_at Any find_fixpoint_IsEq
      \\ irule_at Any find_fixpoint_Var)
  \\ simp [GSYM INTER_ASSOC]
  \\ irule_at Any find_fixpoint_If
  \\ last_x_assum $ irule_at Any
  \\ irule_at Any find_fixpoint_IsEq
  \\ irule_at Any find_fixpoint_Var
  \\ last_x_assum $ dxrule_then assume_tac
  \\ irule_at Any find_fixpoint_Subset
  \\ first_x_assum $ irule_at Any
  \\ first_x_assum $ irule_at Any
  \\ gs []
QED

Theorem FOLDR_lookup_soundness:
  ∀mL id. EVERY (λm'. map_ok m' ∧ cmp_of m' = mlstring$compare) mL ∧
          FOLDR (λm' b. b ∧ lookup m' id = SOME ()) T mL ⇒
          EVERY (λm'. id ∈ FDOM $ to_fmap m') mL
Proof
  Induct \\ gs []
  \\ rw []
  \\ gs [lookup_thm, FLOOKUP_DEF]
QED

Theorem FOLDR_lookup_soundness2:
  ∀mL id. EVERY (λm'. map_ok m' ∧ cmp_of m' = mlstring$compare) mL ∧
          ¬FOLDR (λm' b. b ∧ lookup m' id = SOME ()) T mL ⇒
          EXISTS (λm'. id ∉ FDOM $ to_fmap m') mL
Proof
  Induct \\ gs []
  \\ rw []
  \\ gs [lookup_thm, FLOOKUP_DEF, DISJ_EQ_IMP]
QED

Theorem fixpoint1_Case_lemma2_inner:
  ∀m m2 mL m3.
    EVERY (λm'. map_ok m' ∧ cmp_of m' = compare) mL ∧
    map_ok m2 ∧ cmp_of m2 = mlstring$compare ∧
    m3 = foldrWithKey (λid _ m. if FOLDR (λm' b. b ∧ lookup m' id = SOME ()) T mL
                                 then insert m id ()
                                 else m) m2 (Map compare m) ⇒
    map_ok m3 ∧ cmp_of m3 = compare ∧
    FDOM $ to_fmap m3
    = (FDOM $ to_fmap m2) ∪ ((BIGINTER $ set (MAP (λm'. FDOM $ to_fmap m') mL))
                                              ∩ (FDOM $ to_fmap (Map compare m)))
Proof
  Induct \\ gs [foldrWithKey_def, balanced_mapTheory.foldrWithKey_def]
  >- rw [TotOrd_compare, to_fmap_def]
  \\ rpt $ gen_tac \\ strip_tac \\ gs []
  \\ IF_CASES_TAC \\ gs []
  >- (rename1 ‘map_ok m2’
      \\ first_x_assum $ drule_then $ qspecl_then [‘m2’] assume_tac
      \\ qmatch_goalsub_abbrev_tac ‘insert m3 k ()’
      \\ first_x_assum $ drule_then $ qspecl_then [‘insert m3 k ()’] assume_tac
      \\ gvs [insert_thm]
      \\ gs [to_fmap_def]
      \\ dxrule_all_then mp_tac FOLDR_lookup_soundness
      \\ rpt $ pop_assum kall_tac
      \\ gs [SET_EQ_SUBSET, SUBSET_DEF]
      \\ rw [] \\ gvs []
      \\ gs [EVERY_MEM, MEM_MAP, PULL_EXISTS])
  \\ gs [to_fmap_def]
  \\ dxrule_all_then mp_tac FOLDR_lookup_soundness2
  \\ rpt $ pop_assum kall_tac
  \\ gvs [SET_EQ_SUBSET, SUBSET_DEF]
  \\ rw [] \\ gvs [EXISTS_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem fixpoint1_Case_lemma2:
  ∀m m2 mL m3.
    EVERY (λm'. map_ok m' ∧ cmp_of m' = compare) mL ∧
    map_ok m2 ∧ cmp_of m2 = mlstring$compare ∧
    map_ok m ∧ cmp_of m = compare ∧
    m3 = foldrWithKey (λid _ m. if FOLDR (λm' b. b ∧ lookup m' id = SOME ()) T mL
                                 then insert m id ()
                                 else m) m2 m ⇒
    map_ok m3 ∧ cmp_of m3 = compare ∧
    FDOM $ to_fmap m3
    = (FDOM $ to_fmap m2) ∪ ((BIGINTER $ set (MAP (λm'. FDOM $ to_fmap m') mL))
                                              ∩ (FDOM $ to_fmap m))
Proof
  Cases \\ gvs [cmp_of_def]
  \\ rw []
  \\ pop_assum kall_tac
  \\ dxrule_then (dxrule_then assume_tac) fixpoint1_Case_lemma2_inner
  \\ gs []
QED

Theorem MAPi_MAP_explode:
  MAPi (λi v. (i, v)) (MAP mlstring$explode l) = MAPi (λi v. (i, explode v)) l
Proof
  irule LIST_EQ \\ rw [indexedListsTheory.EL_MAPi, EL_MAP]
QED

Theorem fixpoint1_soundness:
  ∀fds c ds fd binds.
    fixpoint1 c e fds = (ds, fd) ∧
    map_ok fds ∧ cmp_of fds = compare ∧ cexp_wf e ∧
    (∀v. v ∈ FDOM (to_fmap fds) ⇒
         ∃args body. LENGTH args = LENGTH (to_fmap fds ' v) ∧
                     MEM (explode v, ZIP (args, to_fmap fds ' v), body) binds) ⇒
    map_ok ds ∧ cmp_of ds = compare ∧
    ∀l dwas. (case fd of
              | NONE => (l = [] ∧ dwas = empty compare)
              | SOME (l', dwas') => (l = l' ∧ dwas = dwas')) ⇒
             find_fixpoint binds (exp_of e) (ctxt_trans c)
                           (IMAGE explode (FDOM $ to_fmap ds))
                           (IMAGE explode (FDOM $ to_fmap dwas)) l ∧
             map_ok dwas ∧ cmp_of dwas = compare
Proof
  completeInduct_on ‘cexp_size (K 0) e’ \\ gs []
  \\ Cases \\ gs [fixpoint1_def, cexp_wf_def]
  >~[‘Var _’]
  >- (strip_tac \\ rpt $ gen_tac \\ strip_tac
      \\ rename1 ‘lookup fds m’
      \\ Cases_on ‘lookup fds m’
      \\ gs [empty_thm, insert_thm, TotOrd_compare, exp_of_def]
      >- (qpat_x_assum ‘insert _ _ _ = _’ assume_tac
          \\ dxrule_then assume_tac EQ_SYM
          \\ gs [empty_thm, insert_thm, TotOrd_compare, exp_of_def]
          \\ irule find_fixpoint_Var)
      \\ qpat_x_assum ‘SOME _ = _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM
      \\ gs [empty_thm, TotOrd_compare, lookup_thm, FLOOKUP_DEF]
      \\ first_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ drule_then assume_tac find_fixpoint_Var_known
      \\ gs [MAP_ZIP])
  >~[‘App _ c l’]
  >- (strip_tac \\ rpt $ gen_tac \\ strip_tac
      \\ pairarg_tac \\ gs []
      \\ rename1 ‘fixpoint1 _ _ _ = (_, fd1)’
      \\ Cases_on ‘fd1’ \\ gs []
      >- (last_x_assum $ qspec_then ‘cexp_size (K 0) c’ assume_tac
          \\ gs [cexp_size_def]
          \\ pop_assum $ qspec_then ‘c’ assume_tac \\ gs []
          \\ pop_assum $ dxrule_then assume_tac \\ gs []
          \\ pop_assum $ dxrule_then assume_tac \\ gs []
          \\ gs [exp_of_def, empty_thm, TotOrd_compare]
          \\ gs [fixpoint1_App_lemma1])
      \\ rename1 ‘SOME x’ \\ PairCases_on ‘x’ \\ gs []
      \\ qspec_then ‘l’ mp_tac fixpoint1_App_lemma2
      \\ impl_tac
      >- (gen_tac \\ strip_tac
          \\ rename1 ‘val < _’
          \\ last_x_assum $ qspec_then ‘val’ assume_tac
          \\ gs [cexp_size_def])
      \\ strip_tac
      \\ rename1 ‘fixpoint1 ctxt c fds = (_, SOME (bL, ads))’
      \\ Cases_on ‘fixpoint_demands_App bL (MAP (λe. fixpoint1 ctxt e fds) l)’
      \\ first_x_assum $ drule_then assume_tac
      \\ first_x_assum $ drule_then assume_tac
      \\ gs []
      \\ last_x_assum $ qspec_then ‘cexp_size (K 0) c’ assume_tac
      \\ gs [cexp_size_def]
      \\ first_x_assum $ qspec_then ‘c’ assume_tac
      \\ gs []
      \\ first_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ first_x_assum $ drule_then assume_tac
      \\ gs []
      \\ first_x_assum $ dxrule_then assume_tac
      \\ rename1 ‘fixpoint_demands_App _ _ = (q, _)’
      \\ Cases_on ‘q’ \\ gs []
      >- (qpat_x_assum ‘union _ _ = _’ assume_tac
          \\ dxrule_then assume_tac EQ_SYM
          \\ gs [union_thm, empty_thm, TotOrd_compare, exp_of_def]
          \\ gs [SF ETA_ss])
      \\ qpat_x_assum ‘SOME _ = _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM
      \\ gs [exp_of_def, SF ETA_ss, union_thm])
  >~[‘Prim _ op l’]
  >- (Cases_on ‘op’
      >~[‘Cons’]
      >- (rw [empty_thm, TotOrd_compare, fixpoint1_def]
          \\ irule find_fixpoint_refl)
      >~[‘Seq’]
      >- (Cases_on ‘l’
          >~[‘[]’]
          >- (rw [empty_thm, TotOrd_compare, fixpoint1_def]
              \\ irule find_fixpoint_refl)
          \\ rename1 ‘h::t’
          \\ Cases_on ‘t’
          >~[‘[h]’]
          >- (rw [empty_thm, TotOrd_compare, fixpoint1_def]
              \\ irule find_fixpoint_refl)
          \\ rename1 ‘e1::e2::t’
          \\ Cases_on ‘t’
          >~[‘_::_::_::_’]
          >- (rw [empty_thm, TotOrd_compare, fixpoint1_def]
              \\ irule find_fixpoint_refl)
          \\ strip_tac \\ gs [fixpoint1_def, cexp_size_def]
          \\ last_assum $ qspec_then ‘cexp_size (K 0) e1’ assume_tac
          \\ last_x_assum $ qspec_then ‘cexp_size (K 0) e2’ assume_tac
          \\ gs []
          \\ last_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
          \\ last_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
          \\ rpt $ gen_tac \\ strip_tac
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ last_x_assum $ drule_then assume_tac
          \\ last_x_assum $ drule_then assume_tac
          \\ gvs []
          \\ last_x_assum $ drule_then assume_tac
          \\ last_x_assum $ dxrule_then assume_tac
          \\ rename1 ‘fixpoint1 c e1 fds = (_, fd1)’
          \\ Cases_on ‘fd1’
          \\ rename1 ‘fixpoint1 c e2 fds = (_, fd2)’
          \\ Cases_on ‘fd2’
          \\ gs [union_thm, exp_of_def, op_of_def, empty_thm, TotOrd_compare]
          >- (irule find_fixpoint_Seq
              \\ rpt $ first_x_assum $ irule_at Any)
          \\ rename1 ‘SOME x’
          \\ Cases_on ‘x’
          \\ gs [union_thm]
          >- (irule find_fixpoint_Seq
              \\ rpt $ first_x_assum $ irule_at Any)
          >- (irule find_fixpoint_Seq
              \\ rpt $ first_x_assum $ irule_at Any)
          \\ rename1 ‘SOME x’
          \\ Cases_on ‘x’
          \\ gs [union_thm]
          \\ irule find_fixpoint_Seq
          \\ rpt $ first_x_assum $ irule_at Any)
      \\ strip_tac
      \\ gs [fixpoint1_def, empty_thm, TotOrd_compare]
      \\ rpt gen_tac \\ strip_tac
      \\ qspec_then ‘l’ mp_tac fixpoint1_AtomOp_lemma
      \\ impl_tac
      >- (gen_tac \\ strip_tac
          \\ rename1 ‘MEM e _’
          \\ last_x_assum $ qspec_then ‘cexp_size (K 0) e’ assume_tac
          \\ qspec_then ‘K 0’ assume_tac $ GEN_ALL cexp_size_lemma
          \\ gs []
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gs [cexp_size_def]
          \\ first_x_assum $ qspec_then ‘e’ assume_tac
          \\ gs [])
      \\ last_x_assum kall_tac
      \\ disch_then $ dxrule_then assume_tac
      \\ gs [exp_of_def, op_of_def, IMAGE_BIGUNION, GSYM LIST_TO_SET_MAP]
      \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
      \\ rename1 ‘ctxt_trans c’
      \\ first_x_assum $ qspec_then ‘c’ assume_tac
      \\ gs []
      \\ irule find_fixpoint_Atom
      \\ gs [LIST_REL_EL_EQN]
      \\ rw []
      \\ last_x_assum $ drule_then assume_tac
      \\ gs [EL_MAP]
      \\ pairarg_tac \\ gs []
      \\ first_x_assum $ irule_at Any)
  >~[‘Lam _ vL e’]
  >- (rw [empty_thm, TotOrd_compare]
      \\ irule find_fixpoint_refl)
  >~[‘Let _ m e1 e2’]
  >- (strip_tac \\ rpt $ gen_tac \\ strip_tac
      \\ simp [empty_thm, TotOrd_compare]
      \\ irule find_fixpoint_refl)
  >~[‘Letrec _ _ _’]
  >- (rw [empty_thm, TotOrd_compare]
      \\ irule find_fixpoint_refl)
  >~[‘Case _ expr m rows fall’]
  >- (strip_tac \\ gs []
      \\ rpt gen_tac \\ strip_tac
      \\ qspec_then ‘rows’ mp_tac fixpoint1_Case_lemma
      \\ impl_tac
      >- (rpt $ gen_tac \\ strip_tac
          \\ qspec_then ‘K 0’ assume_tac $ GEN_ALL cexp_size_lemma
          \\ gs []
          \\ first_x_assum $ dxrule_then assume_tac
          \\ rename1 ‘cexp_size (K 0) e < _’
          \\ last_x_assum $ qspec_then ‘cexp_size (K 0) e’ assume_tac
          \\ gs [cexp_size_def]
          \\ last_x_assum $ qspec_then ‘e’ assume_tac
          \\ gs [])
      \\ simp []
      \\ rename1 ‘find_fixpoint binds _ (ctxt_trans c)’
      \\ disch_then $ qspecl_then [‘FILTER (λ(v, _). v ≠ explode m) binds’, ‘delete fds m’,
                                   ‘IsFree [m] c’, ‘m’] mp_tac
      \\ impl_tac
      >- simp [delete_thm, DOMSUB_FAPPLY_THM, MEM_FILTER]
      \\ strip_tac
      \\ gs [exp_of_def]
      \\ pairarg_tac \\ gs []
      \\ Cases_on ‘fall’ \\ gs []
      >- (qpat_x_assum ‘(case _ of [] => _ | _::_ => _) = (_, _)’ mp_tac
          \\ CASE_TAC \\ gs []
          \\ strip_tac \\ gs []
          \\ qpat_x_assum ‘union _ _ = _’ assume_tac
          \\ dxrule_then assume_tac EQ_SYM
          \\ gs [empty_thm, TotOrd_compare, union_thm]
          \\ first_x_assum $ qspec_then ‘cexp_size (K 0) expr’ assume_tac
          \\ gs [cexp_size_def]
          \\ first_x_assum $ resolve_then (Pos hd) (drule_then assume_tac) EQ_REFL
          \\ gs []
          \\ pop_assum $ dxrule_then assume_tac
          \\ simp []
          \\ rename1 ‘foldrWithKey  _ (empty compare) map1’
          \\ rename1 ‘FOLDR _ T mL’
          \\ qspecl_then [‘map1’, ‘empty compare’, ‘mL’] mp_tac fixpoint1_Case_lemma2
          \\ simp []
          \\ impl_tac
          >- (pairarg_tac \\ gs []
              \\ simp [empty_thm, TotOrd_compare]
              \\ gs [EVERY_EL, LIST_REL_EL_EQN]
              \\ gen_tac \\ strip_tac
              \\ first_x_assum $ drule_then assume_tac
              \\ gs [EL_MAP]
              \\ pairarg_tac \\ gs [])
          \\ strip_tac
          \\ simp [union_thm, delete_thm]
          \\ irule find_fixpoint_Subset
          \\ irule_at Any find_fixpoint_Let_demands
          \\ simp []
          \\ irule_at Any fixpoint1_Case_rows_of_Fail
          \\ gs [LIST_REL_MAP1, combinTheory.o_DEF, LAMBDA_PROD, ctxt_trans_def]
          \\ ‘find_fixpoint binds (exp_of expr) (ctxt_trans c)
              (IMAGE explode (FDOM (to_fmap $ demands_e))) {} []’
            by (rename1 ‘option_CASE opt _ _ ⇒ find_fixpoint _ (exp_of expr) _ _ _ _ ∧ _ ∧ _’
                \\ Cases_on ‘opt’ \\ gs [empty_thm, TotOrd_compare]
                \\ irule find_fixpoint_drop_fd
                \\ pairarg_tac \\ gs []
                \\ first_x_assum $ irule_at Any)
          \\ pop_assum $ irule_at Any
          \\ qexists_tac ‘MAP (λm. IMAGE explode (FDOM (to_fmap m))) mL’
          \\ qexists_tac ‘IMAGE explode (FDOM $ to_fmap map1)’
          \\ simp []
          \\ conj_tac
          >- (pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ rw [MAPi_MAP_explode])
          \\ conj_tac
          >- (gs [LIST_REL_EL_EQN, EL_MAP]
              \\ gen_tac \\ strip_tac
              \\ last_x_assum $ drule_then assume_tac
              \\ pairarg_tac \\ gs [MAPi_MAP_explode])
          \\ simp [empty_thm, TotOrd_compare]
          \\ simp [SUBSET_DEF, PULL_EXISTS, MEM_MAP])
      \\ pairarg_tac
      \\ gs [empty_thm, TotOrd_compare]
      \\ qpat_x_assum ‘union _ _ = _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM
      \\ gs [empty_thm, TotOrd_compare, union_thm]
      \\ rename1 ‘SOME (disj_cases, fall)’
      \\ first_assum $ qspec_then ‘cexp_size (K 0) expr’ assume_tac
      \\ first_x_assum $ qspec_then ‘cexp_size (K 0) fall’ assume_tac
      \\ gs [cexp_size_def, FST_THM]
      \\ pairarg_tac
      \\ first_x_assum $ resolve_then (Pos hd) (drule_then assume_tac) EQ_REFL
      \\ first_x_assum $ resolve_then (Pos hd) (drule_then assume_tac) EQ_REFL
      \\ gvs []
      \\ first_x_assum $ drule_then assume_tac
      \\ first_x_assum $ qspec_then ‘FILTER (λ(v, _). v ≠ explode m) binds’ mp_tac
      \\ impl_tac
      >- simp [delete_thm, DOMSUB_FAPPLY_THM, MEM_FILTER]
      \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac ‘foldrWithKey _ _ map1’
      \\ qmatch_goalsub_abbrev_tac ‘FOLDR _ T mL’
      \\ qspecl_then [‘map1’, ‘empty compare’, ‘mL’] mp_tac fixpoint1_Case_lemma2
      \\ simp []
      \\ impl_tac
      >- (simp [empty_thm, TotOrd_compare]
          \\ gs [EVERY_EL, LIST_REL_EL_EQN, Abbr ‘mL’]
          \\ gen_tac \\ strip_tac
          \\ first_x_assum $ drule_then assume_tac
          \\ gs [EL_MAP]
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs [])
      \\ gs [union_thm, delete_thm]
      \\ strip_tac
      \\ simp [empty_thm, TotOrd_compare]
      \\ irule find_fixpoint_Subset
      \\ irule_at Any find_fixpoint_Let_demands
      \\ simp []
      \\ irule_at Any fixpoint1_Case_rows_of_expr
      \\ simp [IfDisj_def]
      \\ irule_at Any find_fixpoint_If_Fail
      \\ irule_at (Pos hd) find_fixpoint_refl
      \\ gs [LIST_REL_MAP1, combinTheory.o_DEF, LAMBDA_PROD, ctxt_trans_def]
      \\ ‘find_fixpoint binds (exp_of expr) (ctxt_trans c)
          (IMAGE explode (FDOM (to_fmap $ demands_e))) {} []’
        by (rename1 ‘option_CASE opt _ _ ⇒ find_fixpoint _ (exp_of expr) _ _ _ _ ∧ _ ∧ _’
            \\ Cases_on ‘opt’ \\ gs [empty_thm, TotOrd_compare]
            \\ irule find_fixpoint_drop_fd
            \\ pairarg_tac \\ gs []
            \\ first_x_assum $ irule_at Any)
      \\ pop_assum $ irule_at Any
      \\ qpat_x_assum ‘∀l dwas. option_CASE opt _ _ ⇒
                                find_fixpoint _ (exp_of expr) _ _ _ _ ∧ _ ∧ _’ kall_tac
      \\ ‘find_fixpoint (FILTER (λ(v, p1, p2). v ≠ explode m) binds)
          (exp_of fall) (IsFree (explode m) (ctxt_trans c))
          (IMAGE explode (FDOM (to_fmap $ map1))) {} []’
        by (rename1 ‘option_CASE opt _ _’
            \\ Cases_on ‘opt’ \\ gs [empty_thm, TotOrd_compare]
            \\ irule find_fixpoint_drop_fd
            \\ pairarg_tac \\ gs []
            \\ first_x_assum $ irule_at Any)
      \\ pop_assum $ irule_at Any
      \\ qexists_tac ‘MAP (λm. IMAGE explode (FDOM (to_fmap m))) mL’
      \\ conj_tac
      >- (gs [LIST_REL_EL_EQN, EL_MAP]
          \\ rw [] \\ last_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ gs [MAPi_MAP_explode])
      \\ gvs []
      \\ gs [SUBSET_DEF, PULL_EXISTS, MEM_MAP])
  >~[‘NestedCase _ _ _ _ _ _’]
  >- (rw [empty_thm, TotOrd_compare]
      \\ irule find_fixpoint_refl)
QED

Theorem test_list_rel_soundness:
  ∀l1 l2. test_list_rel l1 l2 ⇒ LIST_REL (λ(_, b1) (_, b2). b2 ⇒ b1) l1 l2
Proof
  Induct
  >- (Cases
      \\ gs [test_list_rel_def])
  \\ gs [FORALL_PROD, EXISTS_PROD]
  \\ gen_tac \\ Cases \\ gs []
  \\ Cases \\ gs [test_list_rel_def]
  \\ rename1 ‘h = (_, _)’
  \\ Cases_on ‘h’
  \\ gvs [test_list_rel_def]
QED

Theorem is_lower_soundness:
  ∀l1 l2. is_lower l1 l2 ⇒
          LIST_REL (λ(_, a1, _, _) (_, a2, _, _).
                      LIST_REL (λ(_, b1) (_, b2). b2 ⇒ b1) a1 a2) l1 l2
Proof
  Induct \\ gs [FORALL_PROD]
  >- (Cases \\ gs [is_lower_def])
  \\ gen_tac \\ gen_tac \\ gen_tac \\ gen_tac
  \\ Cases \\ gs [is_lower_def]
  \\ rename1 ‘is_lower _ (h::_)’
  \\ PairCases_on ‘h’ \\ gs [is_lower_def]
  \\ gs [test_list_rel_soundness]
QED

Theorem FST_handle_fixpoint1:
  ∀fds e. FST (handle_fixpoint1 fds e) = FST e
Proof
  gs [FORALL_PROD, handle_fixpoint1_def]
  \\ rw []
  \\ pairarg_tac \\ gs []
QED

Theorem SND_SND_handle_fixpoint1:
  ∀fds e. SND (SND (handle_fixpoint1 fds e)) = SND (SND e)
Proof
  gs [FORALL_PROD, handle_fixpoint1_def]
  \\ rw []
  \\ pairarg_tac \\ gs []
QED

Theorem handle_fixpoint1_soundness:
  ∀fds arg out binds.
    handle_fixpoint1 fds arg = out ∧
    map_ok fds ∧ cmp_of fds = compare ∧
    cexp_wf (FST (SND (SND arg))) ∧
    (∀v. v ∈ FDOM (to_fmap fds) ⇒
         ∃args body. LENGTH args = LENGTH (to_fmap fds ' v) ∧
                     MEM (explode v, ZIP (args, to_fmap fds ' v), body) binds)
    ⇒
    SND (SND arg) = SND (SND out) ∧
    ∃ds ads fs.
        find_fixpoint binds (exp_of (FST (SND (SND arg)))) Nil ds ads fs ∧
        ∀v. MEM (v, T) (FST (SND out)) ⇒ explode v ∈ ds
Proof
  gs [FORALL_PROD, handle_fixpoint1_def]
  \\ rw []
  \\ pairarg_tac \\ gs []
  \\ dxrule_then assume_tac fixpoint1_soundness
  \\ gs []
  \\ first_x_assum $ dxrule_then mp_tac
  \\ CASE_TAC \\ gs [ctxt_trans_def]
  >- (strip_tac
      \\ first_x_assum $ irule_at Any
      \\ gs [MEM_MAP, PULL_EXISTS, MEM_EL]
      \\ rw []
      \\ gs [EL_MAP]
      \\ pairarg_tac \\ gs [lookup_thm, FLOOKUP_DEF])
  \\ CASE_TAC \\ simp []
  \\ strip_tac
  \\ first_x_assum $ irule_at Any
  \\ gs [MEM_MAP, PULL_EXISTS, MEM_EL]
  \\ rw []
  \\ gs [EL_MAP]
  \\ pairarg_tac \\ gs [lookup_thm, FLOOKUP_DEF]
QED

Theorem compute_fixpoint_rec_lemma:
  ∀binds m binds2.
    ALL_DISTINCT (MAP FST binds) ∧
    EVERY (cexp_wf o FST) (MAP (SND o SND) binds) ∧
    m = FOLDR (λ(v, args, e) m. insert m v (MAP SND args))
                (mlmap$empty mlstring$compare) binds ∧
    binds2 = MAP (λ(v, args, e, label). (explode v, (MAP (explode ## I) args), exp_of e)) binds ⇒
    map_ok m ∧ cmp_of m = compare ∧
    FDOM $ to_fmap m = set (MAP FST binds) ∧
    (∀v. v ∈ FDOM $ to_fmap m ⇒
         ∃args body. LENGTH args = LENGTH (to_fmap m ' v) ∧
                     MEM (explode v, ZIP (args, to_fmap m ' v), body) binds2)
Proof
  Induct \\ gs [empty_thm, insert_thm, TotOrd_compare]
  \\ rw [] \\ pairarg_tac
  \\ gs [insert_thm]
  >- (rename1 ‘_ = (_, args, e)’
      \\ qexists_tac ‘MAP (explode o FST) args’
      \\ qexists_tac ‘exp_of (FST e)’
      \\ gs []
      \\ pairarg_tac \\ gs []
      \\ disj1_tac
      \\ irule LIST_EQ
      \\ rw [EL_MAP, EL_ZIP, SND_THM]
      \\ pairarg_tac \\ gs [])
  \\ gs [FAPPLY_FUPDATE_THM]
  \\ IF_CASES_TAC \\ gs []
  \\ first_x_assum $ dxrule_then assume_tac
  \\ gs []
  \\ metis_tac []
QED

Theorem LIST_REL_binds_handle_fixpoint1:
  ∀binds m.
    LIST_REL (λ(v1, a1, b1, l1) (v2, a2, b2, l2).
                v1 = v2 ∧ MAP FST a1 = MAP FST a2 ∧ b1 = b2 ∧ l1 = l2) binds
             (MAP (handle_fixpoint1 m) binds)
Proof
  Induct \\ gs [FORALL_PROD, handle_fixpoint1_def]
  \\ rw []
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ rw []
  \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
QED

Theorem compute_fixpoint_rec_soundness:
  ∀i binds binds2 binds2b b.
    compute_fixpoint_rec i binds = binds2 ∧
    EVERY (cexp_wf o FST) (MAP (SND o SND) binds) ∧
    ALL_DISTINCT (MAP FST binds) ∧
    binds2b = MAP (λ(v, args, e, label). (explode v, (MAP (explode ## I) args), exp_of e)) binds2
    ⇒ (∀v args body.
        MEM (v, args, body) binds2b
        ⇒ ∃ds ads fs.
            find_fixpoint binds2b body Nil ds ads fs ∧
            ∀v. MEM (v, T) args ⇒ v ∈ ds) ∧
      EVERY (cexp_wf o FST) (MAP (SND o SND) binds) ∧
      LIST_REL (λ(v1, a1, b1, l1) (v2, a2, b2, l2).
                  v1 = v2 ∧ MAP FST a1 = MAP FST a2 ∧ b1 = b2 ∧ l1 = l2) binds binds2
Proof
  Induct \\ gs [compute_fixpoint_rec_def]
  >- (rw []
      \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
      >- (irule_at Any find_fixpoint_refl
          \\ gs [MEM_MAP]
          \\ pairarg_tac
          \\ gs [MEM_MAP, FORALL_PROD])
      \\ gvs [LIST_REL_EL_EQN, EL_MAP]
      \\ rw []
      \\ pairarg_tac
      \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM])
  \\ gen_tac \\ strip_tac
  \\ IF_CASES_TAC \\ gs []
  >~[‘¬is_lower _ _’]
  >- (qmatch_goalsub_abbrev_tac ‘compute_fixpoint_rec _ binds2’
      \\ last_x_assum $ qspec_then ‘binds2’ mp_tac \\ gs []
      \\ impl_tac
      >- (gs [Abbr ‘binds2’]
          \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_handle_fixpoint1, SND_SND_handle_fixpoint1]
          \\ gs [GSYM FST_THM, GSYM LAMBDA_PROD])
      \\ strip_tac \\ gs [Abbr ‘binds2’]
      \\ rw [] \\ gvs []
      >- (first_x_assum $ dxrule_then $ irule_at Any)
      \\ irule LIST_REL_TRANS
      \\ gs [FORALL_PROD]
      \\ first_x_assum $ irule_at Any
      \\ gs [LIST_REL_binds_handle_fixpoint1])
  \\ last_x_assum kall_tac
  \\ gs [LIST_REL_binds_handle_fixpoint1]
  \\ dxrule_then assume_tac is_lower_soundness
  \\ gvs [MEM_MAP, PULL_EXISTS]
  \\ rw []
  \\ pairarg_tac \\ gs []
  \\ gs [MEM_EL]
  \\ dxrule_then assume_tac handle_fixpoint1_soundness
  \\ dxrule_then assume_tac compute_fixpoint_rec_lemma
  \\ gvs [GSYM LAMBDA_PROD, EVERY_EL]
  \\ last_x_assum $ drule_then assume_tac
  \\ gs [EL_MAP]
  \\ last_x_assum $ dxrule_then assume_tac
  \\ gs []
  \\ irule_at Any find_lower_bind
  \\ first_x_assum $ irule_at Any
  \\ rw []
  >- (gs [LIST_REL_EL_EQN]
      \\ rw [] \\ last_x_assum $ drule_then assume_tac
      \\ gs [EL_MAP]
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ qpat_x_assum ‘MAP (explode ## I) _ = _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM
      \\ qpat_x_assum ‘MAP (explode ## I) _ = _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM
      \\ gs [EL_MAP]
      \\ rw []
      \\ first_x_assum $ dxrule_then assume_tac
      \\ gs []
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs [])
  >- (irule LIST_EQ \\ gs [EL_MAP]
      \\ rw []
      \\ pairarg_tac \\ gs []
      \\ qmatch_goalsub_abbrev_tac ‘handle_fixpoint1 m arguments’
      \\ pairarg_tac \\ gs []
      \\ qspecl_then [‘m’, ‘arguments’] assume_tac FST_handle_fixpoint1
      \\ gs [Abbr ‘arguments’])
  \\ gs [EL_MAP, MEM_EL, PULL_EXISTS]
  \\ first_x_assum $ dxrule_then assume_tac
  \\ rename1 ‘(_, _) = (EL n' args') ⇒ _’
  \\ Cases_on ‘EL n' args'’ \\ gs []
QED

Theorem can_compute_fixpoint_soundness2:
  ∀binds b binds2.
    can_compute_fixpoint binds = (b, binds2) ⇒
    binds2 = MAP (λ(v, body). (v, split_body body)) binds ∧
    MAP FST binds2 = MAP FST binds
Proof
  gs [can_compute_fixpoint_def]
  \\ rpt $ gen_tac
  \\ IF_CASES_TAC \\ gs []
  \\ rw []
  \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
  \\ irule LIST_EQ
  \\ rw [EL_MAP]
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
QED

Theorem rev_split_body_inner_MAP_F:
  ∀l a e. rev_split_body_inner a (MAP (λv. (v, F)) l) e = e
Proof
  Induct \\ gs [rev_split_body_inner_def]
QED

Theorem NestedCase_free_rev_split_body:
  ∀args a b. NestedCase_free b ⇒
             NestedCase_free (rev_split_body_inner a args b)
Proof
  Induct \\ gs [rev_split_body_inner_def, FORALL_PROD]
  \\ gen_tac  \\ Cases \\ rw []
  \\ gs [rev_split_body_inner_def, FORALL_PROD]
QED

Theorem cexp_wf_rev_split_body:
  ∀args a b. cexp_wf b ⇒
             cexp_wf (rev_split_body_inner a args b)
Proof
  Induct \\ gs [rev_split_body_inner_def, FORALL_PROD]
  \\ gen_tac  \\ Cases \\ rw []
  \\ gs [rev_split_body_inner_def, FORALL_PROD, cexp_wf_def, num_args_ok_def]
QED

Theorem rev_split_body_inner_soundness:
  ∀args label e.
    exp_of (rev_split_body_inner label args e)
    = mk_seqs (MAP (λ(v, b). (explode v, b)) args) (exp_of e)
Proof
  Induct \\ gs [rev_split_body_inner_def, mk_seqs_def, FORALL_PROD]
  \\ gen_tac \\ Cases \\ gs [rev_split_body_inner_def, mk_seqs_def, exp_of_def, op_of_def]
QED

Theorem rev_split_body_soundness:
  ∀args label e.
    exp_of (rev_split_body label args e)
    =
    Lams (MAP (λ(v, b). explode v) args)
         (mk_seqs (MAP (λ(v, b). (explode v, b)) args) (exp_of e))
Proof
  Cases
  \\ gs [rev_split_body_def, exp_of_def, rev_split_body_inner_soundness, Lams_def, mk_seqs_def]
  \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
  \\ pairarg_tac \\ gs []
QED

Theorem MAP_mk_seq_lams:
  ∀l. MAP (λ(n, x). (explode n, exp_of x)) (MAP (λ(v, args, body, label). (v, rev_split_body label args body)) l)
      = MAP mk_seq_lams
            (MAP (λ(n, args, body, label). (explode n, MAP (λ(v,b). (explode v, b)) args, exp_of body)) l)
Proof
  Induct \\ gs [FORALL_PROD]
  \\ pop_assum kall_tac
  \\ rw [mk_seq_lams_def]
  \\ gs [rev_split_body_soundness, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
QED

Theorem fixpoint_analysis_lemma:
  ∀binds binds2.
    LIST_REL (λ(v1,a1,b1,l1) (v2,a2,b2,l2). v1 = v2 ∧ MAP FST a1 = MAP FST a2 ∧ b1 = b2 ∧ l1 = l2)
             (MAP (λ(p1,p2). (λ(args,body,label). (p1,MAP (λv. (v,T)) args,body,label)) (split_body p2)) binds)
             binds2 ⇒
    MAP2 (λbL (v, args, e, label). (explode v, ZIP (MAP explode args, bL), exp_of e))
         (MAP (λ(_, args, _, _). MAP SND args) binds2)
         (MAP (λ(v, body). (v, split_body body)) binds)
    = MAP (λ(n,args,body,label). (explode n,MAP (λ(v,b). (explode v,b)) args, exp_of body)) binds2
Proof
  Induct \\ gs [PULL_EXISTS]
  \\ pop_assum kall_tac
  \\ gs [FORALL_PROD]
  \\ rw []
  \\ pairarg_tac \\ gs []
  \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
  \\ irule LIST_EQ
  \\ rw [EL_MAP, EL_ZIP]
  \\ pairarg_tac \\ gs []
QED

Theorem fixpoint_analysis_lemma2:
  ∀binds binds2.
    LIST_REL (λ(v1,a1,b1,l1) (v2,a2,b2,l2). v1 = v2 ∧ MAP FST a1 = MAP FST a2 ∧ b1 = b2 ∧ l1 = l2)
             (MAP (λ(p1,p2). (λ(args,body,label). (p1,MAP (λv. (v,T)) args,body,label)) (split_body p2)) binds)
             binds2 ⇒
    MAP FST binds = MAP FST binds2
Proof
  rw [] \\ irule LIST_EQ
  \\ gs [LIST_REL_EL_EQN]
  \\ rw [EL_MAP]
  \\ last_x_assum $ drule_then assume_tac
  \\ gvs [EL_MAP]
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
QED

Theorem ALL_DISTINCT_MAP_explode:
  ∀l. ALL_DISTINCT l ⇒ ALL_DISTINCT (MAP explode l)
Proof
  Induct \\ gs [MEM_MAP, PULL_EXISTS]
QED

Theorem letrecs_distinct_add_all_demands_lemma:
  ∀m a e v0.
    letrecs_distinct (exp_of e) ⇒
    letrecs_distinct (exp_of (foldrWithKey (λid () e. Prim a Seq [Var a id; e]) e (Map compare m)))
Proof
  Induct \\ gs [foldrWithKey_def, balanced_mapTheory.foldrWithKey_def]
  \\ rw []
  \\ last_x_assum irule
  \\ simp [letrecs_distinct_def, exp_of_def]
QED

Theorem letrecs_distinct_rev_split_body_inner:
  ∀args a e. letrecs_distinct (exp_of e) ⇒
             letrecs_distinct (exp_of (rev_split_body_inner a args e))
Proof
  Induct \\ gs [rev_split_body_inner_def, FORALL_PROD]
  \\ gen_tac
  \\ Cases \\ gs [rev_split_body_inner_def, exp_of_def, letrecs_distinct_def]
QED

Theorem letrecs_distinct_rev_split_body:
  ∀args a e. letrecs_distinct (exp_of e) ⇒
             letrecs_distinct (exp_of (rev_split_body a args e))
Proof
  Cases
  \\ gs [letrecs_distinct_rev_split_body_inner, rev_split_body_def, letrecs_distinct_Lams, exp_of_def]
QED

Theorem fixpoint_analysis_soundness:
  ∀binds binds2 a e b.
    fixpoint_analysis binds = (b, binds2) ∧ NestedCase_free (Letrec a binds e) ∧ ALL_DISTINCT (MAP FST binds) ∧
    cexp_wf (Letrec a binds e) ∧ letrecs_distinct (exp_of (Letrec a binds e)) ⇒
    NestedCase_free (Letrec a (MAP (λ(v, args, body, label). (v, rev_split_body label args body)) binds2) e) ∧
    cexp_wf (Letrec a (MAP (λ(v, args, body, label). (v, rev_split_body label args body)) binds2) e) ∧
    letrecs_distinct (exp_of (Letrec a (MAP (λ(v, args, body, label).
                                               (v, rev_split_body label args body)) binds2) e)) ∧
    (b ⇒ EVERY (λ(v, args, body, label). ALL_DISTINCT (MAP FST args)) binds2) ∧
    ∀c. find (exp_of (Letrec a binds e)) c {}
             {} (exp_of (Letrec a (MAP (λ(v, args, body, label). (v, rev_split_body label args body)) binds2) e))
             NONE
Proof
  gs [fixpoint_analysis_def]
  \\ rpt $ gen_tac \\ strip_tac
  \\ pairarg_tac \\ gs []
  \\ rename1 ‘can_compute_fixpoint _ = (b', _)’
  \\ Cases_on ‘b'’ \\ gs []
  >- (drule_then assume_tac can_compute_fixpoint_soundness
      \\ drule_then assume_tac can_compute_fixpoint_soundness2
      \\ drule_then assume_tac compute_fixpoint_rec_soundness
      \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
      \\ pop_assum mp_tac
      \\ impl_tac
      >- (conj_tac
          >- (gs [cexp_wf_def, EVERY_EL, EL_MAP]
              \\ rw []
              \\ last_x_assum $ drule_then kall_tac
              \\ last_x_assum $ drule_then assume_tac
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ rename1 ‘split_body p2' = (p1'', _, _)’
              \\ qspecl_then [‘p2'’, ‘p1''’, ‘MAP (K T) p1''’] assume_tac split_body_soundness
              \\ gs [])
          >- (‘∀l1 : mlstring list l2. ALL_DISTINCT l1 ∧ l1 = l2 ⇒ ALL_DISTINCT l2’ by simp []
              \\ pop_assum $ dxrule_then irule
              \\ irule LIST_EQ
              \\ rw [EL_MAP]
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []))
      \\ strip_tac
      \\ gs [exp_of_def]
      \\ conj_tac
      >- (gs [EVERY_EL, EL_MAP, LIST_REL_EL_EQN]
          \\ gen_tac \\ strip_tac
          \\ first_x_assum $ drule_then assume_tac
          \\ last_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ rw []
          \\ rename1 ‘split_body p2'’
          \\ Cases_on ‘p2'’
          \\ gs [NestedCase_free_def, split_body_def, rev_split_body_def]
          \\ rw [NestedCase_free_def, rev_split_body_def]
          \\ rename1 ‘rev_split_body _ args2 _’
          \\ Cases_on ‘args2’
          \\ gs [rev_split_body_def, NestedCase_free_rev_split_body])
      \\ conj_tac
      >- (gs [EVERY_EL, cexp_wf_def, LIST_REL_EL_EQN]
          \\ conj_tac
          >- (gen_tac \\ strip_tac
              \\ first_x_assum $ drule_then assume_tac
              \\ last_x_assum $ drule_then assume_tac
              \\ last_x_assum $ drule_then assume_tac
              \\ gs [EL_MAP]
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ rw []
              \\ rename1 ‘split_body p2'’
              \\ Cases_on ‘p2'’
              \\ gs [NestedCase_free_def, split_body_def, rev_split_body_def]
              \\ rw [NestedCase_free_def, rev_split_body_def]
              \\ rename1 ‘rev_split_body _ args2 _’
              \\ Cases_on ‘args2’
              \\ gs [rev_split_body_def, cexp_wf_rev_split_body, cexp_wf_def])
          >- (strip_tac \\ gs []))
      \\ conj_tac
      >- (gs [EVERY_EL, letrecs_distinct_def, LIST_REL_EL_EQN]
          \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
          \\ ‘∀l1 : string list l2. ALL_DISTINCT l1 ∧ l1 = l2 ⇒ ALL_DISTINCT l2’ by simp []
          \\ pop_assum $ dxrule_then $ irule_at Any
          \\ conj_tac
          >- (irule LIST_EQ
              \\ rw [EL_MAP]
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ first_x_assum $ drule_then assume_tac
              \\ gs [EL_MAP]
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs [])
          \\ gen_tac \\ strip_tac
          \\ first_x_assum $ drule_then assume_tac
          \\ last_x_assum $ drule_then assume_tac
          \\ last_x_assum $ drule_then assume_tac
          \\ gs [EL_MAP]
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ rename1 ‘split_body p2'’
          \\ Cases_on ‘p2'’
          \\ gs [split_body_def, rev_split_body_def]
          \\ gs [letrecs_distinct_rev_split_body, letrecs_distinct_Lams, exp_of_def])
      \\ conj_tac
      >- (qmatch_goalsub_abbrev_tac ‘EVERY _ binds2’
          \\ last_x_assum $ qspec_then ‘MAP (λ(_, args, _, _). MAP SND args) binds2’ mp_tac
          \\ impl_tac
          >- (gs [Abbr ‘binds2’, LIST_REL_EL_EQN, EL_MAP, EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
              \\ gen_tac \\ strip_tac
              \\ first_x_assum $ drule_then assume_tac
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ gs [MAP_MAP_o, combinTheory.o_DEF])
          \\ strip_tac \\ gs []
          \\ gs [fixpoint_analysis_lemma, EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
          \\ rw []
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, ALL_DISTINCT_IMP2])
      \\ irule_at Any find_Letrec2
      \\ irule_at Any MAP_mk_seq_lams
      \\ qmatch_goalsub_abbrev_tac ‘ALL_DISTINCT (MAP FST (MAP _ binds2))’
      \\ last_x_assum $ qspec_then ‘MAP (λ(_, args, _, _). MAP SND args) binds2’ mp_tac
      \\ gs [EVERY_MAP, LAMBDA_PROD]
      \\ impl_tac
      >-  (gvs [Abbr ‘binds2’, LIST_REL_EL_EQN]
           \\ gen_tac \\ strip_tac
           \\ first_x_assum $ drule_then assume_tac
           \\ gs [EL_MAP]
           \\ pairarg_tac \\ gs []
           \\ pairarg_tac \\ gs []
           \\ pairarg_tac \\ gs []
           \\ gs [MAP_MAP_o, combinTheory.o_DEF])
      \\ strip_tac \\ gs []
      \\ gs [fixpoint_analysis_lemma]
      \\ conj_tac
      >- (rpt $ gen_tac \\ strip_tac
          \\ first_x_assum $ drule_then assume_tac
          \\ gs []
          \\ ‘∀l. MAP (λ(v, b : bool). (explode v, b)) l = MAP (explode ## I) l’
            by (gen_tac
                \\ irule LIST_EQ
                \\ rw [EL_MAP]
                \\ pairarg_tac \\ gs [])
          \\ gvs []
          \\ first_x_assum $ irule_at Any
          \\ first_x_assum $ irule_at Any)
      \\ dxrule_then assume_tac fixpoint_analysis_lemma2
      \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
      \\ gs [GSYM LAMBDA_PROD, GSYM FST_THM]
      \\ dxrule_then mp_tac ALL_DISTINCT_MAP_explode
      \\ rpt $ pop_assum kall_tac
      \\ Induct_on ‘binds2’ \\ gvs [FORALL_PROD, MEM_MAP])
  \\ drule_then assume_tac can_compute_fixpoint_soundness2
  \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
  \\ qmatch_goalsub_abbrev_tac ‘find (exp_of (Letrec _ b1 _)) _ _ _ (exp_of (Letrec _ b2 _)) _’
  \\ qsuff_tac ‘b1 = b2’
  >- (gs [find_Bottom]
      \\ strip_tac
      \\ gvs []
      \\ gs [Abbr ‘b1’, EVERY_EL]
      \\ gen_tac \\ strip_tac
      \\ last_x_assum $ drule_then assume_tac
      \\ gs [EL_MAP]
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ pairarg_tac \\ gs []
      \\ rename1 ‘split_body p2 = (args', body, label)’
      \\ qspecl_then [‘p2’, ‘args'’, ‘GENLIST (K T) (LENGTH args')’] assume_tac split_body_soundness
      \\ gs []
      \\ rw []
      \\ Cases_on ‘args'’
      \\ gs [rev_split_body_def, rev_split_body_inner_def, rev_split_body_inner_MAP_F])
  \\ gs [Abbr ‘b1’, Abbr ‘b2’, cexp_wf_def, EVERY_EL]
  \\ irule LIST_EQ
  \\ rw [EL_MAP]
  \\ first_x_assum $ drule_then assume_tac
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ pairarg_tac \\ gs []
  \\ rw []
  \\ rename1 ‘split_body p2 = _’
  \\ Cases_on ‘p2’
  \\ gs [split_body_def, rev_split_body_def, EL_MAP]
  \\ rename1 ‘Lam _ args _ = _’
  \\ Cases_on ‘args’
  \\ gs [rev_split_body_def, rev_split_body_inner_def, rev_split_body_inner_MAP_F, cexp_wf_def]
  \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
QED

(* ------------------------------ *)

Theorem update_ctxt_soundness:
  ∀l e e' n1 n2 c fds fd.
    find e (update_ctxt n1 n2 c (MAP (λ(i, v). (i, implode v)) l))
           (BIGUNION (IMAGE (λ(v, bL). if MEM v (MAP SND l) then {} else {(v, bL)}) fds))
           {} e' fd
    ⇒ find (lets_for (explode n1) (explode n2) l e) c fds
           {} (lets_for (explode n1) (explode n2) l e') NONE
Proof
  Induct
  \\ gvs [lets_for_def, update_ctxt_def]
  >- (rw [] \\ irule find_Drop_fd
      \\ irule_at Any find_Subset
      \\ pop_assum $ irule_at Any
      \\ simp [SUBSET_DEF, PULL_EXISTS, FORALL_PROD])
  \\ Cases
  \\ rw [lets_for_def, update_ctxt_def]
  \\ irule find_Let
  \\ fs [dest_fd_SND_def]
  \\ rpt $ last_x_assum $ irule_at Any
  \\ irule_at Any find_Bottom
  \\ gvs []
  \\ rename1 ‘_ ≠ r ∧ _ ∈ fds’
  \\ qexists_tac ‘BIGUNION (IMAGE (λ(v, bL). if v = r then {} else {(v, bL)}) fds)’
  \\ irule_at Any find_Subset
  \\ pop_assum $ irule_at Any
  \\ simp [SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
  \\ rw [EXISTS_PROD]
  \\ first_x_assum $ irule_at Any
  \\ gs []
QED

Theorem MAPi_implode_MAP_explode:
  ∀l. MAPi (λi v. (i, implode v)) (MAP explode l) = MAPi (λi v. (i,v)) l
Proof
  Induct using SNOC_INDUCT \\ gvs [MAP_SNOC, indexedListsTheory.MAPi_APPEND]
QED

Theorem find_rows_of_inner:
  ∀l l' ke ke' c s fds fd.
    LIST_REL (λ(a1, b1, e1) (a2, b2, e2).
                a1 = a2 ∧ b1 = b2 ∧
                find (exp_of e1)
                     (update_ctxt a1 s c (MAPi (λi v. (i, v)) b1))
                     (BIGUNION (IMAGE (λ(v, bL). if MEM v (MAP explode b1) then {} else {(v, bL)}) fds))
                     {} (exp_of e2) fd)
             l l' ∧
    find ke c {} {} ke' NONE
    ⇒
    find (rows_of (explode s) ke
          (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) l))
         c fds {}
         (rows_of (explode s) ke'
          (MAP (λ(c,vs,x'). (explode c,MAP explode vs, exp_of x')) l'))
         NONE
Proof
  Induct
  \\ gvs [rows_of_def, find_Fail, FORALL_PROD, PULL_EXISTS]
  \\ rw []
  \\ irule find_Subset >~
  [‘find (If _ _ _)’]
  >- (irule_at Any find_If \\ rw []
      \\ first_x_assum (pop_assum o mp_then (Pos last) assume_tac)
      \\ rpt $ last_x_assum $ irule_at Any
      \\ irule_at Any find_IsEq
      \\ irule_at Any find_Var \\ gvs []
      \\ irule_at Any find_Subset
      \\ irule_at Any update_ctxt_soundness
      \\ gvs [combinTheory.o_DEF, LAMBDA_PROD, MAPi_implode_MAP_explode]
      \\ pop_assum $ irule_at Any
      \\ qexists_tac ‘{}’ \\ fs []
      \\ simp [EVERY_MEM, MEM_MAP, PULL_EXISTS, SUBSET_DEF, FORALL_PROD]
      \\ rw []
      \\ rename1 ‘(explode y, d) ∉ s’ \\ Cases_on ‘(explode y, d) ∈ s’ \\ simp []
      \\ rpt $ gen_tac \\ IF_CASES_TAC \\ rw [] \\ gs []) >>
  simp[] >> first_assum $ irule_at Any >> simp[]
QED

Theorem find_rows_of:
  ∀l l' ke ke' c s fds fd.
    l ≠ [] ∧
    LIST_REL (λ(a1, b1, e1) (a2, b2, e2).
                a1 = a2 ∧ b1 = b2 ∧
                find (exp_of e1)
                     (update_ctxt a1 s c (MAPi (λi v. (i, v)) b1))
                     (BIGUNION (IMAGE (λ(v, bL). if MEM v (MAP explode b1) then {} else {(v, bL)}) fds))
                     {} (exp_of e2) fd)
             l l' ∧
    find ke c {} {} ke' NONE
    ⇒
    find (rows_of (explode s) ke
          (MAP (λ(c,vs,x'). (explode c,MAP explode vs,exp_of x')) l))
         c fds {([], (explode s))}
         (rows_of (explode s) ke'
          (MAP (λ(c,vs,x'). (explode c,MAP explode vs, exp_of x')) l'))
         NONE
Proof
  Cases >> rw [] >>
  pairarg_tac >> simp [] >>
  pairarg_tac >> gvs [rows_of_def] >>
  dxrule_then (dxrule_then assume_tac) find_rows_of_inner >>
  ‘∀e1 c fdc e2 ds fd. find e1 c fdc (ds ∪ ({} ∩ {})) e2 fd ⇒ find e1 c fdc ds e2 fd’ by simp [] >>
  pop_assum irule >>
  irule find_If >>
  pop_assum $ irule_at Any >>
  irule_at Any find_IsEq >>
  irule_at Any find_Var >>
  irule_at Any find_Subset >>
  irule_at Any update_ctxt_soundness >>
  gvs [combinTheory.o_DEF, LAMBDA_PROD, MAPi_implode_MAP_explode] >>
  pop_assum $ irule_at Any >>
  simp [] >>
  simp [EVERY_MEM, MEM_MAP, PULL_EXISTS, SUBSET_DEF, FORALL_PROD] >>
  rw [] >>
  rename1 ‘(explode y, d) ∉ s’ >> Cases_on ‘(explode y, d) ∈ s’ >> simp [] >>
  rpt $ gen_tac >> IF_CASES_TAC >> rw [] >> gs []
QED

Theorem find_subset_aid:
  ∀d ps v. (ps, v) ∈ d ⇒ ∃ps'. (ps ++ ps', v) ∈ d
Proof
  rw [] >> qexists_tac ‘[]’ >> gvs []
QED

Theorem handle_Apps_demands_soundness:
  ∀bL argl bL' fds c m eL a.
    handle_Apps_demands a bL (MAP (λe. demands_analysis_fun c e fds) argl) = (bL', eL, m)
    ∧ EVERY (λ(dm, _, _). map_ok dm ∧ cmp_of dm = compare)
                   (MAP (λe. demands_analysis_fun c e fds) argl)
    ⇒ (bL' = [] ⇔ LENGTH bL ≤ LENGTH argl)
      ∧ (LENGTH bL > LENGTH argl ⇒ ∃bL''. LENGTH bL'' = LENGTH argl ∧  bL = bL'' ++ bL')
      ∧ (∀p. p ∈ demands_map_to_set m
             ⇒ ∃i. i < LENGTH bL ∧ i < LENGTH argl ∧ EL i bL
                   ∧ p ∈ EL i (MAP (λe'. demands_map_to_set (FST e'))
                               (MAP (λe. demands_analysis_fun c e fds) argl)))
      ∧ LENGTH argl = LENGTH eL
      ∧ map_ok m ∧ cmp_of m = compare
      ∧ (LENGTH bL ≤ LENGTH argl
         ⇒ (∃argl1 argl2.
              argl1 ++ argl2 = argl ∧ LENGTH argl1 = LENGTH bL)
           ∧  (∃eL1 eL2.
                 eL1 ++ eL2 = eL ∧ LENGTH eL1 = LENGTH bL))
      ∧ (∀i. i < LENGTH argl ⇒ EL i eL = (if i < LENGTH bL ∧ EL i bL
                                         then FST (SND (demands_analysis_fun c (EL i argl) fds))
                                         else add_all_demands a (demands_analysis_fun c (EL i argl) fds)))
Proof
  Induct >> gvs [handle_Apps_demands_def, empty_thm, TotOrd_compare, demands_map_empty, EL_MAP] >>
  Cases >> Cases >> gvs [handle_Apps_demands_def, empty_thm, TotOrd_compare, demands_map_empty] >>
  rpt $ gen_tac
  >~[‘handle_Apps_demands a (T::bL) (demands_analysis_fun c ehd fds::MAP _ tl)’]
  >- (qabbrev_tac ‘hd = demands_analysis_fun c ehd fds’ >>
      PairCases_on ‘hd’ >> gvs [handle_Apps_demands_def] >>
      qabbrev_tac ‘hAd = handle_Apps_demands a bL (MAP (λe. demands_analysis_fun c e fds) tl)’ >>
      PairCases_on ‘hAd’ >>
      strip_tac >> gvs [] >>
      last_x_assum $ drule_then $ dxrule_then  assume_tac >>
      gvs [union_thm] >> rw []
      >- (qspecl_then [‘$=’] assume_tac LIST_REL_rules >> fs [])
      >- (gvs [demands_map_union]
          >- (qexists_tac ‘0’ >> gvs []) >>
          first_x_assum $ dxrule_then assume_tac >> gvs [] >>
          rename1 ‘EL i bL’ >> qexists_tac ‘SUC i’ >> gvs [EL_MAP])
      >> gvs []
      >>~[‘ehd::(argl1 ++ argl2)’]
      >- (qexists_tac ‘ehd::argl1’ >> qexists_tac ‘argl2’ >> gvs [])
      >- (qexists_tac ‘ehd::argl1’ >> qexists_tac ‘argl2’ >> gvs []) >>
      rename1 ‘EL i _’ >> Cases_on ‘i’ >> gvs []) >>
  rename1 ‘handle_Apps_demands a bL (MAP (λe. demands_analysis_fun c e fds) tl)’ >>
  qabbrev_tac ‘hAd = handle_Apps_demands a bL (MAP (λe. demands_analysis_fun c e fds) tl)’ >>
  PairCases_on ‘hAd’ >>
  strip_tac >> gvs [] >>
  last_x_assum $ drule_then $ dxrule_then assume_tac >>
  gvs [] >> rw []
  >- (qspecl_then [‘$=’] assume_tac LIST_REL_rules >> fs [])
  >- (first_x_assum $ dxrule_then assume_tac >> gvs [] >>
      rename1 ‘EL i bL’ >> qexists_tac ‘SUC i’ >> gvs [EL_MAP]) >>
  gvs []
  >>~[‘h::(argl1 ++ argl2)’]
  >- (qexists_tac ‘h::argl1’ >> qexists_tac ‘argl2’ >> gvs [])
  >- (qexists_tac ‘h::argl1’ >> qexists_tac ‘argl2’ >> gvs []) >>
  rename1 ‘EL i _’ >> Cases_on ‘i’ >> gvs []
QED

Theorem Apps_append:
  ∀eL1 eL2 f. Apps f (eL1 ++ eL2) = Apps (Apps f eL1) eL2
Proof
  Induct >> gvs [Apps_def]
QED

Theorem UNZIP3_LENGTH:
  ∀l v1 v2 v3. UNZIP3 l = (v1, v2, v3) ⇒ LENGTH v1 = LENGTH l ∧ LENGTH v2 = LENGTH l ∧ LENGTH v3 = LENGTH l
Proof
  Induct >> gvs [UNZIP3_DEF, FORALL_PROD] >>
  rename1 ‘UNZIP3 l’ >> qabbrev_tac ‘u3 = UNZIP3 l’ >> PairCases_on ‘u3’ >>
  gvs []
QED

Theorem UNZIP3_MAP:
  ∀l. UNZIP3 l = (MAP FST l, MAP (FST o SND) l, MAP (SND o SND) l)
Proof
  Induct >> gvs [FORALL_PROD, UNZIP3_DEF]
QED

Theorem map_handle_multi_ok:
  ∀mL vL m.
            EVERY (λm2. map_ok m2 ∧ cmp_of m2 = compare) mL ∧ cmp_of m = compare ∧ map_ok m
            ⇒ map_ok (handle_multi_bind m mL vL) ∧ cmp_of (handle_multi_bind m mL vL) = compare
Proof
  Induct >> gvs [handle_multi_bind_def] >>
  gen_tac >> Cases >> gvs [handle_multi_bind_def] >>
  rw [union_thm]
QED

Theorem handle_multi_in:
  ∀mL vL m d.
    d ∈ demands_map_to_set (handle_multi_bind m mL vL) ∧ LENGTH mL = LENGTH vL
    ∧ cmp_of m = compare ∧ map_ok m
    ∧ EVERY (λm2. map_ok m2 ∧ cmp_of m2 = compare) mL
    ⇒ d ∈ demands_map_to_set m
      ∨ ∃ps i. i < LENGTH mL ∧
               (ps, explode (EL i vL)) ∈ demands_map_to_set m ∧
               d ∈ demands_map_to_set (EL i mL)
Proof
  Induct >> gvs [handle_multi_bind_def] >>
  gen_tac >> Cases >> gvs [handle_multi_bind_def] >> rw []
  >- (last_x_assum $ drule_then assume_tac >> gvs [] >>
      disj2_tac >> rename1 ‘(ps, explode (EL i _)) ∈ _’ >>
      qexists_tac ‘ps’ >> qexists_tac ‘SUC i’ >> gvs []) >>
  drule_then assume_tac map_handle_multi_ok >> gvs [demands_map_union]
  >- (disj2_tac >>
      rename1 ‘d ∈ demands_map_to_set _’ >> PairCases_on ‘d’ >>
      rename1 ‘(ps, _) ∈ demands_map_to_set _’ >>
      qexists_tac ‘ps’ >> qexists_tac ‘0’ >>
      gvs [demands_map_to_set_def, lookup_thm, FLOOKUP_DEF] >>
      irule_at Any $ GSYM explode_implode >> gvs []) >>
  last_x_assum $ drule_then assume_tac >> gvs [] >>
  disj2_tac >> rename1 ‘(ps, explode (EL i _)) ∈ _’ >>
  qexists_tac ‘ps’ >> qexists_tac ‘SUC i’ >> gvs []
QED

Theorem demands_map_in_FDOM:
  ∀vname m. vname ∈ FDOM (to_fmap m) ⇒ ([], explode vname) ∈ demands_map_to_set m
Proof
  rw [demands_map_to_set_def] >>
  pop_assum $ irule_at Any >> gvs [explode_implode]
QED

Theorem boolList_of_fdemands_soundness:
  ∀vL m d. map_ok m ⇒
           FST (boolList_of_fdemands m vL)
           = FST (demands_boolList (demands_map_to_set m) (MAP explode vL))
           ∧ map_ok (SND (boolList_of_fdemands m vL))
           ∧ SND (demands_boolList (demands_map_to_set m) (MAP explode vL))
             = IMAGE explode (FDOM (to_fmap (SND (boolList_of_fdemands m vL))))
Proof
  Induct >> gvs [boolList_of_fdemands_def, demands_boolList_def, empty_thm, TotOrd_compare] >>
  rw [] >>
  rename1 ‘boolList_of_fdemands m vL’ >>
  qabbrev_tac ‘fd = boolList_of_fdemands m vL’ >> PairCases_on ‘fd’ >>
  rename1 ‘demands_boolList (_ m) _’ >>
  qabbrev_tac ‘dsBL = demands_boolList (demands_map_to_set m) (MAP explode vL)’ >>
  PairCases_on ‘dsBL’ >>
  fs [] >> last_x_assum $ drule_then assume_tac >> gvs [insert_thm] >>
  once_rewrite_tac [INSERT_SING_UNION, UNION_COMM] >> gvs [lookup_thm, FLOOKUP_DEF] >>
  eq_tac >> rw [demands_map_to_set_def]
QED

Theorem AP_THM2:
  ∀f g a b. a = b ∧ f a = g b ⇒ f a = g b
Proof
  gvs []
QED

Theorem demands_analysis_eq_with_diff_ctxt:
  ∀(f : α -> num) (e: α cexp) c c2 fds.
    NestedCase_free e ⇒
    demands_analysis_fun c e fds = demands_analysis_fun c2 e fds
Proof
  completeInduct_on ‘cexp_size f e’ >> gen_tac >> Cases >>
  rw [] >> rename1 ‘demands_analysis_fun c1 _ fds = demands_analysis_fun c2 _ _’ >>
  gvs [demands_analysis_fun_def]
  >~[‘Prim _ op l’]
  >- (Cases_on ‘op’ >> gvs [demands_analysis_fun_def] >> rw []
      >- (irule LIST_EQ >> rw [EL_MAP] >>
          rename1 ‘n < _’ >>
          last_x_assum $ qspecl_then [‘cexp_size f (EL n l)’] assume_tac >>
          ‘cexp_size f (EL n l) < cexp10_size f l’
            by metis_tac [cexp_size_lemma, EL_MEM] >>
          fs [cexp_size_def] >>
          pop_assum kall_tac >>
          pop_assum $ qspecl_then [‘f’, ‘EL n l’] assume_tac >>
          AP_TERM_TAC >> first_assum irule >>
          gvs [EVERY_MEM, MEM_EL, PULL_EXISTS])
      >- (AP_TERM_TAC >> AP_TERM_TAC >>
          irule LIST_EQ >> rw [EL_MAP] >>
          rename1 ‘n < _’ >>
          last_x_assum $ qspecl_then [‘cexp_size f (EL n l)’] assume_tac >>
          ‘cexp_size f (EL n l) < cexp10_size f l’
            by metis_tac [cexp_size_lemma, EL_MEM] >>
          fs [cexp_size_def] >>
          pop_assum kall_tac >>
          pop_assum $ qspecl_then [‘f’, ‘EL n l’] assume_tac >>
          first_assum irule >> gvs [EVERY_MEM, MEM_EL, PULL_EXISTS]) >>
      Cases_on ‘l’ >> gvs [demands_analysis_fun_def] >>
      rename1 ‘h::l’ >> Cases_on ‘l’ >> gvs [demands_analysis_fun_def] >>
      rename1 ‘h1::h2::l’ >> Cases_on ‘l’ >> gvs [demands_analysis_fun_def] >>
      rename1 ‘_ (demands_analysis_fun c _ fds) = _ (demands_analysis_fun c2 _ _)’ >>
      irule AP_THM >>
      first_assum $ irule_at Any >>
      irule_at Any EQ_REFL >> qexists_tac ‘f’ >> gvs [cexp_size_def] >>
      last_x_assum $ qspecl_then [‘cexp_size f h2’] assume_tac >>
      gvs [cexp_size_def] >>
      pop_assum $ qspecl_then [‘f’, ‘h2’] assume_tac >> gvs [] >>
      pop_assum $ qspecl_then [‘c’, ‘c2’, ‘fds’] assume_tac >> gvs [])
  >- (rw [] >>
      rename1 ‘_ (demands_analysis_fun c1 fun fds) = _ (demands_analysis_fun c2 _ _)’ >>
      first_assum $ qspecl_then [‘cexp_size f fun’] assume_tac >> gvs [cexp_size_def] >>
      pop_assum $ qspecl_then [‘f’, ‘fun’] assume_tac >> gvs [] >>
      pop_assum $ qspecl_then [‘c1’, ‘c2’, ‘fds’] assume_tac >> gvs [] >>
      qabbrev_tac ‘p = demands_analysis_fun c2 fun fds’ >> PairCases_on ‘p’ >> gvs [] >>
      FULL_CASE_TAC >> gvs []
      >- (AP_TERM_TAC >> irule LIST_EQ >> rw [EL_MAP] >>
          last_x_assum $ irule_at Any >>
          irule_at Any EQ_REFL >> qexists_tac ‘f’ >>
          rename1 ‘n < LENGTH _’ >>
          ‘cexp_size f (EL n l) < cexp10_size f l’ by metis_tac [cexp_size_lemma, EL_MEM] >>
          gvs [EVERY_MEM, MEM_EL, PULL_EXISTS]) >>
      FULL_CASE_TAC >> gvs [] >>
      irule AP_THM >> gvs [] >>
      rpt $ AP_TERM_TAC >>
      irule LIST_EQ >> rw [EL_MAP] >>
      last_x_assum $ irule_at Any >>
      irule_at Any EQ_REFL >> qexists_tac ‘f’ >>
      rename1 ‘n < LENGTH _’ >>
      ‘cexp_size f (EL n l) < cexp10_size f l’ by metis_tac [cexp_size_lemma, EL_MEM] >>
      gvs [EVERY_MEM, MEM_EL, PULL_EXISTS])
  >- (rw [] >> AP_TERM_TAC >>
      last_x_assum irule >> irule_at Any EQ_REFL >>
      qexists_tac ‘f’ >> gvs [cexp_size_def])
  >- (rw [] >>
      rename1 ‘_ (demands_analysis_fun c1 e2 fds) = _ (demands_analysis_fun c2 _ _)’ >>
      first_assum $ qspecl_then [‘cexp_size f e2’] assume_tac >> gvs [cexp_size_def] >>
      pop_assum $ qspecl_then [‘f’, ‘e2’] assume_tac >> gvs [] >>
      pop_assum $ qspecl_then [‘c1’, ‘c2’, ‘fds’] assume_tac >> gvs [] >>
      qabbrev_tac ‘p = demands_analysis_fun c2 e2 fds’ >> PairCases_on ‘p’ >> gvs [] >>
      AP_TERM_TAC >>
      last_x_assum irule >>
      irule_at Any EQ_REFL >> qexists_tac ‘f’ >> gvs [])
  >- (rw [] >>
      pairarg_tac >> gs [] >>
      IF_CASES_TAC >> gs []
      >- (rename1 ‘cexp_size f (Letrec a binds e2)’ >>
          last_x_assum $ qspec_then ‘cexp_size f e2’ assume_tac >>
          gs [cexp_size_def] >>
          first_x_assum $ resolve_then (Pos hd) (dxrule_then assume_tac) EQ_REFL >>
          irule AP_THM >> simp []) >>
      rename1 ‘Letrec a binds e2’ >>
      irule AP_THM2 >> conj_asm1_tac
      >- (AP_TERM_TAC >> irule LIST_EQ >>
          rw [EL_MAP] >>
          rename1 ‘_ (EL n _) = _’ >> gs[cexp_size_def, PULL_FORALL] >>
          ‘cexp_size f (SND (EL n binds)) < cexp7_size f binds’
            by (assume_tac cexp_size_lemma >> gvs [] >>
                first_x_assum $ irule_at Any >> gvs [MEM_EL] >>
                first_x_assum $ irule_at Any >>
                irule_at Any PAIR) >>
          qabbrev_tac ‘p = EL n binds’ >> PairCases_on ‘p’ >>
          gvs [] >> last_x_assum irule >> simp[PULL_EXISTS] >>
          irule_at Any LESS_TRANS >> first_assum $ irule_at Any >> simp[] >>
          gvs [EVERY_MEM, PULL_EXISTS, MEM_EL, EL_MAP] >>
          metis_tac[SND]) >>
      rename1 ‘_ = _ p1’ >> PairCases_on ‘p1’ >> gvs [] >>
      AP_TERM_TAC >> last_x_assum $ irule_at Any >>
      simp[cexp_size_def] >> qexists_tac ‘f’ >> simp[])
  >- (rw [] >>
      irule AP_THM2 >> conj_asm1_tac
      >- (last_x_assum $ irule_at Any >>
          irule_at Any EQ_REFL >> qexists_tac ‘f’ >> gvs [cexp_size_def]) >>
      gvs [] >> rename1 ‘_ p = _’ >> PairCases_on ‘p’ >> gvs [] >>
      qmatch_goalsub_abbrev_tac ‘_ list1 = _ list2’ >>
      ‘list1 = list2’
        by (unabbrev_all_tac >>
            pop_assum kall_tac >> pop_assum kall_tac >>
            pop_assum mp_tac >> pop_assum kall_tac >>
            Induct_on ‘l’ >> simp [FORALL_PROD] >>
            gs [cexp_size_def] >> rw [] >>
            qmatch_goalsub_abbrev_tac ‘_ list1 = _ list2’ >>
            ‘list1 = list2’
              by (unabbrev_all_tac >>
                  first_x_assum irule >> simp [] >>
                  rw [] >> first_x_assum irule >>
                  gs [] >>
                  rename1 ‘cexp_size f2 _ < _’ >>
                  qexists_tac ‘f2’ >> simp []) >>
              gvs [] >>
            pairarg_tac >> gs [] >>
            conj_tac >> AP_TERM_TAC >>
            last_x_assum irule >> simp [] >>
            qexists_tac ‘f’ >> simp []) >>
      gvs [] >>
      pairarg_tac >> gs [] >>
      CASE_TAC >> fs [] >> CASE_TAC >> fs [] >>
      AP_TERM_TAC >> first_x_assum irule >> simp [] >>
      qexists_tac ‘f’ >> simp [cexp_size_def])
QED

Theorem EL_EQ:
  (∀n. n < LENGTH l ⇒ P (EL n l)) ⇔
  (∀n. n < LENGTH l ⇒ ∀x. EL n l = x ⇒ P x)
Proof
  simp[]
QED

(*Theorem demands_analysis_ignores_ctxt:
  ∀c1 e2 m c2 m' ce fd.
    demands_analysis_fun c2 e2 m = demands_analysis_fun c1 e2 m
Proof
  recInduct demands_analysis_fun_ind >> simp[demands_analysis_fun_def] >>
  rw[]
  >- (pairarg_tac >>
      gvs[AllCaseEqs(), PULL_EXISTS, Cong MAP_CONG] >>
      simp[SF ETA_ss, SF CONJ_ss] >>
      metis_tac$ map TypeBase.nchotomy_of [“:'a list”, “:α # β”, “:α option”])
  >- (pairarg_tac >> gvs[])
  >- (pairarg_tac >> gvs[])
  >- (pairarg_tac >> gvs[] >> pairarg_tac >> gvs[Cong MAP_CONG])
  >- (simp[Cong MAP_CONG])
  >- (simp[Cong MAP_CONG] >> pairarg_tac >> simp[] >>
      pairarg_tac >> simp[] >> gvs[] >>
      pairarg_tac >> gvs[SF ETA_ss] >>
      pairarg_tac >> gvs[] >>
      qpat_x_assum ‘UNZIP3 _ = _’ mp_tac >>
      qpat_x_assum ‘UNZIP3 _ = _’ mp_tac >>
      rename [‘UNZIP3 _ = (ml1,el1,fdl1) ⇒
               UNZIP3 _ = (ml2,el2,fdl2) ⇒ _’] >>
      qmatch_abbrev_tac ‘X1 = _ ⇒ X2 = _ ⇒ _’ >>
      ‘X1 = X2’
        by (simp[Abbr‘X1’, Abbr‘X2’] >> AP_TERM_TAC >>
            simp[MAP_EQ_f, FORALL_PROD] >> metis_tac[]) >>
      simp[] >> rw[Abbr‘X1’, Abbr‘X2’] >> gvs[])
  >- (pairarg_tac >> gvs[] >>
      conj_tac >- (simp[MAP_EQ_f, FORALL_PROD] >> metis_tac[]) >>
      CASE_TAC >> fs [] >> CASE_TAC >> fs [])
QED

Theorem demands_analysis_nilctxt:
  demands_analysis_fun c e m = demands_analysis_fun Nil e m
Proof
  simp[demands_analysis_ignores_ctxt]
QED*)

Triviality find_IfDisj:
  find e1 c ∅ ds e2 NONE ⇒
  find (IfDisj s p1 e1) c ∅ ds (IfDisj s p1 e2) NONE
Proof
  rw [IfDisj_def]
  \\ rename [‘If xx _ _’]
  \\ ‘find xx c ∅ ∅ xx NONE’ by simp [Once find_cases]
  \\ dxrule find_If
  \\ disch_then dxrule \\ fs []
  \\ ‘find Fail c ∅ UNIV Fail NONE’ by simp [Once find_cases]
  \\ disch_then dxrule \\ fs []
QED

Theorem add_all_demands_soundness' =
        add_all_demands_soundness
          |> SPEC_ALL
          |> UNDISCH_ALL
          |> REWRITE_RULE [ASSUME “demands_map_to_set (m: (mlstring,α)map) = s”]
          |> DISCH_ALL |> GEN_ALL;

Theorem FOLDL_insert_binds:
  ∀(binds : (mlstring # (mlstring # bool) list # α cexp # α) list) m m2.
    map_ok m ∧ cmp_of m = mlstring$compare ∧
    m2 = FOLDL (λf (v, args, body, label). insert f v (MAP SND args)) m binds ⇒
    map_ok m2 ∧ cmp_of m2 = compare
Proof
  Induct \\ gs [union_thm, FORALL_PROD]
  \\ rpt gen_tac \\ strip_tac
  \\ last_x_assum irule
  \\ simp [insert_thm]
QED

Theorem find_exp_of_rev_split_body_inner:
  ∀args a e c.
    find (exp_of (rev_split_body_inner a args e)) c {}
         (set (MAP (λ(v, _). ([], explode v)) (FILTER SND args))) (exp_of (rev_split_body_inner a args e)) NONE
Proof
  Induct \\ gs [FORALL_PROD, rev_split_body_inner_def, find_Bottom]
  \\ gen_tac \\ Cases \\ gs [rev_split_body_inner_def, exp_of_def, op_of_def]
  \\ rw []
  \\ simp [Once INSERT_SING_UNION]
  \\ irule find_Seq2
  \\ gs []
  \\ irule_at Any find_Var
QED

Theorem demands_boolList_lemma:
  ∀args (s : ((string # num) list # string) -> bool).
    ALL_DISTINCT (MAP FST args) ∧
    (∀v. MEM v (MAP (explode o FST) args) ⇒ ((∃ps. (ps, v) ∈ s) ⇔ MEM (v, T) (MAP (λ(v, b). (explode v, b)) args))) ⇒
    demands_boolList s (MAP (explode o FST) args) = (MAP SND args, set (MAP (explode o FST) args))
Proof
  Induct \\ gs [demands_boolList_def, FORALL_PROD]
  \\ rw [] \\ pairarg_tac \\ gs []
  \\ last_x_assum $ qspec_then ‘s’ mp_tac
  \\ impl_tac
  >- (rw []
      \\ eq_tac \\ simp []
      \\ rw []
      \\ gs [MEM_MAP])
  \\ strip_tac \\ gs []
  \\ conj_tac
  >- (rename1 ‘explode p_1’
      \\ first_x_assum $ qspec_then ‘explode p_1’ assume_tac
      \\ gs []
      \\ qpat_x_assum ‘set _ = _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM
      \\ gs [MEM_MAP, EXISTS_PROD])
  \\ simp [SET_EQ_SUBSET, SUBSET_DEF]
QED

Theorem find_exp_of_rev_split_body:
    ALL_DISTINCT (MAP FST args) ∧ args ≠ [] ⇒
    find (exp_of (rev_split_body a args e)) c {} {} (exp_of (rev_split_body a args e)) (SOME (MAP SND args, {}))
Proof
  strip_tac
  \\ qspecl_then [‘args’, ‘a’, ‘e’, ‘FOLDL (λc n. IsFree n c) c (MAP (explode o FST) args)’]
                 assume_tac find_exp_of_rev_split_body_inner
  \\ dxrule_then assume_tac find_Lams_fd
  \\ gs []
  \\ qspecl_then [‘args’, ‘set (MAP (λ(v, _). ([], explode v)) (FILTER SND args))’] mp_tac demands_boolList_lemma
  \\ impl_tac
  >- (simp [MEM_MAP, PULL_EXISTS]
      \\ rw [EXISTS_PROD, MEM_FILTER])
  \\ strip_tac \\ gs []
  \\ Cases_on ‘args’
  \\ gs [rev_split_body_def, exp_of_def, MAP_MAP_o]
QED

Theorem FOLDL_insert_bind_lemma1:
  ∀binds2 v fds.
    ¬MEM v (MAP FST binds2) ∧
    map_ok fds ∧ cmp_of fds = mlstring$compare ⇒
    to_fmap (FOLDL (λf (v,args,body,label). insert f v (MAP SND args)) fds binds2) ' v
    = to_fmap fds ' v
Proof
  Induct \\ gs [FORALL_PROD]
  \\ rw []
  \\ irule EQ_TRANS
  \\ first_x_assum $ irule_at Any
  \\ gs [insert_thm, FAPPLY_FUPDATE_THM]
QED

Theorem FOLDL_insert_bind_lemma:
  ∀binds2 v (args : (mlstring # bool) list) (p : α cexp # α) fds.
    ALL_DISTINCT (MAP FST binds2) ∧ MEM (v, args, p) binds2 ∧
    map_ok fds ∧ cmp_of fds = mlstring$compare ⇒
    MAP SND args =
    to_fmap (FOLDL (λf (v,args,body,label). insert f v (MAP SND args)) fds binds2) ' v
Proof
  Induct \\ gs [FORALL_PROD]
  \\ rw []
  >- (irule EQ_TRANS
      \\ irule_at Any $ GSYM FOLDL_insert_bind_lemma1
      \\ gs [insert_thm, FAPPLY_FUPDATE_THM])
  \\ last_x_assum irule
  \\ gs [insert_thm]
  \\ first_x_assum $ irule_at Any
QED

Theorem in_FOLDL_insert_binds:
  ∀binds v bL fds.
    (v, bL) ∈ fdemands_map_to_set (FOLDL (λf (v, args, body, label). insert f v (MAP SND args)) fds binds) ∧
    map_ok fds ∧ cmp_of fds = mlstring$compare ∧
    ¬MEM v (MAP (explode o FST) binds) ⇒
    (v, bL) ∈ fdemands_map_to_set fds
Proof
  Induct \\ gs [FORALL_PROD]
  \\ rw []
  \\ last_x_assum $ dxrule_then assume_tac
  \\ gs [insert_thm]
  \\ dxrule_then assume_tac fdemands_map_insert
  \\ gs []
QED

Theorem letrecs_distinct_adds_demands:
  ∀vL a m e fd.
      letrecs_distinct (exp_of e) ⇒
      letrecs_distinct (exp_of (adds_demands a (m, e, fd) vL))
Proof
  Induct \\ gs [adds_demands_def]
  \\ rw []
  \\ CASE_TAC \\ gs [exp_of_def, letrecs_distinct_def]
QED

Theorem FOLDR_Case_demands_lemma:
  ∀row l1 l2 c s f a.
    FOLDR (λ(name, args, cd) (lD, lRows).
             (FST (demands_analysis_fun (Unfold name s args c) cd (FOLDL (λm v. delete m v) f args))::lD,
              (name, args, add_all_demands a (demands_analysis_fun (Unfold name s args c) cd
                                              (FOLDL (λm v. delete m v) f args)))::lRows)) (l1, l2) row
    = (MAP (λ(name, args, cd). FST (demands_analysis_fun (Unfold name s args c) cd
                                    (FOLDL (λm v. delete m v) f args))) row ++ l1,
       MAP (λ(name, args, cd). (name, args, add_all_demands a (demands_analysis_fun (Unfold name s args c) cd
                                                               (FOLDL (λm v. delete m v) f args)))) row ++ l2)
Proof
  Induct >> simp [FORALL_PROD]
QED

Theorem demands_analysis_soundness_lemma:
  ∀(f: α -> num) (e: α cexp) c fds m e' fd.
    demands_analysis_fun c e fds = (m, e', fd) ∧ map_ok fds ∧
    cmp_of fds = compare ∧ NestedCase_free e ∧ cexp_wf e ∧
    letrecs_distinct (exp_of e)
    ⇒
    find (exp_of e) (ctxt_trans c) (fdemands_map_to_set fds)
         (demands_map_to_set m) (exp_of e') (fd_to_set fd) ∧
    map_ok m ∧ cmp_of m = compare ∧ letrecs_distinct (exp_of e') ∧
    ∀bL fd_map. SOME (bL, fd_map) = fd ⇒
                map_ok fd_map ∧ cmp_of fd_map = compare
Proof
  gen_tac
  \\ completeInduct_on ‘cexp_size f e’
  \\ gen_tac
  \\ Cases
  \\ rename1 ‘Size = cexp_size _ _’
  \\ strip_tac
  \\ simp [demands_analysis_fun_def, exp_of_def]
  \\ gvs [demands_map_empty, demands_map_insert, demands_map_union,
         TotOrd_compare, insert_thm, empty_thm, cexp_wf_def, letrecs_distinct_def] >~
  [‘Var a n’]
  >- (rw [] \\ rename1 ‘lookup fds n’
      \\ Cases_on ‘lookup fds n’
      \\ gvs [find_Var, fd_to_set_def, demands_map_empty,
              find_Var2, fdemands_map_to_set_soundness, empty_thm,
              TotOrd_compare]) >~
  [‘Prim a op l’]
  >- (Cases_on ‘op’ >~
      [‘Prim a Seq l’]
      >- (Cases_on ‘l’ >~[‘Prim a Seq []’]
          \\ gvs [demands_analysis_fun_def, op_of_def, fd_to_set_def,
                  demands_map_empty, letrecs_distinct_def,
                  exp_of_def, empty_thm, TotOrd_compare, find_Bottom]
          \\ rename1 ‘e1::t’
          \\ Cases_on ‘t’ >~[‘Prim a Seq [e]’]
          >- (rw [demands_analysis_fun_def, empty_thm, fd_to_set_def, demands_map_empty,
                  TotOrd_compare]
              \\ gs [letrecs_distinct_def, exp_of_def, op_of_def]
              \\ irule find_Eq \\ irule_at Any find_Bottom
              \\ irule exp_eq_IMP_exp_eq_in_ctxt
              \\ fs [exp_of_def, op_of_def, eval_wh_IMP_exp_eq,
                     eval_wh_def, eval_wh_to_def, subst_def])
          \\ rename1 ‘e1::e2::t’
          \\ Cases_on ‘t’ >~
          [‘Prim a Seq (e1::e2::e3::t)’]
          >- (rw [demands_analysis_fun_def, empty_thm, fd_to_set_def,
                  demands_map_empty, TotOrd_compare]
              \\ gs [letrecs_distinct_def, exp_of_def, op_of_def]
              \\ irule find_Eq \\ irule_at Any find_Bottom
              \\ irule exp_eq_IMP_exp_eq_in_ctxt
              \\ fs [exp_of_def, op_of_def, eval_wh_IMP_exp_eq,
                     eval_wh_def, eval_wh_to_def, subst_def])
          \\ rw []
          \\ first_assum   $ qspecl_then [‘cexp_size f e1’] assume_tac
          \\ first_x_assum $ qspecl_then [‘cexp_size f e2’] assume_tac
          \\ fs [cexp_size_def, cexp_size_lemma]
          \\ pop_assum     $ qspecl_then [‘f’, ‘e2’] assume_tac
          \\ first_x_assum $ qspecl_then [‘f’, ‘e1’] assume_tac
          \\ fs [demands_analysis_fun_def, exp_of_def]
          \\ rename1 ‘demands_analysis_fun c _ fds’
          \\ pop_assum     $ qspecl_then [‘c’, ‘fds’] assume_tac
          \\ first_x_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
          \\ qabbrev_tac ‘p1 = demands_analysis_fun c e1 fds’
          \\ qabbrev_tac ‘p2 = demands_analysis_fun c e2 fds’
          \\ PairCases_on ‘p1’
          \\ PairCases_on ‘p2’
          \\ gvs [exp_of_def, op_of_def, demands_map_union, union_thm, letrecs_distinct_def]
          \\ dxrule_then (dxrule_then irule) find_Seq2) >~
      [‘AtomOp op = AtomOp (Lit _)’]
      >- (rpt gen_tac \\ strip_tac
          \\ gvs [exp_of_def, op_of_def, demands_analysis_fun_def, UNZIP3_MAP,
                  letrecs_distinct_def, MAP_MAP_o, combinTheory.o_DEF]
          \\ rename1 ‘demands_analysis_fun c _ fds’
          \\ irule_at Any FOLDL_union_cmp_of \\ irule_at Any FOLDL_union_map_ok
          \\ irule_at Any TotOrd_compare
          \\ gvs [empty_thm, TotOrd_compare]
          \\ conj_asm1_tac
          >- (rw [EVERY_EL] \\ rename1 ‘i < LENGTH l’
              \\ last_x_assum $ qspecl_then [‘cexp_size f (EL i l)’] assume_tac
              \\ ‘cexp_size f (EL i l) < list_size (cexp_size f) l’
                   by metis_tac [cexp_size_lemma, EL_MEM, cexp_size_eq]
              \\ fs [cexp_size_def, cexp_size_eq]
              \\ pop_assum kall_tac
              \\ pop_assum $ qspecl_then [‘f’, ‘EL i l’] assume_tac
              \\ fs []
              \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
              \\ qabbrev_tac ‘p = demands_analysis_fun c (EL i l) fds’
              \\ PairCases_on ‘p’
              \\ gvs [EL_MAP, EVERY_MEM, MEM_EL, PULL_EXISTS])
          \\ assume_tac TotOrd_compare
          \\ dxrule_then (drule_then assume_tac) demands_map_FOLDL
          \\ pop_assum $ qspecl_then [‘empty compare’] assume_tac
          \\ gvs [TotOrd_compare, empty_thm, demands_map_empty, EVERY_CONJ,
                  fd_to_set_def]
          \\ conj_tac
          >- (irule find_Atom \\ fs [] \\ qexists_tac ‘NONE’
              \\ rw [LIST_REL_EL_EQN, EL_ZIP, EL_MAP, EVERY_EL]
              \\ rename1 ‘EL n l’
              \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n l)’] assume_tac
              \\ ‘cexp_size f (EL n l) < list_size (cexp_size f) l’
                by metis_tac [cexp_size_lemma, EL_MEM, cexp_size_eq]
              \\ fs [cexp_size_def, cexp_size_eq]
              \\ pop_assum kall_tac
              \\ pop_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
              \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n l) fds’
              \\ PairCases_on ‘p’ \\ gvs [EVERY_EL]
              \\ first_x_assum $ drule_then assume_tac
              \\ gs [EL_MAP]
              \\ dxrule_then assume_tac find_Drop_fd \\ fs [])
          >- (rw [EL_MAP, EVERY_EL]
              \\ rename1 ‘EL n l’
              \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n l)’] assume_tac
              \\ ‘cexp_size f (EL n l) < list_size (cexp_size f) l’
                by metis_tac [cexp_size_lemma, EL_MEM, cexp_size_eq]
              \\ fs [cexp_size_def, cexp_size_eq]
              \\ pop_assum kall_tac
              \\ pop_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
              \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n l) fds’
              \\ PairCases_on ‘p’ \\ gvs [EVERY_EL]
              \\ first_x_assum $ drule_then assume_tac
              \\ gs [EL_MAP]))
      \\ rpt gen_tac \\ strip_tac (* Cons s *)
      \\ fs [empty_thm, TotOrd_compare, demands_analysis_fun_def, letrecs_distinct_def, demands_map_empty]
      \\ qpat_x_assum ‘Prim _ _ _ = _’ assume_tac
      \\ dxrule_then assume_tac EQ_SYM
      \\ gs [exp_of_def, op_of_def, fd_to_set_def, letrecs_distinct_def]
      \\ irule_at Any find_Prim \\ rw [EVERY_EL]
      \\ rename1 ‘k < LENGTH l’
      \\ first_x_assum $ qspecl_then [‘cexp_size f (EL k l)’] assume_tac
      \\ ‘cexp_size f (EL k l) < list_size (cexp_size f) l’
        by metis_tac [cexp_size_lemma, MEM_EL, cexp_size_eq]
      \\ fs [cexp_size_def, cexp_size_eq]
      \\ pop_assum kall_tac
      \\ rename1 ‘demands_analysis_fun c _ fds’
      \\ pop_assum $ qspecl_then [‘f’, ‘EL k l’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
      \\ qabbrev_tac ‘p = demands_analysis_fun c (EL k l) fds’
      \\ PairCases_on ‘p’
      \\ fs [EL_MAP]
      >- (irule_at Any add_all_demands_soundness
          \\ gvs [cmp_of_def, TotOrd_compare, EVERY_EL, EL_MAP]
          \\ first_x_assum $ irule_at Any)
      >- (rename1 ‘add_all_demands _ (p0, _, _)’
          \\ Cases_on ‘p0’
          \\ gs [add_all_demands_def, cmp_of_def, EVERY_EL, EL_MAP]
          \\ irule letrecs_distinct_add_all_demands_lemma
          \\ simp []))
  >~[‘App a fe argl’]
  >- (rpt gen_tac
      \\ rename1 ‘demands_analysis_fun c _ fds’
      \\ qabbrev_tac ‘p = demands_analysis_fun c fe fds’
      \\ PairCases_on ‘p’
      \\ first_assum $ qspecl_then [‘cexp_size f fe’] assume_tac
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘fe’] assume_tac
      \\ fs []
      \\ pop_assum $ drule_then assume_tac \\ strip_tac
      \\ rename1 ‘demands_analysis_fun _ _ _ = (d_fe, fe', fd_fe)’
      \\ Cases_on ‘fd_fe’
      \\ gvs [fd_to_set_def, exp_of_def, EVERY_EL, letrecs_distinct_Apps]
      >- (irule_at Any find_Apps \\ first_x_assum $ irule_at Any
          \\ rw [LIST_REL_EL_EQN, EL_MAP]
          \\ rename1 ‘EL n argl’
          \\ last_x_assum $ qspecl_then [‘cexp_size f (EL n argl)’] assume_tac
          \\ ‘cexp_size f (EL n argl) < list_size (cexp_size f) argl’
            by metis_tac [cexp_size_lemma, MEM_EL, cexp_size_eq]
          \\ fs [cexp_size_def, cexp_size_eq]
          \\ pop_assum kall_tac
          \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl’] assume_tac
          \\ gs [EVERY_EL, EL_MAP]
          \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
          \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl) fds’
          \\ PairCases_on ‘p’ \\ fs []
          >- (irule_at Any add_all_demands_soundness
              \\ gvs [TotOrd_compare] \\ first_x_assum $ irule_at Any)
          >- (rename1 ‘add_all_demands _ (p0, _, _)’
              \\ Cases_on ‘p0’
              \\ gs [add_all_demands_def, cmp_of_def, EVERY_EL, EL_MAP]
              \\ irule letrecs_distinct_add_all_demands_lemma
              \\ simp []))
      \\ FULL_CASE_TAC \\ gvs []
      \\ rename1 ‘handle_Apps_demands a fdL (MAP _ argl)’
      \\ qabbrev_tac ‘hAd = handle_Apps_demands a fdL (MAP (λe. demands_analysis_fun c e fds) argl)’
      \\ PairCases_on ‘hAd’ \\ fs []
      \\ drule_then assume_tac handle_Apps_demands_soundness
      \\ ‘EVERY (λ(dm, e, _). map_ok dm ∧ cmp_of dm = compare)
                (MAP (λe. demands_analysis_fun c e fds) argl)’
        by (rw [EVERY_EL, EL_MAP] \\ rename1 ‘EL n argl’
            \\ last_x_assum $
                 qspecl_then [‘cexp_size f (EL n argl)’] assume_tac
            \\ ‘cexp_size f (EL n argl) < list_size (cexp_size f) argl’
              by metis_tac [cexp_size_lemma, MEM_EL, cexp_size_eq]
            \\ fs [cexp_size_def, cexp_size_eq]
            \\ pop_assum kall_tac
            \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl’] assume_tac
            \\ fs []
            \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
            \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl) fds’
            \\ PairCases_on ‘p’
            \\ gs [EVERY_EL, EL_MAP])
      \\ first_x_assum $ dxrule_then assume_tac
      \\ gvs []
      \\ FULL_CASE_TAC \\ gvs [union_thm, fd_to_set_def, demands_map_union, exp_of_def]
      >- (rename1 ‘argl1 ++ argl2’
          \\ qabbrev_tac ‘hAd' = handle_Apps_demands a fdL (MAP (λe. demands_analysis_fun c e fds) argl1)’
          \\ PairCases_on ‘hAd'’ \\ gvs [Apps_append]
          \\ reverse conj_tac
          >- (gs [letrecs_distinct_Apps, EVERY_EL, EL_MAP]
              \\ rw []
              >- (rename1 ‘n < _’
                  \\ last_x_assum $ qspec_then ‘cexp_size f (EL n (argl1 ++ argl2))’ assume_tac
                  \\ gs []
                  \\ ‘cexp_size f (EL n (argl1 ++ argl2)) < cexp10_size f (argl1 ++ argl2)’
                    by (assume_tac cexp_size_lemma
                        \\ gs []
                        \\ first_x_assum irule
                        \\ gs [EL_MEM])
                  \\ gs [] \\ pop_assum kall_tac
                  \\ rpt $ first_x_assum $ qspec_then ‘n’ assume_tac
                  \\ first_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
                  \\ gs [EL_APPEND_EQN]
                  \\ qabbrev_tac ‘dsf = demands_analysis_fun c (EL n argl1) fds’
                  \\ PairCases_on ‘dsf’
                  \\ gs []
                  \\ first_x_assum $ dxrule_then assume_tac
                  \\ gs [EL_MAP]
                  \\ IF_CASES_TAC \\ gs []
                  \\ rename1 ‘add_all_demands _ (p0, _, _)’
                  \\ Cases_on ‘p0’
                  \\ gs [add_all_demands_def, cmp_of_def, EVERY_EL, EL_MAP]
                  \\ irule letrecs_distinct_add_all_demands_lemma
                  \\ simp [])
              >- (rename1 ‘n < _’
                  \\ last_x_assum $ qspec_then ‘cexp_size f (EL (n + LENGTH argl1) (argl1 ++ argl2))’ assume_tac
                  \\ gs []
                  \\ ‘cexp_size f (EL (n + LENGTH argl1) (argl1 ++ argl2)) < cexp10_size f (argl1 ++ argl2)’
                    by (assume_tac cexp_size_lemma
                        \\ gs []
                        \\ first_x_assum irule
                        \\ gs [EL_MEM])
                  \\ gs [] \\ pop_assum kall_tac
                  \\ rpt $ first_x_assum $ qspec_then ‘n + LENGTH argl1’ assume_tac
                  \\ first_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
                  \\ gs [EL_APPEND_EQN]
                  \\ qabbrev_tac ‘dsf = demands_analysis_fun c (EL n argl2) fds’
                  \\ PairCases_on ‘dsf’
                  \\ gs []
                  \\ first_x_assum $ dxrule_then assume_tac
                  \\ gs [EL_MAP]
                  \\ rename1 ‘add_all_demands _ (p0, _, _)’
                  \\ Cases_on ‘p0’
                  \\ gs [add_all_demands_def, cmp_of_def, EVERY_EL, EL_MAP]
                  \\ irule letrecs_distinct_add_all_demands_lemma
                  \\ simp []))
          \\ irule find_Apps
          \\ irule_at Any find_No_args
          \\ irule_at Any find_Apps_fd
          \\ gvs []
          \\ qpat_x_assum ‘find _ _ _ _ _ _’ $ irule_at Any
          \\ qexists_tac ‘MAP (λe. demands_map_to_set (FST (demands_analysis_fun c e fds))) argl1’
          \\ gvs [LIST_REL_EL_EQN, FORALL_PROD] \\ rw [] \\ gvs []
          >~[‘(ps, v) ∈ demands_map_to_set hAd'2’]
          >- (disj2_tac \\ last_x_assum $ dxrule_then assume_tac
              \\ gvs [] \\ first_assum $ irule_at Any \\ gvs [EL_MAP, EL_APPEND_EQN])
          >- (gvs [EL_ZIP, EL_MAP] \\ rename1 ‘n < LENGTH _’
              \\ first_x_assum $ qspecl_then [‘n’] assume_tac \\ gvs [EL_APPEND_EQN]
              \\ last_x_assum $ qspecl_then [‘cexp_size f (EL n (argl1 ++ argl2))’] assume_tac
              \\ ‘cexp_size f (EL n (argl1 ++ argl2)) <
                  list_size (cexp_size f) (argl1 ++ argl2)’
                by (assume_tac cexp_size_lemma >> gvs [cexp_size_eq] >>
                    first_x_assum irule >>
                    irule EL_MEM >> fs [])
              \\ fs [cexp_size_def, cexp_size_eq]
              \\ pop_assum kall_tac
              \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl1’] assume_tac
              \\ gvs [EL_APPEND_EQN]
              \\ pop_assum $ qspecl_then [‘c’] assume_tac
              \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl1) fds’
              \\ PairCases_on ‘p’ \\ fs []
              \\ first_x_assum $ drule_then assume_tac
              \\ FULL_CASE_TAC \\ gvs [EVERY_EL, EL_MAP]
              >- (first_assum (irule_at Any o cj 1) >>
                  metis_tac[DECIDE “n:num < x ⇒ n < x + y”])
              >- (irule_at Any add_all_demands_soundness
                  \\ first_assum (irule_at Any o cj 1)
                  \\ rename1 ‘n < _’
                  \\ rpt $ last_x_assum $ qspec_then ‘n’ assume_tac
                  \\ gs [TotOrd_compare]))
          >- (gvs [EL_MAP] \\ rename1 ‘n < LENGTH _’
              \\ first_x_assum $ qspecl_then [‘n + LENGTH argl1’] assume_tac \\ gvs [EL_APPEND_EQN]
              \\ last_x_assum $ qspecl_then [‘cexp_size f (EL (n + LENGTH argl1) (argl1 ++ argl2))’] assume_tac
              \\ ‘cexp_size f (EL (n + LENGTH argl1) (argl1 ++ argl2)) <
                  list_size (cexp_size f) (argl1 ++ argl2)’
                by (assume_tac cexp_size_lemma >> gvs [cexp_size_eq] >>
                    first_x_assum irule >>
                    irule EL_MEM >> fs [])
              \\ fs [cexp_size_def, cexp_size_eq]
              \\ pop_assum kall_tac
              \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl2’] assume_tac
              \\ gvs [EL_APPEND_EQN]
              \\ pop_assum $ qspecl_then [‘c’] assume_tac
              \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl2) fds’
              \\ PairCases_on ‘p’ \\ fs []
              \\ first_x_assum $ drule_then assume_tac
              \\ irule_at Any add_all_demands_soundness
              \\ gvs [EVERY_EL, EL_MAP]
              \\ pop_assum mp_tac \\ impl_tac
              >- (first_x_assum $ qspec_then ‘n + LENGTH fdL’ mp_tac >>
                  first_x_assum $ qspec_then ‘n + LENGTH fdL’ mp_tac >>
                  first_x_assum $ qspec_then ‘n + LENGTH fdL’ mp_tac >>
                  simp[])
              \\ strip_tac
              \\ first_x_assum $ irule_at Any
              \\ gvs [TotOrd_compare]))
      \\ reverse conj_tac
      >- (simp [letrecs_distinct_Apps]
          \\ gs [EVERY_EL, EL_MAP]
          \\ gen_tac \\ strip_tac
          \\ rename1 ‘n < _’
          \\ last_x_assum $ qspec_then ‘cexp_size f (EL n argl)’ assume_tac
          \\ ‘cexp_size f (EL n argl) < list_size (cexp_size f) argl’
            by metis_tac [cexp_size_lemma, MEM_EL, cexp_size_eq]
          \\ fs [cexp_size_def, cexp_size_eq]
          \\ pop_assum kall_tac
          \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl’] assume_tac
          \\ fs []
          \\ pop_assum $ qspecl_then [‘c’] assume_tac
          \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl) fds’
          \\ PairCases_on ‘p’ \\ fs []
          \\ first_x_assum $ drule_then assume_tac \\ gvs []
          \\ IF_CASES_TAC \\ gs []
          \\ rename1 ‘add_all_demands _ (p0, _, _)’
          \\ Cases_on ‘p0’
          \\ gs [add_all_demands_def, cmp_of_def, EVERY_EL, EL_MAP]
          \\ irule letrecs_distinct_add_all_demands_lemma
          \\ simp [])
      \\ irule find_Apps_fd
      \\ rename1 ‘bL2 ++ [h] ++ t’ \\ qexists_tac ‘bL2’
      \\ ‘bL2 ++ h::t = bL2 ++ [h] ++ t’ by gvs [] \\ rw []
      \\ pop_assum kall_tac \\ first_x_assum $ irule_at $ Pos last
      \\ qexists_tac ‘MAP (λe. demands_map_to_set (FST (demands_analysis_fun c e fds))) argl’
      \\ rw [LIST_REL_EL_EQN] \\ gvs []
      >- (disj2_tac \\ last_x_assum $ dxrule_then assume_tac
          \\ gvs [] \\ first_assum $ irule_at Any
          \\ gvs [EL_MAP, EL_APPEND_EQN])
      \\ first_x_assum $ drule_then assume_tac
      \\ gvs [EL_ZIP, EL_MAP]
      \\ rename1 ‘EL n _’
      \\ last_x_assum $ qspecl_then [‘cexp_size f (EL n argl)’] assume_tac
      \\ ‘cexp_size f (EL n argl) < list_size (cexp_size f) argl’
        by metis_tac [cexp_size_lemma, MEM_EL, cexp_size_eq]
      \\ fs [cexp_size_def, cexp_size_eq]
      \\ pop_assum kall_tac
      \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’] assume_tac
      \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl) fds’
      \\ PairCases_on ‘p’ \\ fs []
      \\ first_x_assum $ drule_then assume_tac \\ gvs []
      \\ FULL_CASE_TAC
      >- first_assum $ irule_at Any
      \\ irule_at Any add_all_demands_soundness
      \\ first_x_assum $ irule_at Any
      \\ gvs [TotOrd_compare])
  >~ [‘Lam a namel e’]
  >- (rw []
      \\ first_assum $ qspecl_then [‘cexp_size f e’] assume_tac
      \\ fs [cexp_size_def, letrecs_distinct_Lams]
      \\ pop_assum $ qspecl_then [‘f’, ‘e’] assume_tac
      \\ rename1 ‘demands_analysis_fun (IsFree namel c) _ (FOLDL _ fds _)’
      \\ qabbrev_tac ‘p = demands_analysis_fun (IsFree namel c) e
                                               (FOLDL (λf k. delete f k) fds namel)’
      \\ PairCases_on ‘p’ \\ fs [empty_thm, TotOrd_compare]
      \\ first_x_assum $ drule_then assume_tac
      \\ gvs [exp_of_def, fd_to_set_def, demands_map_empty, ctxt_trans_def,
              FOLDL_delete_ok, boolList_of_fdemands_soundness, letrecs_distinct_def]
      >- (irule find_Subset
          \\ irule_at Any find_Lams_fd
          \\ irule_at Any add_all_demands_soundness
          \\ irule_at Any find_Drop_fd \\ gvs [FOLDL_MAP]
          \\ first_x_assum $ irule_at $ Pos hd
          \\ gvs [fdemands_map_FOLDL_delete_subset, boolList_of_fdemands_def, EVERY_MEM,
                  fdemands_map_FOLDL_delete, TotOrd_compare, MEM_MAP, PULL_EXISTS])
      >- (simp [letrecs_distinct_Lams]
          \\ rename1 ‘add_all_demands _ (p0, _, _)’
          \\ Cases_on ‘p0’
          \\ gs [add_all_demands_def, cmp_of_def, EVERY_EL, EL_MAP]
          \\ irule letrecs_distinct_add_all_demands_lemma
          \\ simp []))
  >~ [‘Let a vname e2 e1’]
  >- (rpt gen_tac \\ strip_tac
      \\ rename1 ‘find _ (ctxt_trans c) (fdemands_map_to_set fds)’
      \\ first_assum $ qspecl_then [‘cexp_size f e1’] assume_tac
      \\ first_x_assum $ qspecl_then [‘cexp_size f e2’] assume_tac
      \\ fs [cexp_size_def]
      \\ first_x_assum $ qspecl_then [‘f’, ‘e2’] assume_tac
      \\ first_x_assum $ qspecl_then [‘f’, ‘e1’] assume_tac
      \\ qabbrev_tac ‘p2 = demands_analysis_fun c e2 fds’ \\ PairCases_on ‘p2’ \\ fs []
      \\ rename1 ‘demands_analysis_fun _ _ _ = (_, _, p22)’
      \\ qabbrev_tac ‘p1 = demands_analysis_fun (Bind vname e2 c) e1
                                        (case p22 of
                                           | NONE => delete fds vname
                                           | SOME (bL, _) => insert fds vname bL)’
      \\ PairCases_on ‘p1’ \\ fs []
      \\ last_x_assum $ drule_then assume_tac
      \\ last_x_assum $ drule_then assume_tac
      \\ gvs [demands_map_empty, delete_thm]
      \\ irule_at Any find_Subset
      \\ fs [ctxt_trans_def]
      \\ rpt $ FULL_CASE_TAC
      \\ gvs [ctxt_trans_def, fd_to_set_def, lookup_thm,
              exp_of_def, op_of_def, delete_thm, letrecs_distinct_def]
      >>~[‘FLOOKUP _ _ = NONE’]
      >- (irule_at Any find_Let \\ first_x_assum $ irule_at Any
          \\ first_x_assum $ irule_at Any
          \\ gvs [demands_map_delete, FLOOKUP_DEF, dest_fd_SND_def, demands_map_to_set_def]
          \\ rw [] \\ gvs [implode_explode, delete_thm]
          \\ last_x_assum $ assume_tac
          \\ dxrule_then (dxrule_then assume_tac) fdemands_map_delete_soundness
          \\ fs [])
      >- (irule_at Any find_Let \\ first_x_assum $ irule_at (Pos hd)
          \\ irule_at Any find_smaller_fd \\ first_x_assum $ irule_at Any
          \\ gvs [demands_map_delete, dest_fd_SND_def, demands_map_to_set_def, FLOOKUP_DEF]
          \\ rw [] \\ gvs [implode_explode, delete_thm]
          \\ last_x_assum $ assume_tac
          \\ dxrule_then (dxrule_then assume_tac) fdemands_map_delete_soundness
          \\ fs [])
      >- (FULL_CASE_TAC \\ gvs [insert_thm, delete_thm, fd_to_set_def]
          \\ irule_at Any find_Let
          \\ first_x_assum $ irule_at Any
          \\ first_x_assum $ irule_at Any
          \\ gvs [lookup_thm, demands_map_delete, FLOOKUP_DEF, dest_fd_SND_def,
                  demands_map_to_set_def]
          \\ rw [] \\ gvs [implode_explode, delete_thm]
          \\ dxrule_then assume_tac fdemands_map_insert \\ gvs [])
      >- (FULL_CASE_TAC \\ gvs [insert_thm, fd_to_set_def, delete_thm]
          \\ irule_at Any find_Let
          \\ first_x_assum $ irule_at (Pos hd)
          \\ irule_at Any find_smaller_fd \\ first_x_assum $ irule_at Any
          \\ gvs [lookup_thm, demands_map_delete_subset, dest_fd_SND_def,
                  demands_map_to_set_def, FLOOKUP_DEF]
          \\ rw [] \\ gvs [implode_explode, delete_thm]
          \\ dxrule_then assume_tac fdemands_map_insert \\ gvs [])
      \\ irule_at Any find_Let2 \\ irule_at Any find_Seq
      >- (first_x_assum $ irule_at Any \\ first_x_assum $ irule_at Any
          \\ rpt $ irule_at Any demands_map_in_FDOM
          \\ gvs [dest_fd_SND_def, FLOOKUP_DEF]
          \\ rename1 ‘demands_map_to_set (delete p10 vname)’
          \\ qexists_tac ‘demands_map_to_set (delete p10 vname)’
          \\ rw [find_subset_aid]
          >- (dxrule_then (dxrule_then assume_tac) demands_map_delete_soundness
              \\ gvs [])
          \\ last_x_assum $ assume_tac
          \\ dxrule_then (dxrule_then assume_tac) fdemands_map_delete_soundness
          \\ fs [])
      >- (FULL_CASE_TAC \\ gvs [fd_to_set_def, dest_fd_SND_def, insert_thm]
          \\ first_x_assum $ irule_at Any \\ first_x_assum $ irule_at Any
          \\ rpt $ irule_at Any demands_map_in_FDOM
          \\ gvs [lookup_thm, FLOOKUP_DEF, delete_thm]
          \\ rename1 ‘demands_map_to_set (delete p10 vname)’
          \\ qexists_tac ‘demands_map_to_set (delete p10 vname)’
          \\ rw [find_subset_aid]
          >- (dxrule_then (dxrule_then assume_tac) demands_map_delete_soundness
              \\ gvs [])
          \\ dxrule_then assume_tac fdemands_map_insert
          \\ gvs [])
      >- (gvs [fd_to_set_def, dest_fd_SND_def]
          \\ first_x_assum $ irule_at Any
          \\ irule_at Any find_smaller_fd \\ first_x_assum $ irule_at Any
          \\ rpt $ irule_at Any demands_map_in_FDOM
          \\ gvs [demands_map_delete_subset, demands_map_delete, FLOOKUP_DEF]
          \\ rename1 ‘demands_map_to_set (delete p10 vname)’
          \\ qexists_tac ‘demands_map_to_set (delete p10 vname)’
          \\ rw [find_subset_aid]
          >- (dxrule_then (dxrule_then assume_tac) demands_map_delete_soundness
              \\ gvs [])
          \\ last_x_assum $ assume_tac
          \\ dxrule_then (dxrule_then assume_tac) fdemands_map_delete_soundness
          \\ fs [])
      >- (FULL_CASE_TAC \\ gvs [fd_to_set_def, delete_thm, dest_fd_SND_def, insert_thm]
          \\ first_x_assum $ irule_at Any
          \\ irule_at Any find_smaller_fd \\ first_x_assum $ irule_at Any
          \\ rpt $ irule_at Any demands_map_in_FDOM
          \\ gvs [demands_map_delete_subset, demands_map_delete, FLOOKUP_DEF, lookup_thm]
          \\ rename1 ‘demands_map_to_set (delete p10 vname)’
          \\ qexists_tac ‘demands_map_to_set (delete p10 vname)’
          \\ rw [find_subset_aid]
          >- (dxrule_then (dxrule_then assume_tac) demands_map_delete_soundness
              \\ gvs [])
          \\ dxrule_then assume_tac fdemands_map_insert
          \\ gvs []))
  >~ [‘Letrec a binds exp’]
  >- (rpt gen_tac
      \\ pairarg_tac \\ gs []
      \\ IF_CASES_TAC
      >- (pairarg_tac \\ gs []
          \\ dxrule_then assume_tac fixpoint_analysis_soundness
          \\ strip_tac \\ gs [exp_of_def, cexp_wf_def]
          \\ first_x_assum $ drule_then assume_tac \\ gs []
          \\ irule_at Any find_trans
          \\ irule_at Any find_Subset
          \\ gs [letrecs_distinct_def]
          \\ pop_assum mp_tac
          \\ impl_tac
          >- (irule ALL_DISTINCT_IMP2
              \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
          \\ strip_tac
          \\ first_x_assum $ irule_at Any
          \\ simp []
          \\ qexists_tac ‘{}’ \\ simp []
          \\ rename1 ‘cexp_size f _’
          \\ last_x_assum $ qspec_then ‘cexp_size f exp’ assume_tac
          \\ gs [cexp_size_def]
          \\ pop_assum $ resolve_then (Pos hd) (dxrule_then assume_tac) EQ_REFL
          \\ gs []
          \\ pop_assum mp_tac
          \\ impl_tac
          >- (irule FOLDL_insert_binds
              \\ irule_at Any EQ_REFL
              \\ simp [])
          \\ strip_tac
          \\ qpat_x_assum ‘FOLDL _ _ _ = _’ assume_tac
          \\ dxrule_then assume_tac EQ_SYM
          \\ gs [FOLDL_delete_ok]
          \\ qpat_x_assum ‘Letrec _ _ _ = _’ assume_tac
          \\ dxrule_then assume_tac EQ_SYM \\ simp [exp_of_def]
          \\ irule_at Any find_Subset
          \\ irule_at Any find_Letrec
          \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
          \\ irule_at Any adds_demands_soundness
          \\ simp []
          \\ qpat_x_assum ‘find _ (ctxt_trans _) _ _ _ _’ mp_tac
          \\ qmatch_goalsub_abbrev_tac ‘find _ _ fds_abbrev _ _ _’
          \\ strip_tac
          \\ qexists_tac ‘fds_abbrev’
          \\ qexists_tac ‘BIGUNION $ IMAGE (λ(v, bL). if MEM v (MAP (explode o FST) binds2)
                                                      then {}
                                                      else {(v, bL)}) fds_abbrev’
          \\ qexists_tac ‘MAP (λ(v, args, body, label). SOME (MAP SND args, {})) binds2’
          \\ qexists_tac ‘MAP (K {}) binds2’
          \\ qexists_tac ‘demands_map_to_set (FOLDL (λf k. delete f k) m' (MAP FST binds2))’
          \\ simp [EL_MAP]
          \\ rw []
          >- (rename1 ‘find _ (ctxt_trans _) _ _ _ (fd_to_set fd')’
              \\ Cases_on ‘fd'’
              \\ gs [ctxt_trans_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
              \\ CASE_TAC \\ gs [fd_to_set_def]
              \\ irule find_smaller_fd
              \\ first_x_assum $ irule_at Any
              \\ simp [demands_map_FOLDL_delete_subset])
          >- (pairarg_tac \\ gs []
              \\ rename1 ‘rev_split_body _ args’
              \\ Cases_on ‘args = []’
              \\ gs [rev_split_body_def]
              >- (irule find_Create_fd
                  \\ irule find_Bottom)
              \\ irule find_Subset
              \\ irule_at Any find_exp_of_rev_split_body
              \\ gs [EVERY_EL, EL_MAP]
              \\ first_x_assum $ drule_then assume_tac
              \\ gs [])
          >- (gs [FORALL_PROD]
              \\ rw [EVERY_EL, EL_MAP]
              >- (pairarg_tac \\ gs []
                  \\ rename1 ‘(explode p1, argDs) ∉ s ∨ _’
                  \\ Cases_on ‘(explode p1, argDs) ∈ s’ \\ gs []
                  \\ rw [] \\ gs [MEM_MAP, MEM_EL])
              \\ pairarg_tac \\ gs []
              \\ CASE_TAC \\ gs [dest_fd_SND_def, fd_to_set_def]
              \\ CASE_TAC \\ gs [dest_fd_SND_def, fd_to_set_def]
              \\ irule demands_map_FOLDL_delete
              \\ gs [MEM_MAP, MEM_EL, PULL_EXISTS]
              \\ first_x_assum $ irule_at Any
              \\ simp [])
          >- (simp [PULL_EXISTS]
              \\ rename1 ‘(v, _) ∈ _’
              \\ reverse $ Cases_on ‘MEM v (MAP (explode o FST) binds2)’
              >- (disj1_tac
                  \\ first_x_assum $ irule_at Any
                  \\ simp [])
              \\ disj2_tac
              \\ gs [MEM_EL]
              \\ first_assum $ irule_at Any
              \\ gs [EL_MAP]
              \\ pairarg_tac \\ gs [Abbr ‘fds_abbrev’]
              \\ gs [fdemands_map_to_set_def]
              \\ irule_at Any FOLDL_insert_bind_lemma
              \\ gs [MEM_EL, PULL_EXISTS]
              \\ first_assum $ irule_at Any
              \\ simp []
              \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
              \\ gs [GSYM LAMBDA_PROD]
              \\ dxrule_then irule ALL_DISTINCT_IMP2)
          >- (gs [demands_map_to_set_def, FOLDL_delete_soundness, MEM_MAP]
              \\ gs [FORALL_PROD])
          >- (gs [demands_map_to_set_def, FOLDL_delete_soundness, MEM_MAP]
              \\ gs [FORALL_PROD])
          >- (qexists_tac ‘[]’ \\ simp [])
          >- (gs [Abbr ‘fds_abbrev’, SUBSET_DEF]
              \\ rw []
              \\ pairarg_tac \\ gs []
              \\ Cases_on ‘MEM v (MAP (explode o FST) binds2)’
              \\ gs []
              \\ dxrule_then assume_tac in_FOLDL_insert_binds
              \\ gs [])
          >- (gs [letrecs_distinct_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
              \\ irule letrecs_distinct_adds_demands
              \\ simp [])
          >- (rename1 ‘SOME (_, _) = fd'’
              \\ Cases_on ‘fd'’ \\ gs []
              \\ rename1 ‘(_, _) = x’
              \\ Cases_on ‘x’
              \\ gs [FOLDL_delete_ok])
          >- (rename1 ‘SOME (_, _) = fd'’
              \\ Cases_on ‘fd'’ \\ gs []
              \\ rename1 ‘(_, _) = x’
              \\ Cases_on ‘x’
              \\ gs [FOLDL_delete_ok]))
      \\ gvs [UNZIP3_MAP]
      \\ rename1 ‘demands_analysis_fun (RecBind binds c) _ (FOLDL _ fds _)’
      \\ qabbrev_tac ‘outL = MAP (λ(v, e).
                demands_analysis_fun (RecBind binds c) e
                                (FOLDL (λf k. delete f k) fds (MAP FST binds)))
                                 binds’
      \\ qabbrev_tac ‘e = demands_analysis_fun (RecBind binds c) exp
                        (handle_Letrec_fdemands fds (MAP FST binds) (MAP (SND o SND) outL))’
      \\ PairCases_on ‘e’ \\ gvs [fd_to_set_def, UNZIP3_MAP] \\ strip_tac
      \\ gvs [exp_of_def]
      \\ first_assum $ qspecl_then [‘cexp_size f exp’] assume_tac
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘exp’] assume_tac
      \\ fs [] \\ pop_assum $ drule_then assume_tac
      \\ gvs [FOLDL_delete_ok, ctxt_trans_def]
      \\ irule_at Any find_Subset
      \\ qexists_tac ‘fdemands_map_to_set (FOLDL (λf k. delete f k)
                                           fds (MAP FST binds))’
      \\ irule_at Any find_Letrec
      \\ irule_at Any adds_demands_soundness
      \\ qspecl_then [‘MAP FST binds’, ‘MAP (SND o SND) outL’, ‘fds’]
                     assume_tac handle_Letrec_fdemands_soundness
      \\ rpt $ FULL_CASE_TAC \\ unabbrev_all_tac
      \\ gvs [EL_MAP, EL_ZIP, MAP_MAP_o, LAMBDA_PROD, combinTheory.o_DEF,
              ALL_DISTINCT_FST_MAP, EVERY_EL, fdemands_map_FOLDL_delete_subset,
              FOLDL_delete_ok, fd_to_set_def, dest_fd_SND_def]
      \\ TRY $ irule_at Any find_smaller_fd
      \\ first_x_assum $ irule_at $ Pos hd
      \\ gvs [demands_map_FOLDL_delete_subset]
      \\ ‘EVERY (λm. map_ok m ∧ cmp_of m = compare)
          (MAP (λ(p1, e). FST (demands_analysis_fun (RecBind binds c) e
                                (FOLDL (λf k. delete f k) fds (MAP FST binds)))) binds)’
        by (rw [EVERY_EL] \\ rename1 ‘EL i _’
            \\ last_x_assum $ qspecl_then [‘cexp_size f (SND (EL i binds))’] assume_tac
            \\ ‘cexp_size f (SND (EL i binds)) < cexp7_size f binds’
              by (assume_tac cexp_size_lemma \\ gvs [] \\ first_x_assum irule
                  \\ gvs [MEM_EL] \\ first_assum $ irule_at Any
                  \\ irule_at Any $ PAIR)
            \\ gvs [] \\ pop_assum kall_tac
            \\ pop_assum $ qspecl_then [‘f’, ‘SND (EL i binds)’] assume_tac \\ gvs []
            \\ qabbrev_tac ‘p = demands_analysis_fun (RecBind binds c) (SND (EL i binds))
                                               (FOLDL (λf k. delete f k) fds (MAP FST binds))’
            \\ PairCases_on ‘p’ \\ fs []
            \\ first_x_assum $ drule_then assume_tac
            \\ first_x_assum $ drule_then assume_tac
            \\ first_x_assum $ drule_then assume_tac
            \\ first_x_assum $ drule_then assume_tac
            \\ gvs [FOLDL_delete_ok, EL_MAP, EVERY_EL]
            \\ pairarg_tac \\ gs [])
      \\ rpt $ irule_at Any $ GSYM LENGTH_MAP
      \\ qexists_tac ‘λ(v, e). demands_map_to_set
                               (FST (demands_analysis_fun (RecBind binds c) e
                                     (FOLDL (λf k. delete f k) fds (MAP FST binds))))’
      \\ qexists_tac ‘λ(v, e). fd_to_set (SND (SND (demands_analysis_fun (RecBind binds c) e
                                        (FOLDL (λf k. delete f k) fds (MAP FST binds)))))’
      \\ rename1 ‘demands_analysis_fun _ _ _ = (e0, _, _)’
      \\ qexists_tac ‘demands_map_to_set (FOLDL (λf k. delete f k)
       (handle_multi_bind e0 (MAP (λ(p1, p2). FST (demands_analysis_fun (RecBind binds c) p2
                 (FOLDL (λf k. delete f k) fds (MAP FST binds)))) binds)
        (MAP FST binds)) (MAP FST binds))’
      \\ rw [EL_MAP]
      >>~[‘_ ∉ fdemands_map_to_set _’]
      >- (pairarg_tac \\ gs [] \\ irule fdemands_map_FOLDL_delete \\ gvs [MEM_EL]
          \\ first_assum $ irule_at Any \\ gvs [EL_MAP]
          \\ rename1 ‘_ = FST p’ \\ PairCases_on ‘p’ \\ gvs [])
      >-  (pairarg_tac \\ gs [] \\ irule fdemands_map_FOLDL_delete \\ gvs [MEM_EL]
           \\ first_assum $ irule_at Any \\ gvs [EL_MAP]
           \\ rename1 ‘_ = FST p’ \\ PairCases_on ‘p’ \\ gvs [])
           >>~[‘FST _ = _ (FST _)’]
      >- (pairarg_tac \\ gvs [])
      >- (pairarg_tac \\ gvs [])
         >~[‘_ ∉ demands_map_to_set _’]
      >- (pairarg_tac \\ gs [] \\ irule demands_map_FOLDL_delete \\ gvs [MEM_EL]
          \\ first_assum $ irule_at Any \\ gvs [EL_MAP])
         >>~[‘¬MEM _ _’]
      >- (strip_tac \\ gvs [MEM_MAP] \\ pairarg_tac \\ gs []
          \\ dxrule_then assume_tac demands_map_FOLDL_delete_soundness
          \\ gvs [map_handle_multi_ok] \\ first_x_assum irule
          \\ gvs [MEM_MAP] \\ first_x_assum $ irule_at Any \\ gs [])
      >- (strip_tac \\ gvs [MEM_MAP] \\ pairarg_tac \\ gs []
          \\ dxrule_then assume_tac demands_map_FOLDL_delete_soundness
          \\ gvs [map_handle_multi_ok] \\ first_x_assum irule
          \\ gvs [MEM_MAP] \\ first_x_assum $ irule_at Any \\ gs [])
         >>~[‘(_ ++ _, _) ∈ demands_map_to_set _’]
      >- (qexists_tac ‘[]’ \\ gvs [])
      >- (qexists_tac ‘[]’ \\ gvs [])
         >>~[‘_ ∈ demands_map_to_set _’]
      >- (dxrule_then assume_tac demands_map_FOLDL_delete_soundness \\ gvs [map_handle_multi_ok]
          \\ dxrule_then assume_tac handle_multi_in \\ gvs [EL_MAP, SF CONJ_ss]
          \\ disj2_tac \\ first_assum $ irule_at $ Pos hd
          \\ pairarg_tac \\ gs []
          \\ first_x_assum $ irule_at Any)
      >- (dxrule_then assume_tac demands_map_FOLDL_delete_soundness \\ gvs [map_handle_multi_ok]
          \\ dxrule_then assume_tac handle_multi_in \\ gvs [EL_MAP, SF CONJ_ss]
          \\ disj2_tac \\ first_assum $ irule_at $ Pos hd
          \\ pairarg_tac \\ gs []
          \\ first_x_assum $ irule_at Any)
         >>~[‘(v, argDs) ∈ fdemands_map_to_set (handle_Letrec_fdemands fds (MAP FST binds) _)’]
      >- (first_x_assum $ qspec_then ‘implode v’ assume_tac >> gvs [explode_implode] >>
          last_x_assum $ dxrule_then assume_tac >> gvs [] >>
          disj2_tac >> gvs [EL_MAP, SF CONJ_ss] >>
          first_assum $ irule_at Any >> pairarg_tac >> gs [fd_to_set_def])
      >- (first_x_assum $ qspec_then ‘implode v’ assume_tac >> gvs [explode_implode] >>
          last_x_assum $ dxrule_then assume_tac >> gvs [] >>
          disj2_tac >> gvs [EL_MAP, SF CONJ_ss] >>
          first_assum $ irule_at Any >> pairarg_tac >> gs [fd_to_set_def])
      \\ gvs [ALL_DISTINCT_IMP, FOLDL_delete_ok, map_handle_multi_ok]
      >- (last_x_assum $ qspecl_then [‘cexp_size f (SND (EL i binds))’] assume_tac
          \\ ‘cexp_size f (SND (EL i binds)) < cexp7_size f binds’
            by (assume_tac cexp_size_lemma \\ gvs [] \\ first_x_assum irule
                \\ gvs [MEM_EL] \\ first_assum $ irule_at Any
                \\ irule_at Any $ PAIR)
          \\ gvs [] \\ pop_assum kall_tac
          \\ pop_assum $ qspecl_then [‘f’, ‘SND (EL i binds)’] assume_tac \\ gvs []
          \\ pairarg_tac \\ gs [FST_THM]
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ first_x_assum $ drule_then mp_tac
          \\ impl_tac
          >- (rpt $ last_x_assum $ drule_then assume_tac
              \\ gs [FOLDL_delete_ok])
          \\ gs [ctxt_trans_def])
      >- (last_x_assum $ qspecl_then [‘cexp_size f (SND (EL i binds))’] assume_tac
          \\ ‘cexp_size f (SND (EL i binds)) < cexp7_size f binds’
            by (assume_tac cexp_size_lemma \\ gvs [] \\ first_x_assum irule
                \\ gvs [MEM_EL] \\ first_assum $ irule_at Any
                \\ irule_at Any $ PAIR)
          \\ gvs [] \\ pop_assum kall_tac
          \\ pop_assum $ qspecl_then [‘f’, ‘SND (EL i binds)’] assume_tac \\ gvs []
          \\ qabbrev_tac ‘fds2 = FOLDL (λf k. delete f k) fds (MAP FST binds)’
          \\ qabbrev_tac ‘c2 = (RecBind (ZIP (MAP FST binds,
                                MAP (λ(p1, p2). FST (SND (demands_analysis_fun (RecBind binds c) p2 fds2)))
                                    binds)) c)’
          \\ qabbrev_tac ‘p = demands_analysis_fun c2 (SND (EL i binds)) fds2’
          \\ PairCases_on ‘p’ \\ gvs []
          \\ first_x_assum $ drule_then assume_tac
          \\ qspecl_then [‘f’, ‘SND (EL i binds)’, ‘c2’, ‘RecBind binds c’, ‘fds2’]
                         assume_tac demands_analysis_eq_with_diff_ctxt
          \\ pop_assum mp_tac \\ impl_tac >- simp[] \\ strip_tac
          \\ qabbrev_tac ‘pair = EL i binds’ \\ PairCases_on ‘pair’ \\ gvs []
          \\ unabbrev_all_tac \\ gvs [ctxt_trans_def, FOLDL_delete_ok]
          \\ rpt $ last_x_assum $ drule_then assume_tac \\ gs [])
      >- (rw [letrecs_distinct_def]
          >- (gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
              \\ irule ALL_DISTINCT_IMP
              \\ gs [MAP_ZIP, ALL_DISTINCT_IMP2])
          >- (gs [EVERY_EL, EL_MAP, EL_ZIP] \\ rw [FST_THM, SND_THM]
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ rename1 ‘i < _’
              \\ last_x_assum $ qspecl_then [‘cexp_size f (SND (EL i binds))’] assume_tac
              \\ ‘cexp_size f (SND (EL i binds)) < cexp7_size f binds’
                by (assume_tac cexp_size_lemma \\ gvs [] \\ first_x_assum irule
                \\ gvs [MEM_EL] \\ first_assum $ irule_at Any
                    \\ simp [])
              \\ gvs [] \\ pop_assum kall_tac
              \\ first_x_assum $ resolve_then (Pos hd) (drule_then assume_tac) EQ_REFL
              \\ gs [FOLDL_delete_ok]
              \\ last_x_assum $ drule_then assume_tac
              \\ last_x_assum $ drule_then assume_tac
              \\ last_x_assum $ drule_then assume_tac
              \\ gs [])
          >- gs [letrecs_distinct_adds_demands])
      >- (last_x_assum $ qspecl_then [‘cexp_size f (SND (EL i binds))’] assume_tac
          \\ ‘cexp_size f (SND (EL i binds)) < cexp7_size f binds’
            by (assume_tac cexp_size_lemma \\ gvs [] \\ first_x_assum irule
                \\ gvs [MEM_EL] \\ first_assum $ irule_at Any
                \\ irule_at Any $ PAIR)
          \\ gvs [] \\ pop_assum kall_tac
          \\ pop_assum $ qspecl_then [‘f’, ‘SND (EL i binds)’] assume_tac \\ gvs []
          \\ pairarg_tac \\ gs [FST_THM]
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ first_x_assum $ drule_then mp_tac
          \\ impl_tac
          >- (rpt $ last_x_assum $ drule_then assume_tac
              \\ gs [FOLDL_delete_ok])
          \\ gs [ctxt_trans_def])
      >- (last_x_assum $ qspecl_then [‘cexp_size f (SND (EL i binds))’] assume_tac
          \\ ‘cexp_size f (SND (EL i binds)) < cexp7_size f binds’
            by (assume_tac cexp_size_lemma \\ gvs [] \\ first_x_assum irule
                \\ gvs [MEM_EL] \\ first_assum $ irule_at Any
                \\ irule_at Any $ PAIR)
          \\ gvs [] \\ pop_assum kall_tac
          \\ pop_assum $ qspecl_then [‘f’, ‘SND (EL i binds)’] assume_tac \\ gvs []
          \\ qabbrev_tac ‘fds2 = FOLDL (λf k. delete f k) fds (MAP FST binds)’
          \\ qabbrev_tac ‘c2 = (RecBind (ZIP (MAP FST binds,
                                MAP (λ(p1, p2). FST (SND (demands_analysis_fun (RecBind binds c) p2 fds2)))
                                    binds)) c)’
          \\ qabbrev_tac ‘p = demands_analysis_fun c2 (SND (EL i binds)) fds2’
          \\ PairCases_on ‘p’ \\ gvs []
          \\ first_x_assum $ drule_then assume_tac
          \\ qspecl_then [‘f’, ‘SND (EL i binds)’, ‘c2’, ‘RecBind binds c’, ‘fds2’]
                         assume_tac demands_analysis_eq_with_diff_ctxt
          \\ pop_assum mp_tac \\ impl_tac >- simp[] \\ strip_tac
          \\ qabbrev_tac ‘pair = EL i binds’ \\ PairCases_on ‘pair’ \\ gvs []
          \\ unabbrev_all_tac \\ gvs [ctxt_trans_def, FOLDL_delete_ok]
          \\ rpt $ last_x_assum $ drule_then assume_tac \\ gs [])
      >- (rw [letrecs_distinct_def]
          >- (gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
              \\ irule ALL_DISTINCT_IMP
              \\ gs [MAP_ZIP, ALL_DISTINCT_IMP2])
          >- (gs [EVERY_EL, EL_MAP, EL_ZIP] \\ rw [FST_THM, SND_THM]
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ pairarg_tac \\ gs []
              \\ rename1 ‘i < _’
              \\ last_x_assum $ qspecl_then [‘cexp_size f (SND (EL i binds))’] assume_tac
              \\ ‘cexp_size f (SND (EL i binds)) < cexp7_size f binds’
                by (assume_tac cexp_size_lemma \\ gvs [] \\ first_x_assum irule
                \\ gvs [MEM_EL] \\ first_assum $ irule_at Any
                    \\ simp [])
              \\ gvs [] \\ pop_assum kall_tac
              \\ first_x_assum $ resolve_then (Pos hd) (drule_then assume_tac) EQ_REFL
              \\ gs [FOLDL_delete_ok]
              \\ last_x_assum $ drule_then assume_tac
              \\ last_x_assum $ drule_then assume_tac
              \\ last_x_assum $ drule_then assume_tac
              \\ gs [])
          >- gs [letrecs_distinct_adds_demands]))
  >~ [‘Case a case_exp s l opt’]

  >- (gen_tac \\ gen_tac
      \\ rename1 ‘Bind _ _ c’
      \\ rpt $ gen_tac
      \\ strip_tac \\ gs [letrecs_distinct_rows_of, letrecs_distinct_def]
      \\ first_assum $ qspecl_then [‘cexp_size f case_exp’] assume_tac
      \\ gvs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘case_exp’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
      \\ qabbrev_tac ‘cexp = demands_analysis_fun c case_exp fds’
      \\ PairCases_on ‘cexp’ \\ gvs []
      \\ reverse conj_tac
      >- (gvs [FOLDR_Case_demands_lemma]
          \\ gs [exp_of_def, MAP_MAP_o, combinTheory.o_DEF,
              LAMBDA_PROD, letrecs_distinct_rows_of, letrecs_distinct_def]
          \\ conj_tac
          >- (Cases_on ‘opt’ \\ gs []
              \\ pairarg_tac \\ gs [IfDisj_def, letrecs_distinct_def]
              \\ rename1 ‘demands_analysis_fun _ p2’
              \\ last_x_assum $ qspec_then ‘cexp_size f p2’ assume_tac
              \\ gs [cexp_size_def]
              \\ qmatch_goalsub_abbrev_tac ‘add_all_demands _ daf’
              \\ Cases_on ‘FST daf’
              \\ PairCases_on ‘daf’
              \\ gs []
              \\ first_x_assum $ resolve_then (Pos hd) (drule_then assume_tac) EQ_REFL
              \\ gs [empty_thm, TotOrd_compare, cmp_of_def, add_all_demands_def]
              \\ irule letrecs_distinct_add_all_demands_lemma
              \\ gs [])
          \\ gs [EVERY_EL, EL_MAP]
          \\ gen_tac \\ strip_tac
          \\ pairarg_tac \\ gs []
          \\ pairarg_tac \\ gs []
          \\ qpat_x_assum ‘exp_of _ = _’ assume_tac
          \\ dxrule_then assume_tac EQ_SYM \\ gs []
          \\ rename1 ‘EL i rows = (constructor, vars, expr)’
          \\ last_x_assum $ qspec_then ‘cexp_size f expr’ assume_tac
          \\ ‘cexp_size f expr < cexp2_size f rows’
            by (assume_tac cexp_size_lemma \\ gs []
                \\ first_x_assum irule
                \\ gs [MEM_EL]
                \\ first_x_assum $ irule_at Any
                \\ simp [])
          \\ gs [] \\ pop_assum kall_tac
          \\ qmatch_goalsub_abbrev_tac ‘add_all_demands _ daf’
          \\ Cases_on ‘FST daf’
          \\ PairCases_on ‘daf’
          \\ gs []
          \\ first_x_assum $ resolve_then (Pos hd) (drule_then assume_tac) EQ_REFL
          \\ last_x_assum $ drule_then assume_tac
          \\ last_x_assum $ drule_then assume_tac
          \\ last_x_assum $ drule_then assume_tac
          \\ last_x_assum $ drule_then assume_tac
          \\ gs [FOLDL_delete_ok, delete_thm, cmp_of_def, add_all_demands_def]
          \\ irule letrecs_distinct_add_all_demands_lemma
          \\ gs [])
      \\ gvs [FOLDR_Case_demands_lemma]
      \\ rw [empty_thm, TotOrd_compare, demands_map_empty, find_Bottom,
             exp_of_def, MAP_MAP_o, fd_to_set_def]
      \\ gvs [exp_of_def, find_Bottom, combinTheory.o_DEF, LAMBDA_PROD, MAP_MAP_o]
      \\ rename1 ‘Let (explode s) _ _’
      \\ irule find_Let2
      \\ first_x_assum $ irule_at Any
      \\ rename1 ‘rows_of _ _ (MAP _ l)’
      \\ qspecl_then [
          ‘l’,
          ‘MAP (λ(v,vL,e).
                  (v, vL,
                   add_all_demands a (demands_analysis_fun
                                      (Unfold v s vL (Bind s case_exp c)) e
                                      (FOLDL (λm v. delete m v) (delete fds s) vL)))) l’
         ] assume_tac find_rows_of
      \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
      \\ pop_assum $ irule_at Any
      \\ gvs [dest_fd_SND_def]
      \\ CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["fds0", "fd"]))
      \\ qexists_tac ‘NONE’ \\ qexists_tac ‘fdemands_map_to_set (delete fds s)’
      \\ rw [LIST_REL_EL_EQN, EL_MAP, dest_fd_SND_def]
      >- ((* handling the list of cases *) pairarg_tac
          \\ fs []
          \\ irule find_Subset
          \\ rename1
             ‘demands_analysis_fun (Unfold names s args (Bind s case_exp c)) e' (FOLDL _ (delete fds s) _)’
          \\ qabbrev_tac
             ‘p = demands_analysis_fun
                  (Unfold names s args (Bind s case_exp c)) e' (FOLDL (λm v. delete m v) (delete fds s) args)’
          \\ PairCases_on ‘p’
          \\ irule_at Any add_all_demands_soundness
          \\ first_x_assum $ qspecl_then [‘cexp_size f e'’] assume_tac
          \\ ‘cexp_size f e' < cexp2_size f l’
            by metis_tac [cexp_size_lemma, EL_MEM]
          \\ fs []
          \\ pop_assum kall_tac
          \\ pop_assum $ qspecl_then [‘f’, ‘e' ’] assume_tac
          \\ fs [] \\ pop_assum $ dxrule_then assume_tac
          \\ irule_at Any find_Drop_fd
          \\ gvs[FOLDL_delete_ok, delete_thm, EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
          \\ fs [ctxt_trans_def, TotOrd_compare, fdemands_map_to_set_def, empty_thm]
          \\ pop_assum mp_tac \\ impl_tac >- metis_tac[MEM_EL]
          \\ strip_tac \\ simp[]
          \\ first_x_assum $ irule_at Any \\ gs [TotOrd_compare]
          \\ qpat_x_assum ‘map_ok fds’ mp_tac
          \\ qpat_x_assum ‘cmp_of fds = compare’ mp_tac
          \\ rpt $ pop_assum kall_tac
          \\ simp [SUBSET_DEF, PULL_EXISTS, FORALL_PROD, delete_thm, FOLDL_delete_soundness]
          \\ rw []
          \\ rename1 ‘x ∈ _’ \\ qexists_tac ‘x’ \\ simp []
          \\ qpat_x_assum ‘_ ≠ _’ kall_tac
          \\ qpat_x_assum ‘_ ∈ _’ kall_tac
          \\ qpat_x_assum ‘¬MEM _ _’ mp_tac \\ qid_spec_tac ‘x’
          \\ Induct_on ‘args’ using SNOC_INDUCT \\ gs [delete_thm, FOLDL_APPEND]
          \\ rw [] \\ gs [delete_thm]
          \\ simp [FOLDL_delete_soundness, delete_thm, DOMSUB_FAPPLY_NEQ])
      >- ((* handling the optional fall-through expression at the bottom *)
          rename [‘option_CASE opt Fail’]
          \\ Cases_on ‘opt’ \\ gvs[find_Fail]
          \\ pairarg_tac \\ gvs []
          \\ rename [‘NestedCase_free e’]
          \\ irule find_Subset \\ simp[] (* include ? *)
          \\ qabbrev_tac
             ‘p = demands_analysis_fun (Bind s case_exp c) e (empty compare)’
          \\ PairCases_on ‘p’
          \\ irule_at Any find_IfDisj
          \\ irule_at Any add_all_demands_soundness'
          \\ first_x_assum $ qspec_then ‘cexp_size f e’ assume_tac
          \\ gvs[cexp_size_def, IfDisj_def, letrecs_distinct_def]
          \\ pop_assum (drule_at_then (Pat ‘demands_analysis_fun _ _ _ = _’)
                        strip_assume_tac)
          \\ pop_assum (resolve_then (Pos hd) assume_tac EQ_REFL)
          \\ gvs[ctxt_trans_def, fdemands_map_to_set_def, empty_thm, TotOrd_compare]
          \\ irule_at Any find_Drop_fd
          \\ first_assum $ irule_at Any)
      >- (rename1 ‘n ≠ explode s’ \\ Cases_on ‘n = explode s’
          \\ gs [fdemands_map_delete]
          \\ qspecl_then [‘s’, ‘fds’] assume_tac fdemands_map_delete_subset
          \\ gs [SUBSET_DEF]))
QED

Theorem demands_analysis_soundness:
  ∀(e : α cexp) a. NestedCase_free e ∧ cexp_wf e ∧ letrecs_distinct (exp_of e) ⇒
                   exp_of e ≈ exp_of (demands_analysis c e) ∧
                   letrecs_distinct (exp_of (demands_analysis c e))
Proof
  rpt strip_tac \\ gvs [demands_analysis_def, SND_THM]
  \\ rw [] \\ fs [exp_eq_refl]
  \\ pairarg_tac \\ gs [FST_THM]
  \\ pairarg_tac \\ gs []
  \\ qspecl_then [‘(K 0) : α -> num’, ‘e’, ‘Nil’, ‘empty compare’]
                 assume_tac demands_analysis_soundness_lemma
  \\ gvs [empty_thm, TotOrd_compare, ctxt_trans_def, fdemands_map_to_set_def]
  \\ dxrule_then assume_tac find_soundness
  \\ gs []
QED


(********** Prove that analysis only inserts well-defined Seqs **********)

Triviality empty_map_simps[simp]:
  map_ok (empty compare) ∧
  cmp_of (empty compare) = compare ∧
  to_fmap (empty compare) = FEMPTY ∧
  TotOrd compare
Proof
  simp[empty_def, map_ok_def, to_fmap_def, balanced_mapTheory.empty_def] >>
  simp[balanced_mapTheory.invariant_def, TotOrd_compare]
QED

Theorem freevars_add_all_demands:
  ∀m ce.
    freevars_cexp (add_all_demands d (m,ce,any)) =
    freevars_cexp ce ∪ FDOM (to_fmap m)
Proof
  Cases >> simp[add_all_demands_def, foldrWithKey_def, cmp_of_def] >>
  Induct_on `b` >> rw[balanced_mapTheory.foldrWithKey_def] >>
  gvs[map_ok_def, balanced_mapTheory.invariant_def, to_fmap_def] >>
  rw[EXTENSION] >> eq_tac >> rw[] >> gvs[]
QED

Theorem add_all_demands_insert_seq_lemma[local]:
  ∀m ce ce'.
    map_ok (Map compare m) ∧
    FDOM (to_fmap (Map compare m)) SUBSET freevars_cexp ce ∧
    pure_typingProps$insert_seq ce ce'
  ⇒ pure_typingProps$insert_seq ce (add_all_demands d (Map compare m,ce',any))
Proof
  simp[add_all_demands_def, foldrWithKey_def] >>
  Induct >> rw[balanced_mapTheory.foldrWithKey_def] >>
  qmatch_goalsub_abbrev_tac `foldrWithKey f` >>
  gvs[map_ok_def, balanced_mapTheory.invariant_def] >>
  first_x_assum irule >> simp[] >>
  gvs[to_fmap_def] >>
  simp[Once insert_seq_cases] >> disj1_tac >>
  qspecl_then [`Map compare m'`,`ce'`] assume_tac freevars_add_all_demands >>
  gvs[add_all_demands_def, foldrWithKey_def] >>
  imp_res_tac insert_seq_freevars >> gvs[]
QED

Theorem add_all_demands_insert_seq_lemma[local]:
  ∀m ce ce'.
    FDOM (to_fmap (Map cmp m)) SUBSET freevars_cexp ce ∧
    pure_typingProps$insert_seq ce ce'
  ⇒ pure_typingProps$insert_seq ce (add_all_demands d (Map cmp m, ce', any))
Proof
  simp[add_all_demands_def, foldrWithKey_def] >>
  Induct >> rw[balanced_mapTheory.foldrWithKey_def] >> gvs[to_fmap_def] >>
  qmatch_goalsub_abbrev_tac `foldrWithKey f` >>
  first_x_assum irule >> simp[] >>
  simp[Once insert_seq_cases] >> disj1_tac >>
  qspecl_then [`Map compare m'`,`ce'`] assume_tac freevars_add_all_demands >>
  gvs[add_all_demands_def, foldrWithKey_def] >>
  imp_res_tac insert_seq_freevars >> gvs[]
QED

Theorem add_all_demands_insert_seq:
  ∀d m ce any.
    FDOM (to_fmap m) ⊆ freevars_cexp ce ∧
    NestedCase_free ce
  ⇒ pure_typingProps$insert_seq ce (add_all_demands d (m,ce,any))
Proof
  rw[] >> Cases_on `m` >>
  irule add_all_demands_insert_seq_lemma >> simp[insert_seq_refl]
QED

Theorem adds_demands_freevars:
  ∀vs d m ce fd. map_ok m ⇒
  freevars_cexp (adds_demands d (m,ce,fd) vs) =
  freevars_cexp ce ∪ (FDOM (to_fmap m) ∩ set vs)
Proof
  Induct >> rw[adds_demands_def] >> CASE_TAC >> rw[] >>
  gvs[lookup_thm, FLOOKUP_DEF] >> rw[EXTENSION] >> eq_tac >> rw[] >> gvs[]
QED

Theorem adds_demands_insert_seq:
  ∀vs ce d m fd.
    FDOM (to_fmap m) ⊆ freevars_cexp ce ∧ map_ok m ∧
    NestedCase_free ce
  ⇒ pure_typingProps$insert_seq ce (adds_demands d (m,ce,fd) vs)
Proof
  Induct >> rw[adds_demands_def, insert_seq_refl] >>
  CASE_TAC >> rw[] >> simp[Once insert_seq_cases] >> disj1_tac >>
  gvs[adds_demands_freevars, lookup_thm, FLOOKUP_DEF, SUBSET_DEF]
QED

Theorem handle_Apps_demands_insert_seq:
  ∀d bools args.
    EVERY (λ(m,e,any). FDOM (to_fmap m) ⊆ freevars_cexp e ∧ NestedCase_free e) args
  ⇒ LIST_REL pure_typingProps$insert_seq (MAP (λ(_,ce,_). ce) args)
                                         (FST $ SND $ handle_Apps_demands d bools args)
Proof
  recInduct handle_Apps_demands_ind >> rw[handle_Apps_demands_def]
  >- (
    gvs[EVERY_EL, LIST_REL_EL_EQN, EL_MAP] >> rw[] >> pairarg_tac >> gvs[] >>
    first_x_assum drule >> rw[] >> gvs[add_all_demands_insert_seq]
    )
  >- (pairarg_tac >> gvs[insert_seq_refl])
  >- rpt (pairarg_tac >> gvs[add_all_demands_insert_seq])
QED

Theorem handle_Apps_demands_submap:
  ∀d bools args a b m.
    handle_Apps_demands d bools args = (a,b,m) ∧
    EVERY (λ(m,e,any). map_ok m ∧ cmp_of m = compare) args
    ⇒
    map_ok m ∧ cmp_of m = compare ∧
    ∀x. x ∈ FDOM (to_fmap m) ⇒
      ∃m' e fd. MEM (m',e,fd) args ∧ x ∈ FDOM (to_fmap m')
Proof
  recInduct handle_Apps_demands_ind >> simp[handle_Apps_demands_def] >>
  gvs[mlmapTheory.empty_def, balanced_mapTheory.empty_def, to_fmap_def] >>
  rpt conj_tac >> rpt gen_tac >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> gvs[union_thm] >> metis_tac[]
QED

Theorem rev_split_body_inner_freevars:
  ∀xs d ce.
    freevars_cexp (rev_split_body_inner d xs ce) =
    freevars_cexp ce ∪ { v | MEM (v,T) xs }
Proof
  Induct >> rw[rev_split_body_inner_def] >>
  PairCases_on `h` >> Cases_on `h1` >> rw[rev_split_body_inner_def] >>
  rw[EXTENSION] >> eq_tac >> rw[] >> gvs[]
QED

Theorem rev_split_body_inner_insert_seq:
  ∀xs ce d.
    { v | MEM (v,T) xs } ⊆ freevars_cexp ce ∧
    NestedCase_free ce
  ⇒ pure_typingProps$insert_seq ce (rev_split_body_inner d xs ce)
Proof
  Induct >> rw[]
  >- rw[rev_split_body_inner_def, insert_seq_refl] >>
  PairCases_on `h` >> Cases_on `h1` >> rw[rev_split_body_inner_def] >> gvs[] >>
  simp[Once insert_seq_cases] >> disj1_tac >>
  simp[rev_split_body_inner_freevars] >> gvs[SUBSET_DEF]
QED

Theorem compute_fixpoint_rec_MAP_FST:
  ∀n binds.
    MAP FST (compute_fixpoint_rec n binds) = MAP FST binds
Proof
  Induct >> rw[compute_fixpoint_rec_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
  simp[handle_fixpoint1_def] >> pairarg_tac >> gvs[]
QED

Theorem compute_fixpoint_rec_LIST_REL:
  ∀n binds.
    LIST_REL (λ(v',vbs',ce',lab') (v,vbs,ce,lab).
      ce = ce' ∧ MAP FST vbs = MAP FST vbs') (compute_fixpoint_rec n binds) binds
Proof
  Induct >> rw[compute_fixpoint_rec_def] >> gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
  rpt (pairarg_tac >> gvs[handle_fixpoint1_def]) >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
  >- (rw[MAP_EQ_f] >> pairarg_tac >> gvs[])
  >- (rw[MAP_EQ_f] >> pairarg_tac >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `EL _ $ compute_fixpoint_rec _ binds'` >>
  last_x_assum $ qspec_then `binds'` assume_tac >> gvs[] >>
  pop_assum $ qspec_then `n'` mp_tac >> simp[] >>
  unabbrev_all_tac >> simp[EL_MAP, handle_fixpoint1_def] >>
  rpt (pairarg_tac >> gvs[]) >> rw[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  pop_assum $ assume_tac o GSYM >> rw[MAP_EQ_f] >> pairarg_tac >> gvs[]
QED

Theorem fixpoint_analysis_MAP_FST:
  ∀binds b binds'.
    fixpoint_analysis binds = (b,binds')
  ⇒ MAP FST binds' = MAP FST binds
Proof
  rw[fixpoint_analysis_def] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  gvs[can_compute_fixpoint_def, AllCaseEqs()] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  rw[MAP_EQ_f] >> rpt (pairarg_tac >> gvs[]) >>
  simp[compute_fixpoint_rec_MAP_FST] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  rw[MAP_EQ_f] >> rpt (pairarg_tac >> gvs[])
QED

Theorem fixpoint_analysis_LIST_REL:
  ∀binds b binds'.
    fixpoint_analysis binds = (b,binds')
  ⇒ LIST_REL (λ(v,ce) (v',vbs,ce',lab).
      ∃vs lab'. split_body ce = (vs,ce',lab') ∧ MAP FST vbs = vs) binds binds'
Proof
  rw[fixpoint_analysis_def] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  gvs[can_compute_fixpoint_def, AllCaseEqs()] >> rpt $ pop_assum kall_tac
  >- (
    qmatch_goalsub_abbrev_tac `compute_fixpoint_rec n binds'` >>
    qspecl_then [`n`,`binds'`] mp_tac compute_fixpoint_rec_LIST_REL >>
    rw[] >> gvs[LIST_REL_EL_EQN] >>
    conj_asm1_tac >- (unabbrev_all_tac >> simp[]) >>
    rw[] >> rpt (pairarg_tac >> gvs[]) >>
    first_x_assum $ qspec_then `n'` mp_tac >> rw[] >> pairarg_tac >> gvs[] >>
    unabbrev_all_tac >> fs[] >> gvs[EL_MAP] >>
    pairarg_tac >> gvs[MAP_MAP_o, combinTheory.o_DEF]
    ) >>
  rw[LIST_REL_EL_EQN, EL_MAP] >> rpt (pairarg_tac >> gvs[]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem fixpoint_demands_App_map:
  ∀bs ds vs m FVs.
    fixpoint_demands_App bs ds = (vs, m) ∧
    EVERY (λ(m,_). map_ok m ∧ cmp_of m = compare ∧ FDOM (to_fmap m) ⊆ FVs) ds
  ⇒ map_ok m ∧ cmp_of m = compare ∧ FDOM (to_fmap m) ⊆ FVs
Proof
  recInduct fixpoint_demands_App_ind >> simp[fixpoint_demands_App_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rpt (pairarg_tac >> gvs[])
  >- (res_tac >> simp[])
  >- (first_x_assum drule >> simp[union_thm])
QED

Theorem fixpoint1_map:
  ∀d ce fds m fdopt.
    fixpoint1 d ce fds = (m,fdopt) ∧
    map_ok fds ∧ cmp_of fds = compare
  ⇒ map_ok m ∧ cmp_of m = compare ∧
    FDOM (to_fmap m) ⊆ freevars_cexp ce DIFF FDOM (to_fmap fds) ∧
    (∀bl optm. fdopt = SOME (bl, optm) ⇒
        map_ok optm ∧ cmp_of optm = compare ∧
        FDOM (to_fmap optm) ⊆ freevars_cexp ce DIFF FDOM (to_fmap fds))
Proof
  recInduct fixpoint1_ind >> simp[fixpoint1_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
    gvs[AllCaseEqs(), insert_thm] >> rw[] >> gvs[lookup_thm, FLOOKUP_DEF]
    )
  >- (
    pairarg_tac >> gvs[] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()]
    >- gvs[SUBSET_DEF] >>
      (
        drule fixpoint_demands_App_map >>
        disch_then $ qspec_then
          `BIGUNION (set (MAP freevars_cexp argl)) DIFF FDOM (to_fmap fds)` mp_tac >>
        simp[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> impl_tac
        >- (
          rw[] >> pairarg_tac >> gvs[] >>
          last_x_assum drule >> simp[] >> rw[SUBSET_DEF, MEM_MAP, PULL_EXISTS] >>
          goal_assum $ drule_at Any >> simp[]
          ) >>
        strip_tac >> simp[union_thm] >> gvs[SUBSET_DEF] >>
        gvs[MEM_MAP, PULL_EXISTS] >> metis_tac[]
      )
    )
  >- (
    rpt (pairarg_tac >> gvs[]) >> strip_tac >> simp[union_thm] >> gvs[SUBSET_DEF]
    )
  >- (
    strip_tac >> gvs[FOLDR_MAP, LAMBDA_PROD] >>
    Induct_on `eL` >> gvs[] >> gen_tac >> pairarg_tac >> gvs[] >>
    simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
    DEP_REWRITE_TAC[cj 1 union_thm, cj 2 union_thm, cj 3 union_thm] >> simp[SF CONJ_ss] >>
    qpat_x_assum `(∀e. _) ⇒ _` mp_tac >> impl_tac >- metis_tac[] >>
    strip_tac >> simp[] >> gvs[SUBSET_DEF]
    ) >>
  rpt (pairarg_tac >> gvs[]) >> ntac 3 strip_tac >> gvs[AllCaseEqs()]
  >- (
    DEP_REWRITE_TAC[cj 1 union_thm, cj 2 union_thm, cj 3 union_thm] >> simp[] >>
    DEP_REWRITE_TAC[cj 1 delete_thm, cj 2 delete_thm] >> simp[SF CONJ_ss] >>
    qmatch_goalsub_abbrev_tac `FDOM foo ⊆ bar` >>
    `FDOM foo ⊆ bar` by (unabbrev_all_tac >> gvs[SUBSET_DEF]) >>
    simp[] >> pop_assum kall_tac >> unabbrev_all_tac >>
    DEP_REWRITE_TAC $ map (SRULE []) [cj 1 fixpoint1_Case_lemma2,
      cj 2 fixpoint1_Case_lemma2, cj 3 fixpoint1_Case_lemma2] >>
    simp[] >>
    Cases_on `rows` >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >> pairarg_tac >> gvs[] >>
    qpat_abbrev_tac `h' = fixpoint1 _ _ _` >> PairCases_on `h'` >> gvs[] >>
    last_x_assum mp_tac >> impl_tac
    >- (DEP_REWRITE_TAC[cj 1 FOLDR_delete, cj 2 FOLDR_delete] >> simp[delete_thm]) >>
    strip_tac >> gvs[] >> simp[FOLDR_delete] >> rw[]
    >- (
      simp[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> rpt gen_tac >> strip_tac >>
      qpat_abbrev_tac `res = fixpoint1 _ _ _` >> PairCases_on `res` >> gvs[] >>
      last_x_assum drule >> simp[] >> impl_tac
      >- (DEP_REWRITE_TAC[cj 1 FOLDR_delete, cj 2 FOLDR_delete] >> simp[delete_thm]) >>
      strip_tac >> gvs[] >> simp[FOLDR_delete]
      )
    >- (
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      gvs[SUBSET_DEF] >> simp[MEM_MAP, PULL_EXISTS] >> rw[] >> gvs[] >>
      first_x_assum drule >> DEP_REWRITE_TAC[cj 3 FOLDR_delete] >> simp[delete_thm]
      )
    )
  >- (
    DEP_REWRITE_TAC[cj 1 union_thm, cj 2 union_thm, cj 3 union_thm] >> simp[] >>
    DEP_REWRITE_TAC[cj 1 delete_thm, cj 2 delete_thm] >> simp[SF CONJ_ss] >>
    qmatch_goalsub_abbrev_tac `FDOM foo ⊆ bar` >>
    `FDOM foo ⊆ bar` by (unabbrev_all_tac >> gvs[SUBSET_DEF]) >>
    simp[] >> pop_assum kall_tac >> unabbrev_all_tac >>
    DEP_REWRITE_TAC $ map (SRULE []) [cj 1 fixpoint1_Case_lemma2,
      cj 2 fixpoint1_Case_lemma2, cj 3 fixpoint1_Case_lemma2] >>
    simp[] >> qpat_abbrev_tac `h' = fixpoint1 _ _ _` >>
    PairCases_on `h'` >> gvs[delete_thm] >> rw[]
    >- (
      simp[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> rpt gen_tac >> strip_tac >>
      qpat_abbrev_tac `res = fixpoint1 _ _ _` >> PairCases_on `res` >> gvs[] >>
      last_x_assum drule >> simp[] >> impl_tac
      >- (DEP_REWRITE_TAC[cj 1 FOLDR_delete, cj 2 FOLDR_delete] >> simp[delete_thm]) >>
      strip_tac >> gvs[] >> simp[FOLDR_delete]
      )
    >- (
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      gvs[SUBSET_DEF] >> simp[MEM_MAP, PULL_EXISTS] >> rw[] >> gvs[] >>
      first_x_assum drule >> DEP_REWRITE_TAC[cj 3 FOLDR_delete] >> simp[delete_thm]
      )
    )
QED

Theorem handle_fixpoint1_freevars:
  ∀fds v args body label v' args' body' label' x.
    handle_fixpoint1 fds (v,args,body,label) = (v',args',body',label') ∧
    MEM (x,T) args' ∧ map_ok fds ∧ cmp_of fds = compare
  ⇒ ∃b. MEM (x,b) args ∧ x ∈ freevars_cexp body ∧ x ∉ FDOM (to_fmap fds)
Proof
  rw[handle_fixpoint1_def] >> pairarg_tac >> gvs[] >>
  drule fixpoint1_map >> simp[] >> strip_tac >>
  gvs[MEM_MAP] >> pairarg_tac >> gvs[] >>
  goal_assum drule >> gvs[lookup_thm, FLOOKUP_DEF, SUBSET_DEF]
QED

Theorem compute_fixpoint_rec_freevars:
  ∀n binds binds' fn xs body lab x.
    compute_fixpoint_rec n binds = binds' ∧
    MEM (fn,xs,body,lab) binds' ∧ MEM (x,T) xs
  ⇒ x ∈ freevars_cexp body
Proof
  Induct >> rw[compute_fixpoint_rec_def] >> gvs[]
  >- rpt (gvs[MEM_MAP] >> pairarg_tac)
  >- (
    gvs[MEM_MAP] >> PairCases_on `y` >>
    qpat_x_assum `_ = handle_fixpoint1 _ _` $ assume_tac o GSYM >>
    drule handle_fixpoint1_freevars >> disch_then drule >> reverse impl_tac
    >- (rw[] >> gvs[handle_fixpoint1_def] >> pairarg_tac >> gvs[]) >>
    rpt $ pop_assum kall_tac >>
    Induct_on `binds` >> rw[] >> rpt (pairarg_tac >> gvs[]) >> simp[insert_thm]
    )
  >- (last_x_assum drule >> simp[])
QED

Theorem fixpoint_analysis_freevars:
  fixpoint_analysis binds = (b, binds') ∧
  MEM (fn,xs,body,lab) binds' ∧
  MEM (x,T) xs
  ⇒ x ∈ freevars_cexp body
Proof
  simp[fixpoint_analysis_def] >> pairarg_tac >> gvs[] >>
  reverse IF_CASES_TAC >> rw[] >> gvs[]
  >- (gvs[MEM_MAP] >> pairarg_tac >> gvs[MEM_MAP]) >>
  drule_all $ SRULE [] compute_fixpoint_rec_freevars >> simp[]
QED

Theorem handle_multi_bind_map:
  ∀m ms vs m'.
    handle_multi_bind m ms vs = m' ∧
    EVERY (λm. map_ok m ∧ cmp_of m = compare ∧ FDOM (to_fmap m) ⊆ FVs) (m::ms)
  ⇒ FDOM (to_fmap m') ⊆ FVs
Proof
  recInduct handle_multi_bind_ind >> rw[handle_multi_bind_def] >> gvs[] >>
  DEP_REWRITE_TAC[cj 3 union_thm] >> simp[] >>
  irule map_handle_multi_ok >> simp[] >> gvs[EVERY_MEM]
QED

Theorem demands_analysis_fun_insert_seq:
  ∀ctxt ce fds m ce' fdopt.
    demands_analysis_fun ctxt ce fds = (m, ce', fdopt) ∧
    NestedCase_free ce
  ⇒ map_ok m ∧ cmp_of m = compare ∧
    FDOM (to_fmap m) ⊆ freevars_cexp ce ∧
    (∀bl optm. fdopt = SOME (bl, optm) ⇒
        map_ok optm ∧ cmp_of optm = compare ∧ FDOM (to_fmap optm) ⊆ freevars_cexp ce) ∧
    pure_typingProps$insert_seq ce ce'
Proof
  recInduct demands_analysis_fun_ind >> simp[demands_analysis_fun_def] >>
  rpt conj_tac >> rpt gen_tac
  >- (
    DEP_REWRITE_TAC[cj 1 insert_thm, cj 2 insert_thm] >>
    simp[Once insert_seq_cases] >>
    TOP_CASE_TAC >> gvs[] >> simp[empty_thm, TotOrd_compare]
    )
  >- (
    strip_tac >> pairarg_tac >> gvs[] >> TOP_CASE_TAC >> gvs[] >> strip_tac >> gvs[]
    >- (
      gvs[SUBSET_DEF] >> simp[Once insert_seq_cases] >> disj2_tac >>
      simp[MAP_MAP_o, combinTheory.o_DEF] >> rw[LIST_REL_EL_EQN, EL_MAP] >>
      gvs[MEM_EL, PULL_EXISTS] >> last_x_assum drule >>
      qpat_abbrev_tac `dn = demands_analysis_fun _ _ _` >>
      PairCases_on `dn` >> rw[] >> gvs[EVERY_EL] >>
      irule insert_seq_trans >> goal_assum drule >>
      irule add_all_demands_insert_seq >>
      imp_res_tac insert_seq_NestedCase_free >>
      imp_res_tac insert_seq_freevars >> gvs[SUBSET_DEF]
      ) >>
    simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
      (
        DEP_REWRITE_TAC[cj 1 union_thm, cj 2 union_thm, cj 3 union_thm] >> simp[] >>
        qspecl_then [`a0`,`fdL`,`MAP (λe. demands_analysis_fun c e fds) argl`]
          mp_tac handle_Apps_demands_insert_seq >> impl_tac
        >- (
          rw[EVERY_MAP, EVERY_MEM] >> pairarg_tac >> gvs[] >>
          first_x_assum drule >> simp[] >> rw[] >> gvs[EVERY_MEM]
          >- (imp_res_tac insert_seq_freevars >> gvs[])
          >- imp_res_tac insert_seq_NestedCase_free
          ) >>
        simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> strip_tac >>
        qspecl_then [`a0`,`fdL`,`MAP (λe. demands_analysis_fun c e fds) argl`]
          mp_tac handle_Apps_demands_submap >>
        simp[EVERY_MAP] >> impl_tac
        >- (
          gvs[EVERY_MEM] >> rw[] >> pairarg_tac >> gvs[] >>
          last_x_assum drule >> simp[]
          ) >>
        strip_tac >> gvs[SUBSET_DEF] >> rw[]
        >- (
          first_x_assum drule >> simp[MEM_MAP, PULL_EXISTS] >> rw[Once EQ_SYM_EQ] >>
          first_x_assum drule >> gvs[EVERY_MEM] >> rw[] >>
          first_x_assum drule >> simp[SF SFY_ss]
          ) >>
        simp[Once insert_seq_cases] >> disj1_tac >> qrefine `App a0 f' args` >>
        qmatch_asmsub_abbrev_tac `LIST_REL _ args` >> qexists `args` >>
        simp[Once insert_seq_cases, SF DNF_ss] >> disj2_tac >>
        unabbrev_all_tac >> rw[]
        >- (
          rw[LIST_REL_EL_EQN, EL_MAP] >> pairarg_tac >> gvs[] >>
          gvs[SF DNF_ss] >> last_x_assum irule >> simp[EL_MEM] >> gvs[EVERY_EL]
          ) >>
        simp[Once insert_seq_cases] >> disj2_tac >>
        imp_res_tac insert_seq_NestedCase_free >> simp[insert_seq_refl]
      )
    )
  >- (
    strip_tac >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
    simp[Once insert_seq_cases] >> rpt disj2_tac >>
    irule insert_seq_trans >> goal_assum drule >>
    irule add_all_demands_insert_seq >>
    map_every imp_res_tac [insert_seq_NestedCase_free, insert_seq_freevars] >> gvs[]
    )
  >- (
    strip_tac >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
    DEP_REWRITE_TAC[cj 1 delete_thm, cj 2 delete_thm] >>
    simp[AllCaseEqs(), PULL_EXISTS] >> rpt conj_tac
    >- gvs[SUBSET_DEF]
    >- (
      rpt gen_tac >> strip_tac >>
      DEP_REWRITE_TAC[cj 1 delete_thm, cj 2 delete_thm] >> gvs[SUBSET_DEF]
      ) >>
    TOP_CASE_TAC >> simp[Once insert_seq_cases] >> disj2_tac >>
    simp[Once insert_seq_cases] >> disj1_tac >>
    pop_assum mp_tac >> simp[lookup_thm, FLOOKUP_DEF] >>
    imp_res_tac insert_seq_freevars >> gvs[SUBSET_DEF]
    )
  >- (
    strip_tac >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
    DEP_REWRITE_TAC[cj 1 union_thm, cj 2 union_thm, cj 3 union_thm] >> simp[] >>
    gvs[SUBSET_DEF] >> simp[Once insert_seq_cases]
    )
  >- simp[Once insert_seq_cases]
  >- simp[Once insert_seq_cases, insert_seq_refl]
  >- (
    rw[Once insert_seq_cases, insert_seq_refl] >> disj2_tac >>
    rw[LIST_REL_EL_EQN] >> gvs[EVERY_EL, insert_seq_refl]
    )
  >- (
    strip_tac >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
    DEP_REWRITE_TAC[cj 1 FOLDL_union, cj 2 FOLDL_union, cj 3 FOLDL_union] >>
    gvs[BIGUNION_SUBSET, UNZIP3_MAP, MEM_MAP, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    rpt conj_tac
    >- (
      gen_tac >> strip_tac >>
      qmatch_goalsub_abbrev_tac `FST foo` >> PairCases_on `foo` >> gvs[] >>
      last_x_assum drule >> simp[]
      )
    >- (
      rw[SUBSET_DEF, MEM_MAP, PULL_EXISTS] >> goal_assum $ drule_at Any >>
      last_x_assum drule >>
      qpat_abbrev_tac `foo = demands_analysis_fun _ _ _` >>
      PairCases_on `foo` >> gvs[SUBSET_DEF]
      )
    >- (
      simp[Once insert_seq_cases] >> disj2_tac >>
      rw[LIST_REL_EL_EQN, EL_MAP] >> gvs[MEM_EL, PULL_EXISTS] >>
      last_x_assum drule >>
      qpat_abbrev_tac `foo = demands_analysis_fun _ _ _` >>
      PairCases_on `foo` >> rw[]
      )
    )
  >- (
    strip_tac >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
    simp[Once insert_seq_cases] >> disj2_tac >>
    rw[LIST_REL_EL_EQN, EL_MAP] >> gvs[EVERY_EL, MEM_EL, PULL_EXISTS] >>
    qpat_abbrev_tac `dn = demands_analysis_fun _ _ _` >> PairCases_on `dn` >> gvs[] >>
    irule insert_seq_trans >> irule_at (Pos last) add_all_demands_insert_seq >>
    last_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
    map_every imp_res_tac [insert_seq_NestedCase_free, insert_seq_freevars] >> gvs[]
    )
  >~ [`Case`]
  >- (
    strip_tac >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
    gvs[FOLDR_Case_demands_lemma] >>
    conj_tac >- gvs[SUBSET_DEF] >>
    simp[Once insert_seq_cases] >> disj2_tac >> rw[LIST_REL_EL_EQN, EL_MAP]
    >- (
      rpt (pairarg_tac >> gvs[]) >> gvs[MEM_EL, PULL_EXISTS] >>
      qmatch_goalsub_abbrev_tac `add_all_demands _ foo` >> PairCases_on `foo` >> gvs[] >>
      first_x_assum drule >> rw[] >>
      gvs[EVERY_EL, EL_MAP] >> first_x_assum drule >> rw[] >> gvs[] >>
      irule insert_seq_trans >> goal_assum drule >>
      irule add_all_demands_insert_seq >>
      map_every imp_res_tac [insert_seq_NestedCase_free, insert_seq_freevars] >> gvs[]
      )
    >- (
      Cases_on `eopt` >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
      qmatch_goalsub_abbrev_tac `add_all_demands _ foo` >> PairCases_on `foo` >> gvs[] >>
      irule insert_seq_trans >> goal_assum drule >>
      irule add_all_demands_insert_seq >>
      map_every imp_res_tac [insert_seq_NestedCase_free, insert_seq_freevars] >> gvs[]
      )
    ) >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac fixpoint_analysis_MAP_FST >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  gvs[UNZIP3_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
  >- (
    DEP_REWRITE_TAC[cj 1 FOLDL_delete_ok, cj 2 FOLDL_delete_ok] >> simp[] >>
    DEP_REWRITE_TAC[cj 3 FOLDL_delete_soundness] >> simp[] >>
    conj_tac >- gvs[SUBSET_DEF] >>
    simp[AllCaseEqs(), PULL_EXISTS] >> conj_tac
    >- (
      rpt gen_tac >> strip_tac >> gvs[] >> PairCases_on `a` >> gvs[] >>
      DEP_REWRITE_TAC[cj 1 FOLDL_delete_ok, cj 2 FOLDL_delete_ok] >> simp[] >>
      DEP_REWRITE_TAC[cj 3 FOLDL_delete_soundness] >> gvs[SUBSET_DEF]
      ) >>
    simp[Once insert_seq_cases] >> disj2_tac >> reverse conj_tac
    >- (
      irule insert_seq_trans >> goal_assum drule >> irule adds_demands_insert_seq >>
      map_every imp_res_tac [insert_seq_NestedCase_free, insert_seq_freevars] >> gvs[]
      ) >>
    gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_MAP, EVERY_EL] >> rw[] >>
    rpt (pairarg_tac >> gvs[]) >> last_x_assum drule >> rw[] >>
    Cases_on `args` >> rw[rev_split_body_def] >>
    drule fixpoint_analysis_LIST_REL >> rw[LIST_REL_EL_EQN] >>
    pop_assum drule >> rw[] >> first_x_assum drule >> rw[] >>
    gvs[DefnBase.one_line_ify NONE split_body_def, AllCaseEqs(), insert_seq_refl]
    >- simp[Once insert_seq_cases, insert_seq_refl] >>
    simp[Once insert_seq_cases] >> disj2_tac >>
    irule rev_split_body_inner_insert_seq >> simp[] >>
    drule fixpoint_analysis_freevars >> simp[Once MEM_EL, PULL_EXISTS] >>
    disch_then drule >> simp[SUBSET_DEF]
    )
  >- (
    DEP_REWRITE_TAC[cj 1 FOLDL_delete_ok, cj 2 FOLDL_delete_ok] >> simp[] >>
    DEP_REWRITE_TAC[cj 3 FOLDL_delete_soundness] >> simp[SF CONJ_ss] >>
    DEP_REWRITE_TAC[cj 1 map_handle_multi_ok, cj 2 map_handle_multi_ok] >>
    simp[] >> rpt conj_tac
    >- (
      simp[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> rpt gen_tac >> strip_tac >>
      qmatch_goalsub_abbrev_tac `FST foo` >> PairCases_on `foo` >> gvs[] >>
      last_x_assum drule >> simp[] >> impl_tac >> rw[] >>
      gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> first_x_assum drule >> simp[]
      )
    >- (
      simp[pure_miscTheory.DIFF_SUBSET] >>
      irule SUBSET_TRANS >> irule_at Any $ SRULE [] handle_multi_bind_map >>
      simp[EVERY_MAP, LAMBDA_PROD] >>
      irule_at (Pos last) SUBSET_REFL >> gvs[SUBSET_DEF] >>
      gvs[EVERY_MEM] >> rw[] >> pairarg_tac >> gvs[] >>
      qmatch_goalsub_abbrev_tac `FST foo` >> PairCases_on `foo` >> gvs[] >>
      last_x_assum drule >> simp[] >> impl_tac >> rw[]
      >- (gvs[MEM_MAP, PULL_EXISTS] >> first_x_assum drule >> simp[])
      >- (simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> metis_tac[])
      )
    >- (
      Cases_on `fd'` >> gvs[] >> pairarg_tac >> gvs[] >>
      simp[FOLDL_delete_soundness] >> gvs[SUBSET_DEF]
      ) >>
    simp[Once insert_seq_cases] >> disj2_tac >>
    simp[ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> reverse conj_tac
    >- (
      irule insert_seq_trans >> goal_assum drule >> irule adds_demands_insert_seq >>
      map_every imp_res_tac [insert_seq_NestedCase_free, insert_seq_freevars] >> gvs[]
      ) >>
    rw[LIST_REL_EL_EQN, EL_MAP] >> rpt (pairarg_tac >> gvs[]) >>
    qmatch_goalsub_abbrev_tac `SND foo` >> PairCases_on `foo` >> gvs[] >>
    gvs[MEM_EL, PULL_EXISTS] >> last_x_assum drule >> simp[] >>
    impl_tac >> gvs[EVERY_EL, EL_MAP] >> first_x_assum drule >> simp[]
    )
QED

val _ = export_theory();
