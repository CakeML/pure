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
open pure_letrec_seqTheory;


val _ = new_theory "pure_demands_analysisProof";

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

Theorem split_body_soundness:
  ∀e l bL body v. LENGTH l = LENGTH bL ⇒
                  split_body e = (l, body) ⇒
                  (v, (exp_of e)) = mk_lams (v, ZIP(MAP explode l, bL), (exp_of body)) ∧
                  (NestedCase_free e ⇒ NestedCase_free body)
Proof
  Cases \\ gs [split_body_def, Lams_def, mk_lams_def, NestedCase_free_def]
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
    can_compute_fixpoint binds1 = SOME binds2 ∧ EVERY (λ(v, e). NestedCase_free e) binds1 ⇒
    ∀binds1b binds2b bLfull.
      LIST_REL (λbL (_, args, _). LENGTH bL = LENGTH args) bLfull binds2 ∧
      binds1b = MAP (λ(v, e). (explode v, exp_of e)) binds1 ∧
      binds2b = MAP2 (λbL (v, args, e). (explode v, ZIP (MAP explode args, bL), exp_of e)) bLfull binds2
      ⇒ binds1b = MAP mk_lams binds2b ∧
        ∀v args body.
          ALL_DISTINCT (MAP FST binds1) ∧
          MEM (v, args, body) binds2b ⇒
          ALL_DISTINCT (MAP FST args) ∧
          DISJOINT (set (MAP FST args)) (set (MAP FST binds2b)) ∧
          freevars body ⊆ set (MAP FST binds2b) ∪ set (MAP FST args)
Proof
  gs [can_compute_fixpoint_def]
  \\ gen_tac \\ strip_tac
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
  \\ dxrule_then assume_tac compute_ALL_DISTINCT_soundness
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
  \\ qspec_then ‘binds1’ assume_tac can_compute_fixpoint_lemma
  \\ rename1 ‘split_body body' = (args', body2)’
  \\ rename1 ‘LENGTH (EL n bLfull) = LENGTH _’
  \\ qspecl_then [‘body'’, ‘args'’, ‘EL n bLfull’] assume_tac split_body_soundness
  \\ gvs []
  \\ conj_tac
  >- gs [DISJOINT_ALT, PULL_EXISTS, MEM_MAP, FORALL_PROD]
  \\ gvs [SUBSET_DEF, PULL_EXISTS, MEM_MAP, EXISTS_PROD]
  \\ rw [] \\ last_x_assum $ dxrule_then assume_tac
  \\ gs []
  \\ metis_tac []
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
             ∀fds c ds fd l dwas binds.
               fixpoint1 c e fds = (ds,fd) ∧ map_ok fds ∧
               cmp_of fds = compare ∧
               (∀v. v ∈ FDOM (to_fmap fds) ⇒
                    ∃args body.
                      LENGTH args = LENGTH (to_fmap fds ' v) ∧
                      MEM (explode v,ZIP (args,to_fmap fds ' v),body) binds) ∧
               (case fd of
                  NONE => l = [] ∧ dwas = empty compare
                | SOME (l',dwas') =>
                    l = l' ∧ dwas = dwas') ⇒
               find_fixpoint binds (exp_of e) (ctxt_trans c)
                             (IMAGE explode (FDOM (to_fmap ds)))
                             (IMAGE explode (FDOM (to_fmap dwas))) l ∧
               map_ok ds ∧ cmp_of ds = compare ∧
               map_ok dwas ∧ cmp_of dwas = compare) ⇒
      ∀bL c fds bL2 ds2 binds.
        fixpoint_demands_App bL (MAP (λe. fixpoint1 c e fds) l) = (bL2, ds2) ∧
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

Theorem fixpoint1_soundness:
  ∀fds c ds fd l dwas binds.
    fixpoint1 c e fds = (ds, fd) ∧
    map_ok fds ∧ cmp_of fds = compare ∧
    (∀v. v ∈ FDOM (to_fmap fds) ⇒
         ∃args body. LENGTH args = LENGTH (to_fmap fds ' v) ∧
                     MEM (explode v, ZIP (args, to_fmap fds ' v), body) binds) ∧
    (case fd of
     | NONE => (l = [] ∧ dwas = empty compare)
     | SOME (l', dwas') => (l = l' ∧ dwas = dwas')) ⇒
    find_fixpoint binds (exp_of e) (ctxt_trans c)
                  (IMAGE explode (FDOM $ to_fmap ds))
                  (IMAGE explode (FDOM $ to_fmap dwas)) l ∧
    map_ok ds ∧ cmp_of ds = compare ∧ map_ok dwas ∧ cmp_of dwas = compare
Proof
  completeInduct_on ‘cexp_size (K 0) e’ \\ gs []
  \\ Cases \\ gs [fixpoint1_def]
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
      \\ first_x_assum $ dxrule_then assume_tac
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
  >- (rw [empty_thm, TotOrd_compare]
      \\ irule find_fixpoint_refl)
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
  >~[‘Case _ expr _ rows fall’]
  >- (rw [empty_thm, TotOrd_compare]
      \\ irule find_fixpoint_refl)
  >~[‘NestedCase _ _ _ _ _ _’]
  >- (rw [empty_thm, TotOrd_compare]
      \\ irule find_fixpoint_refl)
QED

Theorem is_lower_soundness:
  ∀l1 l2. is_lower l1 l2 ⇒
          LIST_REL (λ(_, a1, _) (_, a2, _).
                      LIST_REL (λ(_, b1) (_, b2). b2 ⇒ b1) a1 a2) l1 l2
Proof
  Induct \\ gs [FORALL_PROD]
  >- (Cases \\ gs [is_lower_def])
  \\ gen_tac \\ gen_tac \\ gen_tac
  \\ Cases \\ gs [is_lower_def]
  \\ rename1 ‘is_lower _ (h::_)’
  \\ PairCases_on ‘h’ \\ gs [is_lower_def]
QED

Theorem FST_handle_fixpoint1:
  ∀fds e. FST (handle_fixpoint1 fds e) = FST e
Proof
  gs [FORALL_PROD, handle_fixpoint1_def]
  \\ rw []
  \\ pairarg_tac \\ gs []
QED

Theorem handle_fixpoint1_soundness:
  ∀fds arg out binds.
    handle_fixpoint1 fds arg = out ∧
    map_ok fds ∧ cmp_of fds = compare ∧
    (∀v. v ∈ FDOM (to_fmap fds) ⇒
         ∃args body. LENGTH args = LENGTH (to_fmap fds ' v) ∧
                     MEM (explode v, ZIP (args, to_fmap fds ' v), body) binds)
    ⇒
    SND (SND arg) = SND (SND out) ∧
    ∃ds ads fs.
        find_fixpoint binds (exp_of (SND (SND arg))) Nil ds ads fs ∧
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
    m = FOLDR (λ(v, args, e) m. insert m v (MAP SND args))
                (mlmap$empty mlstring$compare) binds ∧
    binds2 = MAP (λ(v, args, e). (explode v, (MAP (explode ## I) args), exp_of e)) binds ⇒
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
      \\ qexists_tac ‘exp_of e’
      \\ gs []
      \\ disj1_tac
      \\ irule LIST_EQ
      \\ rw [EL_MAP, EL_ZIP, SND_THM]
      \\ pairarg_tac \\ gs [])
  \\ gs [FAPPLY_FUPDATE_THM]
  \\ IF_CASES_TAC \\ gs []
QED

Theorem compute_fixpoint_rec_soundness:
  ∀i binds binds2 binds2b.
    compute_fixpoint_rec i binds = binds2 ∧
    ALL_DISTINCT (MAP FST binds) ∧
    binds2b = MAP (λ(v, args, e). (explode v, (MAP (explode ## I) args), exp_of e)) binds2
    ⇒ ∀v args body.
        MEM (v, args, body) binds2b
        ⇒ ∃ds ads fs.
            find_fixpoint binds2b body Nil ds ads fs ∧
            ∀v. MEM (v, T) args ⇒ v ∈ ds
Proof
  Induct \\ gs [compute_fixpoint_rec_def]
  >- (rw []
      \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
      \\ irule_at Any find_fixpoint_refl
      \\ gs [MEM_MAP]
      \\ pairarg_tac
      \\ gs [MEM_MAP, FORALL_PROD])
  \\ rw []
  >~[‘¬is_lower _ _’]
  >- (last_x_assum irule
      \\ first_x_assum $ irule_at Any
      \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_handle_fixpoint1]
      \\ gs [GSYM FST_THM, GSYM LAMBDA_PROD])
  \\ last_x_assum kall_tac
  \\ dxrule_then assume_tac is_lower_soundness
  \\ gvs [MEM_MAP]
  \\ pairarg_tac \\ gs []
  \\ gs [MEM_EL]
  \\ dxrule_then assume_tac handle_fixpoint1_soundness
  \\ dxrule_then assume_tac compute_fixpoint_rec_lemma
  \\ gvs []
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

Theorem update_ctxt_soundness:
  ∀l e e' n1 n2 c fds fd.
    EVERY (λv. ∀d. (v, d) ∉ fds) (MAP SND l)
    ∧ find e (update_ctxt n1 n2 c (MAP (λ(i, v). (i, implode v)) l)) fds {} e' fd
    ⇒ find (lets_for (explode n1) (explode n2) l e) c fds
           {} (lets_for (explode n1) (explode n2) l e') NONE
Proof
  Induct
  \\ gvs [lets_for_def, update_ctxt_def]
  >- (rw [] \\ irule find_Drop_fd \\ pop_assum $ irule_at Any)
  \\ Cases
  \\ rw [lets_for_def, update_ctxt_def]
  \\ irule find_Let
  \\ fs [dest_fd_SND_def]
  \\ rpt $ last_x_assum $ irule_at Any
  \\ irule_at Any find_Bottom
  \\ gvs []
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
                     (update_ctxt a1 s c (MAPi (λi v. (i, v)) b1)) {}
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
      \\ irule_at Any update_ctxt_soundness
      \\ gvs [combinTheory.o_DEF, LAMBDA_PROD, MAPi_implode_MAP_explode]
      \\ pop_assum $ irule_at Any \\ fs []) >>
  simp[] >> first_assum $ irule_at Any >> simp[]
QED

Theorem find_rows_of:
  ∀l l' ke ke' c s fds fd.
    l ≠ [] ∧
    LIST_REL (λ(a1, b1, e1) (a2, b2, e2).
                a1 = a2 ∧ b1 = b2 ∧
                find (exp_of e1)
                     (update_ctxt a1 s c (MAPi (λi v. (i, v)) b1)) {}
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
  simp []
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
      gvs [] >> rename1 ‘_ p = _’ >> PairCases_on ‘p’ >> gvs [] >> conj_tac >~
      [‘MAP _ _ = MAP _ _’]
      >- (irule LIST_EQ >> rw [EL_MAP] >>
          rename1 ‘n < _’ >> qabbrev_tac ‘pair = EL n l’ >>
          PairCases_on ‘pair’ >> gvs [] >>
          AP_TERM_TAC >>
          last_x_assum $ irule_at Any >>
          irule_at Any EQ_REFL >> qexists_tac ‘f’ >>
          assume_tac cexp_size_lemma >> gvs [] >>
          ‘MEM (EL n l) l’ by gvs [EL_MEM] >>
          gvs [cexp_size_def] >> first_x_assum $ dxrule_then assume_tac >>
          gvs [EVERY_MEM, MEM_EL, PULL_EXISTS, EL_MAP] >> metis_tac[SND]) >>
      CASE_TAC \\ fs [] \\ CASE_TAC \\ fs [] >>
      AP_TERM_TAC >> first_x_assum irule >> simp[] >>
      qexists ‘f’ >> simp[] >>
      fs [cexp_size_def])
QED

Theorem ALL_DISTINCT_IMP:
  ∀l. ALL_DISTINCT (MAP FST l) ⇒ ALL_DISTINCT (MAP (λ(p1, p2). explode p1) l)
Proof
  Induct >> gvs [] >> rw [] >>
  strip_tac >> first_x_assum irule >>
  gvs [MEM_EL] >>
  first_assum $ irule_at $ Pos hd >> gvs [EL_MAP] >>
  pairarg_tac >> gs [] >> pairarg_tac >> gs []
QED

Theorem EL_EQ:
  (∀n. n < LENGTH l ⇒ P (EL n l)) ⇔
  (∀n. n < LENGTH l ⇒ ∀x. EL n l = x ⇒ P x)
Proof
  simp[]
QED

Theorem demands_analysis_ignores_ctxt:
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
QED

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

Theorem demands_analysis_soundness_lemma:
  ∀(f: α -> num) (e: α cexp) c fds m e' fd.
    demands_analysis_fun c e fds = (m, e', fd) ∧ map_ok fds ∧
    cmp_of fds = compare ∧ NestedCase_free e
    ⇒
    find (exp_of e) (ctxt_trans c) (fdemands_map_to_set fds)
         (demands_map_to_set m) (exp_of e') (fd_to_set fd) ∧
    map_ok m ∧ cmp_of m = compare ∧
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
         TotOrd_compare, insert_thm, empty_thm] >~
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
                  demands_map_empty,
                  exp_of_def, empty_thm, TotOrd_compare, find_Bottom]
          \\ rename1 ‘e1::t’
          \\ Cases_on ‘t’ >~[‘Prim a Seq [e]’]
          >- (rw [demands_analysis_fun_def, empty_thm, fd_to_set_def, demands_map_empty,
                 TotOrd_compare, exp_of_def, op_of_def]
              \\ irule find_Eq \\ irule_at Any find_Bottom
              \\ irule exp_eq_IMP_exp_eq_in_ctxt
              \\ fs [exp_of_def, op_of_def, eval_wh_IMP_exp_eq,
                     eval_wh_def, eval_wh_to_def, subst_def])
          \\ rename1 ‘e1::e2::t’
          \\ Cases_on ‘t’ >~
          [‘Prim a Seq (e1::e2::e3::t)’]
          >- (rw [demands_analysis_fun_def, empty_thm, fd_to_set_def,
                  demands_map_empty,
                  TotOrd_compare, exp_of_def, op_of_def]
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
          \\ fs [demands_analysis_fun_def]
          \\ rename1 ‘demands_analysis_fun c _ fds’
          \\ pop_assum     $ qspecl_then [‘c’, ‘fds’] assume_tac
          \\ first_x_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
          \\ qabbrev_tac ‘p1 = demands_analysis_fun c e1 fds’
          \\ qabbrev_tac ‘p2 = demands_analysis_fun c e2 fds’
          \\ PairCases_on ‘p1’
          \\ PairCases_on ‘p2’
          \\ gvs [exp_of_def, op_of_def, demands_map_union, union_thm]
          \\ dxrule_then (dxrule_then irule) find_Seq2) >~
      [‘AtomOp op’]
      >- (rpt gen_tac \\ strip_tac
          \\ gvs [exp_of_def, op_of_def, demands_analysis_fun_def, UNZIP3_MAP,
                  MAP_MAP_o, combinTheory.o_DEF]
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
          \\ irule find_Atom \\ fs [] \\ qexists_tac ‘NONE’
          \\ rw [LIST_REL_EL_EQN, EL_ZIP, EL_MAP]
          \\ rename1 ‘EL n l’
          \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n l)’] assume_tac
          \\ ‘cexp_size f (EL n l) < list_size (cexp_size f) l’
            by metis_tac [cexp_size_lemma, EL_MEM, cexp_size_eq]
          \\ fs [cexp_size_def, cexp_size_eq]
          \\ pop_assum kall_tac
          \\ pop_assum $ qspecl_then [‘f’, ‘EL n l’] assume_tac
          \\ fs []
          \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
          \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n l) fds’
          \\ PairCases_on ‘p’ \\ gvs [EVERY_MEM, MEM_EL, PULL_EXISTS]
          \\ dxrule_then assume_tac find_Drop_fd \\ fs [])
      \\ rw [] (* Cons s *)
      \\ fs [empty_thm, TotOrd_compare, demands_analysis_fun_def, demands_map_empty]
      \\ rw [exp_of_def, op_of_def, fd_to_set_def]
      \\ irule_at Any find_Prim \\ rw []
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
      \\ irule_at Any add_all_demands_soundness
      \\ gvs [cmp_of_def, TotOrd_compare, EVERY_MEM, MEM_EL, PULL_EXISTS]
      \\ first_x_assum $ irule_at Any)
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
      \\ gvs [fd_to_set_def, exp_of_def, EVERY_MEM, MEM_EL, PULL_EXISTS]
      >- (irule find_Apps \\ first_x_assum $ irule_at Any
          \\ rw [LIST_REL_EL_EQN, EL_MAP]
          \\ rename1 ‘EL n argl’
          \\ last_x_assum $ qspecl_then [‘cexp_size f (EL n argl)’] assume_tac
          \\ ‘cexp_size f (EL n argl) < list_size (cexp_size f) argl’
            by metis_tac [cexp_size_lemma, MEM_EL, cexp_size_eq]
          \\ fs [cexp_size_def, cexp_size_eq]
          \\ pop_assum kall_tac
          \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl’] assume_tac
          \\ fs []
          \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
          \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl) fds’
          \\ PairCases_on ‘p’ \\ fs []
          \\ irule_at Any add_all_demands_soundness
          \\ gvs [TotOrd_compare] \\ first_x_assum $ irule_at Any)
      \\ FULL_CASE_TAC \\ gvs []
      \\ rename1 ‘handle_Apps_demands a fdL (MAP _ argl)’
      \\ qabbrev_tac ‘hAd = handle_Apps_demands a fdL (MAP (λe. demands_analysis_fun c e fds) argl)’
      \\ PairCases_on ‘hAd’ \\ fs []
      \\ drule_then assume_tac handle_Apps_demands_soundness
      \\ ‘EVERY (λ(dm, _, _). map_ok dm ∧ cmp_of dm = compare)
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
            \\ PairCases_on ‘p’ \\ fs [])
      \\ first_x_assum $ dxrule_then assume_tac
      \\ gvs []
      \\ FULL_CASE_TAC \\ gvs [union_thm, fd_to_set_def, demands_map_union, exp_of_def]
      >- (rename1 ‘argl1 ++ argl2’
          \\ qabbrev_tac ‘hAd' = handle_Apps_demands a fdL (MAP (λe. demands_analysis_fun c e fds) argl1)’
          \\ PairCases_on ‘hAd'’ \\ gvs [Apps_append]
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
              \\ FULL_CASE_TAC \\ gvs []
              >- (first_assum (irule_at Any o cj 1) >>
                  metis_tac[DECIDE “n:num < x ⇒ n < x + y”])
              >- (irule_at Any add_all_demands_soundness
                  \\ first_assum (irule_at Any o cj 1)
                  \\ conj_asm1_tac >- metis_tac[DECIDE “n:num < x ⇒ n < x + y”]
                  \\ gvs [TotOrd_compare]))
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
              \\ gvs[]
              \\ pop_assum mp_tac \\ impl_tac
              >- (first_x_assum $ qspec_then ‘n + LENGTH fdL’ mp_tac >>
                  simp[]) \\ strip_tac
              \\ first_x_assum $ irule_at Any
              \\ gvs [TotOrd_compare]))
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
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘e’] assume_tac
      \\ rename1 ‘demands_analysis_fun (IsFree namel c) _ (FOLDL _ fds _)’
      \\ qabbrev_tac ‘p = demands_analysis_fun (IsFree namel c) e
                                               (FOLDL (λf k. delete f k) fds namel)’
      \\ PairCases_on ‘p’ \\ fs [empty_thm, TotOrd_compare]
      \\ first_x_assum $ drule_then assume_tac
      \\ gvs [exp_of_def, fd_to_set_def, demands_map_empty, ctxt_trans_def,
              FOLDL_delete_ok, boolList_of_fdemands_soundness]
      \\ irule find_Subset
      \\ irule_at Any find_Lams_fd
      \\ irule_at Any add_all_demands_soundness
      \\ irule_at Any find_Drop_fd \\ gvs [FOLDL_MAP]
      \\ first_x_assum $ irule_at $ Pos hd
      \\ gvs [fdemands_map_FOLDL_delete_subset, boolList_of_fdemands_def, EVERY_MEM,
              fdemands_map_FOLDL_delete, TotOrd_compare, MEM_MAP, PULL_EXISTS])
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
      \\ gvs [ctxt_trans_def, fd_to_set_def, lookup_thm, exp_of_def, op_of_def, delete_thm]
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
      \\ reverse IF_CASES_TAC
      >- (rw [empty_thm, TotOrd_compare, fd_to_set_def, demands_map_empty]
          \\ gvs [exp_of_def, find_Bottom])
      \\ dxrule_then assume_tac compute_ALL_DISTINCT_soundness \\ gvs [UNZIP3_MAP]
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
            \\ PairCases_on ‘p’ \\ fs [] \\ first_x_assum $ drule_then assume_tac
            \\ gvs [FOLDL_delete_ok, EL_MAP]
            \\ qabbrev_tac ‘expr = EL i binds’ \\ PairCases_on ‘expr’ \\ gvs [])
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
             >>~[‘find (SND (_ (EL i binds))) (RecBind (MAP _ (ZIP _)) (ctxt_trans c))’]
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
          \\ unabbrev_all_tac \\ gvs [ctxt_trans_def, FOLDL_delete_ok])
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
          \\ unabbrev_all_tac \\ gvs [ctxt_trans_def, FOLDL_delete_ok])
      \\ rename1 ‘find (SND (_ (EL i binds))) _ (fdemands_map_to_set (FOLDL _ fds _))’
      \\ last_x_assum $ qspecl_then [‘cexp_size f (SND (EL i binds))’] assume_tac
      \\ ‘cexp_size f (SND (EL i binds)) < cexp7_size f binds’
        by (assume_tac cexp_size_lemma \\ gvs [] \\ first_x_assum irule
            \\ gvs [MEM_EL] \\ first_assum $ irule_at Any
            \\ irule_at Any $ PAIR)
      \\ gvs [] \\ pop_assum kall_tac
      \\ pop_assum $ qspecl_then [‘f’, ‘SND (EL i binds)’] assume_tac \\ gvs []
      \\ qabbrev_tac ‘fds2 = FOLDL (λf k. delete f k) fds (MAP FST binds)’
      \\ qabbrev_tac ‘p = demands_analysis_fun (RecBind binds c) (SND (EL i binds)) fds2’
      \\ PairCases_on ‘p’ \\ gvs []
      \\ first_x_assum $ drule_then assume_tac
      \\ qabbrev_tac ‘pair = EL i binds’ \\ PairCases_on ‘pair’ \\ gvs []
      \\ unabbrev_all_tac \\ gvs [ctxt_trans_def, FOLDL_delete_ok])
  >~ [‘Case a case_exp s [] opt’]
  >- (gen_tac \\ gen_tac
      \\ rename1 ‘Bind _ _ c’
      \\ rpt $ gen_tac
      \\ IF_CASES_TAC \\ simp []
      >- (gvs [empty_thm, TotOrd_compare, exp_of_def, rows_of_def,
               demands_map_empty, fd_to_set_def] \\ rw []
          \\ rw [find_Bottom,exp_of_def,rows_of_def])
      \\ IF_CASES_TAC \\ simp []
      >- (gvs [empty_thm, TotOrd_compare, exp_of_def, rows_of_def,
               demands_map_empty, fd_to_set_def] \\ rw []
          \\ rw [find_Bottom,exp_of_def,rows_of_def])
      \\ first_assum $ qspecl_then [‘cexp_size f case_exp’] assume_tac
      \\ gvs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘case_exp’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
      \\ qabbrev_tac ‘cexp = demands_analysis_fun c case_exp fds’
      \\ PairCases_on ‘cexp’ \\ gvs []
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
                                      (empty compare)))) l’
         ] assume_tac find_rows_of
      \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
      \\ pop_assum $ irule_at Any
      \\ gvs [dest_fd_SND_def]
      \\ CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["fds0", "fd"]))
      \\ qexists_tac ‘{}’ \\ qexists_tac ‘NONE’
      \\ rw [LIST_REL_EL_EQN, EL_MAP, dest_fd_SND_def]
      >- ((* handling the list of cases *) pairarg_tac
          \\ fs []
          \\ irule find_Subset
          \\ rename1
             ‘demands_analysis_fun (Unfold names s args (Bind s case_exp c)) e'’
          \\ qabbrev_tac
             ‘p = demands_analysis_fun
                  (Unfold names s args (Bind s case_exp c)) e' (empty compare)’
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
          \\ gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
          \\ fs [ctxt_trans_def, TotOrd_compare, fdemands_map_to_set_def, empty_thm]
          \\ pop_assum mp_tac \\ impl_tac >- metis_tac[MEM_EL]
          \\ strip_tac \\ simp[]
          \\ first_x_assum $ irule_at Any \\ gs [TotOrd_compare])
      (* handling the optional fall-through expression at the bottom *)
      \\ rename [‘option_CASE opt Fail’]
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
      \\ gvs[cexp_size_def]
      \\ pop_assum (drule_at_then (Pat ‘demands_analysis_fun _ _ _ = _’)
                    strip_assume_tac)
      \\ pop_assum (resolve_then (Pos hd) assume_tac EQ_REFL)
      \\ gvs[ctxt_trans_def, fdemands_map_to_set_def, empty_thm, TotOrd_compare]
      \\ irule_at Any find_Drop_fd
      \\ first_assum $ irule_at Any)
QED

Theorem demands_analysis_soundness:
  ∀(e : α cexp) a. NestedCase_free e ⇒ exp_of e ≈ exp_of (demands_analysis e)
Proof
  rpt strip_tac \\ gvs [demands_analysis_def, SND_THM]
  \\ pairarg_tac \\ gs [FST_THM]
  \\ pairarg_tac \\ gs []
  \\ qspecl_then [‘(K 0) : α -> num’, ‘e’, ‘Nil’, ‘empty compare’]
                 assume_tac demands_analysis_soundness_lemma
  \\ gvs [empty_thm, TotOrd_compare, ctxt_trans_def, fdemands_map_to_set_def]
  \\ dxrule_then assume_tac find_soundness
  \\ gs []
QED

val _ = export_theory();
