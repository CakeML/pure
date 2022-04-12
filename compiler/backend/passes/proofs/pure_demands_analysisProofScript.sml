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
     pure_cexpTheory pure_demandTheory pure_demands_analysisTheory;

val _ = new_theory "pure_demands_analysisProof";

(** Proof **)

Definition update_ctxt_def:
  (update_ctxt id n c [] = c) ∧
  (update_ctxt id n c ((i,p)::tl) =
   update_ctxt id n (Bind p (Proj id i (Var n)) c) tl)
End

Definition ctxt_trans_def:
  ctxt_trans (Nil: α da_ctxt) = Nil ∧
  ctxt_trans (IsFree l ctxt) = FOLDL (λc n. IsFree n (c:ctxt)) (ctxt_trans ctxt) l ∧
  ctxt_trans (Bind n e ctxt) = Bind n (exp_of e) (ctxt_trans ctxt) ∧
  ctxt_trans ((RecBind (binds: (vname # α cexp) list) ctxt): α da_ctxt) = (RecBind (MAP (λ(n,e). (n, exp_of e)) binds) (ctxt_trans ctxt) : ctxt) ∧
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
  map_ok m ⇒ demands_map_to_set (insert m (implode n) ()) = demands_map_to_set m ∪ {[], n}
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
        ⇒ map_ok (FOLDL (λm2 w. delete m2 (implode w)) m vL)
          ∧ cmp_of (FOLDL (λm2 w. delete m2 ((implode w) : mlstring)) m vL) = cmp_of m
Proof
  Induct_on ‘LENGTH vL’ >> rw [] >>
  rename1 ‘SUC _ = LENGTH vL’ >>
  qspecl_then [‘vL’] assume_tac last_exists >> gvs [FOLDL_APPEND, delete_thm]
QED

Theorem demands_map_delete:
  ∀m v. map_ok m ⇒ ∀ps. (ps, v) ∉ demands_map_to_set (delete m (implode v))
Proof
  rw [demands_map_to_set_def, delete_thm]
QED

Theorem demands_map_delete_subset:
  ∀m v. map_ok m ⇒
        demands_map_to_set (delete m (implode v)) ⊆ demands_map_to_set m
Proof
  rw [demands_map_to_set_def, delete_thm]
QED

Theorem demands_map_FOLDL_delete_subset:
  ∀vL m. map_ok m ⇒
        demands_map_to_set (FOLDL (λf k. delete f (implode k)) m vL) ⊆ demands_map_to_set m
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
    ⇒ ∀ps. (ps, v) ∉ demands_map_to_set (FOLDL (λm2 w. delete m2 (implode w)) m vL)
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
            (lookup fds (implode n) = SOME x ⇔ (n, x) ∈ fdemands_map_to_set fds)
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
           ⇒ fdemands_map_to_set (FOLDL (λf k. delete f (implode k)) fds vL)
                                 ⊆ fdemands_map_to_set fds
Proof
  Induct >> rw [] >>
  irule SUBSET_TRANS >> last_x_assum $ irule_at $ Pos hd >>
  gvs [delete_thm, fdemands_map_delete_subset]
QED

Theorem fdemands_map_delete:
  ∀m v. map_ok m ⇒ ∀ps. (v, ps) ∉ fdemands_map_to_set (delete m (implode v))
Proof
  rw [fdemands_map_to_set_def, delete_thm]
QED

Theorem fdemands_map_insert:
  ∀m v bL d. d ∈ fdemands_map_to_set (insert m (implode v) bL) ∧ map_ok m
             ⇒ (d = (v, bL) ∨ (FST d ≠ v ∧ d ∈ fdemands_map_to_set m))
Proof
  rw [] >> gvs [fdemands_map_to_set_def, insert_thm] >>
  rename1 ‘explode x = v’ >> Cases_on ‘explode x = v’ >> gvs [FAPPLY_FUPDATE_THM] >>
  FULL_CASE_TAC >> gvs [explode_implode]
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
                      ((v, bL) ∈ fdemands_map_to_set (FOLDL (λf k. delete f (implode k)) fds vL)
                       ⇔ ((v, bL) ∈ fdemands_map_to_set fds ∧ ¬MEM v vL))
Proof
  Induct >> rw [] >> eq_tac >> strip_tac >>
  rename1 ‘delete fds (implode h)’ >>
  last_x_assum $ qspecl_then [‘delete fds (implode h)’] assume_tac >>
  gvs [delete_thm] >>
  pop_assum kall_tac >>
  gvs [fdemands_map_to_set_def, delete_thm] >>
  conj_asm2_tac >> gvs [DOMSUB_FAPPLY_NEQ] >>
  strip_tac >> gvs [explode_implode, implode_explode]
QED

Theorem fdemands_map_FOLDL_delete:
  ∀m v.
    map_ok m ∧ MEM v vL
    ⇒ ∀ps. (v, ps) ∉ fdemands_map_to_set (FOLDL (λm2 w. delete m2 (implode w)) m vL)
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
               ∧ (n, ps) ∈ fdemands_map_to_set (delete fds (implode v))
               ⇒ n ≠ v ∧ (n, ps) ∈ fdemands_map_to_set fds
Proof
  rw [fdemands_map_to_set_def] >>
  gvs [delete_thm, DOMSUB_FAPPLY_NEQ]
  >- (strip_tac >> gvs [])
QED

Theorem demands_map_delete_soundness:
  ∀v m n ps. map_ok m
               ∧ (ps, n) ∈ demands_map_to_set (delete m (implode v))
               ⇒ n ≠ v ∧ (ps, n) ∈ demands_map_to_set m
Proof
  rw [demands_map_to_set_def] >>
  gvs [delete_thm, DOMSUB_FAPPLY_NEQ] >>
  strip_tac >> gvs []
QED

Theorem demands_map_FOLDL_delete_soundness:
  ∀vL m n ps. (ps, n) ∈ demands_map_to_set (FOLDL (λm v. delete m (implode v)) m vL) ∧ map_ok m
               ⇒ ¬MEM n vL ∧ (ps, n) ∈ demands_map_to_set m
Proof
  Induct >> rw [] >>
  last_x_assum $ dxrule_then assume_tac >>
  gvs [delete_thm] >>
  dxrule_then (dxrule_then assume_tac) demands_map_delete_soundness >> gvs []
QED

Theorem compute_ALL_DISTINCT_soundness_lemma:
  ∀l m. compute_ALL_DISTINCT l m ∧ map_ok m ⇒
        ALL_DISTINCT l ∧ (∀v. MEM v l ⇒ lookup m (implode v) = NONE)
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
  ∀l. compute_ALL_DISTINCT l (empty compare) ⇒ ALL_DISTINCT l
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
  \\ rename1 ‘lookup m (implode h)’
  \\ Cases_on ‘lookup m (implode h)’
  \\ fs []
  \\ rw [exp_of_def, op_of_def]
  \\ irule find_Seq
  \\ gvs [demands_map_to_set_def, lookup_thm, FLOOKUP_DEF]
  \\ rpt $ first_x_assum $ irule_at Any
  \\ fs [explode_implode]
QED

Theorem handle_Letrec_fdemands_soundness:
  ∀vL (mL : (bool list # (mlstring, unit) map) option list) fds.
    LENGTH vL = LENGTH mL ∧ map_ok fds ∧ cmp_of fds = compare
    ⇒ map_ok (handle_Letrec_fdemands fds vL mL)
      ∧ cmp_of (handle_Letrec_fdemands fds vL mL) = compare
      ∧ ∀v argDs. (v, argDs) ∈ fdemands_map_to_set (handle_Letrec_fdemands fds vL mL)
                  ⇒ (v, argDs) ∈ fdemands_map_to_set (FOLDL (λf v. delete f (implode v)) fds vL)
                    ∨ ∃i fdMap. i < LENGTH vL ∧ EL i vL = v ∧ EL i mL = SOME (argDs, fdMap)
Proof
  Induct >> gvs [handle_Letrec_fdemands_def] >>
  gen_tac >> Cases >> fs [] >>
  rename1 ‘handle_Letrec_fdemands _ _ (h2::_)’ >>
  Cases_on ‘h2’ >> gvs [handle_Letrec_fdemands_def] >> rw [] >>
  last_x_assum $ dxrule_then assume_tac
  >>~[‘FST x’]
  >- (pop_assum $ qspecl_then [‘insert fds (implode h) (FST x)’] assume_tac >> gvs [insert_thm])
  >- (pop_assum $ qspecl_then [‘insert fds (implode h) (FST x)’] assume_tac >> gvs [insert_thm])
  >- (pop_assum $ qspecl_then [‘insert fds (implode h) (FST x)’] assume_tac >> gvs [insert_thm] >>
      first_x_assum $ dxrule_then assume_tac >> gvs []
      >- (rename1 ‘FOLDL _ (insert fds (implode h) (FST x)) vL’ >>
          qspecl_then [‘vL’, ‘insert fds (implode h) (FST x)’] assume_tac fdemands_map_FOLDL_delete2 >>
          gvs [insert_thm] >> pop_assum kall_tac >>
          dxrule_then assume_tac fdemands_map_insert >> gvs []
          >- (disj2_tac >> qexists_tac ‘0’ >> qexists_tac ‘SND x’ >> gvs [])
          >- (qspecl_then [‘vL’, ‘delete fds (implode h)’] assume_tac $ iffRL fdemands_map_FOLDL_delete2 >>
              disj1_tac >> gvs [delete_thm] >> pop_assum irule >>
              gvs [fdemands_map_to_set_def, delete_thm] >>
              conj_asm2_tac >> gvs [DOMSUB_FAPPLY_NEQ] >>
              strip_tac >> gvs [explode_implode]))
      >- (rename1 ‘i < _’ >> disj2_tac >>
          qexists_tac ‘SUC i’ >> gvs [] >> first_x_assum $ irule_at Any))
  >>~[‘delete fds (implode h)’]
  >- (pop_assum $ qspecl_then [‘delete fds (implode h)’] assume_tac >> gvs [delete_thm])
  >- (pop_assum $ qspecl_then [‘delete fds (implode h)’] assume_tac >> gvs [delete_thm])
  >- (pop_assum $ qspecl_then [‘delete fds (implode h)’] assume_tac >> gvs [delete_thm] >>
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

Theorem update_ctxt_soundness:
  ∀l e e' n1 n2 c fds fd.
    EVERY (λv. ∀d. (v, d) ∉ fds) (MAP SND l)
    ∧ find e (update_ctxt n1 n2 c l) fds {} e' fd
    ⇒ find (lets_for n1 n2 l e) c fds {} (lets_for n1 n2 l e') NONE
Proof
  Induct
  \\ gvs [lets_for_def, update_ctxt_def]
  >- (rw [] \\ irule find_Drop_fd \\ pop_assum $ irule_at Any)
  \\ Cases
  \\ rw [lets_for_def, update_ctxt_def]
  \\ irule find_Let
  \\ fs [dest_fd_SND_def]
  \\ irule_at Any find_Bottom
  \\ irule_at Any find_Drop_fd
  \\ last_x_assum $ irule_at Any \\ pop_assum $ irule_at Any
  \\ gvs []
QED

Theorem find_rows_of:
  ∀l l' c s fds fd.
    LIST_REL (λ(a1, b1, e1) (a2, b2, e2).
                a1 = a2 ∧ b1 = b2
                ∧ find e1 (update_ctxt a1 s c (MAPi (λi v. (i, v)) b1)) {} {} e2 fd) l l'
         ⇒ find (rows_of s l) c fds {} (rows_of s l') NONE
Proof
  Induct
  \\ fs [rows_of_def, find_Bottom]
  \\ PairCases
  \\ rw []
  \\ rename1 ‘find _ _ _ _ (rows_of _ (y::ys))’
  \\ PairCases_on ‘y’
  \\ fs [rows_of_def]
  \\ irule find_Subset
  \\ irule_at Any find_If \\ rw []
  \\ rpt $ last_x_assum $ irule_at Any
  \\ irule_at Any find_Bottom
  \\ irule_at Any update_ctxt_soundness
  \\ pop_assum $ irule_at Any \\ fs []
QED

Theorem find_subset_aid:
  ∀d ps v. (ps, v) ∈ d ⇒ ∃ps'. (ps ++ ps', v) ∈ d
Proof
  rw [] >> qexists_tac ‘[]’ >> gvs []
QED

Theorem handle_Apps_demands_soundness:
  ∀bL argl bL' fds c m eL a.
    handle_Apps_demands a bL (MAP (λe. demands_analysis_fun c e fds) argl) = (bL', eL, m)
    ∧ EVERY (λ(dm, _, _). map_ok dm ∧ cmp_of dm = compare) (MAP (λe. demands_analysis_fun c e fds) argl)
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
               (ps, EL i vL) ∈ demands_map_to_set m ∧
               d ∈ demands_map_to_set (EL i mL)
Proof
  Induct >> gvs [handle_multi_bind_def] >>
  gen_tac >> Cases >> gvs [handle_multi_bind_def] >> rw []
  >- (last_x_assum $ drule_then assume_tac >> gvs [] >>
      disj2_tac >> rename1 ‘(ps, EL i _) ∈ _’ >>
      qexists_tac ‘ps’ >> qexists_tac ‘SUC i’ >> gvs []) >>
  drule_then assume_tac map_handle_multi_ok >> gvs [demands_map_union]
  >- (disj2_tac >>
      rename1 ‘d ∈ demands_map_to_set _’ >> PairCases_on ‘d’ >>
      rename1 ‘(ps, _) ∈ demands_map_to_set _’ >>
      qexists_tac ‘ps’ >> qexists_tac ‘0’ >>
      gvs [demands_map_to_set_def, lookup_thm, FLOOKUP_DEF] >>
      irule_at Any $ GSYM explode_implode >> gvs []) >>
  last_x_assum $ drule_then assume_tac >> gvs [] >>
  disj2_tac >> rename1 ‘(ps, EL i _) ∈ _’ >>
  qexists_tac ‘ps’ >> qexists_tac ‘SUC i’ >> gvs []
QED

Theorem demands_map_in_FDOM:
  ∀vname m. implode vname ∈ FDOM (to_fmap m) ⇒ ([], vname) ∈ demands_map_to_set m
Proof
  rw [demands_map_to_set_def] >>
  pop_assum $ irule_at Any >> gvs [explode_implode]
QED

Theorem boolList_of_fdemands_soundness:
  ∀vL m d. map_ok m
              ⇒ FST (boolList_of_fdemands m vL) = FST (demands_boolList (demands_map_to_set m) vL)
                ∧ map_ok (SND (boolList_of_fdemands m vL))
                ∧ SND (demands_boolList (demands_map_to_set m) vL)
                  = IMAGE explode (FDOM (to_fmap (SND (boolList_of_fdemands m vL))))
Proof
  Induct >> gvs [boolList_of_fdemands_def, demands_boolList_def, empty_thm, TotOrd_compare] >>
  rw [] >>
  rename1 ‘boolList_of_fdemands m vL’ >> qabbrev_tac ‘fd = boolList_of_fdemands m vL’ >> PairCases_on ‘fd’ >>
  rename1 ‘demands_boolList (_ m) vL’ >>
  qabbrev_tac ‘dsBL = demands_boolList (demands_map_to_set m) vL’ >> PairCases_on ‘dsBL’ >>
  fs [] >> last_x_assum $ drule_then assume_tac >> gvs [insert_thm] >>
  once_rewrite_tac [INSERT_SING_UNION, UNION_COMM] >> gvs [lookup_thm, FLOOKUP_DEF] >>
  eq_tac >> rw [demands_map_to_set_def] >>
  gvs [implode_explode] >>
  first_x_assum $ irule_at Any >> gvs [explode_implode]
QED

Theorem demands_analysis_soundness_lemma:
  ∀(f: α -> num) (e: α cexp) c fds m e' fd.
    demands_analysis_fun c e fds = (m, e', fd) ∧ map_ok fds ∧ cmp_of fds = compare
    ⇒ find (exp_of e) (ctxt_trans c) (fdemands_map_to_set fds)
         (demands_map_to_set m) (exp_of e') (fd_to_set fd) ∧
      map_ok m ∧ cmp_of m = compare ∧
      (∀bL fd_map. SOME (bL, fd_map) = fd ⇒ map_ok fd_map ∧ cmp_of fd_map = compare)
Proof
  gen_tac
  \\ completeInduct_on ‘cexp_size f e’
  \\ gen_tac
  \\ Cases
  \\ rename1 ‘Size = cexp_size _ _’
  \\ strip_tac
  \\ simp [demands_analysis_fun_def, exp_of_def]
  \\ gvs [demands_map_empty, demands_map_insert, demands_map_union,
         TotOrd_compare, insert_thm, empty_thm]
  >~[‘Var a n’]
  >- (rw [] \\ rename1 ‘lookup fds (implode n)’
      \\ Cases_on ‘lookup fds (implode n)’
      \\ gvs [find_Var, fd_to_set_def, demands_map_empty,
              find_Var2, fdemands_map_to_set_soundness, empty_thm, TotOrd_compare])
  >~[‘Prim a op l’]
  >- (Cases_on ‘op’
      >~[‘Prim a Seq l’]
      >- (Cases_on ‘l’ >~[‘Prim a Seq []’]
          \\ gvs [demands_analysis_fun_def, op_of_def, fd_to_set_def, demands_map_empty,
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
          \\ Cases_on ‘t’ >~ [‘Prim a Seq (e1::e2::e3::t)’]
          >- (rw [demands_analysis_fun_def, empty_thm, fd_to_set_def, demands_map_empty,
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
          \\ dxrule_then (dxrule_then irule) find_Seq2)
      >~ [‘AtomOp op’]
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
              \\ ‘cexp_size f (EL i l) < cexp6_size f l’
                   by metis_tac [cexp_size_lemma, EL_MEM]
              \\ fs [cexp_size_def]
              \\ pop_assum kall_tac
              \\ pop_assum $ qspecl_then [‘f’, ‘EL i l’] assume_tac
              \\ fs []
              \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
              \\ qabbrev_tac ‘p = demands_analysis_fun c (EL i l) fds’
              \\ PairCases_on ‘p’
              \\ gvs [EL_MAP])
          \\ assume_tac TotOrd_compare
          \\ dxrule_then (drule_then assume_tac) demands_map_FOLDL
          \\ pop_assum $ qspecl_then [‘empty compare’] assume_tac
          \\ gvs [TotOrd_compare, empty_thm, demands_map_empty, EVERY_CONJ, fd_to_set_def]
          \\ irule find_Atom \\ fs [] \\ qexists_tac ‘NONE’
          \\ rw [LIST_REL_EL_EQN, EL_ZIP, EL_MAP]
          \\ rename1 ‘EL n l’
          \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n l)’] assume_tac
          \\ ‘cexp_size f (EL n l) < cexp6_size f l’
            by metis_tac [cexp_size_lemma, EL_MEM]
          \\ fs [cexp_size_def]
          \\ pop_assum kall_tac
          \\ pop_assum $ qspecl_then [‘f’, ‘EL n l’] assume_tac
          \\ fs []
          \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
          \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n l) fds’
          \\ PairCases_on ‘p’ \\ gvs []
          \\ dxrule_then assume_tac find_Drop_fd \\ fs [])
      \\ rw [] (* Cons s *)
      \\ fs [empty_thm, TotOrd_compare, demands_analysis_fun_def, demands_map_empty]
      \\ rw [exp_of_def, op_of_def, fd_to_set_def]
      \\ irule_at Any find_Prim \\ rw []
      \\ rename1 ‘k < LENGTH l’
      \\ first_x_assum $ qspecl_then [‘cexp_size f (EL k l)’] assume_tac
      \\ ‘cexp_size f (EL k l) < cexp6_size f l’
        by metis_tac [cexp_size_lemma, MEM_EL]
      \\ fs [cexp_size_def]
      \\ pop_assum kall_tac
      \\ rename1 ‘demands_analysis_fun c _ fds’
      \\ pop_assum $ qspecl_then [‘f’, ‘EL k l’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
      \\ qabbrev_tac ‘p = demands_analysis_fun c (EL k l) fds’
      \\ PairCases_on ‘p’
      \\ fs [EL_MAP]
      \\ irule_at Any add_all_demands_soundness
      \\ gvs [cmp_of_def, TotOrd_compare]
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
      \\ Cases_on ‘fd_fe’ \\ gvs [fd_to_set_def, exp_of_def]
      >- (irule find_Apps \\ first_x_assum $ irule_at Any
          \\ rw [LIST_REL_EL_EQN, EL_MAP]
          \\ rename1 ‘EL n argl’
          \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n argl)’] assume_tac
          \\ ‘cexp_size f (EL n argl) < cexp6_size f argl’ by metis_tac [cexp_size_lemma, MEM_EL]
          \\ fs [cexp_size_def]
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
      \\ ‘EVERY (λ(dm, _, _). map_ok dm ∧ cmp_of dm = compare) (MAP (λe. demands_analysis_fun c e fds) argl)’
        by (rw [EVERY_EL, EL_MAP] \\ rename1 ‘EL n argl’
            \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n argl)’] assume_tac
            \\ ‘cexp_size f (EL n argl) < cexp6_size f argl’ by metis_tac [cexp_size_lemma, MEM_EL]
            \\ fs [cexp_size_def]
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
              \\ ‘cexp_size f (EL n (argl1 ++ argl2)) < cexp6_size f (argl1 ++ argl2)’
                by (assume_tac cexp_size_lemma >> gvs [] >> first_x_assum irule >>
                    irule EL_MEM >> fs [])
              \\ fs [cexp_size_def]
              \\ pop_assum kall_tac
              \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl1’] assume_tac
              \\ gvs [EL_APPEND_EQN]
              \\ pop_assum $ qspecl_then [‘c’] assume_tac
              \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl1) fds’
              \\ PairCases_on ‘p’ \\ fs []
              \\ first_x_assum $ drule_then assume_tac
              \\ FULL_CASE_TAC \\ gvs []
              >- first_assum $ irule_at Any
              >- (irule_at Any add_all_demands_soundness
                  \\ first_assum $ irule_at Any
                  \\ gvs [TotOrd_compare]))
          >- (gvs [EL_MAP] \\ rename1 ‘n < LENGTH _’
              \\ first_x_assum $ qspecl_then [‘n + LENGTH argl1’] assume_tac \\ gvs [EL_APPEND_EQN]
              \\ last_x_assum $ qspecl_then [‘cexp_size f (EL (n + LENGTH argl1) (argl1 ++ argl2))’] assume_tac
              \\ ‘cexp_size f (EL (n + LENGTH argl1) (argl1 ++ argl2)) < cexp6_size f (argl1 ++ argl2)’
                by (assume_tac cexp_size_lemma >> gvs [] >> first_x_assum irule >>
                    irule EL_MEM >> fs [])
              \\ fs [cexp_size_def]
              \\ pop_assum kall_tac
              \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl2’] assume_tac
              \\ gvs [EL_APPEND_EQN]
              \\ pop_assum $ qspecl_then [‘c’] assume_tac
              \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl2) fds’
              \\ PairCases_on ‘p’ \\ fs []
              \\ first_x_assum $ drule_then assume_tac
              \\ irule_at Any add_all_demands_soundness
              \\ gvs [TotOrd_compare]
              \\ first_x_assum $ irule_at Any))
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
      \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n argl)’] assume_tac
      \\ ‘cexp_size f (EL n argl) < cexp6_size f argl’ by metis_tac [cexp_size_lemma, MEM_EL]
      \\ fs [cexp_size_def]
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
                                               (FOLDL (λf k. delete f (implode k)) fds namel)’
      \\ PairCases_on ‘p’ \\ fs [empty_thm, TotOrd_compare]
      \\ first_x_assum $ drule_then assume_tac
      \\ gvs [exp_of_def, fd_to_set_def, demands_map_empty, ctxt_trans_def,
              FOLDL_delete_ok, boolList_of_fdemands_soundness]
      \\ irule find_Subset
      \\ irule_at Any find_Lams_fd
      \\ irule_at Any find_Drop_fd
      \\ first_x_assum $ irule_at $ Pos hd
      \\ gvs [fdemands_map_FOLDL_delete_subset, boolList_of_fdemands_def, EVERY_MEM,
              fdemands_map_FOLDL_delete])
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
                                                   | NONE => delete fds (implode vname)
                                                   | SOME (bL, _) => insert fds (implode vname) bL)’
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
          \\ gvs [lookup_thm, demands_map_delete, FLOOKUP_DEF, dest_fd_SND_def, demands_map_to_set_def]
          \\ rw [] \\ gvs [implode_explode, delete_thm]
          \\ dxrule_then assume_tac fdemands_map_insert \\ gvs [])
      >- (FULL_CASE_TAC \\ gvs [insert_thm, fd_to_set_def, delete_thm]
          \\ irule_at Any find_Let
          \\ first_x_assum $ irule_at (Pos hd)
          \\ irule_at Any find_smaller_fd \\ first_x_assum $ irule_at Any
          \\ gvs [lookup_thm, demands_map_delete_subset, dest_fd_SND_def, demands_map_to_set_def, FLOOKUP_DEF]
          \\ rw [] \\ gvs [implode_explode, delete_thm]
          \\ dxrule_then assume_tac fdemands_map_insert \\ gvs [])
      \\ irule_at Any find_Let2 \\ irule_at Any find_Seq
      >- (first_x_assum $ irule_at Any \\ first_x_assum $ irule_at Any
          \\ rpt $ irule_at Any demands_map_in_FDOM
          \\ gvs [dest_fd_SND_def, FLOOKUP_DEF]
          \\ rename1 ‘demands_map_to_set (delete p10 (implode vname))’
          \\ qexists_tac ‘demands_map_to_set (delete p10 (implode vname))’
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
          \\ rename1 ‘demands_map_to_set (delete p10 (implode vname))’
          \\ qexists_tac ‘demands_map_to_set (delete p10 (implode vname))’
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
          \\ rename1 ‘demands_map_to_set (delete p10 (implode vname))’
          \\ qexists_tac ‘demands_map_to_set (delete p10 (implode vname))’
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
          \\ rename1 ‘demands_map_to_set (delete p10 (implode vname))’
          \\ qexists_tac ‘demands_map_to_set (delete p10 (implode vname))’
          \\ rw [find_subset_aid]
          >- (dxrule_then (dxrule_then assume_tac) demands_map_delete_soundness
              \\ gvs [])
          \\ dxrule_then assume_tac fdemands_map_insert
          \\ gvs []))
  >~ [‘Letrec a binds exp’]
  >- (rpt gen_tac
      \\ IF_CASES_TAC
      >- (dxrule_then assume_tac compute_ALL_DISTINCT_soundness \\ gvs [UNZIP3_MAP]
          \\ qabbrev_tac ‘outL = MAP (λ(v, e). demands_analysis_fun Nil e (empty compare)) binds’
          \\ rename1 ‘demands_analysis_fun (RecBind binds c) _ (handle_Letrec_fdemands fds _ _)’
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
          \\ qexists_tac ‘fdemands_map_to_set (FOLDL (λf k. delete f (implode k)) fds (MAP FST binds))’
          \\ irule_at Any find_Letrec
          \\ irule_at Any adds_demands_soundness
          \\ qspecl_then [‘MAP FST binds’, ‘MAP (SND o SND) outL’, ‘fds’] assume_tac handle_Letrec_fdemands_soundness
          \\ rpt $ FULL_CASE_TAC \\ unabbrev_all_tac
          \\ gvs [EL_MAP, EL_ZIP, MAP_MAP_o, LAMBDA_PROD, combinTheory.o_DEF, ALL_DISTINCT_FST_MAP, EVERY_EL,
                  fdemands_map_FOLDL_delete_subset, FOLDL_delete_ok, fd_to_set_def, dest_fd_SND_def]
          \\ TRY $ irule_at Any find_smaller_fd
          \\ first_x_assum $ irule_at $ Pos hd
          \\ gvs [demands_map_FOLDL_delete_subset]
          \\ ‘EVERY (λm. map_ok m ∧ cmp_of m = compare)
              (MAP (λ(p1, p2). FST (demands_analysis_fun Nil p2 (empty compare))) binds)’
            by (rw [EVERY_EL] \\ rename1 ‘EL i _’
                \\ last_x_assum $ qspecl_then [‘cexp_size f (SND (EL i binds))’] assume_tac
                \\ ‘cexp_size f (SND (EL i binds)) < cexp4_size f binds’
                  by (assume_tac cexp_size_lemma \\ gvs [] \\ first_x_assum irule
                      \\ gvs [MEM_EL] \\ first_assum $ irule_at Any
                      \\ irule_at Any $ PAIR)
                \\ gvs [] \\ pop_assum kall_tac
                \\ pop_assum $ qspecl_then [‘f’, ‘SND (EL i binds)’] assume_tac \\ gvs []
                \\ qabbrev_tac ‘p = demands_analysis_fun Nil (SND (EL i binds)) (empty compare)’
                \\ PairCases_on ‘p’ \\ fs [] \\ first_x_assum $ drule_then assume_tac
                \\ gvs [empty_thm, TotOrd_compare, EL_MAP]
                \\ qabbrev_tac ‘expr = EL i binds’ \\ PairCases_on ‘expr’ \\ gvs [])
          \\ rpt $ irule_at Any $ GSYM LENGTH_MAP
          \\ qexists_tac ‘λ(v, e). demands_map_to_set (FST (demands_analysis_fun Nil e (empty compare)))’
          \\ qexists_tac ‘λ(v, e). fd_to_set (SND (SND (demands_analysis_fun Nil e (empty compare))))’
          \\ rename1 ‘demands_analysis_fun _ _ _ = (e0, _, _)’
          \\ qexists_tac ‘demands_map_to_set (FOLDL (λf k. delete f (implode k))
                (handle_multi_bind e0 (MAP (λ(p1, p2). FST (demands_analysis_fun Nil p2 (empty compare))) binds)
                 (MAP FST binds)) (MAP FST binds))’
          \\ rw [EL_MAP]
                >>~[‘_ ∉ fdemands_map_to_set _’]
          >- (irule fdemands_map_FOLDL_delete \\ gvs [MEM_EL]
              \\ first_assum $ irule_at Any \\ gvs [EL_MAP]
              \\ rename1 ‘_ = FST p’ \\ PairCases_on ‘p’ \\ gvs [])
          >-  (irule fdemands_map_FOLDL_delete \\ gvs [MEM_EL]
               \\ first_assum $ irule_at Any \\ gvs [EL_MAP]
               \\ rename1 ‘_ = FST p’ \\ PairCases_on ‘p’ \\ gvs [])
              >>~[‘FST p = FST _’]
          >- (PairCases_on ‘p’ \\ gvs [])
          >- (PairCases_on ‘p’ \\ gvs [])
          >~[‘_ ∉ demands_map_to_set _’]
          >- (irule demands_map_FOLDL_delete \\ gvs [MEM_EL]
              \\ first_assum $ irule_at Any \\ gvs [EL_MAP]
              \\ rename1 ‘_ = FST p’ \\ PairCases_on ‘p’ \\ gvs [])
             >>~[‘¬MEM _ _’]
          >- (dxrule_then assume_tac demands_map_FOLDL_delete_soundness
              \\ gvs [map_handle_multi_ok] \\ strip_tac \\ first_x_assum irule
              \\ gvs [MEM_MAP] \\ first_x_assum $ irule_at Any
              \\ rename1 ‘_ = FST p’ \\ PairCases_on ‘p’ \\ gvs [])
          >- (dxrule_then assume_tac demands_map_FOLDL_delete_soundness
              \\ gvs [map_handle_multi_ok] \\ strip_tac \\ first_x_assum irule
              \\ gvs [MEM_MAP] \\ first_x_assum $ irule_at Any
              \\ rename1 ‘_ = FST p’ \\ PairCases_on ‘p’ \\ gvs [])
             >>~[‘(_ ++ _, _) ∈ demands_map_to_set _’]
          >- (qexists_tac ‘[]’ \\ gvs [])
          >- (qexists_tac ‘[]’ \\ gvs [])
             >>~[‘_ ∈ demands_map_to_set _’]
          >- (dxrule_then assume_tac demands_map_FOLDL_delete_soundness \\ gvs [map_handle_multi_ok]
              \\ dxrule_then assume_tac handle_multi_in \\ gvs []
              \\ disj2_tac \\ rename1 ‘(ps2, EL i _) ∈ _’
              \\ qexists_tac ‘ps2’ \\ qexists_tac ‘i’
              \\ gvs [EL_MAP]
              \\ qabbrev_tac ‘pair = EL i binds’ \\ PairCases_on ‘pair’ \\ gvs [])
          >- (dxrule_then assume_tac demands_map_FOLDL_delete_soundness \\ gvs [map_handle_multi_ok]
              \\ dxrule_then assume_tac handle_multi_in \\ gvs []
              \\ disj2_tac \\ rename1 ‘(ps2, EL i _) ∈ _’
              \\ qexists_tac ‘ps2’ \\ qexists_tac ‘i’
              \\ gvs [EL_MAP]
              \\ qabbrev_tac ‘pair = EL i binds’ \\ PairCases_on ‘pair’ \\ gvs [])
          \\ gvs [FOLDL_delete_ok, map_handle_multi_ok]
                 >>~[‘find _ Nil {}’]
          >- (rename1 ‘EL i _’
              \\ last_x_assum $ qspecl_then [‘cexp_size f (SND (EL i binds))’] assume_tac
              \\ ‘cexp_size f (SND (EL i binds)) < cexp4_size f binds’
                by (assume_tac cexp_size_lemma \\ gvs [] \\ first_x_assum irule
                    \\ gvs [MEM_EL] \\ first_assum $ irule_at Any
                    \\ irule_at Any $ PAIR)
              \\ gvs [] \\ pop_assum kall_tac
              \\ pop_assum $ qspecl_then [‘f’, ‘SND (EL i binds)’] assume_tac \\ gvs []
              \\ qabbrev_tac ‘p = demands_analysis_fun Nil (SND (EL i binds)) (empty compare)’
              \\ PairCases_on ‘p’ \\ fs [] \\ first_x_assum $ drule_then assume_tac
              \\ gvs [empty_thm, TotOrd_compare]
              \\ qabbrev_tac ‘expr = EL i binds’ \\ PairCases_on ‘expr’
              \\ gvs [fdemands_map_to_set_def, empty_thm, ctxt_trans_def])
          >- (rename1 ‘EL i _’
              \\ last_x_assum $ qspecl_then [‘cexp_size f (SND (EL i binds))’] assume_tac
              \\ ‘cexp_size f (SND (EL i binds)) < cexp4_size f binds’
                by (assume_tac cexp_size_lemma \\ gvs [] \\ first_x_assum irule
                    \\ gvs [MEM_EL] \\ first_assum $ irule_at Any
                    \\ irule_at Any $ PAIR)
              \\ gvs [] \\ pop_assum kall_tac
              \\ pop_assum $ qspecl_then [‘f’, ‘SND (EL i binds)’] assume_tac \\ gvs []
              \\ qabbrev_tac ‘p = demands_analysis_fun Nil (SND (EL i binds)) (empty compare)’
              \\ PairCases_on ‘p’ \\ fs [] \\ first_x_assum $ drule_then assume_tac
              \\ gvs [empty_thm, TotOrd_compare]
              \\ qabbrev_tac ‘expr = EL i binds’ \\ PairCases_on ‘expr’
              \\ gvs [fdemands_map_to_set_def, empty_thm, ctxt_trans_def])
          \\ first_x_assum $ dxrule_then assume_tac \\ gvs []
          \\ disj2_tac \\ first_assum $ irule_at Any
          \\ gvs [EL_MAP] \\ rename1 ‘EL i _’
          \\ qabbrev_tac ‘p = EL i binds’ \\ PairCases_on ‘p’ \\ gvs [fd_to_set_def])
      \\ rw [empty_thm, TotOrd_compare, fd_to_set_def, demands_map_empty]
      \\ gvs [exp_of_def, find_Bottom])
  >~ [‘Case a case_exp s l’]
  >- (gen_tac \\ gen_tac
      \\ rename1 ‘Bind _ _ c’
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
      \\ rename1 ‘Let s _ _’
      \\ irule find_Let
      \\ first_x_assum $ irule_at Any
      \\ irule_at Any find_rows_of
      \\ qexists_tac ‘{}’ \\ qexists_tac ‘NONE’
      \\ rw [LIST_REL_EL_EQN, EL_MAP, dest_fd_SND_def]
      \\ rename1 ‘EL n l’
      \\ qabbrev_tac ‘e = EL n l’
      \\ PairCases_on ‘e’
      \\ fs []
      \\ irule find_Subset
      \\ rename1 ‘demands_analysis_fun (Unfold names s args (Bind s case_exp c)) e'’
      \\ qabbrev_tac ‘p = demands_analysis_fun (Unfold names s args (Bind s case_exp c)) e' (empty compare)’
      \\ PairCases_on ‘p’
      \\ irule_at Any adds_demands_soundness
      \\ first_x_assum $ qspecl_then [‘cexp_size f e'’] assume_tac
      \\ ‘cexp_size f e' < cexp1_size f l’ by metis_tac [cexp_size_lemma, EL_MEM]
      \\ fs []
      \\ pop_assum kall_tac
      \\ pop_assum $ qspecl_then [‘f’, ‘e' ’] assume_tac
      \\ fs [] \\ pop_assum $ dxrule_then assume_tac
      \\ irule_at Any find_Drop_fd
      \\ fs [ctxt_trans_def, TotOrd_compare, fdemands_map_to_set_def, empty_thm]
      \\ last_x_assum $ irule_at Any)
QED

Theorem demands_analysis_fun_soundness:
  ∀(e : α cexp). exp_of e ≈ exp_of (FST (SND (demands_analysis_fun Nil e (empty compare))))
Proof
  rpt gen_tac
  \\ qspecl_then [‘(K 0) : α -> num’, ‘e’, ‘Nil’, ‘empty compare’]
                 assume_tac demands_analysis_soundness_lemma
  \\ qabbrev_tac ‘e' = demands_analysis_fun Nil e (empty compare)’
  \\ PairCases_on ‘e'’
  \\ gvs [fdemands_map_to_set_def, empty_thm, ctxt_trans_def, TotOrd_compare]
  \\ drule find_soundness \\ fs []
QED


val _ = export_theory();
