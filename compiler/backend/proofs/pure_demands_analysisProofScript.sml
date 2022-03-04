(*
   Proof of the demands analysis handler
*)

open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory dep_rewrite
     optionTheory pairTheory ltreeTheory llistTheory bagTheory mlmapTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory
     finite_mapTheory mlstringTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_miscTheory pure_exp_relTheory pure_congruenceTheory
     pure_cexpTheory pure_demandTheory;

val _ = new_theory "pure_demands_analysisProof";

Datatype:
  da_ctxt =
      | Nil
      | IsFree (vname list) da_ctxt
      | Bind vname (α cexp) da_ctxt da_ctxt
      | RecBind ((vname # (α cexp)) list) da_ctxt da_ctxt
      | Unfold vname vname (vname list) da_ctxt
End

Definition adds_demands_def:
  (adds_demands a0 (m, e) [] = e) ∧
  (adds_demands a0 (m, e) (name::tl) =
     case lookup m (implode name) of
       | SOME () => Prim a0 Seq [Var a0 name; adds_demands a0 (m, e) tl]
       | _ => adds_demands a0 (m, e) tl)
End

Definition demands_analysis_fun_def:
  (demands_analysis_fun c ((Var a0 a1): 'a cexp) =
    (mlmap$insert (mlmap$empty mlstring$compare) (implode a1) (), (Var a0 a1 : 'a cexp))) ∧
  (demands_analysis_fun c (App a0 f argl) =
     let (m1, f') = demands_analysis_fun c f in
       let e' = MAP SND ((MAP (demands_analysis_fun c)) argl) in
         (m1, App a0 f' e')) ∧
  (demands_analysis_fun c (Lam a0 vl e) =
     let (m, e') = demands_analysis_fun (IsFree vl c) e in
       (empty compare, Lam a0 vl (adds_demands a0 (m, e') vl))) ∧
  (demands_analysis_fun c (Let a0 name e1 e2) =
     let (m1, e1') = demands_analysis_fun c e1 in
       let (m2, e2') = demands_analysis_fun (Bind name e1 c c) e2 in
         (empty compare, Let a0 name e1' e2')) ∧
  (demands_analysis_fun c (Prim a0 Seq [e1; e2]) =
     let (m1, e1') = demands_analysis_fun c e1 in
       let (m2, e2') = demands_analysis_fun c e2 in
         (union m1 m2, Prim a0 Seq [e1'; e2'])) ∧
  (demands_analysis_fun c (Prim a0 Seq _) =
   (empty compare, Prim a0 Seq [])) ∧
  (demands_analysis_fun c (Prim a0 (AtomOp op) el) =
     let outL = MAP (demands_analysis_fun c) el in
       let (mL, el') = UNZIP outL in
         let m = FOLDL union (empty compare) mL in
           (m, Prim a0 (AtomOp op) el')) ∧
  (demands_analysis_fun c (Prim a0 (Cons s) el) =
     let el = MAP (λe. SND (demands_analysis_fun c e)) el in
       (empty compare, Prim a0 (Cons s) el)) ∧
  (demands_analysis_fun c (Letrec a0 binds e) =
     let (m, e') = demands_analysis_fun (RecBind binds c c) e in
       (empty compare, Letrec a0 binds e')) ∧
  (demands_analysis_fun c (Case a0 e n cases) =
   if MEM n (FLAT (MAP (FST o SND) cases))
   then
     (empty compare, Case a0 e n cases)
   else
     let (m, e') = demands_analysis_fun c e in
       let cases' = MAP (λ(name,args,ce). (name, args,
                                           adds_demands a0 (demands_analysis_fun
                                                (Unfold name n args (Bind n e c c)) ce) args)) cases in
             (empty compare, Case a0 e' n cases'))
Termination
  WF_REL_TAC ‘measure $ (cexp_size (K 0)) o SND’ \\ rw []
  \\ imp_res_tac cexp_size_lemma
  \\ fs []
End

Definition update_ctxt_def:
  (update_ctxt id n c [] = c) ∧
  (update_ctxt id n c ((i,p)::tl) =
   update_ctxt id n (Bind p (Proj id i (Var n)) c c) tl)
End

Definition ctxt_trans_def:
  ctxt_trans (Nil: α da_ctxt) = Nil ∧
  ctxt_trans (IsFree l ctxt) = FOLDL (λc n. IsFree n (c:ctxt)) (ctxt_trans ctxt) l ∧
  ctxt_trans (Bind n e c1 c2) = Bind n (exp_of e) (ctxt_trans c1) (ctxt_trans c2) ∧
  ctxt_trans ((RecBind (binds: (vname # α cexp) list) c1 c2): α da_ctxt) = (RecBind (MAP (λ(n,e). (n, exp_of e)) binds) (ctxt_trans c1) : ctxt) ∧
  ctxt_trans (Unfold id n names c) = update_ctxt id n (ctxt_trans c) (MAPi (λi v. (i, v)) names)
End

Theorem adds_demands_soundness:
  ∀vl e e' m ds c ds a. map_ok m ∧ find (exp_of e) c (IMAGE (λx. ([],explode x)) (FDOM (to_fmap m))) (exp_of e')
                      ⇒ find (exp_of e) c (IMAGE (λx. ([],explode x)) (FDOM (to_fmap m)))
                             (exp_of (adds_demands a (m, e') vl))
Proof
  Induct
  \\ rw [adds_demands_def]
  \\ rename1 ‘lookup m (implode h)’
  \\ Cases_on ‘lookup m (implode h)’
  \\ fs []
  \\ rw [exp_of_def, op_of_def]
  \\ irule find_Seq
  \\ first_x_assum $ irule_at Any
  \\ qexists_tac ‘[]’
  \\ gvs [lookup_thm, FLOOKUP_DEF]
  \\ pop_assum $ irule_at Any
  \\ fs [explode_implode]
QED

(*
Theorem test:
  exp_of (Prim 0 Seq [x; y; z]) ≅ exp_of (Prim 0 Seq [])
Proof
  rw [exp_of_def, op_of_def]
  \\ irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_def, eval_wh_to_def]
QED
*)

Theorem FOLDL_union_map_ok:
  ∀l cmp m. TotOrd cmp ∧ EVERY (λm. map_ok m ∧ cmp_of m = cmp) l ∧ map_ok m ∧ cmp_of m = cmp ⇒
          map_ok (FOLDL union m l)
Proof
  Induct
  \\ fs [empty_thm]
  \\ rw [union_thm]
QED

Theorem FOLDL_union_cmp_of:
  ∀l cmp m. TotOrd cmp ∧ EVERY (λm. cmp_of m = cmp ∧ map_ok m) l ∧ map_ok m ∧ cmp_of m = cmp ⇒
          cmp_of (FOLDL union m l) = cmp
Proof
  Induct
  \\ fs [empty_thm]
  \\ rw [union_thm]
QED

Theorem FOLDL_union_lookup:
  ∀l cmp m v. TotOrd cmp ∧ EVERY (λm. cmp_of m = cmp ∧ map_ok m) l ∧ map_ok m ∧ cmp_of m = cmp ⇒
            (lookup (FOLDL union m l) v = SOME () ⇔ lookup m v = SOME () ∨ ∃m2. MEM m2 l ∧ lookup m2 v = SOME ())
Proof
  Induct
  \\ fs [empty_thm]
  \\ rw [union_thm, lookup_thm, FLOOKUP_FUNION]
  \\ eq_tac
  \\ rw []
  \\ Cases_on ‘FLOOKUP (to_fmap m) v’
  \\ fs []
  >- (rename1 ‘_ = h’
      \\ qexists_tac ‘h’
      \\ rw [lookup_thm])
  >- (first_x_assum $ irule_at Any
      \\ fs [])
  >- gvs [lookup_thm]
  >- metis_tac []
QED

Theorem set_FOLDL_union:
  ∀l m cmp f.  map_ok m ∧ cmp_of m = cmp ∧ TotOrd cmp ∧
                     EVERY (λm. cmp_of m = cmp ∧ map_ok m) l ⇒
                       IMAGE f ((FDOM o to_fmap) (FOLDL union m l))
                       = IMAGE f ((FDOM o to_fmap) m)
                               ∪ BIGUNION (set (MAP ((IMAGE f) o FDOM o to_fmap) l))
Proof
  Induct
  \\ fs []
  \\ rw []
  \\ rename1 ‘union m hd’
  \\ first_x_assum $ qspecl_then [‘union m hd’, ‘f’] assume_tac
  \\ gvs [union_thm]
  \\ fs [UNION_ASSOC]
QED

Theorem map_does_not_changes:
  ∀l (f: α -> β -> γ -> γ). MAP (FST o SND) l = MAP (FST o SND o (λ(a, b, c). (a, b, f a b c))) l
Proof
  Induct
  \\ fs []
  \\ PairCases
  \\ fs []
QED

Theorem update_ctxt_soundness:
  ∀l e e' n1 n2 c. find e (update_ctxt n1 n2 c l) {} e' ⇒ find (lets_for n1 n2 l e) c {} (lets_for n1 n2 l e')
Proof
  Induct
  \\ fs [lets_for_def, update_ctxt_def]
  \\ Cases
  \\ rw [lets_for_def, update_ctxt_def]
  \\ irule find_Let
  \\ fs []
  \\ irule_at Any find_Bottom
QED

Theorem find_rows_of:
  ∀l l' c s. LIST_REL (λ(a1, b1, e1) (a2, b2, e2). a1 = a2 ∧ b1 = b2 ∧ find e1 (update_ctxt a1 s c (MAPi (λi v. (i, v)) b1)) {} e2) l l'
         ⇒ find (rows_of s l) c {} (rows_of s l')
Proof
  Induct
  \\ fs [rows_of_def, find_Bottom]
  \\ PairCases
  \\ rw []
  \\ rename1 ‘y::ys’
  \\ PairCases_on ‘y’
  \\ fs [rows_of_def]
  \\ irule find_Subset
  \\ irule_at Any find_If
  \\ irule_at Any find_Bottom
  \\ first_x_assum $ irule_at Any
  \\ fs []
  \\ irule_at Any update_ctxt_soundness
  \\ rw []
QED

Theorem demands_analysis_soudness_lemma:
  ∀(f: num -> α) (e: α cexp) c m e'.
    demands_analysis_fun c e = (m, e') ⇒
       find (exp_of e) (ctxt_trans c) (IMAGE (λx. ([],explode x)) (FDOM (to_fmap m))) (exp_of e') ∧
            map_ok m ∧ cmp_of m = compare
Proof
  gen_tac
  \\ completeInduct_on ‘cexp_size f e’
  \\ gen_tac
  \\ Cases
  \\ rename1 ‘Size = cexp_size _ _’
  \\ strip_tac
  \\ simp [demands_analysis_fun_def, exp_of_def]
  >~[‘Var a n’]
  >- fs [empty_thm, TotOrd_compare, insert_thm, lookup_insert, lookup_thm, find_Var]
  >~[‘Prim a op l’]
  >- (Cases_on ‘op’
      >~[‘Prim a Seq l’]
      >- (Cases_on ‘l’ >~[‘Prim a Seq []’]
          >- fs [demands_analysis_fun_def, op_of_def, empty_thm,
                 lookup_thm, TotOrd_compare, exp_of_def, find_Bottom]
          \\ rename1 ‘e1::t’
          \\ Cases_on ‘t’ >~[‘Prim a Seq [e]’]
          >- fs [demands_analysis_fun_def, empty_thm, lookup_thm, TotOrd_compare, exp_of_def,
                 op_of_def, find_Eq, eval_wh_IMP_exp_eq, eval_wh_def, eval_wh_to_def, subst_def]
          \\ rename1 ‘e1::e2::t’
          \\ Cases_on ‘t’ >~ [‘Prim a Seq (e1::e2::e3::t)’]
          >- fs [demands_analysis_fun_def, empty_thm, lookup_thm, TotOrd_compare, exp_of_def, op_of_def,
                  find_Eq, eval_wh_IMP_exp_eq, eval_wh_def, eval_wh_to_def, subst_def]
          \\ rw []
          \\ first_assum   $ qspecl_then [‘cexp_size f e1’] assume_tac
          \\ first_x_assum $ qspecl_then [‘cexp_size f e2’] assume_tac
          \\ fs [cexp_size_def, cexp_size_lemma]
          \\ pop_assum     $ qspecl_then [‘f’, ‘e2’] assume_tac
          \\ first_x_assum $ qspecl_then [‘f’, ‘e1’] assume_tac
          \\ fs [demands_analysis_fun_def]
          \\ rename1 ‘demands_analysis_fun c _’
          \\ pop_assum     $ qspecl_then [‘c’] assume_tac
          \\ first_x_assum $ qspecl_then [‘c’] assume_tac
          \\ qabbrev_tac ‘p1 = demands_analysis_fun c e1’
          \\ qabbrev_tac ‘p2 = demands_analysis_fun c e2’
          \\ PairCases_on ‘p1’
          \\ PairCases_on ‘p2’
          \\ fs []
          \\ rw [exp_of_def, op_of_def]
          \\ fs [union_thm]
          \\ irule_at Any find_Seq2
          \\ fs [])
      >~ [‘AtomOp op’]
      >- (rw [exp_of_def, op_of_def, demands_analysis_fun_def]
          >- (rw [exp_of_def, op_of_def]
              \\ rename1 ‘demands_analysis_fun c’
              \\ fs [UNZIP_MAP, MAP_MAP_o]
              \\ qspecl_then [‘MAP (FST o (λa. demands_analysis_fun c a)) l’, ‘empty compare’, ‘compare’, ‘λx. ([]: (string # num) list, explode x)’] assume_tac set_FOLDL_union
              \\ gvs [empty_thm, TotOrd_compare]
              \\ ‘EVERY (λm. cmp_of m = compare ∧ map_ok m) (MAP (FST o (λa. demands_analysis_fun c a)) l)’ by
                (pop_assum kall_tac
                 \\ fs [EVERY_EL]
                 \\ rw [EL_MAP]
                 \\ rename1 ‘EL n l’
                 \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n l)’] assume_tac
                 \\ ‘cexp_size f (EL n l) < cexp6_size f l’
                   by metis_tac [cexp_size_lemma, EL_MEM]
                 \\ fs [cexp_size_def]
                 \\ pop_assum kall_tac
                 \\ pop_assum $ qspecl_then [‘f’, ‘EL n l’] assume_tac
                 \\ fs []
                 \\ pop_assum $ qspecl_then [‘c’] assume_tac
                 \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n l)’
                 \\ PairCases_on ‘p’
                 \\ fs [])
              \\ fs []
              \\ rw [exp_of_def, op_of_def]
              \\ irule find_Atom
              \\ gvs [LENGTH_MAP, LIST_REL_EL_EQN]
              \\ rw [EL_ZIP, EL_MAP]
              \\ rename1 ‘EL n l’
              \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n l)’] assume_tac
              \\ ‘cexp_size f (EL n l) < cexp6_size f l’
                 by metis_tac [cexp_size_lemma, EL_MEM]
              \\ fs [cexp_size_def]
              \\ pop_assum kall_tac
              \\ pop_assum $ qspecl_then [‘f’, ‘EL n l’] assume_tac
              \\ fs []
              \\ pop_assum $ qspecl_then [‘c’] assume_tac
              \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n l)’
              \\ PairCases_on ‘p’
              \\ fs [])
          >- (gvs [UNZIP_MAP, MAP_MAP_o]
              \\ irule FOLDL_union_map_ok
              \\ fs [empty_thm, TotOrd_compare, EVERY_EL]
              \\ rw [EL_MAP]
              \\ rename1 ‘demands_analysis_fun c (EL n l)’
              \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n l)’] assume_tac
              \\ ‘cexp_size f (EL n l) < cexp6_size f l’
                 by metis_tac [cexp_size_lemma, EL_MEM]
              \\ fs [cexp_size_def]
              \\ pop_assum kall_tac
              \\ pop_assum $ qspecl_then [‘f’, ‘EL n l’] assume_tac
              \\ fs []
              \\ pop_assum $ qspecl_then [‘c’] assume_tac
              \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n l)’
              \\ PairCases_on ‘p’
              \\ fs [])
          >- (gvs [UNZIP_MAP, MAP_MAP_o]
              \\ irule FOLDL_union_cmp_of
              \\ fs [empty_thm, TotOrd_compare, EVERY_EL]
              \\ rw [MAP_MAP_o, EL_MAP]
              \\ rename1 ‘demands_analysis_fun c (EL n l)’
              \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n l)’] assume_tac
              \\ ‘cexp_size f (EL n l) < cexp6_size f l’
                 by metis_tac [cexp_size_lemma, EL_MEM]
              \\ fs [cexp_size_def]
              \\ pop_assum kall_tac
              \\ pop_assum $ qspecl_then [‘f’, ‘EL n l’] assume_tac
              \\ fs []
              \\ pop_assum $ qspecl_then [‘c’] assume_tac
              \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n l)’
              \\ PairCases_on ‘p’
              \\ fs []))
      \\ rw [] (* Cons s *)
      \\ fs [empty_thm, TotOrd_compare, demands_analysis_fun_def, lookup_thm]
      \\ rw [exp_of_def, op_of_def]
      \\ irule_at Any find_Prim
      \\ fs [empty_thm, TotOrd_compare, lookup_thm]
      \\ rw [EL_MAP]
      \\ rename1 ‘EL k l’
      \\ first_x_assum $ qspecl_then [‘cexp_size f (EL k l)’] assume_tac
      \\ ‘cexp_size f (EL k l) < cexp6_size f l’
        by metis_tac [cexp_size_lemma, MEM_EL]
      \\ fs [cexp_size_def]
      \\ pop_assum kall_tac
      \\ rename1 ‘demands_analysis_fun c _’
      \\ pop_assum $ qspecl_then [‘f’, ‘EL k l’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’] assume_tac
      \\ qabbrev_tac ‘p = demands_analysis_fun c (EL k l)’
      \\ PairCases_on ‘p’
      \\ fs []
      \\ first_x_assum $ irule_at Any)
  >~[‘App a fe argl’]
  >- (rw []
      \\ rename1 ‘demands_analysis_fun c’
      \\ qabbrev_tac ‘p = demands_analysis_fun c fe’
      \\ PairCases_on ‘p’
      \\ fs [demands_analysis_fun_def]
      \\ rw [exp_of_def]
      \\ first_assum $ qspecl_then [‘cexp_size f fe’] assume_tac
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘fe’] assume_tac
      \\ fs []
      \\ pop_assum drule
      \\ rw []
      \\ irule find_Apps
      \\ fs []
      \\ fs [LIST_REL_EL_EQN]
      \\ rw []
      \\ rename1 ‘EL n _’
      \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n argl)’] assume_tac
      \\ ‘cexp_size f (EL n argl) < cexp6_size f argl’ by metis_tac [cexp_size_lemma, MEM_EL]
      \\ fs [cexp_size_def]
      \\ pop_assum kall_tac
      \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’] assume_tac
      \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl)’
      \\ PairCases_on ‘p’
      \\ fs [EL_MAP]
      \\ first_x_assum $ irule_at Any)
  >~ [‘Lam a namel e’]
  >- (rw []
      \\ first_assum $ qspecl_then [‘cexp_size f e’] assume_tac
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘e’] assume_tac
      \\ fs []
      \\ rename1 ‘demands_analysis_fun (IsFree namel c)’
      \\ pop_assum $ qspecl_then [‘IsFree namel c’] assume_tac
      \\ qabbrev_tac ‘p = demands_analysis_fun (IsFree namel c) e’
      \\ PairCases_on ‘p’
      \\ fs [empty_thm, TotOrd_compare]
      \\ rw [exp_of_def]
      \\ irule find_Lams
      \\ rename1 ‘to_fmap p0’
      \\ qexists_tac ‘IMAGE (λx. ([], explode x)) (FDOM (to_fmap p0))’
      \\ fs [ctxt_trans_def, adds_demands_soundness, lookup_thm])
  >~ [‘Let a vname e2 e1’]
  >- (rw []
      \\ rename1 ‘demands_analysis_fun (Bind _ _ _ c) _’
      \\ first_assum $ qspecl_then [‘cexp_size f e1’] assume_tac
      \\ first_x_assum $ qspecl_then [‘cexp_size f e2’] assume_tac
      \\ fs [cexp_size_def]
      \\ first_x_assum $ qspecl_then [‘f’, ‘e2’] assume_tac
      \\ first_x_assum $ qspecl_then [‘f’, ‘e1’] assume_tac
      \\ qabbrev_tac ‘p1 = demands_analysis_fun (Bind vname e2 c c) e1’
      \\ qabbrev_tac ‘p2 = demands_analysis_fun c e2’
      \\ PairCases_on ‘p1’
      \\ PairCases_on ‘p2’
      \\ fs [empty_thm, TotOrd_compare]
      \\ irule find_Subset
      \\ rw [exp_of_def]
      \\ Cases_on ‘FLOOKUP (to_fmap p10) (implode vname)’
      \\ fs []
      >- (irule_at Any find_Let
          \\ fs []
          \\ first_x_assum $ dxrule
          \\ first_x_assum $ dxrule
          \\ rw []
          \\ first_x_assum $ irule_at Any
          \\ fs [ctxt_trans_def]
          \\ first_x_assum $ irule_at Any
          \\ gen_tac
          \\ strip_tac
          \\ gvs [IMAGE_DEF, FLOOKUP_DEF])
      \\ irule_at Any find_Let2
      \\ first_x_assum $ dxrule
      \\ first_x_assum $ dxrule
      \\ rw []
      \\ first_assum $ irule_at Any
      \\ fs [ctxt_trans_def]
      \\ first_assum $ irule_at Any
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘{}’
      \\ fs [IMAGE_DEF, FLOOKUP_DEF]
      \\ first_x_assum $ irule_at Any
      \\ fs [explode_implode])
  >~ [‘Letrec a binds exp’]
  >- (rw []
      \\ rename1 ‘demands_analysis_fun (RecBind binds c c) _’
      \\ qabbrev_tac ‘e = demands_analysis_fun (RecBind binds c c) exp’
      \\ PairCases_on ‘e’
      \\ fs [empty_thm, lookup_thm, TotOrd_compare]
      \\ rw [exp_of_def]
      \\ irule find_Letrec
      \\ rw []
      >- (rename1 ‘LIST_REL _ l _’
          \\ qexists_tac ‘l’
          \\ pop_assum kall_tac
          \\ pop_assum kall_tac
          \\ Induct_on ‘l’
          \\ fs [exp_eq_refl]
          \\ gen_tac
          \\ rename1 ‘_ hd hd’
          \\ PairCases_on ‘hd’
          \\ fs [exp_eq_refl])
      \\ first_x_assum $ qspecl_then [‘cexp_size f exp’] assume_tac
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘exp’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘RecBind binds c c’, ‘e0’, ‘e1’] assume_tac
      \\ pop_assum $ drule
      \\ rw [ctxt_trans_def]
      \\ first_x_assum $ irule_at Any)
  >~ [‘Case a case_exp s l’]
  >- (gen_tac
      \\ rename1 ‘Bind _ _ c c’
      \\ first_assum $ qspecl_then [‘cexp_size f case_exp’] assume_tac
      \\ gvs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘case_exp’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’] assume_tac
      \\ qabbrev_tac ‘cexp = demands_analysis_fun c case_exp’
      \\ PairCases_on ‘cexp’
      \\ rw []
      \\ fs [empty_thm, lookup_thm, TotOrd_compare, find_Bottom, exp_of_def, MAP_MAP_o]
      \\ qspecl_then [‘l’] assume_tac map_does_not_changes
      \\ rename1 ‘Let s _ _’
      \\ pop_assum $ qspecl_then [‘λnames args ce. adds_demands a (demands_analysis_fun (Unfold names s args (Bind s case_exp c c)) ce) args’] assume_tac
      \\ fs []
      \\ rw []
      \\ irule find_Let
      \\ fs []
      \\ first_x_assum $ irule_at Any
      \\ irule find_rows_of
      \\ fs [LIST_REL_EL_EQN]
      \\ rw [EL_MAP]
      \\ rename1 ‘EL n l’
      \\ qabbrev_tac ‘e = EL n l’
      \\ PairCases_on ‘e’
      \\ fs []
      \\ irule find_Subset
      \\ rename1 ‘demands_analysis_fun (Unfold names s args (Bind s case_exp c c)) e'’
      \\ qabbrev_tac ‘p = demands_analysis_fun (Unfold names s args (Bind s case_exp c c)) e'’
      \\ PairCases_on ‘p’
      \\ irule_at Any adds_demands_soundness
      \\ fs []
      \\ first_x_assum $ qspecl_then [‘cexp_size f e'’] assume_tac
      \\ ‘cexp_size f e' < cexp1_size f l’ by metis_tac [cexp_size_lemma, EL_MEM]
      \\ fs []
      \\ pop_assum kall_tac
      \\ pop_assum $ qspecl_then [‘f’, ‘e' ’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘Unfold names s args (Bind s case_exp c c)’] assume_tac
      \\ fs [ctxt_trans_def])
QED

Theorem demands_analysis_fun_soudness:
  ∀(f: α -> num) (e : α cexp). exp_of e ≈ exp_of (SND (demands_analysis_fun Nil e))
Proof
  rpt gen_tac
  \\ qspecl_then [‘f’, ‘e’, ‘Nil’] assume_tac demands_analysis_soudness_lemma
  \\ qabbrev_tac ‘e' = demands_analysis_fun Nil e’
  \\ PairCases_on ‘e'’
  \\ fs []
  \\ drule find_soundness_lemma
  \\ fs []
QED

val _ = export_theory();
