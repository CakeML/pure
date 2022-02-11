(*
   Formalises the notion of "demand" as used in demand/strictness analysis.
*)

open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory dep_rewrite
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_miscTheory pure_exp_relTheory pure_congruenceTheory;

val _ = new_theory "pure_demand";

Definition Projs_def:
  Projs [] e = e ∧
  Projs ((x,i)::ps) e = Projs ps (Proj x i e)
End

Theorem demands_proj_end:
  ∀ ps x i e. Projs (ps++[(x,i)]) e = Proj x i (Projs ps e)
Proof
  Induct THEN1 rw [Projs_def]
  \\ gen_tac \\ rename1 ‘hd::ps’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
QED

val _ = set_fixity "demands" (Infixl 480);

Definition demands_def:
  (e demands (p,v)) = (e ≅ Seq (Projs p (Var v)) e)
End

Theorem demands_Var:
  (Var v) demands ([],v)
Proof
  fs [demands_def,Projs_def]
  \\ metis_tac [Seq_id,exp_eq_sym]
QED

Theorem demands_Proj:
  e demands d ⇒
  (Proj n i e) demands d
Proof
  PairCases_on ‘d’
  \\ rename1 ‘(ps,v)’
  \\ rw [demands_def,Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq e (Proj n i e)’
  \\ conj_tac THEN1 fs [Proj_Seq]
  \\ qabbrev_tac ‘p = Projs ps (Var v)’
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Seq p e) (Proj n i e)’
  \\ conj_tac THEN1
   (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq p (Seq e (Proj n i e))’
  \\ conj_tac THEN1 fs [Seq_assoc]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
  \\ metis_tac [Proj_Seq,exp_eq_sym]
QED

Theorem demands_Projs:
  ∀ps2 e ps v. e demands (ps, v) ⇒
  (Projs ps2 e) demands (ps, v)
Proof
  Induct
  >-  rw [Projs_def]
  \\ gen_tac \\ rename1 ‘(hd::ps2)’ \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
  \\ first_assum $ irule_at Any
  \\ irule demands_Proj
  \\ fs []
QED

Theorem demands_Proj_Var:
  (Proj s i (Var v)) demands ([(s,i)],v)
Proof
  rw [demands_def,Projs_def]
  \\ metis_tac [Seq_id,exp_eq_sym]
QED

Theorem exp_eq_Projs_cong:
  ∀ps x y. x ≅ y ⇒ Projs ps x ≅ Projs ps y
Proof
  Induct \\ fs [Projs_def,FORALL_PROD]
  \\ rw [] \\ first_x_assum irule
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
QED

Theorem Projs_Seq:
  ∀ps e e'. Projs ps (Seq e e') ≅ Seq e (Projs ps e')
Proof
  Induct
  THEN1 (rw [Projs_def] \\ fs [exp_eq_refl])
  \\ rpt gen_tac
  \\ rename1 ‘hd::ps’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
  \\ irule exp_eq_trans \\ qexists_tac ‘Projs ps (Seq e (Proj hd0 hd1 e'))’
  \\ conj_tac
  THEN1 (irule exp_eq_Projs_cong \\ irule eval_wh_IMP_exp_eq \\ rw [subst_def, eval_wh_Proj, eval_wh_Seq])
  \\ rw []
QED

Theorem Let_Projs:
  ∀ps x w y. Let w y (Projs ps x) ≅ Projs ps (Let w y x)
Proof
  Induct \\ fs [Projs_def,exp_eq_refl,FORALL_PROD] \\ rw []
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ps (Let w y (Proj p_1 p_2 x))’
  \\ conj_tac THEN1 fs []
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Prim_alt]
QED

Theorem demands_Seq:
  e demands d ⇒ (Seq e e') demands d
Proof
  PairCases_on ‘d’
  \\ rw [demands_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Seq (Projs d0 (Var d1)) e) e'’
  \\ conj_tac THEN1 (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ fs [Seq_assoc]
QED

(*
Theorem seq2_means_same:
  Var v ≅ Seq (Var w) (Var v) ⇒ v = w
Proof
  rw []
  \\ qsuff_tac ‘Seq (Var v) (Var v) ≅ Seq (Var w) (Var v)’
  \\ rw []
  \\ qsuff_tac ‘Var v ≅ Var w’

\\ rw [exp_eq_def]

  \\ qsuff_tac ‘v ∈ FDOM (λn. (Var n)) ∧ w ∈ FDOM (λn. (Var n)) ⇒ bind (λn. (Var n)) (Var v) ≃ bind (λn. (Var n)) (Var w)’
QED

Theorem demands_Proj2:
  ∀e v. e demands ([], v) ⇒
  ∀n i.
  (Proj n i e) demands ([(n,i)], v)
Proof
  Induct \\ rw [demands_def, Projs_def]

  rw [demands_def, Projs_def, Once exp_eq_def]
  irule eval_wh_IMP_exp_eq
  gen_tac
  rw [eval_wh_def]
  Induct
  THEN1 (gen_tac \\ gen_tac \\ strip_tac
   \\ qsuff_tac ‘v = s’ by ( pop_assum // rw [demands_def])
   \\ rw [] \\ fs [demands_Proj_Var])

  rw [demands_def, Projs_def]
  \\ irule exp_eq_trans \\ qexists_tac ‘Proj n i (Seq (Proj n i (Var v)) e)’
  \\ conj_tac
QED
*)

Theorem demands_Let1:
  e demands d ∧ e' demands ([],w) ⇒ (Let w e e') demands d
Proof
  PairCases_on ‘d’
  \\ rw [demands_def,Projs_def]
  \\ irule exp_eq_trans
  \\ qabbrev_tac ‘p = (Projs d0 (Var d1))’
  \\ qexists_tac ‘Let w e (Seq (Var w) e')’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Let w e (Var w)) (Let w e e')’
  \\ conj_tac THEN1 fs [Let_Seq]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq e (Let w e e')’
  \\ conj_tac
  THEN1 (irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Seq p e) (Let w e e')’
  \\ conj_tac THEN1
   (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq p (Seq e (Let w e e'))’
  \\ conj_tac THEN1 fs [Seq_assoc]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
  \\ once_rewrite_tac [exp_eq_sym]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Let w e (Seq (Var w) e')’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Let w e (Var w)) (Let w e e')’
  \\ conj_tac THEN1 fs [Let_Seq]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq e (Let w e e')’
  \\ conj_tac THEN1
    (irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var])
  \\ fs [exp_eq_refl]
QED

Theorem demands_Let2:
  e' demands (p,v) ∧ v ≠ w ⇒ (Let w e e') demands (p,v)
Proof
  rw [demands_def,Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Let w e (Seq (Projs p (Var v)) e')’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Let w e (Projs p (Var v))) (Let w e e')’
  \\ conj_tac THEN1 fs [Let_Seq]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
  \\ qid_spec_tac ‘p’ \\ Induct
  THEN1 fs [Projs_def,Let_Var2]
  \\ fs [FORALL_PROD,Projs_def] \\ rw []
  \\ fs [GSYM Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ((p_1,p_2)::p') (Let w e (Var v))’
  \\ conj_tac THEN1 fs [Let_Projs]
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var2]
QED

Theorem demands_Let_Proj: (* expects program to be in ANF *)
  e demands (ps,w) ⇒
  (Let w (Proj s i (Var v)) e) demands ((s,i)::ps,v)
Proof
  rw [demands_def,Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Let w (Proj s i (Var v)) (Seq (Projs ps (Var w)) e)’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Let w (Proj s i (Var v)) (Projs ps (Var w)))
                      (Let w (Proj s i (Var v)) e)’
  \\ conj_tac THEN1 fs [Let_Seq]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ps (Let w (Proj s i (Var v)) (Var w))’
  \\ conj_tac THEN1 fs [Let_Projs]
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var]
QED

Theorem demands_Let_Cons: (* expects program to be in ANF *)
  e demands ((s,LENGTH xs)::ps,w) ⇒
  (Let w (Cons s (xs ++ (Var v)::ys)) e) demands (ps,v)
Proof
  rw [demands_def,Projs_def]
  \\ qabbrev_tac ‘cons = (Cons s (xs ++ Var v::ys))’
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Let w cons (Seq (Projs ps (Proj s (LENGTH xs) (Var w))) e)’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Seq
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
  \\ fs [GSYM Projs_def]
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Projs
  \\ fs [Projs_def]
  \\ irule exp_eq_Projs_cong \\ fs [exp_eq_refl,Let_Var]
  \\ irule exp_eq_trans
  \\ irule_at Any exp_eq_Prim_cong \\ fs [PULL_EXISTS]
  \\ irule_at Any Let_Var
  \\ unabbrev_all_tac
  \\ fs [Proj_Cons]
QED


Theorem Seq_App:
  App (Seq proj f) e ≅ Seq proj (App f e)
Proof
  irule eval_wh_IMP_exp_eq \\ rw []
  \\ fs [subst_def, eval_wh_Seq, eval_wh_App]
  \\ rw [] \\ fs []
QED

Theorem demands_App:
  f demands d ⇒ (App f e) demands d
Proof
  PairCases_on ‘d’ \\ rename1 ‘(ps,v)’
  \\ rw [demands_def]
  \\ qabbrev_tac ‘proj = Projs ps (Var v)’
  \\ irule exp_eq_trans
  \\ qexists_tac ‘App (Seq proj f) e’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ rw [exp_eq_refl])
  \\ fs [Seq_App]
QED

Theorem demands_If:
  e demands d ⇒ (If e e' e'') demands d
Proof
  PairCases_on ‘d’
  \\ rw [demands_def]
  \\ qabbrev_tac ‘p = Projs d0 (Var d1)’
  \\ irule exp_eq_trans \\ qexists_tac ‘If (Seq p e) e' e''’ \\ conj_tac
  THEN1 (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule eval_wh_IMP_exp_eq \\ rw []
  \\ fs [subst_def, eval_wh_Seq, eval_wh_If]
  \\ rw [] \\ fs []
QED

Theorem Projs_subst:
  ∀ps f e. subst f (Projs ps e) = Projs ps (subst f e)
Proof
  Induct THEN1 rw [Projs_def]
  \\ gen_tac
  \\ rename1 ‘Projs (hd::_) _’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def, subst_def]
QED

Definition well_formed_def:
  well_formed (Cons s) l = (s ≠ s) ∧
  well_formed (Proj s i) l = (∃ e. l = [e]) ∧
  well_formed (IsEq s i) l = (∃e. l = [e]) ∧
  well_formed If (l: exp list) = (∃e e' e''. l = e::e'::e''::[]) ∧
  well_formed Seq l = (∃e e'. l = e::e'::[]) ∧
  well_formed (AtomOp op) l = (op ≠ op)
End

Theorem exp_eq_l_refl:
  ∀l. LIST_REL $≅ l l
Proof
  Induct \\ fs [exp_eq_refl]
QED

Theorem demands_Prim:
  e demands d ∧ well_formed ope (e::l) ⇒ Prim ope (e::l) demands d
Proof
  PairCases_on ‘d’
  \\ rw [demands_def]
  \\ qabbrev_tac ‘p = Projs d0 (Var d1)’
  \\ irule exp_eq_trans \\ qexists_tac ‘Prim ope ((Seq p e)::l)’
  \\ conj_tac
  >- (irule exp_eq_Prim_cong \\ fs [exp_eq_l_refl])
  \\ Cases_on ‘ope’ \\ fs [well_formed_def]
  \\ irule eval_wh_IMP_exp_eq \\ rw []
  >- (fs [subst_def, eval_wh_Seq, eval_wh_If]
      \\ rw [] \\ fs [])
  >- (fs [subst_def, eval_wh_Seq, eval_wh_IsEq]
      \\ rw [] \\ fs [])
  >- (fs [subst_def, eval_wh_Seq, eval_wh_Proj]
      \\ rw [] \\ fs [])
  >- (fs [subst_def, eval_wh_Seq]
     \\ rw [] \\ fs [])
QED

(*
Theorem demands_Seq2:
  eval_wh e ≠ wh_Error ∧ eval_wh e ≠ wh_Diverge
  ∧ eval_wh (Projs ps (Var v)) ≠ wh_Error ∧ eval_wh (Projs ps (Var v)) ≠ wh_Diverge
  ∧ e' demands (ps, v)
   ⇒ (Seq e e') demands (ps, v)
Proof
  rw [demands_def, Projs_def, eval_wh_def]
  \\ irule exp_eq_trans \\ qexists_tac ‘Seq e (Seq (Projs ps (Var v)) e')’
  \\ conj_tac
  THEN1 (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule eval_wh_IMP_exp_eq
  \\ rw []
  \\ fs [subst_def]
  \\ fs [Projs_subst]
  \\ fs [eval_wh_Seq]
  \\ fs [subst_def]
  \\ rw []

  \\ rw [subst_def, eval_wh_Seq]
*)

(*
Theorem demands_If2:
  wh_eval e ≠ wh_Diverge ∧ wh_eval e ≠ wh_Error ∧ e1 demands d ∧ e2 demands d ⇒ (If e e1 e2) demands d
Proof
  PairCases_on ‘d’
  \\ rw [demands_def]
  \\ rename1 ‘Projs ps (Var v)’
  \\ qabbrev_tac ‘p = Projs ps (Var v)’
  \\ irule exp_eq_trans \\ qexists_tac ‘If e (Seq p e1) (Seq p e2)’
  \\ conj_tac
  THEN1 (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule eval_wh_IMP_exp_eq \\ rw []
  \\ fs [subst_def, eval_wh_Seq, eval_wh_If]
  \\ rw [] \\ fs []
QED
*)
(*
Definition fun_demands2_def:
  f fun_demands (ps,(k:num),(n:num)) ⇒ ∀l hd v. LENGTH l = n ∧ LENGTH hd = k ∧ (l = hd++v::tl) ⇒ Apps f (MAP Var l) demands ([],v)
End
*)
Definition fun_demands_pre_def:
  fun_demands_pre (k:num) f ps = if k = 0
                        then ∀n. n ∉ freevars f ⇒ (App f (Var n)) demands (ps, n)
                        else ∀e. fun_demands_pre (k - 1) (App f e) ps
End

val _ = set_fixity "fun_demands" (Infixl 478);

Definition fun_demands_def:
  f fun_demands (ps, k) = fun_demands_pre k f ps
End
(*
Theorem Let_Var_eq:
  ∀e v. Let v (Var v) e ≅ e
Proof
  Induct \\ rw []
  THEN1 (qsuff_tac ‘v = s ∨ v ≠ s’
         THEN1 (DISCH_TAC \\ pop_assum DISJ_CASES_TAC
                THEN1 (rw [] \\ fs [Let_Var])
                \\ fs [Let_Var2])
         \\ rw [])
  THEN1 (irule exp_eq_trans \\ qexists_tac ‘Prim o' (MAP (Let v (Var v)) l)’
         \\ conj_tac
         THEN1 fs [Let_Prim]
QED
*)
(*
Theorem fun_demands_Lam:
  e demands (ps, v) ⇒ (Lam v e) fun_demands (ps, 0)
Proof
  rw [fun_demands_def, fun_demands_pre_def, demands_def]
  \\ irule exp_eq_trans
  THEN1 (qexists_tac ‘Let v (Var n) (Seq (Projs ps (Var v)) e)’
         \\ conj_tac
         THEN1 (irule exp_eq_App_cong \\ fs [exp_eq_refl]
                \\ irule exp_eq_Lam_cong \\ fs [])
         \\ irule exp_eq_trans \\ qexists_tac ‘Seq (Let v (Var n) (Projs ps (Var v))) (Let v (Var n) e)’
         \\ conj_tac
         THEN1 fs [Let_Seq]
         \\ irule exp_eq_Prim_cong
         \\ fs [exp_eq_refl]
         \\ irule exp_eq_trans \\ qexists_tac ‘Projs ps (Let v (Var n) (Var v))’
         \\ conj_tac
         THEN1 fs [Let_Projs]
         \\ irule exp_eq_Projs_cong \\ fs [Let_Var])
  \\ qexists_tac ‘e’ \\ conj_tac
  THEN1 fs [Let_Var_eq]
  \\ irule exp_eq_trans \\ qexists_tac ‘Seq (Projs ps (Var n)) e’
  THEN1 fs []
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
QED

Theorem fun_demands_Let:
  ∀f. (f fun_demands (ps, k) ⇒ ∀e v. (App (Lam v f) e) fun_demands (ps, k))
Proof
  rw [fun_demands_def, Once fun_demands_pre_def, demands_def]
  THEN1 (rw [fun_demands_pre_def]
   \\ rw [demands_def]
   \\ irule exp_eq_trans \\ qexists_tac ‘Let v e (App f (Var n))’
   \\ conj_tac
   THEN1 (irule exp_eq_trans \\ qexists_tac ‘App (Let v e f) (Let v e (Var n))’
    \\ conj_tac
    THEN1 (irule exp_eq_App_cong \\ fs [exp_eq_refl])
*)

(*
Theorem fun_demands_Lam2:
  f fun_demands (ps,k) ⇒ (Lam v f) fun_demands (ps, k+1)
Proof
  rw [fun_demands_def]
\\  rw [Once fun_demands_pre_def]
\\ cheat
QED
*)

Datatype:
  ctxt_bind = Bind string exp (ctxt_bind list)
       | RecBind ((string # exp) list) (ctxt_bind list)
End
(*
Definition ctxt_size_def:
  ctxt_size [] = 0 ∧
  ctxt_size (Bind s e ctxt::ctxt') = ctxt_size ctxt + ctxt_size ctxt' ∧
  ctxt_size (RecBind sel ctxt::ctxt') = ctxt_size ctxt + ctxt_size ctxt'
End

Definition subst_ctxt_def:
  (subst_ctxt: ctxt_bind list -> exp -> exp) ctxt (App f e) = App (subst_ctxt ctxt f) (subst_ctxt ctxt e) ∧
  (subst_ctxt: ctxt_bind list -> exp -> exp)  ctxt (Prim op l) = Prim op (MAP (subst_ctxt ctxt) l) ∧
  (subst_ctxt: ctxt_bind list -> exp -> exp) ctxt (Lam v e) = Lam v (subst_ctxt ((Bind v (Var v) [])::ctxt) e) ∧
  (subst_ctxt: ctxt_bind list -> exp -> exp) [] (Var n) = Var n ∧
  (subst_ctxt: ctxt_bind list -> exp -> exp) ((Bind v exp ctxt)::tl) (Var n) = if n = v
                                         then subst_ctxt ctxt exp
                                         else subst_ctxt tl (Var n) ∧
  (subst_ctxt: ctxt_bind list -> exp -> exp) ((RecBind nel ctxt)::tl) (Var n) = if MEM n (MAP FST nel)
                                                then Var n
                                                else subst_ctxt tl (Var n) ∧
  (subst_ctxt : ctxt_bind list -> exp -> exp) ctxt (Letrec nel e) = Letrec nel (subst_ctxt ((RecBind nel ctxt)::ctxt) e)
End
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λ(c,e). (LENGTH c, exp_size e)) ’
  \\ rw []
End
*)

Inductive find: (* i i o o *)
[find_Bottom:]
  (∀e (c:ctxt_bind list).
    find e c {} e) ∧
[find_Seq:]
  (∀e e' c (p:(string#num) list) ds v.
    find e c ds e' ∧ (p,v) ∈ ds ⇒
    find e c ds (Seq (Var v) e')) ∧
[find_Seq2:]
  (∀e e' e2 e2' c ds ds2.
     find e c ds e' ∧ find e2 c ds2 e2' ⇒
     find (Seq e e2) c ds (Seq e' e2')) ∧
[find_If:]
  (∀ec et ee ec' et' ee' c dsc dst dse.
     find ec c dsc ec' ∧
     find et c dst et' ∧
     find ee c dse ee' ⇒
     find (If ec et ee) c dsc (If ec' et' ee')) ∧
[find_Var:]
  (∀n c. find (Var n) c {([],n)} (Var n)) ∧
[find_App:]
  (∀f f' e e' c ds ds2.
     find f c ds f' ∧
     find e c ds2 e' ⇒
     find (App f e) c ds (App f' e')) ∧
[find_Prim:]
  (∀el c edsel ope.
     (∀e ds e'. MEM (e, ds, e') edsel ⇒ find e c ds e')
     ∧ el = MAP FST edsel ⇒ find (Prim ope el) c {} (Prim ope (MAP (SND o SND) edsel))) ∧
[find_Prim1:]
  (∀c edsel tl ope e ds e'.
     (∀ e ds e'. MEM (e, ds, e') edsel ⇒ find e c ds e')
     ∧ edsel = (e, ds, e')::tl ∧ well_formed ope (MAP FST edsel) ⇒ find (Prim ope (MAP FST edsel)) c ds (Prim ope (MAP (SND o SND) edsel))) ∧
[find_Proj:]
  (∀e e' n i c ds.
     find e c ds e' ⇒ find (Proj n i e) c ds (Proj n i e')) ∧
[find_Subset:]
  (∀e e' c ds ds'.
     find e c ds e' ∧ (∀d. d ∈ ds' ⇒ d ∈ ds) ⇒ find e c ds' e') ∧
[find_Let:]
  (∀e e' e2 e2' ds ds' v.
     find e c ds e' ∧ find e2 c ds' e2'
     ∧ (∀ps. (ps, v) ∉ ds')
     ⇒ find (Let v e e2) c ds' (Let v e' e2')) ∧
[find_Let2:]
  (∀ e e' e2 e2' ds ds' ds'' v ps.
     find e c ds e' ∧ find e2 c ds' e2'
     ∧ (ps,v) ∈ ds'
     ∧ (∀ps' v'. (ps', v') ∈ ds'' ⇒ ((ps', v') ∈ ds' ∧ v' ≠ v) ∨ (ps', v') ∈ ds)
     ⇒ find (Let v e e2) c ds'' (Let v e' e2'))
End

Theorem demands_Projs_empty:
  ∀ps v. (Projs ps (Var v)) demands ([], v)
Proof
  Induct \\ rw [demands_def, Projs_def]
  THEN1 (irule eval_wh_IMP_exp_eq
         \\ fs [subst_def, eval_wh_Seq]
         \\ rw [] \\ fs [])
  \\ rename1 ‘hd::ps’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
  \\ irule exp_eq_trans \\ qexists_tac ‘Projs ps (Seq (Var v) (Proj hd0 hd1 (Var v)))’
  \\ conj_tac
  THEN1 (irule exp_eq_Projs_cong
         \\ ‘(Proj hd0 hd1 (Var v)) demands ([], v)’
           by (irule demands_Proj \\ fs [demands_Var])
         \\ fs [demands_def, Projs_def])
  \\ fs [Projs_Seq]
QED

Theorem demands_empty_proj:
  e demands (ps, v) ⇒ e demands ([], v)
Proof
  rw [demands_def, Projs_def]
  \\ irule exp_eq_trans \\ qexists_tac ‘Seq (Seq (Var v) (Projs ps (Var v))) e’
  \\ conj_tac
  >- (irule exp_eq_trans \\ qexists_tac ‘Seq (Projs ps (Var v)) e’
      \\ fs []
      \\ irule exp_eq_Prim_cong
      \\ fs [exp_eq_refl]
      \\ ‘(Projs ps (Var v)) demands ([], v)’ by fs [demands_Projs_empty]
      \\ fs [demands_def, Projs_def])
  \\ irule exp_eq_trans \\ qexists_tac ‘Seq (Var v) (Seq (Projs ps (Var v)) e)’
  \\ fs [Seq_assoc]
  \\ irule exp_eq_Prim_cong
  \\ fs [exp_eq_refl, exp_eq_sym]
QED

Theorem find_soundness_lemma:
  ∀e c ds e'. find e c ds e'  ⇒ e ≅ e' ∧ ∀d. d ∈ ds ⇒ e demands d
Proof
  Induct_on ‘find’
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- fs [exp_eq_refl]
  >- (strip_tac
      \\ fs []
      \\ first_x_assum $ drule
      \\ rw []
      \\ dxrule_then assume_tac demands_empty_proj
      \\ fs [demands_def, Projs_def]
      \\ irule exp_eq_trans
      \\ first_assum $ irule_at Any
      \\ irule exp_eq_Prim_cong
      \\ fs [exp_eq_refl])
  >- (strip_tac
      \\ conj_tac
      >- fs [exp_eq_Prim_cong]
      \\ rw []
      \\ irule demands_Seq
      \\ fs [])
  >- (strip_tac
      \\ conj_tac
      >- fs [exp_eq_Prim_cong]
      \\ rw []
      \\ irule demands_If
      \\ fs [])
  >- (fs [exp_eq_refl]
      \\ fs [demands_Var])
  >- (strip_tac
     \\ fs [exp_eq_App_cong]
     \\ rw []
     \\ fs [demands_App])
  >- (strip_tac
      \\ fs []
      \\ irule exp_eq_Prim_cong
      \\ rw [LIST_REL_EL_EQN, EL_MAP]
      \\ ‘MEM (EL n edsel) edsel’ by fs [EL_MEM]
      \\ qabbrev_tac ‘triple = EL n edsel’
      \\ PairCases_on ‘triple’
      \\ fs []
      \\ first_x_assum drule
      \\ fs [])
  >- (strip_tac
     \\ conj_tac
     >- (irule exp_eq_Prim_cong
         \\ rw [LIST_REL_EL_EQN, EL_MAP]
         \\ ‘MEM (EL n ((e,ds,e')::tl)) ((e,ds,e')::tl)’ by fs [EL_MEM]
         \\ qabbrev_tac ‘t = EL n ((e,ds,e')::tl)’
         \\ PairCases_on ‘t’
         \\ rw []
         \\ first_x_assum drule
         \\ fs [])
      \\ rw []
      \\ ‘e demands d’ by (‘MEM (e,ds,e') ((e,ds,e')::tl)’ by fs [EL_MEM]
                           \\ first_x_assum drule
                           \\ fs [])
      \\ irule demands_Prim
      \\ fs [])
  >- (strip_tac
      \\ fs [exp_eq_Prim_cong]
      \\ rw []
      \\ irule demands_Proj
      \\ fs [])
  >- fs []
  >- (strip_tac
      \\ conj_tac
      >- (irule exp_eq_App_cong \\ fs []
          \\ irule exp_eq_Lam_cong
          \\ fs [])
      \\ rw []
      \\ PairCases_on ‘d’
      \\ irule demands_Let2
      \\ conj_tac
      \\ ‘d1 = v ∨ d1 ≠ v’ by fs []
      \\ fs []
      \\ ‘(d0, v) ∉ ds'’ by (first_x_assum $ irule_at Any)
      \\ first_x_assum drule
      \\ fs [])
  >- (strip_tac
      \\ conj_tac
      >- (irule exp_eq_App_cong \\ fs []
          \\ irule exp_eq_Lam_cong
          \\ fs [])
      \\ rw []
      \\ PairCases_on ‘d’
      \\ first_x_assum drule
      \\ rw []
      >- (irule demands_Let2
          \\ fs [])
      \\ irule demands_Let1
      \\ fs []
      \\ first_x_assum drule
      \\ rw []
      \\ drule demands_empty_proj
      \\ fs [])
QED

Theorem find_soundness:
  find e Nil ds e' ⇒ e ≅ e'
Proof
  rw []
  \\ drule find_soundness_lemma
  \\ fs []
QED
(*

  let foo = lam (a + 2) in
    lam x (foo x)
-->
  let foo = lam a (seq a (a + 2)) in
    lam x (foo x)
-->
  let foo = lam a (seq a (a + 2)) in
    lam x (seq x (foo x))

  Letrec [(f,x)] rest
*)

val _ = export_theory();
