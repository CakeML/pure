(*
   Define an alternative version of the eval function
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite;
open pure_expTheory pure_valueTheory pure_evalTheory
     pure_exp_lemmasTheory pure_limitTheory;

val _ = new_theory "pure_eval_weak_head";

Datatype:
  wh = wh_Constructor string (exp list)
     | wh_Closure string exp
     | wh_Atom lit
     | wh_Error
     | wh_Diverge
End

Definition dest_wh_Closure_def:
  dest_wh_Closure (wh_Closure s e) = SOME (s,e) ∧
  dest_wh_Closure _ = NONE
End

Definition eval_wh_to_def:
  eval_wh_to n (Var s) = wh_Error ∧
  eval_wh_to k (Lam s x) = wh_Closure s x ∧
  eval_wh_to k (App x y) =
    (let v = eval_wh_to k x in
       if v = wh_Diverge then wh_Diverge else
         case dest_wh_Closure v of
           NONE => wh_Error
         | SOME (s,body) => if k = 0 then wh_Diverge
                            else eval_wh_to (k − 1) (bind s y body)) ∧
  eval_wh_to k (Letrec f y) =
    (if k = 0 then wh_Diverge else eval_wh_to (k − 1) (subst_funs f y)) ∧
  eval_wh_to k (Prim p xs) =
    if k = 0n then wh_Diverge else
    case p of
    | Cons s => wh_Constructor s xs
    | Proj s i =>
        (if LENGTH xs ≠ 1 then wh_Error else
           case eval_wh_to (k-1) (HD xs) of
           | wh_Constructor t ys => if t = s ∧ i < LENGTH ys
                                     then eval_wh_to (k-1) (EL i ys)
                                     else wh_Error
           | wh_Diverge => wh_Diverge
           | _ => wh_Error)
    | Lit l => wh_Atom l
    | _ => wh_Error
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λ(k,x).(k,(exp_size x)))`
End

Definition eval_wh_def:
  eval_wh e =
    case some k. eval_wh_to k e ≠ wh_Diverge of
    | SOME k => eval_wh_to k e
    | NONE => wh_Diverge
End

(*
Definition eval_wh_def:
  eval_wh e =
    case some v. ∃k. eval_wh_to k e = v ∧ v ≠ wh_Diverge of
    | SOME v => v
    | NONE => wh_Diverge
End
*)

Theorem eval_wh_to_IMP_eval_wh:
  eval_wh_to k x ≠ wh_Diverge ⇒
  eval_wh_to k x = eval_wh x
Proof
  cheat (* easy-ish *)
QED

Theorem eval_wh_eq_Diverge:
  eval_wh e = wh_Diverge ⇔
  ∀k. eval_wh_to k e = wh_Diverge
Proof
  cheat (* easy *)
QED

Theorem eval_wh_eq_eval_Diverge:
  eval_wh e = wh_Diverge ⇔ eval e = Diverge
Proof
  cheat (* see eval_eq_eval' further down *)
QED

CoInductive Diverges:
  (∀f x.
    Diverges (subst_funs f x) ⇒
    Diverges (Letrec f x))
  ∧
  (∀x y.
    Diverges x ⇒
    Diverges (App x y))
  ∧
  (∀x y s body.
    eval x = Closure s body ∧
    Diverges (bind s y body) ⇒
    Diverges (App x y))
  ∧
  (∀s n x.
    Diverges x ⇒
    Diverges (IsEq s n x))
  ∧
  (∀s i x.
    Diverges x ⇒
    Diverges (Proj s i x))
  ∧
  (∀s xs y ys x.
    eval_wh x = wh_Constructor s (xs ++ y::ys) ∧
    Diverges y ⇒
    Diverges (Proj s (LENGTH xs) x))
  ∧
  (∀x y z.
    Diverges x ⇒
    Diverges (If x y z))
  ∧
  (∀x y z.
    Diverges y ∧ eval x = True ⇒
    Diverges (If x y z))
  ∧
  (∀x y z.
    Diverges z ∧ eval x = False ⇒
    Diverges (If x y z))
  ∧
  (∀a x xs.
    Diverges x ∧ MEM x xs ⇒
    Diverges (Prim (AtomOp a) xs))
End

Theorem eval_IMP_eval_wh_Cons:
  eval x = Constructor s xs ⇒
  ∃ys. eval x = eval (Cons s ys) ∧
       eval_wh x = wh_Constructor s ys
Proof
  cheat
QED

Triviality LESS_LENGTH_IMP:
  ∀xs n. n < LENGTH xs ⇒ ∃ys y zs. xs = ys ++ y::zs ∧ LENGTH ys = n
Proof
  Induct \\ fs [] \\ Cases_on ‘n’ \\ fs []
  \\ rw [] \\ res_tac \\ gvs []
  \\ qexists_tac ‘h::ys’ \\ fs []
  \\ qexists_tac ‘y’ \\ fs []
  \\ qexists_tac ‘zs’ \\ fs []
QED

Theorem Diverges_iff:
  ∀e. eval e = Diverge ⇔ Diverges e
Proof
  rw [] \\ eq_tac
  THEN1
   (qid_spec_tac ‘e’
    \\ ho_match_mp_tac Diverges_coind
    \\ rw [] \\ reverse (Cases_on ‘e’) \\ fs []
    \\ TRY (fs [eval_thm] \\ NO_TAC)
    THEN1
     (rename [‘eval (App f x)’]
      \\ gvs [eval_thm,AllCaseEqs()]
      \\ Cases_on ‘eval f’ \\ fs [dest_Closure_def])
    \\ rename [‘eval (Prim p xs)’]
    \\ reverse (Cases_on ‘p’) \\ fs [eval_thm]
    \\ gvs [eval_Prim,DefnBase.one_line_ify NONE eval_op_def,
            AllCaseEqs(),MAP_EQ_CONS,is_eq_def,el_def,MEM_MAP]
    THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ pop_assum (assume_tac o GSYM) \\ fs []
    \\ drule eval_IMP_eval_wh_Cons
    \\ fs [eval_thm] \\ rw [] \\ fs []
    \\ drule LESS_LENGTH_IMP \\ rw [] \\ fs []
    \\ qexists_tac ‘ys'’
    \\ qexists_tac ‘y’
    \\ qexists_tac ‘zs’ \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ qabbrev_tac ‘qs = MAP eval ys'’
    \\ ‘LENGTH ys' = LENGTH qs’ by fs [Abbr‘qs’]
    \\ fs [EL_LENGTH_APPEND])
  \\ fs [GSYM eval_wh_eq_eval_Diverge,eval_wh_eq_Diverge,PULL_FORALL]
  \\ gen_tac \\ qid_spec_tac ‘e’ \\ qid_spec_tac ‘k’
  \\ ho_match_mp_tac eval_wh_to_ind \\ rw []
  THEN1 (rename [‘Var’] \\ fs [Once Diverges_cases])
  THEN1 (rename [‘Lam’] \\ fs [Once Diverges_cases])
  THEN1
   (rename [‘App’] \\ cheat (* TODO *))
  THEN1
   (rename [‘Letrec’]
    \\ rw [eval_wh_to_def] \\ fs [AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    \\ last_x_assum mp_tac
    \\ simp [Once Diverges_cases] \\ fs [])
  \\ rename [‘Prim p xs’]
  \\ Cases_on ‘∃s i. p = Proj s i’ (* the interesting case *)
  THEN1
   (gvs [] \\ pop_assum mp_tac
    \\ simp [Once Diverges_cases] \\ rw [] \\ gvs []
    \\ rw [eval_wh_to_def] \\ fs []
    \\ Cases_on ‘eval_wh_to (k − 1) x = wh_Diverge’ \\ fs []
    \\ drule eval_wh_to_IMP_eval_wh \\ strip_tac \\ gvs []
    \\ fs [] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ fs [EL_LENGTH_APPEND])
  \\ Cases_on ‘∃s. p = Cons s’
  THEN1 (gvs [] \\ fs [Once Diverges_cases] \\ rw [] \\ gvs [])
  \\ cheat
QED


Definition follow_path_def:
  follow_path f e [] =
    (case f e of
     | wh_Constructor s xs => (Constructor' s,LENGTH xs)
     | wh_Closure s x => (Closure' s x,0)
     | wh_Atom a => (Atom' a,0)
     | wh_Diverge => (Diverge',0)
     | wh_Error => (Error',0)) ∧
  follow_path f e (n::ns) =
    case f e of
    | wh_Constructor s xs => follow_path f (EL n xs) ns
    | _ => (Error',0)
End

Definition v_unfold_def:
  v_unfold f seed = gen_v (follow_path f seed)
End

Theorem v_unfold:
  v_unfold f x =
    case f x of
    | wh_Constructor s xs => Constructor s (MAP (v_unfold f) xs)
    | wh_Closure s x => Closure s x
    | wh_Atom a => Atom a
    | wh_Diverge => Diverge
    | wh_Error => Error
Proof
  fs [v_unfold_def]
  \\ simp [Once gen_v]
  \\ fs [follow_path_def]
  \\ Cases_on ‘f x’ \\ fs []
  \\ qid_spec_tac ‘l’
  \\ Induct using SNOC_INDUCT \\ rw []
  \\ rewrite_tac [GENLIST,GSYM ADD1]
  \\ fs [SNOC_APPEND,EL_LENGTH_APPEND]
  \\ fs [v_unfold_def]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
  \\ pop_assum (assume_tac o GSYM)
  \\ fs [GENLIST_FUN_EQ]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ fs [EL_APPEND1]
QED

Definition eval'_def:
  eval' x = v_unfold eval_wh x
End

Theorem eval_eq_eval':
  eval = eval'
Proof
  cheat (* complicated proof -- is it worth doing?
                                should eval be replcaed by eval'? *)
QED

val _ = export_theory();
