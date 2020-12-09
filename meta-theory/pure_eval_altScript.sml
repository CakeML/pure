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

val _ = new_theory "pure_eval_alt";

Datatype:
  v_alt = alt_Constructor string (exp list)
        | alt_Closure string exp
        | alt_Atom lit
        | alt_Error
        | alt_Diverge
End

Definition dest_alt_Closure_def:
  dest_alt_Closure (alt_Closure s e) = SOME (s,e) ∧
  dest_alt_Closure _ = NONE
End

Definition eval_alt_to_def:
  eval_alt_to n (Var s) = alt_Error ∧
  eval_alt_to k (Lam s x) = alt_Closure s x ∧
  eval_alt_to k (App x y) =
    (let v = eval_alt_to k x in
       if v = alt_Diverge then alt_Diverge else
         case dest_alt_Closure v of
           NONE => alt_Error
         | SOME (s,body) => if k = 0 then alt_Diverge
                            else eval_alt_to (k − 1) (bind s y body)) ∧
  eval_alt_to k (Letrec f y) =
    (if k = 0 then alt_Diverge else eval_alt_to (k − 1) (subst_funs f y)) ∧
  eval_alt_to k (Prim p xs) =
    if k = 0 then alt_Diverge else
    case p of
    | Cons s => alt_Constructor s xs
    | Proj s i =>
        (if LENGTH xs ≠ 1 then alt_Error else
           case eval_alt_to (k-1) (HD xs) of
           | alt_Constructor t ys => if t = s ∧ i < LENGTH ys
                                     then eval_alt_to (k-1) (EL i ys)
                                     else alt_Error
           | alt_Diverge => alt_Diverge
           | _ => alt_Error)
    | Lit l => alt_Atom l
    | _ => alt_Error
Termination
  cheat
End

Definition eval_alt_def:
  eval_alt e =
    case some k. eval_alt_to k e ≠ alt_Diverge of
    | SOME k => eval_alt_to k e
    | NONE => alt_Diverge
End

Theorem eval_alt_to_IMP_eval_alt:
  eval_alt_to k x ≠ alt_Diverge ⇒
  eval_alt_to k x = eval_alt x
Proof
  cheat (* easy-ish *)
QED

Theorem eval_alt_eq_Diverge:
  eval_alt e = alt_Diverge ⇔
  ∀k. eval_alt_to k e = alt_Diverge
Proof
  cheat (* easy *)
QED

Theorem eval_alt_eq_eval_Diverge:
  eval_alt e = alt_Diverge ⇔ eval e = Diverge
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
    eval_alt x = alt_Constructor s (xs ++ y::ys) ∧
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

Theorem eval_IMP_eval_alt_Cons:
  eval x = Constructor s xs ⇒
  ∃ys. eval x = eval (Cons s ys) ∧
       eval_alt x = alt_Constructor s ys
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
    \\ drule eval_IMP_eval_alt_Cons
    \\ fs [eval_thm] \\ rw [] \\ fs []
    \\ drule LESS_LENGTH_IMP \\ rw [] \\ fs []
    \\ qexists_tac ‘ys'’
    \\ qexists_tac ‘y’
    \\ qexists_tac ‘zs’ \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ qabbrev_tac ‘qs = MAP eval ys'’
    \\ ‘LENGTH ys' = LENGTH qs’ by fs [Abbr‘qs’]
    \\ fs [EL_LENGTH_APPEND])
  \\ fs [GSYM eval_alt_eq_eval_Diverge,eval_alt_eq_Diverge,PULL_FORALL]
  \\ gen_tac \\ qid_spec_tac ‘e’ \\ qid_spec_tac ‘k’
  \\ ho_match_mp_tac eval_alt_to_ind \\ rw []
  THEN1 (rename [‘Var’] \\ fs [Once Diverges_cases])
  THEN1 (rename [‘Lam’] \\ fs [Once Diverges_cases])
  THEN1
   (rename [‘App’] \\ cheat (* TODO *))
  THEN1
   (rename [‘Letrec’]
    \\ rw [eval_alt_to_def] \\ fs [AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    \\ last_x_assum mp_tac
    \\ simp [Once Diverges_cases] \\ fs [])
  \\ rename [‘Prim p xs’]
  \\ Cases_on ‘∃s i. p = Proj s i’ (* the interesting case *)
  THEN1
   (gvs [] \\ pop_assum mp_tac
    \\ simp [Once Diverges_cases] \\ rw [] \\ gvs []
    \\ rw [eval_alt_to_def] \\ fs []
    \\ Cases_on ‘eval_alt_to (k − 1) x = alt_Diverge’ \\ fs []
    \\ drule eval_alt_to_IMP_eval_alt \\ strip_tac \\ gvs []
    \\ fs [] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ fs [EL_LENGTH_APPEND])
  \\ Cases_on ‘∃s. p = Cons s’
  THEN1 (gvs [] \\ fs [Once Diverges_cases] \\ rw [] \\ gvs [])
  \\ cheat
QED


Definition follow_path_def:
  follow_path f e [] =
    (case f e of
     | alt_Constructor s xs => (Constructor' s,LENGTH xs)
     | alt_Closure s x => (Closure' s x,0)
     | alt_Atom a => (Atom' a,0)
     | alt_Diverge => (Diverge',0)
     | alt_Error => (Error',0)) ∧
  follow_path f e (n::ns) =
    case f e of
    | alt_Constructor s xs => follow_path f (EL n xs) ns
    | _ => (Error',0)
End

Definition v_unfold_def:
  v_unfold f seed = gen_v (follow_path f seed)
End

Theorem v_unfold:
  v_unfold f x =
    case f x of
    | alt_Constructor s xs => Constructor s (MAP (v_unfold f) xs)
    | alt_Closure s x => Closure s x
    | alt_Atom a => Atom a
    | alt_Diverge => Diverge
    | alt_Error => Error
Proof
  fs [v_unfold_def]
  \\ simp [Once gen_v]
  \\ fs [follow_path_def]
  \\ Cases_on ‘f x’ \\ fs []
  \\ qid_spec_tac ‘l’
  \\ ho_match_mp_tac SNOC_INDUCT \\ rw []
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
  eval' x = v_unfold eval_alt x
End

Theorem eval_eq_eval':
  eval = eval'
Proof
  cheat (* complicated proof -- is it worth doing?
                                should eval be replcaed by eval'? *)
QED

val _ = export_theory();
