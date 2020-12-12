(*
   Defines a weak-head eval (eval_wh) and an unbounded eval function (eval)
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_valueTheory;

val _ = new_theory "pure_eval";

(* weak-head values *)

Datatype:
  wh = wh_Constructor string (exp list)
     | wh_Closure string exp
     | wh_Atom lit
     | wh_Error
     | wh_Diverge
End

(* weak-head evalation *)

Definition dest_wh_Closure_def[simp]:
  dest_wh_Closure (wh_Closure s e) = SOME (s,e) ∧
  dest_wh_Closure _ = NONE
End

Definition get_atoms_def:
  get_atoms [] = SOME (SOME []) ∧
  get_atoms (v::vs) =
    case v of
    | wh_Diverge => NONE (* diverge *)
    | wh_Atom a =>
        (case get_atoms vs of
         | NONE => NONE
         | SOME NONE => SOME NONE
         | SOME (SOME vs) => SOME (SOME (a::vs)))
    | _ => SOME NONE (* error *)
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
    let vs = MAP (eval_wh_to (k-1)) xs in
      case p of
      | Cons s => wh_Constructor s xs
      | Proj s i =>
        (if LENGTH xs ≠ 1 then wh_Error else
           case HD vs of
           | wh_Constructor t ys => if t = s ∧ i < LENGTH ys
                                     then eval_wh_to (k-1) (EL i ys)
                                     else wh_Error
           | wh_Diverge => wh_Diverge
           | _ => wh_Error)
      | IsEq s i =>
        (if LENGTH xs ≠ 1 then wh_Error else
           case HD vs of
           | wh_Constructor t ys => if t ≠ s then wh_Constructor "False" [] else
                                    if i = LENGTH ys then wh_Constructor "True" []
                                                     else wh_Error
           | wh_Diverge => wh_Diverge
           | _ => wh_Error)
      | Lit l => (if xs = [] then wh_Atom l else wh_Error)
      | If =>
        (if LENGTH xs ≠ 3 then wh_Error else
           case HD vs of
           | wh_Constructor t ys =>
              (if t = "True" ∧ ys = [] then EL 1 vs else
               if t = "False" ∧ ys = [] then EL 2 vs else wh_Error)
           | wh_Diverge => wh_Diverge
           | _ => wh_Error)
      | AtomOp a =>
        (case get_atoms vs of
         | NONE => wh_Diverge
         | SOME NONE => wh_Error
         | SOME (SOME as) =>
             case config.parAtomOp a as of SOME v => wh_Atom v | NONE => wh_Error)
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λ(k,x).(k,(exp_size x)))`
End

Definition eval_wh_def:
  eval_wh e =
    case some k. eval_wh_to k e ≠ wh_Diverge of
    | SOME k => eval_wh_to k e
    | NONE => wh_Diverge
End

Theorem eval_wh_eq_Diverge:
  eval_wh e = wh_Diverge ⇔ ∀k. eval_wh_to k e = wh_Diverge
Proof
  fs [eval_wh_def] \\ DEEP_INTRO_TAC some_intro
  \\ rw [] \\ metis_tac []
QED

Theorem eval_wh_neq_Diverge:
  eval_wh e ≠ wh_Diverge ⇔ ∃k. eval_wh_to k e ≠ wh_Diverge
Proof
  fs [eval_wh_eq_Diverge]
QED

Theorem eval_wh_inc:
  ∀m e n.
    eval_wh_to n e ≠ wh_Diverge ∧ n ≤ m ⇒
    eval_wh_to m e = eval_wh_to n e
Proof
  recInduct eval_wh_to_ind \\ rw []
  \\ fs [eval_wh_to_def]
  THEN1
   (Cases_on ‘eval_wh_to n x = wh_Diverge’ \\ fs []
    \\ first_x_assum drule_all \\ fs []
    \\ TOP_CASE_TAC \\ PairCases_on ‘x'’ \\ fs []
    \\ Cases_on ‘n = 0’ \\ fs [])
  THEN1 (Cases_on ‘n = 0’ \\ fs [])
  \\ Cases_on ‘∃s. p = Cons s’ \\ gvs []
  THEN1 (rw [] \\ fs [])
  \\ Cases_on ‘∃s. p = Lit s’ \\ gvs []
  THEN1 (rw [] \\ fs [])
  \\ Cases_on ‘∃s. p = If’ \\ gvs []
  THEN1
   (Cases_on ‘n = 0’ \\ fs []
    \\ Cases_on ‘LENGTH xs = 3’ \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ first_assum (qspec_then ‘h’ assume_tac) \\ fs []
    \\ ‘n-1 ≤ k-1’ by fs []
    \\ first_x_assum (first_assum o mp_then (Pos last) mp_tac)
    \\ Cases_on ‘eval_wh_to (n − 1) h’ \\ fs []
    \\ first_assum (qspec_then ‘h'’ assume_tac) \\ fs []
    \\ first_x_assum (qspec_then ‘h''’ assume_tac) \\ fs []
    \\ ‘n-1 ≤ k-1’ by fs []
    \\ rpt (first_x_assum (first_assum o mp_then (Pos last) mp_tac))
    \\ rw [] \\ gvs [])
  \\ Cases_on ‘∃s. p = AtomOp s’ \\ gvs []
  THEN1
   (Cases_on ‘n = 0’ \\ fs []
    \\ rpt AP_THM_TAC \\ AP_TERM_TAC
    \\ fs [PULL_FORALL,AND_IMP_INTRO]
    \\ ‘n-1 ≤ k-1’ by fs []
    \\ rpt (first_x_assum (first_assum o mp_then (Pos last) mp_tac))
    \\ Cases_on ‘get_atoms (MAP (λa. eval_wh_to (n − 1) a) xs) = NONE’ \\ fs []
    \\ pop_assum mp_tac \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [] \\ rw []
    \\ first_assum (qspec_then ‘h’ mp_tac) \\ strip_tac \\ fs []
    \\ Cases_on ‘eval_wh_to (n − 1) h’ \\ fs [get_atoms_def]
    \\ Cases_on ‘get_atoms (MAP (λa. eval_wh_to (n − 1) a) xs')’ \\ fs [])
  \\ Cases_on ‘∃s i. p = Proj s i’
  THEN1
   (Cases_on ‘n = 0’ \\ gvs []
    \\ Cases_on ‘LENGTH xs = 1’ \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ ‘n-1 ≤ k-1’ by fs []
    \\ rpt (first_x_assum (first_assum o mp_then (Pos last) mp_tac))
    \\ Cases_on ‘eval_wh_to (n − 1) h = wh_Diverge’ \\ fs []
    \\ Cases_on ‘eval_wh_to (n − 1) h’ \\ fs []
    \\ rw [] \\ fs [] \\ fs [AllCaseEqs()] \\ gvs [])
  \\ Cases_on ‘∃s i. p = IsEq s i’
  THEN1
   (Cases_on ‘n = 0’ \\ gvs []
    \\ Cases_on ‘LENGTH xs = 1’ \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ ‘n-1 ≤ k-1’ by fs []
    \\ rpt (first_x_assum (first_assum o mp_then (Pos last) mp_tac))
    \\ Cases_on ‘eval_wh_to (n − 1) h = wh_Diverge’ \\ fs [])
  \\ Cases_on ‘p’ \\ fs []
QED

Theorem eval_wh_to_agree:
  eval_wh_to k e ≠ wh_Diverge ∧
  eval_wh_to x e ≠ wh_Diverge ⇒
  eval_wh_to x e = eval_wh_to k e
Proof
  ‘k ≤ x ∨ x ≤ k’ by fs []
  \\ metis_tac [eval_wh_inc]
QED

Theorem eval_wh_eq:
  eval_wh e = v ⇔
    if v = wh_Diverge
    then ∀k. eval_wh_to k e = wh_Diverge
    else ∃k. eval_wh_to k e = v
Proof
  rw [] THEN1 fs [eval_wh_eq_Diverge]
  \\ eq_tac \\ rw []
  THEN1
   (fs [eval_wh_neq_Diverge]
    \\ qexists_tac ‘k’ \\ fs []
    \\ fs [eval_wh_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ match_mp_tac eval_wh_to_agree \\ fs [])
  THEN1
   (fs [eval_wh_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ match_mp_tac eval_wh_to_agree \\ fs [])
QED

Theorem eval_wh_Bottom:
  eval_wh Bottom = wh_Diverge
Proof
  fs [eval_wh_eq_Diverge,Bottom_def]
  \\ completeInduct_on ‘k’ \\ Cases_on ‘k’ \\ simp [Once eval_wh_to_def]
  \\ fs [subst_funs_def,bind_def,FUPDATE_LIST,FLOOKUP_DEF,closed_def,subst_def]
QED

Theorem eval_wh_Var:
  eval_wh (Var s) = wh_Error
Proof
  fs [eval_wh_eq,eval_wh_to_def]
QED

Theorem eval_wh_Lam:
  eval_wh (Lam s x) = wh_Closure s x
Proof
  fs [eval_wh_eq,eval_wh_to_def]
QED

Theorem eval_wh_App:
  eval_wh (App x y) =
     let v = eval_wh x in
       if v = wh_Diverge then wh_Diverge else
         case dest_wh_Closure v of
           NONE => wh_Error
         | SOME (s,body) => eval_wh (bind s y body)
Proof
  fs [] \\ Cases_on ‘eval_wh x = wh_Diverge’ \\ fs []
  THEN1 (fs [eval_wh_eq] \\ fs [eval_wh_to_def])
  \\ Cases_on ‘eval_wh x’ \\ fs [dest_wh_Closure_def]
  \\ TRY (fs [eval_wh_eq] \\ fs [eval_wh_to_def]
          \\ qexists_tac ‘k’ \\ fs [dest_wh_Closure_def] \\ NO_TAC)
  \\ fs [eval_wh_eq] \\ fs [eval_wh_to_def]
  \\ IF_CASES_TAC
  THEN1
   (rw [] \\ fs []
    \\ ‘eval_wh_to k x ≠ wh_Diverge’ by fs []
    \\ drule eval_wh_to_agree \\ pop_assum kall_tac
    \\ disch_then drule \\ fs [dest_wh_Closure_def])
  \\ fs []
  \\ qexists_tac ‘k+k'+1’ \\ fs []
  \\ ‘eval_wh_to (k+k'+1) x = eval_wh_to k x’ by (match_mp_tac eval_wh_inc \\ fs [])
  \\ fs [dest_wh_Closure_def,PULL_EXISTS]
  \\ qexists_tac ‘k+k'’ \\ fs []
  \\ ‘k' ≤ k + k'’ by fs []
  \\ metis_tac [eval_wh_inc]
QED

Theorem eval_wh_Letrec:
  eval_wh (Letrec f y) = eval_wh (subst_funs f y)
Proof
  fs [Once eval_wh_eq] \\ IF_CASES_TAC
  \\ fs [eval_wh_eq_Diverge,eval_wh_to_def]
  \\ qexists_tac ‘k+1’ \\ fs []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [eval_wh_eq] \\ qexists_tac ‘k’ \\ fs []
QED

Theorem eval_wh_Cons:
  eval_wh (Cons s xs) = wh_Constructor s xs
Proof
  fs [Once eval_wh_eq,eval_wh_to_def]
  \\ qexists_tac ‘1’ \\ fs []
QED

Theorem eval_wh_Lit:
  eval_wh (Lit l) = wh_Atom l
Proof
  fs [Once eval_wh_eq,eval_wh_to_def]
  \\ qexists_tac ‘1’ \\ fs []
QED

Theorem eval_wh_Fail:
  eval_wh Fail = wh_Error
Proof
  fs [Once eval_wh_eq,eval_wh_to_def]
  \\ qexists_tac ‘1’ \\ fs []
QED

Theorem eval_wh_If:
  eval_wh (If x y z) =
    if eval_wh x = wh_Diverge                then wh_Diverge else
    if eval_wh x = wh_Constructor "True" []  then eval_wh y  else
    if eval_wh x = wh_Constructor "False" [] then eval_wh z  else wh_Error
Proof
  fs [] \\ Cases_on ‘eval_wh x = wh_Diverge’ \\ fs []
  THEN1 (fs [eval_wh_eq] \\ fs [eval_wh_to_def])
  \\ Cases_on ‘eval_wh x’ \\ fs []
  \\ TRY (fs [eval_wh_eq] \\ fs [eval_wh_to_def]
          \\ qexists_tac ‘k+1’ \\ fs [] \\ NO_TAC)
  \\ fs [eval_wh_eq] \\ fs [eval_wh_to_def]
  \\ reverse (Cases_on ‘l=[]’) \\ gvs []
  THEN1 (qexists_tac ‘k+1’ \\ fs [])
  \\ Cases_on ‘s ≠ "True" ∧ s ≠ "False"’
  THEN1 (fs [] \\ qexists_tac ‘k+1’ \\ fs [])
  \\ gvs [] \\ rename [‘eval_wh q = wh_Diverge’]
  \\ (Cases_on ‘eval_wh q = wh_Diverge’ \\ fs []
      THEN1
       (Cases \\ fs []
        \\ Cases_on ‘eval_wh_to n x = wh_Diverge’ \\ fs []
        \\ ‘eval_wh_to n x = eval_wh_to k x’ by (irule eval_wh_to_agree \\ fs [])
        \\ gvs [] \\ fs [eval_wh_eq])
      \\ fs [eval_wh_eq]
      \\ qexists_tac ‘k+k'+1’ \\ fs []
      \\ ‘eval_wh_to (k+k') x = eval_wh_to k x’ by (match_mp_tac eval_wh_inc \\ fs [])
      \\ ‘eval_wh_to (k+k') q = eval_wh_to k' q’ by (match_mp_tac eval_wh_inc \\ fs [])
      \\ fs [] \\ qexists_tac ‘k'’ \\ fs [])
QED

Theorem eval_wh_IsEq:
  eval_wh (IsEq s i x) =
    case eval_wh x of
    | wh_Constructor t ys => if t ≠ s then wh_Constructor "False" []
                             else if i = LENGTH ys then wh_Constructor "True" []
                             else wh_Error
    | wh_Diverge => wh_Diverge
    | _ => wh_Error
Proof
  fs [] \\ Cases_on ‘eval_wh x = wh_Diverge’ \\ fs []
  THEN1 (fs [eval_wh_eq] \\ fs [eval_wh_to_def])
  \\ Cases_on ‘eval_wh x’ \\ fs []
  \\ TRY (fs [eval_wh_eq] \\ fs [eval_wh_to_def]
          \\ qexists_tac ‘k+1’ \\ fs [] \\ NO_TAC)
  \\ fs [eval_wh_eq] \\ fs [eval_wh_to_def]
  \\ fs [AllCaseEqs()]
  \\ qexists_tac ‘k+1’ \\ fs []
  \\ CCONTR_TAC \\ fs [] \\ gvs []
QED

Theorem eval_wh_Proj:
  eval_wh (Proj s i x) =
    case eval_wh x of
    | wh_Constructor t ys => if t = s ∧ i < LENGTH ys
                             then eval_wh (EL i ys) else wh_Error
    | wh_Diverge => wh_Diverge
    | _ => wh_Error
Proof
  fs [] \\ Cases_on ‘eval_wh x = wh_Diverge’ \\ fs []
  THEN1 (fs [eval_wh_eq] \\ fs [eval_wh_to_def])
  \\ Cases_on ‘eval_wh x’ \\ fs []
  \\ TRY (fs [eval_wh_eq] \\ fs [eval_wh_to_def]
          \\ qexists_tac ‘k+1’ \\ fs [] \\ NO_TAC)
  \\ fs [eval_wh_eq] \\ fs [eval_wh_to_def]
  \\ Cases_on ‘s ≠ s'’ \\ gvs []
  THEN1 (qexists_tac ‘k+1’ \\ fs [])
  \\ Cases_on ‘LENGTH l ≤ i’ \\ fs []
  THEN1 (qexists_tac ‘k+1’ \\ fs [])
  \\ IF_CASES_TAC
  THEN1
   (Cases \\ fs [GSYM NOT_LESS] \\ fs [eval_wh_eq]
    \\ Cases_on ‘eval_wh_to n x = wh_Diverge’ \\ fs []
    \\ ‘eval_wh_to k x = eval_wh_to n x’ by
      (match_mp_tac eval_wh_to_agree \\ fs [])
    \\ fs [])
  \\ fs [eval_wh_eq]
  \\ qexists_tac ‘k+k'+1’ \\ fs []
  \\ ‘eval_wh_to (k + k') x = eval_wh_to k x’ by (irule eval_wh_inc \\ fs [])
  \\ ‘eval_wh_to (k + k') (EL i l) =
      eval_wh_to k' (EL i l)’ by (irule eval_wh_inc \\ fs [])
  \\ fs [] \\ qexists_tac ‘k+k'’ \\ fs []
QED

Theorem eval_wh_thm:
  eval_wh (Var s) = wh_Error ∧
  eval_wh (Lam s x) = wh_Closure s x ∧
  eval_wh (App x y) =
    (let v = eval_wh x in
       if v = wh_Diverge then wh_Diverge else
         case dest_wh_Closure v of
           NONE => wh_Error
         | SOME (s,body) => eval_wh (bind s y body)) ∧
  eval_wh (Letrec f y) = eval_wh (subst_funs f y) ∧
  eval_wh (Cons s xs) = wh_Constructor s xs ∧
  eval_wh (Lit l) = wh_Atom l ∧
  eval_wh (If x y z) =
    (if eval_wh x = wh_Diverge                then wh_Diverge else
     if eval_wh x = wh_Constructor "True" []  then eval_wh y  else
     if eval_wh x = wh_Constructor "False" [] then eval_wh z  else wh_Error) ∧
  eval_wh (IsEq s i x) =
    (case eval_wh x of
     | wh_Constructor t ys => if t ≠ s then wh_Constructor "False" []
                              else if i = LENGTH ys then wh_Constructor "True" []
                              else wh_Error
     | wh_Diverge => wh_Diverge
     | _ => wh_Error) ∧
  eval_wh Fail = wh_Error ∧
  eval_wh Bottom = wh_Diverge
Proof
  fs [eval_wh_Lam,eval_wh_Var,eval_wh_App,eval_wh_Letrec,eval_wh_Cons,
      eval_wh_Bottom,eval_wh_Lit,eval_wh_Fail,eval_wh_If,eval_wh_IsEq]
QED

(* unlimitied evaluation *)

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

Definition eval_def:
  eval x = v_unfold eval_wh x
End

Definition dest_Closure_def:
  dest_Closure x =
    case x of Closure s x => SOME (s,x) | _ => NONE
End

Theorem dest_Closure_Closure[simp]:
  dest_Closure (Closure s x) = SOME (s,x)
Proof
  fs [dest_Closure_def]
QED

Theorem dest_Closure_Closure_IMP:
  dest_Closure v = SOME (s,x) ⇒ v = Closure s x
Proof
  rw [] \\ Cases_on ‘v’ \\ gs[dest_Closure_def]
QED

Overload True  = “Constructor "True" []”;
Overload False = “Constructor "False" []”;

Definition el_def:
  el s i x =
    if x = Diverge then Diverge else
      case x of
      | Constructor t xs =>
          if s = t ∧ i < LENGTH xs then EL i xs
          else Error
      | _ => Error
End

Definition is_eq_def:
  is_eq s n x =
    if x = Diverge then Diverge else
      case x of
        Constructor t xs =>
          if s = t then
            (if n = LENGTH xs then True else Error)
          else False
      | _ => Error
End

Theorem eval_App:
  eval (App x y) =
    (let v = eval x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (s,body) => eval (bind s y body))
Proof
  simp [eval_def,Once v_unfold,eval_wh_thm]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once v_unfold,eval_wh_thm]
  \\ Cases_on ‘eval_wh x’ \\ fs [dest_wh_Closure_def]
  \\ simp [Once v_unfold,eval_wh_thm,dest_wh_Closure_def,dest_Closure_def]
  \\ simp [Once v_unfold,eval_wh_thm,dest_wh_Closure_def,dest_Closure_def]
QED

Theorem eval_Bottom:
  eval Bottom = Diverge
Proof
  simp [eval_def,Once v_unfold,eval_wh_thm]
QED

Theorem eval_Fail:
  eval Fail = Error
Proof
  simp [eval_def,Once v_unfold,eval_wh_thm]
QED

Theorem eval_Var:
  eval (Var s) = Error
Proof
  simp [eval_def,Once v_unfold,eval_wh_thm]
QED

Theorem eval_Cons:
  eval (Cons s xs) = Constructor s (MAP eval xs)
Proof
  simp [eval_def,Once v_unfold,eval_wh_thm,MAP_EQ_f]
QED

Theorem eval_Lam:
  eval (Lam s x) = Closure s x
Proof
  simp [eval_def,Once v_unfold,eval_wh_thm]
QED

Theorem eval_Letrec:
  eval (Letrec f x) = eval (subst_funs f x)
Proof
  simp [eval_def,eval_wh_thm] \\ once_rewrite_tac [v_unfold] \\ fs [eval_wh_thm]
QED

Theorem eval_IsEq:
  eval (IsEq s n x) = is_eq s n (eval x)
Proof
  simp [eval_def,is_eq_def]
  \\ once_rewrite_tac [v_unfold]
  \\ Cases_on ‘eval_wh x’ \\ fs [eval_wh_IsEq]
  \\ rw [] \\ fs []
QED

Theorem eval_Proj:
  eval (Proj s i x) = el s i (eval x)
Proof
  simp [eval_def,el_def]
  \\ once_rewrite_tac [v_unfold]
  \\ Cases_on ‘eval_wh x’ \\ fs [eval_wh_Proj,EL_MAP]
  \\ Cases_on ‘s ≠ s'’ \\ gvs []
  \\ Cases_on ‘i < LENGTH l’ \\ gvs []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once v_unfold]
QED

Theorem eval_Lit:
  eval (Lit l) = Atom l
Proof
  simp [eval_def,Once v_unfold,eval_wh_thm]
QED

Theorem eval_Let:
  eval (Let s x y) = eval (bind s x y)
Proof
  fs [eval_App,eval_Lam]
QED

Theorem eval_If:
  eval (If x y z) =
     if eval x = Diverge then Diverge else
     if eval x = True    then eval y  else
     if eval x = False   then eval z  else Error
Proof
  simp [eval_def]
  \\ once_rewrite_tac [v_unfold]
  \\ Cases_on ‘eval_wh x’ \\ fs [eval_wh_If]
  \\ Cases_on ‘l=[]’ \\ gvs []
  \\ rw [] \\ fs []
QED

Theorem eval_thm:
  eval Fail = Error ∧
  eval Bottom = Diverge ∧
  eval (Var s) = Error (* free variables are not allowed *) ∧
  eval (Cons s xs) = Constructor s (MAP eval xs) ∧
  eval (IsEq s n x) = is_eq s n (eval x) ∧
  eval (Proj s i x) = el s i (eval x) ∧
  eval (Lit l) = Atom l ∧
  eval (Let s x y) = eval (bind s x y) ∧
  eval (If x y z) =
    (if eval x = Diverge then Diverge  else
     if eval x = True    then eval y else
     if eval x = False   then eval z else Error) ∧
  eval (Lam s x) = Closure s x ∧
  eval (Letrec f x) = eval (subst_funs f x) ∧
  eval (App x y) =
    (let v = eval x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (s,body) => eval (bind s y body))
Proof
  fs [eval_App,eval_Fail,eval_Bottom,eval_Var,eval_Cons,eval_Lam,eval_Letrec,
      eval_If,eval_Proj,eval_IsEq,eval_Lit]
QED

val _ = export_theory();
