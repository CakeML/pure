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
    | _ => wh_Error (* TODO: fill in rest *)
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λ(k,x).(k,(exp_size x)))`
End

Definition eval_wh_def:
  eval_wh e =
    case some k. eval_wh_to k e ≠ wh_Diverge of
    | SOME k => eval_wh_to k e
    | NONE => wh_Diverge
End

(* TODO: prove clock-free equations for eval_wh *)

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

Theorem eval_thm:
  eval (Fail)  = Error ∧
  eval (Var s) = Error (* free variables are not allowed *) ∧
  eval (Cons s xs) = Constructor s (MAP eval xs) ∧
  eval (IsEq s n x) = is_eq s n (eval x) ∧
  eval (Proj s i x) = el s i (eval x) ∧
  eval (Let s x y) = eval (bind s x y) ∧
  eval (If x y z) = (
       if eval x = Diverge then Diverge  else
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
  cheat (* TODO *)
QED

val _ = export_theory();
