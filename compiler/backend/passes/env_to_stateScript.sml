(*
  Compiler from envLang to stateLang
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_miscTheory pure_configTheory
     env_cexpTheory state_cexpTheory;
local open pure_semanticsTheory in end

val _ = new_theory "env_to_state";

val _ = set_grammar_ancestry ["env_cexp", "state_cexp"];

Definition dest_Message_def:
  dest_Message (Message s) = SOME s ∧
  dest_Message _ = NONE
End

Definition Lets_def:
  Lets [] x = (x:state_cexp$cexp) ∧
  Lets ((v,y)::ys) x = Let v y (Lets ys x)
End

Definition Letrec_imm_def:
  (Letrec_imm vs ((Var v):env_cexp$cexp) ⇔ MEM v vs) ∧
  (Letrec_imm vs (Lam _ _) ⇔ T) ∧
  (Letrec_imm vs _ ⇔ F)
End

Definition dest_Delay_def:
  dest_Delay (Delay x) = SOME (x:env_cexp$cexp) ∧
  dest_Delay _ = NONE
End

Definition dest_Lam_def:
  dest_Lam (Lam v x) = SOME (v,x:env_cexp$cexp) ∧
  dest_Lam _ = NONE
End

Definition Letrec_split_def:
  Letrec_split vs [] = ([],[]) ∧
  Letrec_split vs ((v:mlstring,x)::fns) =
    let (xs,ys) = Letrec_split vs fns in
      case dest_Delay x of
      | SOME y => ((v,Letrec_imm vs y,y)::xs,ys)
      | NONE =>
        case dest_Lam x of
        | SOME (n,z) => (xs,(v,n,z)::ys)
        | NONE => (xs,ys)
End

Definition Bool_def[simp]:
  Bool T = (True  :state_cexp$cexp) ∧
  Bool F = (False :state_cexp$cexp)
End

Definition some_ref_bool_def:
  some_ref_bool (v:mlstring,b,y:state_cexp$cexp) =
    (SOME v, App Ref [Bool b; Bool b])
End

Definition unsafe_update_def:
  unsafe_update (v,b,y) =
    (NONE:mlstring option, App UnsafeUpdate [Var v; IntLit 1; if b then y else Lam NONE y])
End

Triviality Letrec_split_MEM_funs:
  ∀xs delays funs m n x.
    (delays,funs) = Letrec_split ns xs ∧ MEM (m,n,x) funs ⇒
    cexp_size x ≤ list_size (pair_size mlstring_size cexp_size) xs
Proof
  Induct \\ fs [Letrec_split_def]
  \\ PairCases \\ fs [Letrec_split_def] \\ rw []
  \\ pairarg_tac \\ fs []
  \\ gvs [AllCaseEqs()]
  \\ res_tac \\ fs []
  \\ fs [list_size_def,basicSizeTheory.pair_size_def]
  \\ Cases_on ‘h1’ \\ gvs [dest_Lam_def,env_cexpTheory.cexp_size_def]
QED

Triviality Letrec_split_MEM_delays:
  ∀xs delays funs m n x.
    (delays,funs) = Letrec_split ns xs ∧ MEM (m,n,x) delays ⇒
    cexp_size x ≤ list_size (pair_size mlstring_size cexp_size) xs
Proof
  Induct \\ fs [Letrec_split_def]
  \\ PairCases \\ fs [Letrec_split_def] \\ rw []
  \\ pairarg_tac \\ fs []
  \\ gvs [AllCaseEqs()]
  \\ res_tac \\ fs []
  \\ fs [list_size_def,basicSizeTheory.pair_size_def]
  \\ Cases_on ‘h1’ \\ gvs [dest_Delay_def,env_cexpTheory.cexp_size_def]
QED

Overload ret[local] =
  “λx. Let (SOME «v») x
         (Let (SOME «v») (App Ref [False; Lam NONE (Var «v»)]) (Var «v»))”

Overload raw_ret[local] =
  “λx. Let (SOME «v») x (Let (SOME «v») (Var «v») (Var «v»))”

Overload box[local] = “λx. App Ref [True]”
Overload delay[local] = “λx. App Ref [False; Lam NONE x]”

Definition to_state_def:
  to_state ((Var n):env_cexp$cexp) = (Var n):state_cexp$cexp ∧
  to_state (App x y) =
    app (to_state x) (to_state y) ∧
  to_state (Lam v x) =
    Lam (SOME v) (to_state x) ∧
  to_state (Ret x) =
    Let (SOME «v») (to_state x) (Lam NONE (Var «v»)) ∧
  to_state (Raise x) =
    Let (SOME «v») (to_state x) (Lam NONE (Raise (Var «v»))) ∧
  to_state (Bind x y) =
    Lam NONE (app (app (to_state y) (app (to_state x) Unit)) Unit) ∧
  to_state (Handle x y) =
    Lam NONE (app (HandleApp (to_state y)
      (Let (SOME «v») (app (to_state x) Unit) (Lam NONE (Var «v»)))) Unit) ∧
  to_state (Act x) =
    Lam NONE (ret (app (to_state x) Unit)) ∧
  to_state (Length x) =
    Lam NONE (ret (App Length [to_state x])) ∧
  to_state (Alloc x y) =
    Lam NONE (ret (App Alloc [to_state x; delay (to_state y)])) ∧
  to_state (Update x y z) =
    Lam NONE (ret (Handle (App Update [to_state x;
                                       to_state y;
                                       delay (to_state z)])
                     «v» (Raise (delay (Var «v»))))) ∧
  to_state (Deref x y) =
    Lam NONE (raw_ret (Handle (App Sub [to_state x; to_state y])
                        «v» (Raise (delay (Var «v»))))) ∧
  to_state (Box x) =
    App Ref [True; (to_state x)] ∧
  to_state (Delay x) =
    App Ref [False; Lam NONE (to_state x)] ∧
  to_state (Force x) =
    (Let (SOME «v») (to_state x) $
     Let (SOME «v1») (App UnsafeSub [Var «v»; IntLit 0]) $
     Let (SOME «v2») (App UnsafeSub [Var «v»; IntLit 1]) $
       If (Var «v1») (Var «v2») $
         Let (SOME «wh») (app (Var «v2») Unit) $
         Let NONE (App UnsafeUpdate [Var «v»; IntLit 0; True]) $
         Let NONE (App UnsafeUpdate [Var «v»; IntLit 1; Var «wh»]) $
           Var «wh») ∧
  to_state (Letrec xs y) =
    (let (delays,funs) = Letrec_split (MAP FST xs) xs in
     let delays = MAP (λ(m,n,x). (m,n,to_state x)) delays in
     let funs = MAP (λ(m,n,x). (m,n,to_state x)) funs in
       Lets (MAP some_ref_bool delays) $
       Letrec funs $
       Lets (MAP unsafe_update delays) (to_state y)) ∧
  to_state (Let vo x y) =
    Let vo (to_state x) (to_state y) ∧
  to_state (If x y z) =
    If (to_state x) (to_state y) (to_state z) ∧
  to_state (Case x v rs) =
    Case (to_state x) v (MAP (λ(c,vs,y). (c,vs,to_state y)) rs) ∧
  to_state (Prim (Cons m) xs) =
    App (Cons m) (MAP to_state xs) ∧
  to_state (Prim (AtomOp b) xs) =
    (let ys = MAP to_state xs in
       case dest_Message b of
       | SOME m => Let (SOME «v») (case ys of [] => Var «v» | (y::_) => y)
                     (Lam NONE $ App (FFI (implode m)) [Var «v»])
       | _ => App (AtomOp b) ys)
Termination
  WF_REL_TAC ‘measure cexp_size’
  \\ fs [env_cexpTheory.cexp_size_eq] \\ rw []
  \\ (drule_all Letrec_split_MEM_delays ORELSE drule_all Letrec_split_MEM_funs)
  \\ fs []
End

Definition compile_def:
  compile x = app (to_state x) Unit
End

val _ = export_theory ();
