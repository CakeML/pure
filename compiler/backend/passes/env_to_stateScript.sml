(*
  Compiler from envLang to stateLang
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_miscTheory pure_configTheory pure_comp_confTheory
     env_cexpTheory state_cexpTheory
     state_app_unitTheory state_namesTheory;
local open pure_semanticsTheory in end

val _ = new_theory "env_to_state";

val _ = set_grammar_ancestry ["env_cexp", "state_cexp", "pure_comp_conf"];

Definition Letrec_imm_def:
  (Letrec_imm vs ((Var v):env_cexp$cexp) ⇔ MEM v vs) ∧
  (Letrec_imm vs (Lam _ _) ⇔ T) ∧
  (Letrec_imm vs _ ⇔ F)
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

Overload box[local] = “λx. App Ref [True]”
Overload delay[local] = “λx. App Ref [False; Lam NONE x]”
Overload suspend[local] = ``Lam NONE``
Overload trigger[local] = ``λe. app e Unit``

Definition to_state_def:
  to_state ((Var n):env_cexp$cexp) = (Var n):state_cexp$cexp ∧
  to_state (App x y) =
    app (to_state x) (to_state y) ∧
  to_state (Lam v x) =
    Lam (SOME v) (to_state x) ∧
  to_state (Ret x) =
    suspend $ to_state x ∧
  to_state (Raise x) =
    suspend $ Raise $ to_state x ∧
  to_state (Bind x y) =
    suspend $ trigger $ app (to_state y) (trigger $ to_state x) ∧
  to_state (Handle x y) =
    suspend $ trigger $
      HandleApp (to_state y)
        (Let (SOME «v») (trigger $ to_state x) (suspend $ Var «v»)) ∧
  to_state (Act x) =
    suspend $ trigger $ to_state x ∧
  to_state (Length x) =
    suspend $ App Length [to_state x] ∧
  to_state (Alloc x y) =
    suspend $ App Alloc [to_state x; to_state y] ∧
  to_state (Update x y z) =
    suspend $ App Update [to_state x; to_state y; to_state z] ∧
  to_state (Deref x y) =
    suspend $ App Sub [to_state x; to_state y] ∧
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
  to_state (Case v rs d) =
    Case v (MAP (λ(c,vs,y). (c,vs,to_state y)) rs)
           (case d of NONE => NONE | SOME (d,e) => SOME (d,to_state e)) ∧
  to_state (Prim (Cons m) xs) =
    App (Cons m) (MAP to_state xs) ∧
  to_state (Prim (AtomOp b) xs) =
    (let ys = MAP to_state xs in
       case dest_Message b of
       | SOME m => Let (SOME «v») (case ys of [] => Var «v» | (y::_) => y)
                     (suspend $ App (FFI (implode m)) [Var «v»])
       | _ => App (AtomOp b) ys)
Termination
  WF_REL_TAC ‘measure cexp_size’
  \\ fs [] \\ rw []
  \\ (drule_all Letrec_split_MEM_delays ORELSE drule_all Letrec_split_MEM_funs)
  \\ fs []
End

Definition compile_def:
  compile x = app (to_state x) Unit
End

Definition compile_to_state_def:
  compile_to_state (c:compiler_opts) e =
    let x = compile e in
    let y = state_app_unit$optimise_app_unit c.do_app_unit x in
    let z = state_names$give_all_names y in
      z
End

val _ = export_theory ();
