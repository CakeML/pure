(*
  Proof of correctness for the thunk_to_env compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pred_setTheory rich_listTheory thunkLang_primitivesTheory envLangTheory
     finite_mapTheory thunkLangTheory env_semanticsTheory thunk_semanticsTheory;
open thunk_to_envTheory thunk_to_env_1ProofTheory thunk_exp_ofTheory;
open pure_miscTheory thunkLangPropsTheory thunk_cexpTheory;

val _ = new_theory "thunk_to_envProof";

val _ = set_grammar_ancestry ["thunk_to_envProof","thunk_exp_of"]

Definition Lams_def:
  Lams [] x = x ∧
  Lams (y::ys) x = env_cexp$Lam y (Lams ys x)
End

Definition Apps_def:
  Apps x [] = x ∧
  Apps x (y::ys) = Apps (env_cexp$App x y) ys
End

Definition get_arg_def:
  get_arg n [] = env_cexp$Prim (Cons (strlit "")) [] ∧
  get_arg n (x::xs) = if n = 0:num then x else get_arg (n-1) xs
End

Definition remove_Delay_def[simp]:
  remove_Delay (env_cexp$Delay x) = x ∧
  remove_Delay y = y
End

Definition to_env_def:
  to_env ((Var v):thunk_cexp$cexp) = Var v:env_cexp$cexp ∧
  to_env (Let opt x y) = Let opt (to_env x) (to_env y) ∧
  to_env (Lam vs x) = Lams vs (to_env x) ∧
  to_env (App x xs) = Apps (to_env x) (MAP to_env xs) ∧
  to_env (Delay x) = Delay (to_env x) ∧
  to_env (Force x) = Force (to_env x) ∧
  to_env (Box x) = Box (to_env x) ∧
  to_env (Letrec fs x) = Letrec (REVERSE (MAP (λ(n,x). (n,to_env x)) fs)) (to_env x) ∧
  to_env (Case v rows d) = Case v (MAP (λ(n,p,x). (n,p,to_env x)) rows)
                                  (case d of NONE => NONE | SOME e => SOME (to_env e)) ∧
  to_env (Prim p xs) =
    let ys = MAP to_env xs in
      case p of
      | AtomOp a => Prim (AtomOp a) ys
      | Cons n =>
          let y0 = get_arg 0 ys in
          let x0 = remove_Delay (get_arg 0 ys) in
          let x1 = remove_Delay (get_arg 1 ys) in
          let x2 = remove_Delay (get_arg 2 ys) in
            if n = strlit "Ret"    then Ret y0          else
            if n = strlit "Raise"  then Raise y0        else
            if n = strlit "Bind"   then Bind x0 x1      else
            if n = strlit "Handle" then Handle x0 x1    else
            if n = strlit "Act"    then Act x0          else
            if n = strlit "Length" then Length x0       else
            if n = strlit "Alloc"  then Alloc x0 x1     else
            if n = strlit "Deref"  then Deref x0 x1     else
            if n = strlit "Update" then Update x0 x1 x2 else
              Prim (Cons n) ys
Termination
  WF_REL_TAC ‘measure cexp_size’
End

Theorem to_env_exp_of:
  ∀x. cexp_wf x ⇒ exp_rel [] (exp_of x) (exp_of (to_env x))
Proof
  ho_match_mp_tac to_env_ind \\ rw [cexp_wf_def] \\ fs []
  >~ [‘Var’] >-
   (fs [to_env_def]
    \\ irule exp_rel_Var \\ fs [])
  >~ [‘Let’] >-
   (fs [to_env_def]
    \\ Cases_on ‘opt’ \\ fs []
    >- (irule exp_rel_Let_NONE \\ fs [])
    \\ irule exp_rel_Let_SOME \\ fs [])
  >~ [‘Lam’] >-
   (last_x_assum mp_tac \\ fs [to_env_def]
    \\ qid_spec_tac ‘vs’ \\ Induct
    \\ fs [Lams_def] \\ rw [] \\ fs []
    \\ irule exp_rel_Lam \\ fs [])
  >~ [‘App’] >-
   (fs [to_env_def]
    \\ qpat_x_assum ‘EVERY _ _’ mp_tac
    \\ last_x_assum mp_tac
    \\ last_x_assum mp_tac
    \\ last_x_assum mp_tac
    \\ qid_spec_tac ‘x’
    \\ qid_spec_tac ‘xs’
    \\ Induct
    \\ fs [Apps_def] \\ rw [] \\ fs [SF DNF_ss]
    \\ ‘cexp_wf (App x [h])’ by fs [cexp_wf_def]
    \\ last_x_assum drule
    \\ fs [to_env_def,Apps_def]
    \\ disch_then irule
    \\ irule exp_rel_App
    \\ gs [])
  >~ [‘Delay’] >-
   (fs [to_env_def] \\ irule exp_rel_Delay \\ fs [cexp_wf_def])
  >~ [‘Force’] >-
   (fs [to_env_def] \\ irule exp_rel_Force \\ fs [cexp_wf_def])
  >~ [‘Box’] >-
   (fs [to_env_def] \\ irule exp_rel_Box \\ fs [cexp_wf_def])
  >~ [‘Letrec’] >-
   (fs [to_env_def] \\ irule exp_rel_Letrec \\ fs [cexp_wf_def]
    \\ fs [GSYM MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF]
    \\ fs [LIST_REL_MAP_MAP,LAMBDA_PROD]
    \\ irule EVERY2_refl \\ fs [FORALL_PROD,SF SFY_ss,EVERY_MEM])
  >~ [‘Case’] >-
   (fs [to_env_def]
    \\ qpat_x_assum ‘d = NONE ⇒ _’ kall_tac
    \\ qpat_x_assum ‘~(MEM _ _)’ kall_tac
    \\ Induct_on ‘rows’ \\ fs []
    >-
     (fs [rows_of_def,envLangTheory.rows_of_def]
      \\ Cases_on ‘d’ \\ fs []
      \\ simp [Once exp_rel_cases])
    \\ PairCases \\ simp [SF DNF_ss, SF CONJ_ss, AND_IMP_INTRO]
    \\ rw [] \\ fs []
    \\ fs [rows_of_def,envLangTheory.rows_of_def]
    \\ irule exp_rel_If \\ fs []
    \\ conj_tac
    >-
     (irule_at Any exp_rel_Prim \\ fs []
      \\ irule_at Any exp_rel_Var \\ fs [])
    \\ reverse conj_tac
    >- (first_x_assum irule \\ fs [SF SFY_ss])
    \\ qspec_tac (‘LENGTH h1’,‘l’)
    \\ qspec_tac (‘(MAPi (λi v. (i,v)) (MAP explode h1))’,‘xs’)
    \\ Induct \\ fs [FORALL_PROD]
    \\ fs [lets_for_def,envLangTheory.lets_for_def]
    \\ rw []
    \\ irule exp_rel_Let_NONE
    \\ irule_at Any exp_rel_Let_SOME \\ fs []
    \\ irule_at Any exp_rel_Prim \\ fs []
    \\ irule_at Any exp_rel_Var \\ fs []
    \\ irule_at Any exp_rel_If \\ fs []
    \\ irule_at Any exp_rel_Prim \\ fs []
    \\ irule_at Any exp_rel_Var \\ fs []
    \\ rpt (irule_at Any exp_rel_Prim \\ fs []))
  \\ rename [‘Prim’]
  \\ reverse (Cases_on ‘p’)
  >-
   (fs [to_env_def]
    \\ irule exp_rel_Prim
    \\ last_x_assum mp_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [])
  \\ fs [to_env_def,SF ETA_ss]
  \\ fs [args_ok_def]
  \\ rw [] \\ fs [get_arg_def,to_env_def,SF DNF_ss]
  \\ irule exp_rel_Prim \\ fs [] \\ gvs []
  \\ Induct_on ‘xs’ \\ fs []
QED

Theorem to_env_semantics:
  cexp_wf x ∧ closed (exp_of x) ⇒
  itree_of (exp_of x) =
  itree_of (exp_of (to_env x))
Proof
  rw [thunk_semanticsTheory.itree_of_def,env_semanticsTheory.itree_of_def]
  \\ imp_res_tac to_env_exp_of
  \\ drule_all exp_rel_semantics \\ fs []
QED

val _ = export_theory ();
