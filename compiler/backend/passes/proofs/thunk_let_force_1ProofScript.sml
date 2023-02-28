(*
  This transformation allows rewriting

     Force (Var n)    into    Var m

  inside ‘body’ in expressions such as

     Let (SOME m) (Force (Var n)) body

*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory arithmeticTheory;
open pure_miscTheory thunkLangPropsTheory thunk_cexpTheory
     thunk_let_forceProofTheory thunk_exp_ofTheory;

val _ = new_theory "thunk_let_force_1Proof";

val _ = set_grammar_ancestry ["thunk_let_forceProof","thunk_cexp",
                              "finite_map", "pred_set", "rich_list",
                              "thunkLang", "wellorder", "quotient_sum",
                              "quotient_pair", "thunkLangProps", "thunk_exp_of"];

Overload safe_itree = “pure_semantics$safe_itree”

val _ = numLib.prefer_num ();

Definition d_Var_def[simp]:
  d_Var (Var n : thunk_cexp$cexp) = SOME n ∧
  d_Var _ = NONE
End

Definition d_Force_Var_def:
  d_Force_Var v (Force x) =
    (case d_Var x of NONE => NONE | SOME n => if n ≠ v then SOME n else NONE) ∧
  d_Force_Var v _ = NONE
End

Definition can_keep_def:
  can_keep m (a,b) ⇔ m ≠ a ∧ m ≠ b:mlstring
End

Definition let_force_def:
  let_force (m:(mlstring # mlstring) list) ((Var v):thunk_cexp$cexp) = Var v:thunk_cexp$cexp∧
  let_force m (Let opt x y) =
    (case opt of
     | NONE => Let opt (let_force m x) (let_force m y)
     | SOME v =>
       case d_Force_Var v x of
       | NONE => Let opt (let_force m x) (let_force (FILTER (can_keep v) m) y)
       | SOME w =>
         let m1 = FILTER (can_keep v) m in
           case ALOOKUP m w of
           | SOME t => Let opt (Var t) (let_force m1 y)
           | NONE => Let opt x (let_force ((w,v)::m1) y)) ∧
  let_force m (Lam vs x) = Lam vs (let_force [] x) ∧
  let_force m (App x xs) = App (let_force m x) (MAP (let_force m) xs) ∧
  let_force m (Delay x) = Delay (let_force m x) ∧
  let_force m (Force x) =
    (case d_Var x of
     | NONE => Force (let_force m x)
     | SOME v => case ALOOKUP m v of
                 | NONE => Force (let_force m x)
                 | SOME t => Var t) ∧
  let_force m (Box x) = Box (let_force m x) ∧
  let_force m (Letrec fs x) =
    Letrec (MAP (λ(n,x). (n,let_force [] x)) fs) (let_force [] x) ∧
  let_force m (Case v rows d) =
    Case v (MAP (λ(n,p,x). (n,p,let_force m x)) rows)
      (case d of NONE => NONE | SOME (a,e) => SOME (a,let_force m e)) ∧
  let_force m (Prim p xs) = Prim p (MAP (let_force m) xs)
Termination
  WF_REL_TAC ‘measure $ cexp_size o SND’
End

Definition simp_let_force_def:
  simp_let_force e = let_force [] e
End

Definition dest_Var_def[simp]:
  dest_Var (Var n:lhs) = n
End

Triviality MAP_filter_clash_NONE:
  ∀m. MAP (filter_clash NONE) m = m
Proof
  Induct \\ fs [filter_clash_def,name_clash_def]
QED

Theorem let_force_thm:
  ∀m x.
    EVERY (λm. ∀n x. m = SOME (n,x) ⇒ ∃v. n = Var v) m ⇒
    e_rel m (exp_of x)
            (exp_of (let_force (MAP (λ(x,n). (implode (dest_Var x),implode n))
                        (MAP THE (FILTER IS_SOME m))) x))
Proof

  rpt gen_tac \\ qid_spec_tac ‘m’ \\ qid_spec_tac ‘x’
  \\ ho_match_mp_tac (cns_arities_ind |> SIMP_RULE std_ss [])
  \\ rpt conj_tac \\ rpt gen_tac
  >~ [‘Var’] >-
   (fs [let_force_def,e_rel_Var])
  >~ [‘Delay’] >-
   (fs [let_force_def] \\ rw [] \\ irule e_rel_Delay
    \\ first_x_assum irule \\ fs [])
  >~ [‘Box’] >-
   (fs [let_force_def] \\ rw [] \\ irule e_rel_Box
    \\ first_x_assum irule \\ fs [])
  >~ [‘Force’] >-
   (rw [] \\ fs [let_force_def]
    \\ CASE_TAC \\ gvs []
    >- (irule e_rel_Force \\ res_tac \\ fs [])
    \\ CASE_TAC \\ gvs []
    >- (irule e_rel_Force \\ res_tac \\ fs [])
    \\ gvs [d_Var_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
    \\ imp_res_tac ALOOKUP_MEM
    \\ gvs [MEM_MAP,MEM_FILTER]
    \\ gvs [IS_SOME_EXISTS,UNCURRY]
    \\ gvs [EVERY_MEM] \\ res_tac \\ fs []
    \\ PairCases_on ‘x’ \\ gvs []
    \\ irule e_rel_Force_Var \\ fs [])
  >~ [‘Let opt’] >-
   (Cases_on ‘opt’ \\ fs []
    >-
     (rw [] \\ simp [let_force_def]
      \\ irule e_rel_Let \\ res_tac \\ fs [MAP_filter_clash_NONE])
    \\ rw [] \\ simp [let_force_def]
    \\ CASE_TAC \\ fs []
    >- (irule e_rel_Let \\ res_tac \\ fs []
        \\ first_x_assum $ qspec_then ‘MAP (filter_clash (SOME (explode x))) m’ mp_tac
        \\ impl_tac >-
         (qpat_x_assum ‘EVERY _ _’ mp_tac
          \\ qid_spec_tac ‘m’ \\ Induct
          \\ fs [filter_clash_def])
        \\ match_mp_tac (METIS_PROVE [] “b = c ⇒ (b ⇒ c)”)
        \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
        \\ qpat_x_assum ‘EVERY _ _’ mp_tac
        \\ qid_spec_tac ‘m’ \\ Induct
        \\ fs []
        \\ Cases \\ fs [filter_clash_def]
        \\ rename [‘name_clash _ (SOME t)’] \\ PairCases_on ‘t’ \\ gvs []
        \\ strip_tac
        \\ gvs [name_clash_def,can_keep_def]
        \\ rpt (IF_CASES_TAC \\ gvs []))
    \\ rename [‘d_Force_Var _ xx’] \\ Cases_on ‘xx’ \\ fs [d_Force_Var_def]
    \\ gvs [d_Var_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
    \\ CASE_TAC \\ fs []
    >- (irule e_rel_Let_Force_Var \\ res_tac \\ fs []
        \\ rename [‘let_force ((a,b)::_)’]
        \\ first_x_assum $ qspec_then ‘SOME (Var (explode a), explode b) ::
                                       MAP (filter_clash (SOME (explode b))) m’ mp_tac
        \\ impl_tac >-
         (qpat_x_assum ‘EVERY _ _’ mp_tac
          \\ qid_spec_tac ‘m’ \\ Induct
          \\ fs [filter_clash_def])
        \\ match_mp_tac (METIS_PROVE [] “b = c ⇒ (b ⇒ c)”)
        \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
        \\ fs []
        \\ qpat_x_assum ‘EVERY _ _’ mp_tac
        \\ qid_spec_tac ‘m’ \\ Induct
        \\ gvs [name_clash_def,can_keep_def]
        \\ Cases \\ fs [filter_clash_def]
        \\ rename [‘name_clash _ (SOME t)’] \\ PairCases_on ‘t’ \\ gvs []
        \\ strip_tac
        \\ gvs [name_clash_def,can_keep_def]
        \\ rpt (IF_CASES_TAC \\ gvs []))
    \\ irule e_rel_Let \\ res_tac \\ fs []
    \\ conj_tac
    >-
     (irule e_rel_Force_Var
      \\ imp_res_tac ALOOKUP_MEM \\ gvs [MEM_MAP,MEM_FILTER]
      \\ gvs [IS_SOME_EXISTS]
      \\ rename [‘(_,_) = _ aa’] \\ PairCases_on ‘aa’ \\ gvs [EVERY_MEM]
      \\ res_tac \\ gvs [])
    \\ first_x_assum $ qspec_then ‘MAP (filter_clash (SOME (explode x))) m’ mp_tac
    \\ impl_tac >-
     (qpat_x_assum ‘EVERY _ _’ mp_tac
      \\ qid_spec_tac ‘m’ \\ Induct
      \\ fs [filter_clash_def])
    \\ match_mp_tac (METIS_PROVE [] “b = c ⇒ (b ⇒ c)”)
    \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ qpat_x_assum ‘EVERY _ _’ mp_tac
    \\ qid_spec_tac ‘m’ \\ Induct
    \\ fs []
    \\ Cases \\ fs [filter_clash_def]
    \\ rename [‘name_clash _ (SOME t)’] \\ PairCases_on ‘t’ \\ gvs []
    \\ strip_tac
    \\ gvs [name_clash_def,can_keep_def]
    \\ rpt (IF_CASES_TAC \\ gvs []))

  \\ cheat
QED

Theorem simp_let_force_thm:
  e_rel [] (exp_of x) (exp_of (simp_let_force x))
Proof
  qspec_then ‘[]’ mp_tac let_force_thm
  \\ fs [simp_let_force_def]
QED

val _ = export_theory ();
