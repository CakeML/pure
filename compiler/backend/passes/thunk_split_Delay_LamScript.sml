(*
  TBD
*)

open HolKernel Parse boolLib bossLib term_tactic pairTheory listTheory;
open thunk_cexpTheory mlmapTheory mlstringTheory pred_setTheory var_setTheory;

val _ = new_theory "thunk_split_Delay_Lam";

Definition dest_Delay_Lam_def:
    (dest_Delay_Lam (Delay (Lam v e)) = SOME (Lam v e)) /\
    (dest_Delay_Lam _ = NONE)
End

Definition letrec_split_def:
    (letrec_split [] var_creator maps = ([], var_creator, maps)) /\
    (letrec_split ((name, expr)::list) var_creator maps =
        case dest_Delay_Lam expr of
            | SOME e =>
                let (name2, var_creator) = invent_var name var_creator in
                  let (l, vc, maps) = letrec_split list var_creator
                                                   (mlmap$insert maps name name2) in
                ((name2, e)::(name, Delay (Var name2))::l, vc, maps)
            | NONE =>
                let (l, vc, maps) = letrec_split list var_creator (delete maps name) in
                  ((name, expr)::l, vc, maps))
End

Theorem MEM_letrec_split:
  ∀binds binds' vc m. MEM (v, e) binds' ∧ binds' = FST (letrec_split binds vc m) ⇒
               MEM (Delay e) (MAP SND binds) ∨ MEM e (MAP SND binds) ∨ (∃v. e = Delay (Var v))
Proof
  Induct \\ gvs [letrec_split_def, FORALL_PROD]
  \\ gen_tac \\ Cases \\ gvs [dest_Delay_Lam_def]
  \\ rw [] \\ pairarg_tac \\ gvs [is_Lam_def]
  \\ rename1 ‘letrec_split _ (vc1, vc2) maps = _’
  \\ last_assum $ qspecl_then [‘vc1’, ‘vc2’, ‘maps’] assume_tac \\ gvs []
  \\ rename1 ‘dest_Delay_Lam (Delay c)’
  \\ Cases_on ‘dest_Delay_Lam (Delay c)’ \\ gs []
  \\ pairarg_tac \\ gvs []
  \\ Cases_on ‘c’ \\ gs [dest_Delay_Lam_def]
  \\ pairarg_tac \\ gvs []
  \\ last_x_assum $ qspecl_then [‘FST var_creator'’, ‘SND var_creator'’, ‘insert m p_1 name2’] assume_tac
  \\ gvs []
QED

Theorem MEM_cexp6_size:
  ∀binds p. MEM p binds ⇒ cexp_size (SND p) < cexp6_size binds
Proof
  Induct \\ gvs [cexp_size_def, FORALL_PROD]
  \\ rw []
  >- gvs []
  \\ last_x_assum $ dxrule_then assume_tac \\ gvs []
QED

Definition split_Delayed_Lam_def:
    (split_Delayed_Lam (Var v) var_creator maps = (Var v, var_creator)) /\
    (split_Delayed_Lam (thunk_cexp$App e1 e2) var_creator maps =
        let (e1', vc) = split_Delayed_Lam e1 var_creator maps in
          let (e2', vc) = FOLDR (λe (l, vc).
                                   let (e', vc) = split_Delayed_Lam e vc maps in
                                     (e'::l, vc)) ([], vc) e2 in
            (App e1' e2', vc)) /\
    (split_Delayed_Lam (Lam v e) var_creator maps =
        let (e', vc) = split_Delayed_Lam e var_creator (FOLDL delete maps v) in
        (Lam v e', vc)) /\
    (split_Delayed_Lam (thunk_cexp$Letrec binds expr) var_creator maps =
        let (binds', vc, maps2) = letrec_split binds var_creator maps in
          let (binds', vc) = FOLDR (λ(v, e) (l, vc).
                                      let (e', vc) = split_Delayed_Lam e vc maps2 in
                                          ((v, e')::l, vc)) ([], vc) binds' in
        let (expr', vc) = split_Delayed_Lam expr vc maps2 in
        (Letrec binds' expr', vc)) /\
    (split_Delayed_Lam (Prim op xs) var_creator maps =
     let (xs', vc) = FOLDR (λe (l, vc).
                              let (e', vc) = split_Delayed_Lam e vc maps in
                                (e'::l, vc)) ([], var_creator) xs in
       (Prim op xs', vc)) /\
    (split_Delayed_Lam (Monad mop xs) var_creator maps =
     let (xs', vc) = FOLDR (λe (l, vc).
                              let (e', vc) = split_Delayed_Lam e vc maps in
                                (e'::l, vc)) ([], var_creator) xs in
       (Monad mop xs', vc)) /\
    (split_Delayed_Lam (Let NONE expr1 expr2) var_creator maps =
     let (expr1, vc) = split_Delayed_Lam expr1 var_creator maps in
       let (expr2, vc) = split_Delayed_Lam expr2 vc maps in
         (Let NONE expr1 expr2, vc)) ∧
    (split_Delayed_Lam (Let (SOME name) expr1 expr2) var_creator maps =
        case dest_Delay_Lam expr1 of
            | SOME e =>
                let (name2, vc) = invent_var name var_creator in
                let (e', vc) = split_Delayed_Lam e vc maps in
                let (expr2', vc) = split_Delayed_Lam expr2 vc (insert maps name name2) in
                (Let (SOME name2) e'
                    (Let (SOME name) (Delay (Var name2)) expr2'), vc)
            | NONE =>
                let (expr1', vc) = split_Delayed_Lam expr1 var_creator maps in
                let (expr2', vc) = split_Delayed_Lam expr2 vc (delete maps name) in
                (Let (SOME name) expr1' expr2', vc)) /\
    (split_Delayed_Lam (Delay e) var_creator maps =
        let (e', vc) = split_Delayed_Lam e var_creator maps in
        (Delay e', vc)) /\
    (split_Delayed_Lam (Delay e) var_creator maps =
        let (e', vc) = split_Delayed_Lam e var_creator maps in
        (Delay e', vc)) /\
    (split_Delayed_Lam (Force e) var_creator maps =
        case dest_Var e of
            | SOME v =>
                (case lookup maps v of
                    | NONE => (Force e, var_creator)
                    | SOME v2 => (Var v2, var_creator))
            | NONE =>
                let (e', vc) = split_Delayed_Lam e var_creator maps in
                (Force e', vc)) /\
    (split_Delayed_Lam (thunk_cexp$Case vname list fallthrough) var_creator maps =
     let (fallthrough', vc) = case fallthrough of
                              | NONE => (NONE, var_creator)
                              | SOME (terms, expr) =>
                                  let (expr, vc) = split_Delayed_Lam expr var_creator maps in
                                    (SOME (terms, expr), vc) in
        let (list', vc) = FOLDR (λ(v, vL, expr) (l, vc).
                        let (expr', vc) = split_Delayed_Lam expr vc (FOLDL delete maps vL) in
                          ((v, vL, expr')::l, vc)) ([], vc) list in
        (Case vname list' fallthrough', vc))
Termination
  WF_REL_TAC ‘measure $ (λe. case e of
                             | Var _ => 0
                             | Delay (thunk_cexp$Var v) => 1
                             | _ => cexp_size e) o FST’ \\ rw []
  >~[‘MEM _ _’]
  >- (dxrule_then assume_tac MEM_letrec_split \\ gvs []
      \\ rename1 ‘letrec_split binds var_creator maps'’
      \\ pop_assum $ qspecl_then [‘binds’, ‘var_creator’, ‘maps'’] assume_tac
      \\ Cases_on ‘letrec_split binds var_creator maps'’ \\ gvs [MEM_MAP]
      >- (dxrule_then assume_tac MEM_cexp6_size \\ gvs []
          \\ rename1 ‘cexp_size (SND y) < _’ \\ PairCases_on ‘y’ \\ gvs [cexp_size_def]
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [])
      >- (dxrule_then assume_tac MEM_cexp6_size \\ gvs []
          \\ rename1 ‘cexp_size (SND y) < _’ \\ PairCases_on ‘y’ \\ gvs [cexp_size_def]
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [])
      >- (rename1 ‘cexp_size expr’
          \\ Cases_on ‘expr’ \\ gs [cexp_size_def]))
  >~[‘dest_Delay_Lam _’]
  >- (CASE_TAC \\ gs [] \\ CASE_TAC \\ gs [])
  >~[‘dest_Delay_Lam _’]
  >- (rename1 ‘dest_Delay_Lam expr1’
      \\ Cases_on ‘expr1’ \\ gs [dest_Delay_Lam_def]
      \\ rename1 ‘dest_Delay_Lam (Delay expr1)’
      \\ Cases_on ‘expr1’ \\ gvs [dest_Delay_Lam_def, cexp_size_def])
  >>~[‘MEM _ _’]
  >- (assume_tac cexp_size_lemma \\ gs []
      \\ first_x_assum $ dxrule_then assume_tac
      \\ CASE_TAC \\ gs []
      \\ CASE_TAC \\ gs [])
  >- (assume_tac cexp_size_lemma \\ gs []
      \\ first_x_assum $ dxrule_then assume_tac
      \\ CASE_TAC \\ gs []
      \\ CASE_TAC \\ gs [])
  >- (assume_tac cexp_size_lemma \\ gs []
      \\ first_x_assum $ dxrule_then assume_tac
      \\ CASE_TAC \\ gs []
      \\ CASE_TAC \\ gs [])
  >- (assume_tac cexp_size_lemma \\ gs []
      \\ first_x_assum $ dxrule_then assume_tac
      \\ CASE_TAC \\ gs []
      \\ CASE_TAC \\ gs [])
  \\ CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs [cexp_size_def]
End

Definition split_delated_lam_def:
  split_delated_lam do_it e1 vs =
    if do_it then split_Delayed_Lam e1 vs (empty compare) else (e1,vs)
End

val _ = export_theory ();
