(*
    Definition of the demands analysis pass
*)

open HolKernel Parse boolLib bossLib term_tactic;
open pure_cexpTheory mlmapTheory mlstringTheory;

val _ = new_theory "pure_demands_analysis";

Datatype:
  da_ctxt =
      | Nil
      | IsFree (vname list) da_ctxt
      | Bind vname (α cexp) da_ctxt
      | RecBind ((vname # (α cexp)) list) da_ctxt
      | Unfold vname vname (vname list) da_ctxt
End

Definition adds_demands_def:
  (adds_demands a0 (m, e, fd) [] = e) ∧
  (adds_demands a0 (m, e, fd) (name::tl) =
     case lookup m (implode name) of
       | SOME () => Prim a0 Seq [Var a0 name; adds_demands a0 (m, e, fd) tl]
       | _ => adds_demands a0 (m, e, fd) tl)
End

Definition add_all_demands_def:
  add_all_demands a (m, e, _) = foldrWithKey (λ id () e. Prim a Seq [Var a (explode id); e] ) e m
End

Definition compute_ALL_DISTINCT_def:
  compute_ALL_DISTINCT [] m = T ∧
  compute_ALL_DISTINCT (v::tl) m =
              (mlmap$lookup m (mlstring$implode v) = NONE
               ∧ compute_ALL_DISTINCT tl (insert m (implode v) ()))
End

Definition UNZIP3_DEF:
  UNZIP3 [] = ([], [], []) ∧
  UNZIP3 ((h1, h2, h3)::tl) =
    let (l1, l2, l3) = UNZIP3 tl in
      (h1::l1, h2::l2, h3::l3)
End

Definition boolList_of_fdemands_def:
  boolList_of_fdemands m [] = ([], mlmap$empty mlstring$compare) ∧
  boolList_of_fdemands m (h::tl) =
  let (bL, m2) = boolList_of_fdemands m tl in
    let h2 = implode h in
      ((lookup m h2 = SOME () ∧ lookup m2 h2 = NONE)::bL, insert m2 (implode h) ())
End

Definition handle_Apps_demands_def:
  handle_Apps_demands a [] args = ([], MAP (add_all_demands a) args, mlmap$empty mlstring$compare)  ∧
  handle_Apps_demands a bL [] = (bL, [], empty compare) ∧
  (handle_Apps_demands a (T::bL) ((m, e, fd)::args) =
    let (bL', eL', m') = handle_Apps_demands a bL args in
      (bL', e::eL', union m m')) ∧
  (handle_Apps_demands a (F::bL) (arg0::args) =
    let (bL', eL', m') = handle_Apps_demands a bL args in
      (bL', (add_all_demands a arg0)::eL', m'))
End

Definition handle_multi_bind_def:
  handle_multi_bind m []  _ = m ∧
  handle_multi_bind m  _ [] = m ∧
  handle_multi_bind m1 (m2::mL) (v::vL) =
    (if mlmap$lookup m1 (mlstring$implode v) = NONE
     then handle_multi_bind m1 mL vL
     else union m2 (handle_multi_bind m1 mL vL))
End

Definition handle_Letrec_fdemands_def:
  handle_Letrec_fdemands m []  _ = m ∧
  handle_Letrec_fdemands m  _ [] = m ∧
  handle_Letrec_fdemands m (h::vL) (NONE::fdL) = handle_Letrec_fdemands (delete m (mlstring$implode h)) vL fdL ∧
  handle_Letrec_fdemands m (h::vL) (SOME fd::fdL) = handle_Letrec_fdemands (insert m (implode h) (FST fd)) vL fdL
End

Definition demands_analysis_fun_def:
  (demands_analysis_fun c ((Var a0 a1): 'a cexp) fds =
     let fd = case mlmap$lookup fds (implode a1) of
            | SOME l => SOME (l, mlmap$empty mlstring$compare)
            | NONE => NONE
     in
       (mlmap$insert (mlmap$empty mlstring$compare) (implode a1) (),
        Var a0 a1 : 'a cexp,
        fd)) ∧

  (demands_analysis_fun c (App a0 (f: 'a cexp) (argl: 'a cexp list)) fds =
     let (m1, f', fd) = demands_analysis_fun c f fds ;
         eL' = MAP (λe. demands_analysis_fun c e fds) argl
     in
       case fd of
       | NONE =>
           (let e' = MAP (λe. add_all_demands a0 e) eL' in
              (m1, (App (a0: 'a) (f': 'a cexp) (e': 'a cexp list) : 'a cexp),
               NONE))
       | SOME (fdL, m2) =>
           (case handle_Apps_demands a0 fdL eL' of
            | ([], eL'', m3) => (union m1 (union m2 m3), App a0 f' eL'', NONE)
            | (fdL', eL'', m3) =>
                (m1, App a0 f' eL'', SOME (fdL', union m2 m3)))) ∧

  (demands_analysis_fun c (Lam a0 vl e) fds =
   let (m, e', fd) =
       demands_analysis_fun (IsFree vl c) e
          (FOLDL (λf k. mlmap$delete f (mlstring$implode k)) fds vl)
   in
     (empty compare,
      Lam a0 vl (add_all_demands a0 (m, e', fd)),
      SOME (FST (boolList_of_fdemands m vl), empty compare))) ∧

  (demands_analysis_fun c (Let a0 name e1 e2) fds =
     let (m1, e1', fd1) = demands_analysis_fun c e1 fds ;
         fds2 = case fd1 of
                | NONE => delete fds (implode name)
                | SOME (bL, _) => insert fds (implode name) bL ;
         (m2, e2', fd2) = demands_analysis_fun (Bind name e1 c) e2 fds2
     in
       (delete m2 (implode name),
        (case lookup m2 (implode name) of
         | NONE => Let a0 name e1' e2'
         | SOME () => Let a0 name e1' (Prim a0 Seq [Var a0 name; e2'])),
        case fd2 of
        | NONE => NONE
        | SOME (fdL, fd_map) => SOME (fdL, delete fd_map (implode name)))) ∧

  (demands_analysis_fun c (Prim a0 Seq [e1; e2]) fds =
     let (m1, e1', fd1) = demands_analysis_fun c e1 fds in
       let (m2, e2', fd2) = demands_analysis_fun c e2 fds in
         (union m1 m2, Prim a0 Seq [e1'; e2'], fd2)) ∧
  (demands_analysis_fun c (Prim a0 Seq _) fds =
   (empty compare, Prim a0 Seq [], NONE)) ∧

  (demands_analysis_fun c (Prim a0 (AtomOp op) el) fds =
     let outL = MAP (λe. demands_analysis_fun c e fds) el in
       let (mL, el', fdL) = UNZIP3 outL in
           let m = FOLDL union (empty compare) mL in
             (m, Prim a0 (AtomOp op) (el': 'a cexp list), NONE)) ∧

  (demands_analysis_fun c (Prim a0 (Cons s) el) fds =
     let el = MAP (λe. add_all_demands a0 (demands_analysis_fun c e fds)) el in
       (empty compare, Prim a0 (Cons s) el, NONE)) ∧

  (demands_analysis_fun c (Letrec a0 binds e) fds =
   let vL = MAP FST binds in
     if compute_ALL_DISTINCT vL (empty compare)
     then
       let outL = MAP (λ(v, e). demands_analysis_fun Nil e (empty compare)) binds in
         let (mL, eL', fdL) = UNZIP3 outL in
           let (m, e2, fd) = demands_analysis_fun (RecBind binds c) e
                                                  (handle_Letrec_fdemands fds vL fdL) in
               let e3 = adds_demands a0 (m, e2, fd) vL in
                 (FOLDL (λf k. delete f (implode k)) (handle_multi_bind m mL vL) vL,
                  Letrec a0 (ZIP (vL, eL')) e3,
                  case fd of
                    | NONE => NONE
                    | SOME (bL, fd_map) => SOME (bL, FOLDL (λf k. delete f (implode k)) fd_map vL))
     else (empty compare, Letrec a0 binds e, NONE)) ∧

  (demands_analysis_fun c (Case a0 e n cases) fds =
   if MEM n (FLAT (MAP (FST o SND) cases))
   then
     (empty compare, Case a0 e n cases, NONE)
   else
     let (m, e', fd) = demands_analysis_fun c e fds in
       let cases' = MAP (λ(name,args,ce).
                           (name, args,
                            adds_demands a0
                                         (demands_analysis_fun
                                          (Unfold name n args (Bind n e c))
                                          ce
                                          (empty compare)) args)) cases in
             (m, Case a0 e' n cases', NONE)) ∧
  (demands_analysis_fun c (NestedCase i _ _ _) fds =
   (empty compare, Var i "Fail: demands analysis on NestedCase", NONE))
Termination
  WF_REL_TAC ‘measure $ (cexp_size (K 0)) o (FST o SND)’ \\ rw []
  \\ imp_res_tac cexp_size_lemma
  \\ fs []
End

Definition demands_analysis_def:
    demands_analysis a0 e = add_all_demands a0 (demands_analysis_fun Nil e (empty compare))
End

(*
let foo = Lam a (a + 2) in
    Lam x (foo x)

 -->

let foo = Lam a (Seq a (a + 2)) in
    Lam x (foo x)

 -->

let foo = Lam a (Seq a (a + 2)) in
    Lam x (Seq x (Seq foo (foo x)))
*)

val _ = export_theory();
