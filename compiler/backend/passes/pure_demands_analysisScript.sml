(*
    Definition of the demands analysis pass
*)

open HolKernel Parse boolLib bossLib term_tactic;
open pure_cexpTheory mlmapTheory mlstringTheory;

val _ = new_theory "pure_demands_analysis";

Datatype:
  da_ctxt =
      | Nil
      | IsFree (cvname list) da_ctxt
      | Bind cvname (α cexp) da_ctxt
      | RecBind ((cvname # (α cexp)) list) da_ctxt
      | Unfold cvname cvname (cvname list) da_ctxt
End

Definition adds_demands_def:
  (adds_demands a0 (m, e, fd) [] = e) ∧
  (adds_demands a0 (m, e, fd) (name::tl) =
     case lookup m name of
       | SOME () => Prim a0 Seq [Var a0 name; adds_demands a0 (m, e, fd) tl]
       | _ => adds_demands a0 (m, e, fd) tl)
End

Definition add_all_demands_def:
  add_all_demands a (m, e, _) =
  foldrWithKey (λ id () e. Prim a Seq [Var a id; e] ) e m
End

Definition compute_ALL_DISTINCT_def:
  compute_ALL_DISTINCT [] m = T ∧
  compute_ALL_DISTINCT (v::tl) m =
              (mlmap$lookup m v = NONE
               ∧ compute_ALL_DISTINCT tl (insert m v ()))
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
  let (bL, m2) = boolList_of_fdemands m tl
  in
    ((lookup m h = SOME () ∧ lookup m2 h = NONE)::bL, insert m2 h ())
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
    (if mlmap$lookup m1 v = NONE
     then handle_multi_bind m1 mL vL
     else union m2 (handle_multi_bind m1 mL vL))
End

Definition handle_Letrec_fdemands_def:
  handle_Letrec_fdemands m []  _ = m ∧
  handle_Letrec_fdemands m  _ [] = m ∧
  handle_Letrec_fdemands m (h::vL) (NONE::fdL) =
    handle_Letrec_fdemands (delete m h) vL fdL ∧
  handle_Letrec_fdemands m (h::vL) (SOME fd::fdL) =
    handle_Letrec_fdemands (insert m h (FST fd)) vL fdL
End

Definition split_body_def:
  (split_body (pure_cexp$Lam a l e) = (l, e)) ∧
  (split_body e = ([], e))
End

Definition compute_freevars_def:
  (compute_freevars (Var a v) = (mlmap$insert (empty mlstring$compare) v ())) ∧
  (compute_freevars (App a f eL) =
   FOLDR (λe m. union m (compute_freevars e)) (compute_freevars f) eL : (mlstring, unit) map) ∧
  (compute_freevars (Lam a l e) =
   FOLDR (λv m. mlmap$delete m v) (compute_freevars e) l : (mlstring, unit) map) ∧
  (compute_freevars (Prim a op eL) =
   FOLDR (λe m. union m (compute_freevars e)) (empty compare) eL : (mlstring, unit) map) ∧
  (compute_freevars (Let a w e1 e2) =
   union (compute_freevars e1) (mlmap$delete (compute_freevars e2) w) : (mlstring, unit) map) ∧
  (compute_freevars (Letrec a b e) =
   let m = FOLDR (λ(v, e) m. mlmap$union m (compute_freevars e)) (compute_freevars e) b in
     FOLDR (λ(v, e) m. mlmap$delete m v) m b : (mlstring, unit) map) ∧
  (compute_freevars (Case a0 e n cases eopt) =
   let m1 = case eopt of
            | NONE => empty compare
            | SOME (a,e) => compute_freevars e in
     let m2 = FOLDR (λ(_, vL, e) m.
                       union (FOLDR (λv m. delete m v) (compute_freevars e) vL) m) m1 cases in
       union (compute_freevars e) (delete m2 n)) ∧
  (compute_freevars (NestedCase d g gv p e pes) = empty compare : (mlstring, unit) map)
Termination
  WF_REL_TAC ‘measure $ (cexp_size (K 0))’ \\ rw []
End

Definition compute_is_subset_def:
  (compute_is_subset (m1 : (mlstring, unit) map) m2 =
   foldrWithKey (λid () b.
                   case mlmap$lookup m2 id of
                        | NONE => F
                        | SOME () => b) T m1)
End

Definition compute_is_disjoint_def:
  (compute_is_disjoint (m1 : (mlstring, unit) map) m2 =
   foldrWithKey (λid () b.
                   case mlmap$lookup m2 id of
                        | NONE => b
                        | SOME () => F) T m1)
End

Definition are_valid_def:
  are_valid map1 args body =
  (let map2 = FOLDR (λv m. insert m v ()) (empty compare) args in
     let free = compute_freevars body in
     compute_is_disjoint map1 map2 ∧ compute_is_subset free (union map1 map2))
End

Definition can_compute_fixpoint_def:
  can_compute_fixpoint binds =
  let binds2 = MAP (λ(v, body). v, split_body body) binds in
    if EVERY (λ(v, args, body). compute_ALL_DISTINCT args (empty compare)) binds2 ∧
       compute_ALL_DISTINCT (MAP FST binds) (empty compare)
    then (let map1 = FOLDR (λ(v, _) m. insert m v ()) (empty compare) binds2 in
            if EVERY (λ(v, args, body). are_valid map1 args body) binds2
            then SOME (binds2)
            else NONE)
    else NONE
End

Definition fixpoint_demands_App_def:
  (fixpoint_demands_App [] eL = ([], mlmap$empty mlstring$compare)) ∧
  (fixpoint_demands_App tl [] = (tl, mlmap$empty mlstring$compare)) ∧
  (fixpoint_demands_App (F::tl) (e::eL) = fixpoint_demands_App tl eL) ∧
  (fixpoint_demands_App (T::tl) ((m1, fds)::eL) =
   let (l, m2) = fixpoint_demands_App tl eL in
       (l, union m1 m2))
End

Definition fixpoint1_def:
  (fixpoint1 (c : α da_ctxt) ((Var a0 a1): 'a cexp) fds =
     case mlmap$lookup fds a1 of
            | SOME l => (mlmap$empty mlstring$compare, SOME (l, mlmap$empty mlstring$compare))
            | NONE => (insert (empty compare) a1 (), NONE)) ∧

  (fixpoint1 c (App a0 (f: 'a cexp) (argl: 'a cexp list)) fds =
     let (m1, fd) = fixpoint1 c f fds ;
         eL' = MAP (λe. fixpoint1 c e fds) argl
     in
       case fd of
       | NONE => (m1, NONE)
       | SOME (fdL, m2) =>
           (case fixpoint_demands_App fdL eL' of
            | ([], m3) => (union m1 (union m2 m3), NONE)
            | (fdL', m3) => (m1, SOME (fdL', union m2 m3)))) ∧

  (fixpoint1 c e fds = (mlmap$empty mlstring$compare, NONE))
Termination
  WF_REL_TAC ‘measure $ (cexp_size (K 0)) o (FST o SND)’ \\ rw []
End

Definition demands_analysis_fun_def:
  (demands_analysis_fun c ((Var a0 a1): 'a cexp) fds =
     let fd = case mlmap$lookup fds a1 of
            | SOME l => SOME (l, mlmap$empty mlstring$compare)
            | NONE => NONE
     in
       (mlmap$insert (mlmap$empty mlstring$compare) a1 (),
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
          (FOLDL (λf k. mlmap$delete f k) fds vl)
   in
     (empty compare,
      Lam a0 vl (add_all_demands a0 (m, e', fd)),
      SOME (FST (boolList_of_fdemands m vl), empty compare))) ∧

  (demands_analysis_fun c (Let a0 name e1 e2) fds =
     let (m1, e1', fd1) = demands_analysis_fun c e1 fds ;
         fds2 = case fd1 of
                | NONE => delete fds name
                | SOME (bL, _) => insert fds name bL ;
         (m2, e2', fd2) = demands_analysis_fun (Bind name e1 c) e2 fds2
     in
       (delete m2 name,
        (case lookup m2 name of
         | NONE => Let a0 name e1' e2'
         | SOME () => Let a0 name e1' (Prim a0 Seq [Var a0 name; e2'])),
        case fd2 of
        | NONE => NONE
        | SOME (fdL, fd_map) => SOME (fdL, delete fd_map name))) ∧

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
   let vL : mlstring list = MAP FST binds in
     if compute_ALL_DISTINCT vL (empty compare)
     then
       let outL = MAP (λ(v, e). demands_analysis_fun (RecBind binds c) e
                                    (FOLDL (λf k. delete f k) fds vL)) binds ;
           (mL, eL', fdL) = UNZIP3 outL ;
           reduced_fds = handle_Letrec_fdemands fds vL fdL ;
           (m, e2, fd) = demands_analysis_fun (RecBind binds c) e reduced_fds ;
           e3 = adds_demands a0 (m, e2, fd) vL
       in
         (FOLDL (λf k. delete f k) (handle_multi_bind m mL vL) vL,
          Letrec a0 (ZIP (vL, eL')) e3,
          case fd of
          | NONE => NONE
          | SOME (bL, fd_map) => SOME (bL, FOLDL (λf k. delete f k) fd_map vL))
     else (empty compare, Letrec a0 binds e, NONE)) ∧

  (demands_analysis_fun c (Case a0 e n cases eopt) fds =
   if cases = []
   then (empty compare, Case a0 e n cases eopt, NONE)
   else
     if MEM n (FLAT (MAP (FST o SND) cases))
     then
       (empty compare, Case a0 e n cases eopt, NONE)
     else
       let (m, e', fd) = demands_analysis_fun c e fds ;
           cases' = MAP (λ(name,args,ce).
                           (name, args,
                            add_all_demands a0
                                            (demands_analysis_fun
                                             (Unfold name n args (Bind n e c))
                                             ce
                                             (empty compare)))) cases ;
           eopt' = (case eopt of
                    | NONE => NONE
                    | SOME (a,e0) =>
                      SOME (a,add_all_demands a0
                              (demands_analysis_fun (Bind n e c) e0 (empty compare))))
       in
         (m, Case a0 e' n cases' eopt', NONE)) ∧
  (demands_analysis_fun c (NestedCase i _ _ _ _ _) fds =
   (empty compare,
    Var i (implode "Fail: demands analysis on NestedCase"),
    NONE))
Termination
  WF_REL_TAC ‘measure $ (cexp_size (K 0)) o (FST o SND)’ \\ rw []
  \\ imp_res_tac cexp_size_lemma
  \\ fs []
End

Definition demands_analysis_def:
    demands_analysis e = FST (SND (demands_analysis_fun Nil e (empty compare)))
End

Definition demands_analysis2_def:
    demands_analysis2 a0 e = add_all_demands a0 (demands_analysis_fun Nil e (empty compare))
End

(*
Let foo = Lam a (Prim op [a]) in Lam x (App foo x)
 -->

Let foo = Lam a (a; Prim op [a]) in Lam x (foo; x; App foo x)
*)

Theorem demands_analysis_test_0:
  demands_analysis2 0
  (Let 0 «foo» (Lam 0 [«a»] (Prim 0 (AtomOp op) [Var 0 «a»]))
   (Lam 0 [«x»] (App 0 (Var 0 «foo») [Var 0 «x»]))) =
  Let 0 «foo»
      (Lam 0 [«a»] (Prim 0 Seq [Var 0 «a»; Prim 0 (AtomOp op) [Var 0 «a»]]))
      (Lam 0 [«x»]
       (Prim 0 Seq
        [Var 0 «foo»;
         Prim 0 Seq [Var 0 «x»; App 0 (Var 0 «foo») [Var 0 «x»]]]))
Proof
  EVAL_TAC
QED

(*
  Letrec fact = Lam n c -> if n = 0 then c else n * c
  in fact n0 c1

  -->

  n0;
  Letrec fact = Lam n c -> n; if n = 0 then c else n * c
  in fact; fact n0 c1


*)

Theorem demands_analysis_test_1:
  demands_analysis2 0
  (Letrec 0
   [(«fact»,
     Lam 0 [«n»; «c»]
         (Case 0
          (Prim 0 (AtomOp Eq)
           [Var 0 «n»; Prim 0 (AtomOp (Lit (Int 0))) []]) «n2»
          [(«True»,[],Var 0 «c»);
           («False»,[],Prim 0 (AtomOp Mul) [Var 0 «n»; Var 0 «c»])] NONE))]
   (App 0 (Var 0 «fact») [Var 0 «n0»; Var 0 «c1»])) =
  Prim 0 Seq
       [Var 0 «n0»;
        Letrec 0
               [(«fact»,
                 Lam 0 [«n»; «c»]
                     (Prim 0 Seq
                      [Var 0 «n»;
                       Case 0
                            (Prim 0 (AtomOp Eq)
                             [Var 0 «n»; Prim 0 (AtomOp (Lit (Int 0))) []]) «n2»
                            [(«True»,[],Prim 0 Seq [Var 0 «c»; Var 0 «c»]);
                             («False»,[],Prim 0 Seq [Var 0 «c»;
                                         Prim 0 Seq [Var 0 «n»;
                                                     Prim 0 (AtomOp Mul) [Var 0 «n»; Var 0 «c»]]])] NONE]))]
               (Prim 0 Seq
                [Var 0 «fact»;
                 App 0 (Var 0 «fact»)
                     [Var 0 «n0»; Prim 0 Seq [Var 0 «c1»; Var 0 «c1»]]])]
Proof
  EVAL_TAC
QED

(*
EVAL ``demands_analysis 0 (Let 0 «foo» (Lam 0 [«a»] (Prim 0 (AtomOp op) [Var 0 «a»]))
(Lam 0 [«x»] (App 0 (Var 0 «foo») [Var 0 «x»]) ))``;
*)

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
