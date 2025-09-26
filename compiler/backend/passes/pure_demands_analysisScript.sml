(*
    Definition of the demands analysis pass
*)
Theory pure_demands_analysis
Ancestors
  pure_cexp mlmap mlstring pure_comp_conf
Libs
  term_tactic


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

Definition extract_label_def:
  extract_label (Var a _) = a ∧
  extract_label (Let a _ _ _) = a ∧
  extract_label (Lam a _ _) = a ∧
  extract_label (App a _ _) = a ∧
  extract_label (Prim a _ _) = a ∧
  extract_label (Letrec a _ _) = a ∧
  extract_label (Case a _ _ _ _) = a ∧
  extract_label (NestedCase a _ _ _ _ _) = a
End

Definition split_body_def:
  (split_body (pure_cexp$Lam a l e) = (l, e, a)) ∧
  (split_body e = ([], e, extract_label e))
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
    if EVERY (λ(v, args, body, label). compute_ALL_DISTINCT args (empty compare)) binds2
    then (let map1 = FOLDR (λ(v, _) m. insert m v ()) (empty compare) binds2 in
            (EVERY (λ(v, args, body, label). are_valid map1 args body) binds2, binds2))
    else (F, binds2)
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

  (fixpoint1 c (Prim a0 Seq [e1; e2]) fds =
     let (m1, fd1) = fixpoint1 c e1 fds in
       let (m2, fd2) = fixpoint1 c e2 fds in
         (union m1 m2, fd2)) ∧

  (fixpoint1 c (Prim a0 (AtomOp op) eL) fds =
   let outL = MAP (λe. fixpoint1 c e fds) eL in
     let m = FOLDR (λ(ds, _) m. union ds m) (empty compare) outL in
       (m, NONE)) ∧

  (fixpoint1 c (Case (a0 : α) (e : α cexp) (n : cvname) (rows : (cvname # (cvname list) # α cexp) list) fall : α cexp) fds =
   let (demands_e, _) = fixpoint1 c e fds in
     let outL =
         MAP (λ(cons, vL, e). FOLDR (λv m. delete m v) (FST (fixpoint1 (IsFree vL (IsFree [n] c)) e
                                                          (FOLDR (λv m. delete m v) (delete fds n) vL))) vL) rows in
       let fallL = case fall of
                   | NONE => outL
                   | SOME (a, e) => FST (fixpoint1 (IsFree [n] c) e (delete fds n))::outL in
         case fallL of
         | [] => (empty compare, NONE)
         | hd::tl =>
             (let m = foldrWithKey (λid _ m. if FOLDR (λm2 b. b ∧ lookup m2 id = SOME ()) T tl
                                              then mlmap$insert m id ()
                                              else m) (empty compare) hd in
                (union demands_e (delete m n), NONE))) ∧

  (fixpoint1 c e fds = (mlmap$empty mlstring$compare, NONE))
Termination
  WF_REL_TAC ‘measure $ (cexp_size (K 0)) o (FST o SND)’ \\ rw []
End

(* LIST_REL (λ(v1, b1) (v2, b2). b2 ⇒ b1) args1 args2 *)
Definition test_list_rel_def:
  (test_list_rel [] [] = T) ∧
  (test_list_rel [] _ = F) ∧
  (test_list_rel _ [] = F) ∧
  (test_list_rel ((hd1, b1)::tl1) ((hd2, b2)::tl2) =
   ((b1 ∨ ¬b2) ∧ test_list_rel tl1 tl2))
End

Definition is_lower_def:
  (is_lower [] [] = T) ∧
  (is_lower [] _ = F) ∧
  (is_lower _ [] = F) ∧
  (is_lower ((v1, args1, body1, lab1)::tl1) ((v2, args2, body2, lab2)::tl2) =
   (test_list_rel args1 args2 ∧ is_lower tl1 tl2))
End

Definition handle_fixpoint1_def:
  handle_fixpoint1 fds (v, args, body, label) =
       let (ds, _) = fixpoint1 Nil body fds in
         (v, MAP (λ(v, b). (v, lookup ds v = SOME ())) args, body, label)
End

Definition compute_fixpoint_rec_def:
  (compute_fixpoint_rec 0 binds =
   MAP (λ(v, args, e, label). (v, MAP (λ(v, b). (v, F)) args, e, label)) binds) ∧
  (compute_fixpoint_rec (SUC fuel) binds =
   let fds = FOLDR (λ(v, args, e, lab) m. insert m v (MAP SND args)) (empty compare) binds in
     let binds2 = MAP (handle_fixpoint1 fds) binds in
       if is_lower binds2 binds
       then binds2
       else compute_fixpoint_rec fuel binds2)
End

Definition rev_split_body_inner_def:
  rev_split_body_inner a [] e = e ∧
  rev_split_body_inner a ((_,F)::xs) e = rev_split_body_inner a xs e ∧
  rev_split_body_inner a ((v,T)::xs) e = Prim a Seq [Var a v; rev_split_body_inner a xs e]
End

Definition rev_split_body_def:
  rev_split_body a [] e = e ∧
  rev_split_body a l e = Lam a (MAP FST l) (rev_split_body_inner a l e)
End

Definition fixpoint_analysis_def:
  fixpoint_analysis binds =
  let (b, binds) = can_compute_fixpoint binds in
    (if b
    then (b, compute_fixpoint_rec 10 (MAP (λ(v, args, body, label). (v, MAP (λv. (v, T)) args, body, label)) binds))
    else (b, (MAP (λ(v, args, body, label). (v, MAP (λv. (v, F)) args, body, label)) binds)))
End

(*Definition fixpoint_analysis_wrapped_def:
  fixpoint_analysis_wrapped binds =
  let (_, binds2) = fixpoint_analysis binds in
    MAP (λ(v, args, body, label). (v, rev_split_body label args body)) binds2
End*)

Definition demands_analysis_fun_def:
  (demands_analysis_fun c ((Var a0 a1): 'a cexp) fds =
     let fd = case mlmap$lookup fds a1 of
            | SOME l => SOME (l, mlmap$empty mlstring$compare)
            | NONE => NONE: (bool list # (mlstring, unit) map) option
     in
       (mlmap$insert (mlmap$empty mlstring$compare) a1 (),
        Var a0 a1 : 'a cexp,
        fd)) ∧

  (demands_analysis_fun c (App a0 (f: 'a cexp) (argl: 'a cexp list)) fds =
     let (m1, f', fd) = demands_analysis_fun c f fds ;
         eL' = MAP (λe. demands_analysis_fun c e fds) argl
     in
           (let e' = MAP (λ(_,e,_). e) eL' in
              (m1, (App (a0: 'a) (f': 'a cexp) (e': 'a cexp list) : 'a cexp),
               NONE))) ∧

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
  (demands_analysis_fun c (Prim a0 Seq bad) fds =
   (empty compare, Prim a0 Seq bad, NONE)) ∧

  (demands_analysis_fun c (Prim a0 (AtomOp op) el) fds =
     let outL = MAP (λe. demands_analysis_fun c e fds) el in
       let (mL, el', fdL) = UNZIP3 outL in
           let m = FOLDL union (empty compare) mL in
             (m, Prim a0 (AtomOp op) (el': 'a cexp list), NONE)) ∧

  (demands_analysis_fun c (Prim a0 (Cons s) el) fds =
     let el = MAP (λe. add_all_demands a0 (demands_analysis_fun c e fds)) el in
       (empty compare, Prim a0 (Cons s) el, NONE)) ∧

  (demands_analysis_fun c (Letrec a0 binds e) fds =
   let (b, binds2) = fixpoint_analysis binds in
     if b
     then
       let vL = MAP FST binds2 ;
           fds2 = FOLDL (λf (v, args, body, label). insert f v (MAP SND args)) fds binds2 ;
           binds3 = MAP (λ(v, args, body, label). (v, rev_split_body label args body)) binds2 ;
           (m, e2, fd) = demands_analysis_fun (RecBind binds3 c) e (fds2 : (mlstring, bool list) map);
           e3 = adds_demands a0 (m, e2, fd) vL
       in
         (FOLDL (λf k. delete f k) m vL,
          Letrec a0 binds3 e3,
          case fd of
          | NONE => NONE
          | SOME (bL, fd_map) => SOME (bL, FOLDL (λf k. delete f k) fd_map vL))
     else
       let vL : mlstring list = MAP FST binds in
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
            | SOME (bL, fd_map) => SOME (bL, FOLDL (λf k. delete f k) fd_map vL))) ∧

  (demands_analysis_fun c (Case a0 e n cases eopt) fds =
   let (m, e', fd) = demands_analysis_fun c e fds ;
       (demands, cases') = FOLDR (λ(name,args,ce) (lD, lRows).
                         let result = (demands_analysis_fun
                                  (Unfold name n args (Bind n e c))
                                  ce (FOLDL (λm v. delete m v) (delete fds n) args)) in
                       (FST result::lD, (name, args, add_all_demands a0 result)::lRows)) ([], []) cases ;
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
    demands_analysis c e =
      if c.do_demands then FST (SND (demands_analysis_fun Nil e (empty compare)))
      else e
End

Definition demands_analysis2_def:
    demands_analysis2 a0 e = add_all_demands a0 (demands_analysis_fun Nil e (empty compare))
End

(*
Letrec g = Lam x (App g x) in _
 -->
Letrec g = Lam x (Seq x (App g x)) in _
*)

Theorem fixpoint_analysis_test_0:
  fixpoint_analysis [(«g», Lam (0 : num) [«x»] (App 0 (Var 0 «g») [Var 0 «x»]))]
  =
  (T, [(«g», [(«x», T)], App 0 (Var 0 «g») [Var 0 «x»], 0)])
Proof
  EVAL_TAC
QED

(*
Letrec g = Lam x y (App g x y) in _
 -->
Letrec g = Lam x y (Seq x (App g x y)) in _
*)

Theorem fixpoint_analysis_test_1:
  fixpoint_analysis [(«g», Lam (0 : num) [«x»; «y»] (App 0 (Var 0 «g») [Var 0 «x»; Var 0 «x»]))]
  =
  (T, [(«g», [(«x», T); («y», F)], App 0 (Var 0 «g») [Var 0 «x»; Var 0 «x»], 0)])
Proof
  EVAL_TAC
QED

(*
Letrec fact = Lam n c (If n == 0 then c else fac (n - 1) (n * c)) in _
 -->
Letrec fact = Lam n c (Seq n (Seq c (If n == 0 then c else fac (n - 1) (n * c))) in _
*)

Theorem fixpoint_analysis_test_2:
  fixpoint_analysis
  [(«fact»,
    Lam 0 [«n»; «c»]
    (Case 0
     (Prim 0 (AtomOp Eq)
      [Var 0 «n»; Prim 0 (AtomOp (Lit (Int 0))) []]) «n2»
     [(«True»,[],Var 0 «c»);
      («False»,[], App 0 (Var 0 «fact»)
                       [Prim 0 (AtomOp Sub) [Var 0 «n»; Prim 0 (AtomOp (Lit (Int 1))) []];
                        Prim 0 (AtomOp Mul) [Var 0 «n»; Var 0 «c»]])]
     NONE))]
  =
  (T,
   [(«fact», [(«n», T); («c», T)],
     (pure_cexp$Case 0
      (Prim 0 (AtomOp Eq)
       [Var 0 «n»; Prim 0 (AtomOp (Lit (Int 0))) []]) «n2»
      [(«True»,[],Var 0 «c»);
       («False»,[], App 0 (Var 0 «fact»)
                       [Prim 0 (AtomOp Sub) [Var 0 «n»; Prim 0 (AtomOp (Lit (Int 1))) []];
                        Prim 0 (AtomOp Mul) [Var 0 «n»; Var 0 «c»]])]
      NONE), 0)])
Proof
  EVAL_TAC
QED

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
            App 0 (Var 0 «foo») [Var 0 «x»]]))
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
  demands_analysis default_conf
  (Letrec 0
    [(«fact», Lam 0 [«n»; «c»]
     (Case 0
      (Prim 0 (AtomOp Eq)
       [Var 0 «n»; Prim 0 (AtomOp (Lit (Int 0))) []]) «n2»
      [(«True»,[],Var 0 «c»);
       («False»,[], App 0 (Var 0 «fact»)
                        [Prim 0 (AtomOp Sub) [Var 0 «n»; Prim 0 (AtomOp (Lit (Int 1))) []];
                         Prim 0 (AtomOp Mul) [Var 0 «n»; Var 0 «c»]])]
      NONE))]
    (Let 0 «n0» (Prim 0 (AtomOp (Lit (Int 5))) [])
         (Let 0 «c0» (Prim 0 (AtomOp (Lit (Int 1))) [])
          (App 0 (Var 0 «fact») [Var 0 «n0»; Var 0 «c0»])))) =
   Letrec 0
     [(«fact», Lam 0 [«n»; «c»]
         (Prim 0 Seq [Var 0 «n»;
             Prim 0 Seq [Var 0 «c»;
                (Case 0
                  (Prim 0 (AtomOp Eq)
                     [Var 0 «n»; Prim 0 (AtomOp (Lit (Int 0))) []]) «n2»
                  [(«True»,[],Var 0 «c»);
                   («False»,[], App 0 (Var 0 «fact»)
                      [Prim 0 (AtomOp Sub) [Var 0 «n»; Prim 0 (AtomOp (Lit (Int 1))) []];
                       Prim 0 (AtomOp Mul) [Var 0 «n»; Var 0 «c»]])]
                    NONE)]]))]
     (Prim 0 Seq [Var 0 «fact»;
         (Let 0 «n0» (Prim 0 (AtomOp (Lit (Int 5))) [])
           (Let 0 «c0» (Prim 0 (AtomOp (Lit (Int 1))) [])
              (App 0 (Var 0 «fact»)
                 [Var 0 «n0»; Var 0 «c0»])))])
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

