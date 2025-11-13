(*
  Inlining optimization for cexp
*)
Theory pure_inline_cexp
Ancestors
  list pair topological_sort pure_cexp pure_vars balanced_map
  pure_freshen pure_letrec_spec_cexp pure_dead_let pure_comp_conf
  mlstring
Libs
  BasicProvers

(*******************)

(* heuristic for deciding when to inline *)
Type heuristic = “:'a cexp -> bool”

Theorem cexp_size_lemma[local]:
  ∀vbs.
    list_size (cexp_size (K 0)) (MAP SND vbs) ≤
    list_size (pair_size mlstring_size (cexp_size (K 0))) vbs
Proof
  Induct  \\ fs [] \\ rw [] \\ res_tac
  \\ fs [list_size_def,basicSizeTheory.pair_size_def]
  \\ PairCases_on `h`
  \\ fs [list_size_def,basicSizeTheory.pair_size_def]
QED

Definition cheap_def:
  cheap (Var _ e) = T ∧
  cheap (Lam _ _ _) = T ∧
  cheap (Prim _ _ xs) = NULL xs ∧
  cheap _ = F
End

Definition heuristic_insert_def:
  heuristic_insert m h v e =
    if cheap e ∧ h e then
      insert m v e
    else
      m
End

Definition heuristic_insert_Rec_def:
  heuristic_insert_Rec m h fs =
    case fs of
      | [(v, e)] =>
        if h e then (
          case specialise v e of
          | NONE => m
          | SOME b => insert m v b
        )
        else
          m
      | _ => m
End

Theorem size_lemma[local]:
  ∀bs.
    list_size (λx. cexp_size (K 0) (SND (SND x))) bs ≤
    list_size (pair_size mlstring_size
                 (pair_size (list_size mlstring_size) (cexp_size (K 0)))) bs
Proof
  Induct \\ fs [list_size_def,FORALL_PROD,basicSizeTheory.pair_size_def]
QED

(*
It can be the case that we create sth like:
```
(\x -> x + 1) y
```
by inlining in the App case. The problem now is that
```
(\x -> x + 1) y ≠ let x = y in x + 1
```
And so goint further won't do anything
*)
Definition App_Lam_to_Lets_def:
  App_Lam_to_Lets (App a (Lam _ vs b) es) =
    (if LENGTH es < LENGTH vs (* not fully applied *) then NONE else
       let es1 = TAKE (LENGTH vs) es in
       let es2 = DROP (LENGTH vs) es in
         SOME $ SmartApp a (Lets a (ZIP (vs,es1)) b) es2) ∧
  App_Lam_to_Lets e = NONE
End

Definition inline_def:
  inline (m: ('a cexp) var_map) ns (cl: num) (h: 'a heuristic) (Var (a: 'a) v) =
    (case lookup m v of
    | NONE => (Var a v, ns)
    | SOME e =>
      if is_Lam e
      then (Var a v, ns)
      else if cl = 0 then (Var a v, ns)
        else (
          inline m ns (cl - 1) h e
        )) ∧
  inline m ns cl h (App a e es) = (
    let (es1, ns1) = inline_list m ns cl h es
    in (
      case get_Var_name e of
      (* Var applied to arguments *)
      | SOME v => (
        case lookup m v of
        | SOME e_m =>
          let (exp, ns2) = freshen_cexp (App a e_m es1) ns1
          in (case App_Lam_to_Lets exp of
          | NONE => (App a e es1, ns1)
          | SOME exp1 =>
            if cl = 0 then (App a e es1, ns1)
            else inline m ns2 (cl - 1) h exp1
          )
        | _ =>
          let (e1, ns2) = inline m ns1 cl h e
          in (App a e1 es1, ns2)
        )
      (* Not a Var -- can't inline *)
      | _ =>
        let (e1, ns2) = inline m ns1 cl h e
        in (App a e1 es1, ns2)
    )
  ) ∧
  inline m ns cl h (Let a v e1 e2) =
    (let m1 = heuristic_insert m h v e1
     in let (e3, ns3) = inline m ns cl h e1
     in let (e4, ns4) = inline m1 ns3 cl h e2
     in (Let a v e3 e4, ns4)) ∧
  inline m ns cl h (Letrec a vbs e) =
    (let m1 = heuristic_insert_Rec m h vbs
     in let (vbs1, ns1) = inline_list m ns cl h (MAP SND vbs)
     in let (e2, ns2) = inline m1 ns1 cl h e
     in (Letrec a (MAP2 (λ(v,_) x. (v, x)) vbs vbs1) e2, ns2)) ∧
  inline m ns cl h (Lam a vs e) =
    (let (e1, ns1) = inline m ns cl h e
    in (Lam a vs e1, ns1)) ∧
  inline m ns cl h (Prim a op es) =
    (let (es2, ns2) = inline_list m ns cl h es
     in (Prim a op es2, ns2)) ∧
  inline m ns cl h (Case a e v bs f) =
    (let (e1, ns1) = inline m ns cl h e
     in let (bs2, ns2) = inline_list m ns1 cl h (MAP (λ(v, vs, e). e) bs)
     in let (f3, ns3) = case f of
        | NONE => (NONE, ns2)
        | SOME (vs, e) =>
          let (e4, ns4) = inline m ns2 cl h e
          in (SOME (vs, e4), ns4)
     in (Case a e1 v (MAP2 (λ(v, vs, _) e. (v, vs, e)) bs bs2) f3, ns3)) ∧
  inline m ns cl h (NestedCase a e v p e' bs) =
    (NestedCase a e v p e' bs, ns) ∧
  inline_list m ns cl h [] = ([], ns) ∧
  inline_list m ns cl h (e::es) =
    (let (e1, ns1) = inline m ns cl h e in
     let (es2, ns2) = inline_list m ns1 cl h es
     in (e1::es2, ns2))
Termination
  WF_REL_TAC `inv_image ($< LEX $<) $ λx. case x of
    | INL (m, ns, cl, h, e) => (cl, cexp_size (K 0) e)
    | INR (m, ns, cl, h, es) => (cl, list_size (cexp_size (K 0)) es)`
  \\ fs [] \\ rw [] \\ gvs []
  \\ qspec_then `vbs` assume_tac cexp_size_lemma \\ fs []
  \\ qspec_then ‘bs’ assume_tac size_lemma \\ fs []
End

Definition inline_all_def:
  inline_all cl h e =
    let (e1, s) = freshen_cexp e (boundvars_of e)
    in let (inlined_e, _) = inline empty s cl h e1
    in dead_let inlined_e
End

Theorem cexp_size_lemma2[local]:
  ∀xs e.
    MEM e xs ⇒
    cexp_size (K 0) e ≤ list_size (cexp_size (K 0)) xs
Proof
  Induct  \\ fs [] \\ rw [] \\ res_tac \\ fs [list_size_def]
QED

Definition tree_size_heuristic_rec_def:
  tree_size_heuristic_rec (n: num) (Var a v) = (n - 1) ∧
  tree_size_heuristic_rec n (Prim a op es) =
    FOLDL (λa e. if a < 0 then a else tree_size_heuristic_rec a e) (n - 1) es ∧
  tree_size_heuristic_rec n (App a e es) =
    FOLDL (λa e. if a < 0 then a else tree_size_heuristic_rec a e) (n - 1) (e::es) ∧
  tree_size_heuristic_rec n (Lam a vs e) =
    tree_size_heuristic_rec (n - 1) e ∧
  tree_size_heuristic_rec n (Let a v e1 e2) =
    (let n1 = tree_size_heuristic_rec (n - 1) e1
    in if n1 < 0 then n1 else tree_size_heuristic_rec n1 e2) ∧
  tree_size_heuristic_rec n (Letrec a vbs e) =
    (let n1 = FOLDL (λa (v, e). if a < 0 then a else tree_size_heuristic_rec a e) (n - 1) vbs
    in if n1 < 0 then n1 else tree_size_heuristic_rec n1 e) ∧
  tree_size_heuristic_rec n (Case a e v bs f) =
    (let n1 = FOLDL (λa (v, vs, e). if a < 0 then a else tree_size_heuristic_rec a e) (n - 1) bs
    in if n1 < 0 then n1 else
      case f of
        NONE => n1
      | SOME (vs, e) => tree_size_heuristic_rec n1 e) ∧
  tree_size_heuristic_rec n (NestedCase a e v p e' bs) =
    (let n1 = FOLDL (λa (p, e). if a < 0 then a else tree_size_heuristic_rec a e) (n - 1) bs
    in if n1 < 0 then n1 else tree_size_heuristic_rec n1 e')
Termination
  WF_REL_TAC ‘measure (λx. case x of
    | (n, e) => cexp_size (K 0) e)’
  \\ fs [] \\ rw [] \\ gvs []
  \\ imp_res_tac cexp_size_lemma2 \\ fs []
End

Definition tree_size_heuristic_def:
  tree_size_heuristic n e =
    (tree_size_heuristic_rec n e ≥ 0)
End

(*******************)

Definition inline_top_level_def:
  inline_top_level c e =
    inline_all c.inlining.depth (tree_size_heuristic c.inlining.heuristic) e
End

(*******************)

