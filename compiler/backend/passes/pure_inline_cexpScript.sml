(*
  Inlining optimization for cexp
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open listTheory pairTheory topological_sortTheory;
open pure_cexpTheory pure_varsTheory balanced_mapTheory
     pure_freshenTheory pure_letrec_spec_cexpTheory
     pure_dead_letTheory pure_comp_confTheory
     mlstringTheory mlmapTheory;

val _ = new_theory "pure_inline_cexp";

(*******************)

(* heuristic for deciding when to inline *)
Type heuristic = “:'a cexp -> bool”

Triviality cexp_size_lemma:
  ∀vbs.
    list_size (cexp_size (K 0)) (MAP SND vbs) ≤
    list_size (pair_size mlstring_size (cexp_size (K 0))) vbs
Proof
  Induct  \\ fs [] \\ rw [] \\ res_tac
  \\ fs [list_size_def,basicSizeTheory.pair_size_def]
  \\ PairCases_on `h`
  \\ fs [list_size_def,basicSizeTheory.pair_size_def]
QED

Triviality size_lemma:
  ∀bs.
    list_size (cexp_size (K 0)) (MAP (λ(v,vs,e). e) bs) ≤
    list_size (pair_size mlstring_size
                 (pair_size (list_size mlstring_size) (cexp_size (K 0)))) bs
Proof
  Induct \\ fs [list_size_def,FORALL_PROD,basicSizeTheory.pair_size_def]
QED

(*
Expressions kept in the inling map. Either:
- `Simple e` -- normal (non-recursive) expression
- `Rec e` -- recursive expression, takes the original expression and the specialised one
*)
Datatype:
  inlineable_cexp = Simple ('a cexp) | Rec ('a cexp)
End

Datatype:
  inline_tag = InlineTag | ConLikeTag | RecursiveTag
End

Type inline_mods = ``:(inline_tag, unit) mlmap$map``

Definition tags_to_mlstring_def:
  tags_to_mlstring InlineTag = «InlineTag» ∧
  tags_to_mlstring ConLikeTag = «ConLikeTag» ∧
  tags_to_mlstring RecursiveTag = «RecursiveTag»
End

Definition tags_cmp_def:
  tags_cmp t1 t2 = mlstring$compare (tags_to_mlstring t1) (tags_to_mlstring t2)
End

Definition mods_empty_def:
  mods_empty = mlmap$empty tags_cmp
End

(*
Inlining context carries all info unnecessary for proof, but necessary for inlining.
- `heuristic` -- heuristic for inlining
- `inline` -- set of names that should be inlined
- `conlike` -- set of names that should be inlined and are conlike -- super cheap (force inlining)
*)
Datatype:
  inline_ctx = InlineCtx ('a heuristic) ('a heuristic) (var_set) (var_set)
End

Definition memorise_heuristic_def:
  memorise_heuristic (InlineCtx h _ _ _) = h
End

Definition inline_heuristic_def:
  inline_heuristic (InlineCtx _ h _ _) = h
End

Definition inline_set_def:
  inline_set (InlineCtx _ _ s _) = s
End

Definition add_inline_set_def:
  add_inline_set (InlineCtx hr hi s c) v = InlineCtx hr hi (insert s v ()) c
End

Definition conlike_set_def:
  conlike_set (InlineCtx _ _ _ s) = s
End

Definition add_conlike_set_def:
  add_conlike_set (InlineCtx hr hi s c) v = InlineCtx hr hi s (insert c v ())
End

Definition cheap_def:
  cheap (Var _ e) = T ∧
  cheap (Prim _ _ es) = (NULL es ∨ EVERY cheap es) ∧
  cheap _ = F
Termination
  WF_REL_TAC ‘measure (cexp_size (K 0))’
End

Definition elem_set_def:
  elem_set s v =
    case lookup s v of
    | SOME _ => T
    | NONE => F
End

Definition insert_set_def:
  insert_set s v = insert s v ()
End

Definition get_annot_def:
  get_annot (Annot _ annot _) = (SOME annot) ∧
  get_annot _ = NONE
End

Definition insert_based_on_annot_def:
  insert_based_on_annot v (Annot _ annot e) = (
    case annot of
    | Inline => T
    | Inlineable => T
    | ConLike => T
    | _ => F
  ) ∧
  insert_based_on_annot v e = F
End

Definition is_noinline_def:
  is_noinline (Annot _ annot e) = (
    case annot of
    | NoInline => T
    | _ => F
  ) ∧
  is_noinline e = F
End

Definition remove_annotation_def:
  remove_annotation (Annot a _ e) = remove_annotation e ∧
  remove_annotation e = e
End

Definition should_inline_var_def:
  should_inline_var h v e mods =
    if is_Lam e then F
    else if elem_set mods ConLikeTag then T
    else if elem_set mods InlineTag then T
    else h e
    (* //TODO *)
End

Definition should_inline_app_def:
  should_inline_app h v e es mods =
    if elem_set mods ConLikeTag then T
    else if elem_set mods InlineTag then T
    else h e
    (* //TODO *)
End

(* //TODO(kπ) should we pass the info about it being a Rec or not? *)
Definition should_memorise_def:
  should_memorise h v e =
    case get_annot e of
    | SOME NoInline => NONE
    | SOME Inline => SOME (insert_set mods_empty InlineTag)
    | SOME ConLike => SOME (insert_set mods_empty ConLikeTag)
    | SOME Inlineable => (
      if cheap e ∧ h e then SOME (insert_set mods_empty InlineTag)
      else SOME mods_empty
    )
    | _ => (
      if cheap e ∧ h e then SOME (insert_set mods_empty InlineTag)
      else NONE
    )
End

Definition insert_m_def:
  insert_m m v e mods = (
    let e1 = remove_annotation e in
    insert m v (e, mods)
  )
End

Definition remember_def:
  remember m ctx v e =
    case should_memorise (λce. (memorise_heuristic ctx) ce ∧ cheap ce) v e of 
    | SOME mods => insert_m m v e mods
    | NONE => m
End

Definition insert_specialise_def:
  insert_specialise m v e mods =
    let e1 = remove_annotation e in
    case specialise v e1 of
      | SOME e2 => insert_m m v e2 mods
      | NONE => insert_m m v e1 mods
End

Definition remember_Rec_def:
  remember_Rec m ctx v e =
    case should_memorise (memorise_heuristic ctx) v e of
    | SOME mods => insert_m m v e (insert_set mods RecursiveTag)
    | NONE => m
End

Definition remember_specialise_def:
  remember_specialise m ctx v e =
    case should_memorise (memorise_heuristic ctx) v e of
    | SOME mods => insert_specialise m v e mods
    | NONE => remember_Rec m ctx v e
End

Definition remember_Recs_def:
  remember_Recs m ctx fs =
    FOLDL (λm (v, e). remember_Rec m ctx v e) m fs
End

Definition extract_var_def:
  extract_var (Var _ v) = SOME v ∧
  extract_var (App _ e _) = extract_var e ∧
  extract_var _ = NONE
End

Definition add_tag_def:
  add_tag m v tag =
    case lookup m v of
    | SOME (e, mods) => insert_m m v e (insert_set mods tag)
    | NONE => m
End

Definition update_inline_scope_def:
  update_inline_scope m (Annot _ annot e) = (
    case annot of
    | InlineHere v => add_tag m v ConLikeTag
    | InlineUseHere =>
      case extract_var e of
      | SOME v => add_tag m v ConLikeTag
      | NONE => m
    | _ => m
  ) ∧
  update_inline_scope m _ = m
End

Definition is_inline_annotation_def:
  is_inline_annotation (SOME Inline) = T ∧
  is_inline_annotation (SOME ConLike) = T ∧
  is_inline_annotation NONE = F
End

Definition designated_rec_ms_def:
  designated_rec_ms m vbs =
    let with_annots = MAP (λ(v, e). (v, e, get_annot e)) vbs in
    let recs = FILTER (λ(v, e, annot). is_inline_annotation annot) with_annots in
    let r = (
      case recs of
      | [(v, e, SOME (ConLike))] =>
        let m1 = insert_m m v e (insert_set (insert_set mods_empty RecursiveTag) ConLikeTag) in
        SOME (m1, v)
      | [(v, e, SOME Inline)] =>
        let m1 = insert_m m v e (insert_set (insert_set mods_empty RecursiveTag) InlineTag) in
        SOME (m1, v)
      | [(v, e, SOME Inlineable)] =>
        let m1 = insert_m m v e (insert_set mods_empty RecursiveTag) in
        SOME (m1, v)
      | _ => NONE
    ) in
    case r of
    | SOME (m_d, designated_v) =>
      MAP (λ(v, e). if v = designated_v then m else m_d) vbs
    | NONE =>
      MAP (λ(v, e). m) vbs
End

(*
It can be the case that we create sth like:
```
(\x -> x + 1) y
```
by inlining in the App case. The problem now is that
```
(\x -> x + 1) y ≠ let x = y in x + 1
```
And so going further won't do anything
*)
Definition App_Lam_to_Lets_def:
  App_Lam_to_Lets (App a (Lam _ vs b) es) =
    (if LENGTH es < LENGTH vs (* not fully applied *) then NONE else
       let es1 = TAKE (LENGTH vs) es in
       let es2 = DROP (LENGTH vs) es in
         SOME $ SmartApp a (Lets a (ZIP (vs,es1)) b) es2) ∧
  App_Lam_to_Lets e = NONE
End

Definition lookup_ctx_def:
  lookup_ctx m ctx v =
    if elem_set (inline_set ctx) v ∨ elem_set (conlike_set ctx) v
    then lookup m v
    else NONE
End

(*
end-to-end case simpl example:

list_size l =
  case l of
  | [] => 0
  | x::xs => 1 + list_size xs
  << given >>
list_size (1::2::3::[])
==>
let l = (1::2::3::[])
case l of
| [] => 0
| x::xs => 1 + list_size xs
==>
case (1::2::3::[]) of
| [] => 0
| x::xs => 1 + list_size xs
==>
let tmp = (1::2::3::[])
let x = 1
let xs = (2::3::[])
1 + list_size xs

might also want to handle prim operations e.g. `if`
 *)

(* 
case (Prim a (Cons c_name) es) of
...
| (c_name, vs) => res
...
==>
let tmp = (Prim a op es)
let vs_1 = es_1
let vs_2 = es_2
...
res
*)
Definition case_simp_def:
  case_simp exp =
    case exp of
    | Case a scrutinee p_name bs fallthrough => (
      case scrutinee of
      | Prim a (Cons c_name) es => (
        let matches = FILTER (λ(v, vs, e). v = c_name ∧ LENGTH vs = LENGTH es) bs in
        case matches of
        | [(v, vs, e)] =>
          let param_bindings = Lets a (ZIP (vs, es)) e in
          SOME (Lets a [(p_name, scrutinee)] param_bindings)
        | _ => NONE
      )
      | _ => NONE
    )
    | Let a v e_b e => (
      case case_simp e of
      | NONE => NONE
      | SOME e1 => SOME (Let a v e e1)
    )
    | _ => NONE
End

(* 
TODO(kπ) in paper:
- explain the correct semantics of INLINEABLE
- update implementation
- implement stip_lets function
*)
(*
- filetest function in selftest.ml -- inspiration for testing
*)
(*
  Annots meaning:
  - inline name -> add to bindings and to inline_set (skip some checks at use site)
  - inlineable -> add to bindings but not to inline_set (check normally at use site)
  - inline + conlike name -> always add to bindings ++ add to conlike_set (conlike set forces inlining the bindings)
  - noinline name -> don't add to bindings (or remove from bindings)
  - inlinehere name -> add to conlike set (for the current scope) if it's in the bindings
  - #(__inline) name -> force inline the expression if it's in the bindings

  Might have to add some more checks at the use site. So we can distinguish conlike set and inline set.

  Context:
  - conlike set: forces inlining the bindings
  - inline set: says that you should inline when possible
  Others are a result of inlineable and should only be inlined when forced using inlinehere or #(__inline)
*)
(*
//TODO(kπ) be more careful when inlining Recs, might want to remove the binding from the map after using it (so we don't inline too many times)
  Actually, maybe we just remove it from the inline set (or conlike set) and allow inlining later if some simplification will be triggered
  Proposition:
  - for Rec that is conslike, we allways inlne it
  - for Rec that is inline, we inline it if there is a simplification that can be triggered
    but then how do we easily check if there is a simplification that can be triggered?
*)
Definition inline_def:
  inline (m: ('a cexp # inline_mods) var_map) ns (cl: num) (ctx: 'a inline_ctx) (Var (a: 'a) v) = (
    let exp = Var a v in
    case lookup m v of
    | NONE => (exp, ns)
    | SOME (e, mods) =>
      if should_inline_var (inline_heuristic ctx) v e mods ∧ cl > 0 then
        inline m ns (cl - 1) ctx e
      else (exp, ns)
  ) ∧
  inline m ns cl ctx (App a e es) = (
    let (es1, ns1) = inline_list m ns cl ctx es in
    let exp = App a e es1 in
    case e of
    | Var _ v => (
      case lookup m v of
      | NONE => (exp, ns1)
      | SOME (e_m, mods) =>
        if should_inline_app (inline_heuristic ctx) v e_m es1 mods ∧ cl > 0 then
          let (exp1, ns2) = freshen_cexp (App a e_m es1) ns1 in
          case App_Lam_to_Lets exp1 of
          | NONE => (exp, ns1)
          | SOME exp2 => inline m ns2 (cl - 1) ctx exp2
        else (exp, ns1)
    )
    | _ => (
      let (e1, ns2) = inline m ns1 cl ctx e in
      (App a e1 es1, ns2)
    )
  ) ∧
  inline m ns cl ctx (Let a v e_b e) = (
    let m1 = remember m ctx v e_b in
    let (e_b1, ns3) = inline m ns cl ctx e_b in
    let (e1, ns4) = inline m1 ns3 cl ctx e in
    (Let a v e_b1 e1, ns4)
    ) ∧
  inline m ns cl ctx (Letrec a [(v, er)] e) = (
    let m1 = remember_specialise m ctx v er in
    let (er1, ns1) = inline m ns cl ctx er in
    let (e1, ns2) = inline m1 ns1 cl ctx e in
    (Letrec a [(v, er1)] e1, ns2)
  ) ∧
  inline m ns cl ctx (Letrec a vbs e) = (
    let m1 = remember_Recs m ctx vbs in
    let ms = designated_rec_ms m vbs in
    let (es1, ns1) = inline_recs ms ns cl ctx (MAP SND vbs) in
    let (e1, ns2) = inline m1 ns1 cl ctx e in
    (Letrec a (MAP2 (λ(v,_) x. (v, x)) vbs es1) e1, ns2)
  ) ∧
  inline m ns cl ctx (Lam a vs e) = (
    let (e1, ns1) = inline m ns cl ctx e in
    (Lam a vs e1, ns1)
  ) ∧
  inline m ns cl ctx (Prim a op es) = (
    let (es1, ns1) = inline_list m ns cl ctx es in
    (Prim a op es1, ns1)
  ) ∧
  inline m ns cl ctx (Case a e v bs f) = (
    let (e1, ns1) = inline m ns cl ctx e in
    let (f3, ns3) = (
      case f of
      | NONE => (NONE, ns2)
      | SOME (vs, e) =>
        let (e4, ns4) = inline m ns2 cl ctx e in
        (SOME (vs, e4), ns4)
    ) in
    let exp1 = Case a e1 v (MAP2 (λ(v, vs, _) e. (v, vs, e)) bs bs) f3 in
    case case_simp exp1 of
    | SOME exp2 => inline m ns3 cl ctx exp2 (* //TODO might need (cl - 1) *)
    | NONE => (exp1, ns3)
  ) ∧
  inline m ns cl ctx (NestedCase a e v p e' bs) =
    (NestedCase a e v p e' bs, ns) ∧
  inline m ns cl ctx (Annot a annot e) = (
    let exp = Annot a annot e in
    let m1 = update_inline_scope m exp in
    let (e1, ns1) = inline m1 ns cl ctx e in
    (Annot a annot e1, ns1)
  ) ∧
  inline_list m ns cl ctx [] = ([], ns) ∧
  inline_list m ns cl ctx (e::es) = (
    let (e1, ns1) = inline m ns cl ctx e in
    let (es2, ns2) = inline_list m ns1 cl ctx es in
    (e1::es2, ns2)
  ) ∧
  inline_recs [] ns cl ctx [] = ([], ns) ∧
  inline_recs (m::ms) ns cl ctx (e::es) = (
    let (e1, ns1) = inline m ns cl ctx e in
    let (es1, ns2) = inline_recs ms ns1 cl ctx es in
    (e1::es1, ns2)
  )
Termination
  WF_REL_TAC `inv_image ($< LEX $<) $ λx. case x of
    | INL (m, ns, cl, ctx, e) => (cl, cexp_size (K 0) e)
    | INR y => case y of
      | INL (m, ns, cl, ctx, es) => (cl, list_size (cexp_size (K 0)) es)
      | INR (ms, ns, cl, ctxs, es) => (cl, list_size (cexp_size (K 0)) es)`
  \\ gvs [list_size_def]
  \\ fs [cexp_size_eq] \\ rw [] \\ gvs []
  \\ qspec_then `vbs` assume_tac cexp_size_lemma \\ fs []
  \\ qspec_then ‘bs’ assume_tac size_lemma \\ fs []
  \\ rename1 `MAP SND fs`
  \\ qspec_then `fs` assume_tac cexp_size_lemma \\ fs []
  \\ cheat
End

Definition inline_all_def:
  inline_all cl hr hi e =
    let (e1, s) = freshen_cexp e (boundvars_of e)
    in let (inlined_e, _) = inline empty s cl (InlineCtx hr hi empty empty) e1
    in dead_let inlined_e
End

Triviality cexp_size_lemma2:
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
    in if n1 < 0 then n1 else tree_size_heuristic_rec n1 e') ∧
  tree_size_heuristic_rec n (Annot a annot e) =
    tree_size_heuristic_rec (n - 1) e
Termination
  WF_REL_TAC ‘measure (λx. case x of
    | (n, e) => cexp_size (K 0) e)’
  \\ fs [cexp_size_eq] \\ rw [] \\ gvs []
  \\ imp_res_tac cexp_size_lemma2 \\ fs []
End

Definition tree_size_heuristic_def:
  tree_size_heuristic n e =
    (tree_size_heuristic_rec n e ≥ 0)
End

Definition false_heuristic_def:
  false_heuristic _ = F
End

Definition true_heuristic_def:
  true_heuristic _ = T
End

(*******************)

Definition inline_top_level_def:
  inline_top_level c e =
    inline_all c.inlining.depth (tree_size_heuristic c.inlining.heuristic) true_heuristic e
End

(*******************)

val _ = export_theory();
