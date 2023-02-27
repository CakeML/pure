(*
  Compilation from pureLang to thunkLang
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_namesTheory thunk_cexpTheory pure_cexpTheory thunk_split_Delay_LamTheory;
open pure_comp_confTheory;

val _ = new_theory "pure_to_thunk";

val _ = set_grammar_ancestry
  ["pure_cexp", "thunk_cexp", "pure_names", "thunk_split_Delay_Lam"];

Definition any_el_def:
  any_el n [] = thunk_cexp$Prim (AtomOp Add) [] ∧
  any_el n (x::xs) = if n = 0 then x else any_el (n-1) xs
End

Definition get_var_name_def:
  get_var_name ((pure_cexp$Var c v)::_) = v ∧
  get_var_name _ = strlit "forced"
End

Definition mk_delay_def:
  mk_delay (x:thunk_cexp$cexp) =
    case x of
    | Force (Var n) => Var n
    | _             => Delay x
End

Definition must_delay_def:
  must_delay s ⇔
    s = strlit "Bind"   ∨
    s = strlit "Handle" ∨
    s = strlit "Act"    ∨
    s = strlit "Length" ∨
    s = strlit "Alloc"  ∨
    s = strlit "Deref"  ∨
    s = strlit "Update"
End

Definition to_thunk_def:
  to_thunk (s:vars) (pure_cexp$Var c v) =
    (thunk_cexp$Force (Var v),s) ∧
  to_thunk s (Lam c ns x) =
    (let (x,s) = to_thunk s x in (Lam ns x,s)) ∧
  to_thunk s (App c x ys) =
    (let (x,s) = to_thunk s x in
     let (ys,s) = to_thunk_list s ys in
       (App x (MAP mk_delay ys), s)) ∧
  to_thunk s (Letrec c xs y) =
    (let (y,s) = to_thunk s y in
     let (ys,s) = to_thunk_list s (MAP SND xs) in
       (Letrec (MAP2 (λ(n,_) y. (n, Delay y)) xs ys) y,s)) ∧
  to_thunk s (Let c v x y) =
    (let (x,s) = to_thunk s x in
     let (y,s) = to_thunk s y in
       (Let (SOME v) (mk_delay x) y,s)) ∧
  to_thunk s (Prim c p ys) =
    (let (xs,s) = to_thunk_list s ys in
       case p of
       | Cons t => (Prim (Cons t) (if must_delay t
                                   then MAP Delay xs
                                   else MAP mk_delay xs),s)
       | AtomOp a => (Prim (AtomOp a) xs,s)
       | Seq =>
           let x = any_el 0 xs in
           let y = any_el 1 xs in
           let (fresh,s) = invent_var (get_var_name ys) s in
             (Let (SOME fresh) x y,s)) ∧
  to_thunk s (Case c x v ys opt) =
    (let (x,s) = to_thunk s x in
     let (rs,s) = to_thunk_list s (MAP (SND o SND) ys) in
     let (w,s) = invent_var (v ^ strlit "_forced") s in
       case opt of
       | NONE =>
           ((Let (SOME v) (mk_delay x) $
             Let (SOME w) (Force (Var v)) $
              Case w (MAP2 (λ(c,n,_) y. (c,n,y)) ys rs) NONE,s))
       | SOME (a,y) =>
          let (y,s) = to_thunk s y in
            ((Let (SOME v) (mk_delay x) $
              Let (SOME w) (Force (Var v)) $
               Case w (MAP2 (λ(c,n,_) y. (c,n,y)) ys rs) (SOME (a,y))),s)) ∧
  to_thunk s (NestedCase c g gv p e pes) = to_thunk s e ∧
  to_thunk_list s [] = ([],s) ∧
  to_thunk_list s (x::xs) =
    (let (x,s) = to_thunk s x in
     let (xs,s) = to_thunk_list s xs in
       (x::xs,s))
Termination
  WF_REL_TAC `measure $ λx. case x of
              | INL x => cexp_size (K 0) (SND x)
              | INR x => list_size (cexp_size (K 0)) (SND x)`
  \\ fs [pure_cexpTheory.cexp_size_eq] \\ rw []
  >~ [‘list_size (cexp_size (K 0)) (MAP SND xs)’] >-
    (pop_assum kall_tac
     \\ Induct_on ‘xs’ \\ fs [listTheory.list_size_def,FORALL_PROD]
     \\ rw [] \\ fs [basicSizeTheory.pair_size_def])
  >~ [‘list_size (cexp_size (K 0)) (MAP (λx. SND (SND x)) ys)’] >-
    (Induct_on ‘ys’ \\ fs [listTheory.list_size_def,FORALL_PROD]
     \\ rw [] \\ fs [basicSizeTheory.pair_size_def])
End

Definition compile_to_thunk_def:
  compile_to_thunk (c:compiler_opts) e =
    let (e1, vs) = to_thunk (pure_names e) e in
    let (e2, vs2) = split_Delayed_Lam e1 vs (empty compare) in
      e2
End

val _ = export_theory ();
