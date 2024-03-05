(*
  Elimination of dead let-bindings
*)
open HolKernel Parse boolLib bossLib;
open pure_letrec_cexpTheory;

val _ = new_theory "pure_dead_let";

(*
  dead_let keeps track of free variables as it goes
  (as in `pure_letrec_cexpTheory`)
*)

Definition dead_let_def:
  dead_let (Let c x ce1 ce2) = (
    let ce2' = dead_let ce2 in
    case lookup (get_info ce2') x of (* if x not free in ce2' *)
    | NONE   => ce2' (* remove let-binding *)
    | SOME _ => let ce1' = dead_let ce1 (* otherwise recurse *)
                in Let (union (get_info ce1') (delete (get_info ce2') x))
                    x ce1' ce2') ∧

(* Boilerplate: *)
  dead_let (Var c v) = Var (insert empty v ()) v ∧
  dead_let (Prim c cop ces) = (
    let ces' = MAP dead_let ces
    in Prim (list_union $ MAP get_info ces') cop ces') ∧
  dead_let (App c ce ces) = (
    let ces' = MAP dead_let ces;
        ce'  = dead_let ce
    in App (list_union (MAP get_info (ce'::ces'))) ce' ces') ∧
  dead_let (pure_cexp$Lam c xs ce) = (
    let ce'  = dead_let ce
    in Lam (list_delete (get_info ce') xs) xs ce') ∧
  dead_let (Letrec c fns ce) = (
    let fns' = MAP (λ(f,body). f, dead_let body) fns;
        ce'  = dead_let ce;
        c'   = list_delete
                (list_union (get_info ce' :: MAP (λ(f,body). get_info body) fns'))
                (MAP FST fns')
    in Letrec c' fns' ce') ∧
  dead_let (Case c ce x css us) = (
    let ce'  = dead_let ce;
        css' = MAP (λ(cn,vs,ce). cn, vs, dead_let ce) css;
        us'  = OPTION_MAP (λ(cn_ars,ce). cn_ars, dead_let ce) us;
        c'   = union (get_info ce') $ combin$C delete x $ list_union $
                (case us' of NONE => empty | SOME (_,ce') => get_info ce') ::
                  MAP (λ(cn,vs,ce). list_delete (get_info ce) vs) css'
    in Case c' ce' x css' us') ∧
  dead_let (NestedCase c ce x p pce pces) = (
    let ce'   = dead_let ce;
        pce'  = dead_let pce;
        pces' = MAP (λ(p,ce). p, dead_let ce) pces;
        c'    = union (get_info ce') $ combin$C delete x $ list_union $
                  MAP (λ(p,ce). list_delete (get_info ce) (cepat_vars_l p)) $
                    (p,pce')::pces'
    in NestedCase c' ce' x p pce' pces') ∧
  dead_let (Annot c annot ce) =
    let ce'   = dead_let ce
    in Annot (get_info ce') annot ce'
Termination
  WF_REL_TAC `measure $ cexp_size (K 0)`
End

val _ = export_theory();
