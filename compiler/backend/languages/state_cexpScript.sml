(*
  Compiler expressions for stateLang
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory pure_semanticsTheory arithmeticTheory mlstringTheory;

val _ = new_theory "state_cexp";

val _ = set_grammar_ancestry ["pure_exp","mlstring"];

val _ = numLib.prefer_num();

Type vname = “:mlstring”

Datatype:
  csop = (* Primitive operations *)
       | AppOp              (* function application                     *)
       | Cons mlstring      (* datatype constructor                     *)
       | AtomOp atom_op     (* primitive parametric operator over Atoms *)
       | Alloc              (* allocate an array                        *)
       | Ref                (* allocates an array in a different way    *)
       | Length             (* query the length of an array             *)
       | Sub                (* de-reference a value in an array         *)
       | UnsafeSub          (* de-reference but without a bounds check  *)
       | Update             (* update a value in an array               *)
       | UnsafeUpdate       (* update without a bounds check            *)
       | FFI mlstring       (* make an FFI call                         *)
End

Datatype:
  cexp = (* stateLang expressions *)
       | Var vname                                 (* variable                *)
       | App csop (cexp list)                      (* application - prim/fun  *)
       | Lam (vname option) cexp                   (* lambda                  *)
       | Letrec ((vname # vname # cexp) list) cexp (* mutually recursive funs *)
       | Let (vname option) cexp cexp              (* non-recursive let       *)
       | If cexp cexp cexp                         (* if-then-else            *)
       | Case vname ((vname # vname list # cexp) list) (cexp option)  (* case *)
       | Raise cexp                                (* raise an exception      *)
       | Handle cexp vname cexp                    (* handle an exception     *)
       | HandleApp cexp cexp                       (* handle that takes fun   *)
End

Overload True  = “App (Cons (strlit "True"))  []”;
Overload False = “App (Cons (strlit "False")) []”;

Overload "app" = “λe1 e2. App AppOp [e1;(e2:cexp)]”;
Overload "Unit" = “App (Cons (strlit "")) [] :cexp”;

Overload IntLit = “λi. App (AtomOp (Lit (Int i))) []”
Overload StrLit = “λs. App (AtomOp (Lit (Str s))) []”
Overload Eq = “λx y. App (AtomOp Eq) [x; y]”

(* We require the correct number of arguments to be passed to the following.
   We could specify this for all operations, but it isn't necessary *)
Definition op_args_ok_def:
  op_args_ok (AtomOp $ Lit (Int i)) n = (n = 0n) ∧
  op_args_ok (AtomOp $ Lit (Str s)) n = (n = 0) ∧
  op_args_ok (AtomOp $ Lit _)       _ = F ∧
  op_args_ok (AtomOp $ Div)         n = (n = 2) ∧
  op_args_ok (AtomOp $ Mod)         n = (n = 2) ∧
  op_args_ok (AtomOp $ Elem)        n = (n = 2) ∧
  op_args_ok (AtomOp $ Substring)   n = (n = 2 ∨ n = 3) ∧
  op_args_ok (AtomOp $ StrLeq)      n = (n = 2) ∧
  op_args_ok (AtomOp $ StrLt)       n = (n = 2) ∧
  op_args_ok (AtomOp $ StrGeq)      n = (n = 2) ∧
  op_args_ok (AtomOp $ StrGt)       n = (n = 2) ∧
  op_args_ok (AtomOp $ Message s)   n = F ∧
  op_args_ok  Alloc                 n = (n = 2) ∧
  op_args_ok (FFI ch)               n = (n = 1) ∧
  op_args_ok (_ :csop)              n = T
End

Definition cexp_wf_def:
  cexp_wf (Var v :cexp) = T ∧
  cexp_wf (App op es) = (EVERY cexp_wf es ∧ op_args_ok op (LENGTH es) ∧
    ∀ch. op = FFI ch ⇒ ch ≠ «») ∧
  cexp_wf (Lam (SOME x) e) = cexp_wf e ∧
  cexp_wf (Letrec funs e) = (
    cexp_wf e ∧ EVERY (λ(v,x,e). cexp_wf e) funs ∧ ALL_DISTINCT (MAP FST funs)) ∧
  cexp_wf (Let (SOME x) e1 e2) = (cexp_wf e1 ∧ cexp_wf e2) ∧
  cexp_wf (If e e1 e2) = (cexp_wf e ∧ cexp_wf e1 ∧ cexp_wf e2) ∧
  cexp_wf (Case v css d) = (
    OPTION_ALL cexp_wf d ∧ ALL_DISTINCT (MAP FST css) ∧
    EVERY (λ(cn,vs,ce). ALL_DISTINCT vs ∧ cexp_wf ce) css) ∧
  cexp_wf (Raise e) = cexp_wf e ∧
  cexp_wf (Handle e1 x e2) = (cexp_wf e1 ∧ cexp_wf e2) ∧
  cexp_wf _ = F
Termination
  WF_REL_TAC `measure cexp_size`
End

Definition cns_arities_def:
  cns_arities (Var v :cexp) = {} ∧
  cns_arities (App op es) = (
    (case op of | Cons cn => {{explode cn, LENGTH es}} | _ => {}) ∪
      BIGUNION (set (MAP cns_arities es))) ∧
  cns_arities (Lam x e) = cns_arities e ∧
  cns_arities (Letrec funs e) =
    BIGUNION (set (MAP (λ(v,x,e). cns_arities e) funs)) ∪ cns_arities e ∧
  cns_arities (Let x e1 e2) = cns_arities e1 ∪ cns_arities e2 ∧
  cns_arities (If e e1 e2) = cns_arities e ∪ cns_arities e1 ∪ cns_arities e2 ∧
  cns_arities (Case v css d) = set (MAP (λ(cn,vs,e). explode cn, LENGTH vs) css) INSERT
    (case d of NONE => {} | SOME e => cns_arities e) ∪
    BIGUNION (set (MAP (λ(cn,vs,e). cns_arities e) css)) ∧
  cns_arities (Raise e) = cns_arities e ∧
  cns_arities (Handle e1 x e2) = cns_arities e1 ∪ cns_arities e2 ∧
  cns_arities (HandleApp e1 e2) = cns_arities e1 ∪ cns_arities e2
Termination
  WF_REL_TAC `measure cexp_size`
End

val _ = export_theory();
