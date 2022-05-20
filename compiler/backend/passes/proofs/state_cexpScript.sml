(*
  Compiler expressions for stateLang
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory pure_semanticsTheory arithmeticTheory stateLangTheory
     mlstringTheory;

val _ = new_theory "state_cexp";

val _ = set_grammar_ancestry ["stateLang","mlstring"];

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
       | FFI string         (* make an FFI call                         *)
End

Datatype:
  cexp = (* stateLang expressions *)
       | Var vname                                 (* variable                *)
       | App csop (cexp list)                      (* application - prim/fun  *)
       | Lam (vname option) cexp                   (* lambda                  *)
       | Letrec ((vname # vname # cexp) list) cexp (* mutually recursive funs *)
       | Let (vname option) cexp cexp              (* non-recursive let       *)
       | If cexp cexp cexp                         (* if-then-else            *)
       | Case cexp vname ((vname # vname list # cexp) list)        (* case of *)
       | Raise cexp                                (* raise an exception      *)
       | Handle cexp vname cexp                    (* handle an exception     *)
       | HandleApp cexp cexp                       (* handle that takes fun   *)
End

Definition sop_of_def[simp]:
  sop_of (AppOp:csop) = (AppOp:sop) ∧
  sop_of (Cons n) = Cons (explode n) ∧
  sop_of (AtomOp m) = AtomOp m ∧
  sop_of Alloc = Alloc
End

Definition exp_of_def:
  exp_of ((Var n):cexp) = (Var (explode n)):exp ∧
  exp_of (App op xs) = App (sop_of op) (MAP exp_of xs) ∧
  exp_of (Lam vn x) = Lam (OPTION_MAP explode vn) (exp_of x) ∧
  exp_of (Letrec funs x) =
    Letrec (MAP (λ(f,v,y). (explode f,Lam (SOME (explode v)) (exp_of y))) funs) (exp_of x) ∧
  exp_of (Let vn x y) = Let (OPTION_MAP explode vn) (exp_of x) (exp_of y) ∧
  exp_of (If x y z) = If (exp_of x) (exp_of y) (exp_of z) ∧
  exp_of (Case x v rows) =
    Case (exp_of x) (explode v) (MAP (λ(v,vs,y). (explode v,MAP explode vs,exp_of y)) rows) ∧
  exp_of (Raise x) = Raise (exp_of x) ∧
  exp_of (Handle x v y) = Handle (exp_of x) (explode v) (exp_of y) ∧
  exp_of (HandleApp x y) = HandleApp (exp_of x) (exp_of y)
Termination
  WF_REL_TAC ‘measure cexp_size’
End

Theorem exp_of_def[simp] = exp_of_def |> CONV_RULE (DEPTH_CONV ETA_CONV);

val _ = export_theory();
