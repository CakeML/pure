(*
  Compiler expressions for stateLang
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory pure_semanticsTheory arithmeticTheory envLangTheory
     mlstringTheory;

val _ = new_theory "env_cexp";

val _ = set_grammar_ancestry ["envLang","mlstring"];

val _ = numLib.prefer_num();

Type vname = “:mlstring”

Datatype:
  cop = Cons mlstring
      | AtomOp atom_op
End

Datatype:
  cexp = Var vname
       | Prim cop (cexp list)
       | App cexp cexp
       | Lam vname cexp
       | Letrec ((vname # cexp) list) cexp
       | Let (vname option) cexp cexp
       | If cexp cexp cexp
       | Delay cexp
       | Box cexp
       | Force cexp
       | Case cexp vname ((vname # (vname list) # cexp) list)
       (* monads *)
       | Ret cexp
       | Bind cexp cexp
End

Definition op_of_def[simp]:
  op_of ((Cons n):cop) = (Cons (explode n)):op ∧
  op_of (AtomOp m) = AtomOp m
End

Definition exp_of_def:
  exp_of ((Var n):cexp) = (Var (explode n)):envLang$exp ∧
  exp_of (Prim p xs) = Prim (op_of p) (MAP exp_of xs) ∧
  exp_of (App x y) = App (exp_of x) (exp_of y) ∧
  exp_of (Lam v x) = Lam (explode v) (exp_of x) ∧
  exp_of (Letrec fs x) = Letrec (MAP (λ(n,y). (explode n,exp_of y)) fs) (exp_of x) ∧
  exp_of (Let v x y) = Let (OPTION_MAP explode v) (exp_of x) (exp_of y) ∧
  exp_of (If x y z) = If (exp_of x) (exp_of y) (exp_of z) ∧
  exp_of (Delay x) = Delay (exp_of x) ∧
  exp_of (Box x) = Box (exp_of x) ∧
  exp_of (Force x) = Force (exp_of x) ∧
  exp_of (Delay x) = Delay (exp_of x) ∧
  exp_of (Case e v rs) = Let (SOME (explode v)) (exp_of e)
                           (rows_of (explode v) (MAP (λ(cn,vs,e).
                              (explode cn, MAP explode vs, exp_of e)) rs)) ∧
  (* monads *)
  exp_of (Ret x) = Prim (Cons "Ret") [exp_of x] ∧
  exp_of (Bind x y) = Prim (Cons "Bind") [Delay (exp_of x); Delay (exp_of y)]
Termination
  WF_REL_TAC ‘measure cexp_size’
End

Theorem exp_of_def[simp] = exp_of_def |> CONV_RULE (DEPTH_CONV ETA_CONV);

val _ = export_theory();
