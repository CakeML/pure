
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     ltreeTheory llistTheory bagTheory quotient_llistTheory;

val _ = new_theory "exp";

(* AST for a small functional language *)

Type vname = “:string”  (* variable name *)
Type fname = “:string”  (* function name *)

(*configuration record for the parametric atoms.

   parAtomOp:
     It takes an element of type 'a (from AtomOp) and returns a
     function that takes a "'b list" element and SOME b if the
     number of arguments is correct, NONE otherwise

*)
Datatype:
  conf = <| parAtomOp  : 'a -> 'b list -> 'b option; |>
End

Datatype:
  op = If               (* if-expression                            *)
     | Cons string      (* datatype constructor                     *)
     | IsEq string num  (* compare cons tag and num of args         *)
     | Proj string num  (* reading a field of a constructor         *)
     | AtomOp 'a        (* primitive parametric operator over Atoms *)
     | Lit 'b           (* parametric literal Atom                  *)
End

Datatype:
  exp = Var vname                     (* variable                   *)
      | Prim (('a,'b) op) (exp list)  (* primitive operations       *)
      | App exp exp                   (* function application       *)
      | Lam vname exp                 (* lambda                     *)
      | Letrec ((fname # vname # exp) list) exp   (* mut. rec. funs *)
      | Case exp vname ((vname # vname list # exp) list) (*case pat.*)
End

(* some abbreviations *)
Overload Let  = “λs x y. App (Lam s y) x”      (* let-expression    *)
Overload If   = “λx y z. Prim If [x; y; z]”    (* If   at exp level *)
Overload Lit  = “λa. Prim (Lit a) []”           (* Lit at exp level *)
Overload Cons = “λs. Prim (Cons s)”            (* Cons at exp level *)
Overload IsEq = “λs n x. Prim (IsEq s n) [x]”  (* IsEq at exp level *)
Overload Proj = “λs i x. Prim (Proj s i) [x]”  (* Proj at exp level *)
Overload Fail = “Prim (Lit ARB) [Prim (Lit ARB)[]]” (* causes Error *)

val _ = export_theory ();

