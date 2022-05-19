open HolKernel Parse boolLib bossLib;

open listTheory
open pure_cexpTheory

val _ = new_theory "pure_nestedcase";

Definition updlast_def[simp]:
  updlast [] rep = rep ∧
  updlast [h] rep = rep ∧
  updlast (h1::h2::t) rep = h1 :: updlast (h2::t) rep
End

Theorem updlast_EQ_NIL[simp]:
  ∀l rep. updlast l rep = [] ⇔ rep = [] ∧ LENGTH l < 2
Proof recInduct updlast_ind >> rw[]
QED

Theorem LAST_updlast:
  ∀l rep. rep ≠ [] ⇒ LAST (updlast l rep) = LAST rep
Proof
  recInduct updlast_ind >> rw[] >> gs[] >> simp[LAST_CONS_cond]
QED

Definition lift_uscore1_def:
  (lift_uscore1 (NestedCase c texp tv pes) =
   if pes = [] then NestedCase c texp tv pes
   else
     case LAST pes of
       (p,e) => if p = cepatUScore then
                  case dest_nestedcase e of
                    SOME (texp', _, pes') =>
                      (case dest_var texp' of
                         SOME vnm =>
                           if tv = vnm then
                             NestedCase c texp tv (updlast pes pes')
                           else NestedCase c texp tv pes
                       | NONE => NestedCase c texp tv pes)
                  | NONE => NestedCase c texp tv pes
                else
                  NestedCase c texp tv pes) ∧
  (lift_uscore1 e = e)
End

case x@v of
  C (p,y) =>
  D (p2,y) =>

  -->

  case x of
     C (v, y) => ....
   | _ => case x of
             D(p2,_)


             --->

             case x of
               C(v1,..)
               D(v1,..)

Overload lift_uscore = “gencexp_recurse lift_uscore1”

Theorem lift_uscore_thm =
        gencexp_recurse_def
          |> CONJUNCTS
          |> map SPEC_ALL
          |> map (Q.INST [‘f’ |-> ‘lift_uscore1’])
          |> map GEN_ALL |> LIST_CONJ
          |> SRULE [lift_uscore1_def, SF boolSimps.ETA_ss,
                    listTheory.LAST_MAP]

val _ = export_theory();
