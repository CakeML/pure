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
  (lift_uscore1 (NestedCase c t tv p e pes) =
     case LAST ((p,e)::pes) of
       (lp,le) => if lp = cepatUScore then
                  case dest_nestedcase le of
                    SOME (v, vnm, pes') =>
                      if tv = vnm ∧ dest_var v = SOME vnm then
                        case updlast ((p,e)::pes) pes' of
                          [] => Var c "Fail/can't happen"
                        | (p',e')::rest =>
                            NestedCase c t tv p' e' rest
                      else NestedCase c t tv p e pes
                  | NONE => NestedCase c t tv p e pes
                else
                  NestedCase c t tv p e pes) ∧
  (lift_uscore1 e = e)
End

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
