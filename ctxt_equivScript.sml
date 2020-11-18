
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     ltreeTheory llistTheory bagTheory pure_langTheory;


val _ = new_theory "ctxt_equiv";

Datatype:
  ctxt = Hole
       | Prim (('a,'b) op) (('a,'b) exp list) ctxt (('a,'b) exp list)
       | AppL ctxt (('a,'b) exp)
       | AppR (('a,'b) exp) ctxt
       | Lam vname ctxt
       | LetrecL ((fname # vname # (('a,'b) exp)) list)
                  (fname # vname # ctxt)
                 ((fname # vname # (('a,'b) exp)) list) (('a,'b) exp)
       | LetrecR ((fname # vname # ('a,'b) exp) list) ctxt
       | CaseL ctxt vname ((vname # vname list # ('a,'b) exp) list)
       | CaseR (('a,'b) exp) vname ((vname # vname list # ('a,'b) exp) list)
                                    (vname # vname list # ctxt)
                                   ((vname # vname list # ('a,'b) exp) list)
End

Definition plug_def:
  plug Hole n = n ∧
  plug (AppL h y) n = App (plug h n) y ∧
  plug (AppR x h) n = App x (plug h n) ∧
  plug (Lam v h) n = Lam v (plug h n) ∧
  plug (LetrecL xs1 (f,v,h) xs2 x) n = Letrec (xs1 ++ [(f,v,plug h n)] ++ xs2) x ∧
  plug (LetrecR xs h) n = Letrec xs (plug h n) ∧
  plug (CaseL h w rows) n = Case (plug h n) w rows ∧
  plug (CaseR x w rows1 (v,vs,h) rows2) n =
    Case x w (rows1 ++ [(v,vs,plug h n)] ++ rows2)
End

Definition exp_sim_def:
  exp_sim c x y ⇔
    set (freevars x) = set (freevars y) ∧
    ∀bindings.
      set (MAP FST bindings) = set (freevars y) ⇒
      exp_rel c (bind bindings x) (bind bindings y)
End

Theorem exp_sim_closed:
  closed x ∧ closed y ⇒
  exp_sim c x y = exp_rel c x y
Proof
  fs [closed_def,exp_sim_def,bind_def]
QED

Theorem exp_sim:
  exp_sim c x y ⇒ exp_sim c (plug h x) (plug h y)
Proof
  cheat (* help? *)
QED

val _ = export_theory();
