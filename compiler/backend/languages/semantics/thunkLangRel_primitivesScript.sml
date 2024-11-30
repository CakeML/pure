open HolKernel Parse boolLib bossLib listTheory;
open thunkLangTheory;

val _ = new_theory "thunkLangRel_primitives";
val _ = numLib.prefer_num ();

Datatype:
  res = Ok 'a
      | Fail
      | OOT
End

Definition isok_def[simp]:
  (isok (Ok x) = T) ∧
  (isok _ = F)
End

Definition isfail_def[simp]:
  (isfail Fail = T) ∧
  (isfail _ = F)
End

Definition isoot_def[simp]:
  (isoot OOT = T) ∧
  (isoot _ = F)
End

Definition outok_def[simp,compute]:
  outok (Ok x) = x
End

Type fuel = ``:num``;
Type trace = ``:num``;
Datatype:
  state = <| c : fuel; t : trace |>
End

Definition state_add_def[simp]:
  state_add s s' = state (s.c + s'.c) (s.t + s'.t)
End
Overload "+" = ``state_add``

Definition state_sub_def[simp]:
  state_sub s s' = state (s.c - s'.c) (s.t - s'.t)
End
Overload "-" = ``state_sub``

Definition fuel_def:
  (fuel (e : exp) : fuel = 1)
End

Definition trace_def:
  (trace (App f x) : trace = 1) ∧
  (trace e = 0)
End

Definition with_fst_def:
  with_fst f (x, y) = (f x, y)
End

Definition with_snd_def:
  with_snd f (x, y) = (x, f y)
End

Theorem FIND_pred_thm:
  (∀P xs x. FIND P xs = SOME x ⇒ P x) ∧
  (∀P xs. FIND P xs = NONE ⇒ (∀x. MEM x xs ⇒ ¬(P x)))
Proof
  rw []
  >> Induct_on `xs` >> gvs [FIND_thm]
  >> ntac 2 (rw [])
QED

Theorem FIND_MEM_thm:
  ∀P xs x. FIND P xs = SOME x ⇒ MEM x xs
Proof
  Induct_on `xs` >> gvs [FIND_thm]
  >> rw []
  >> res_tac
  >> rw []
QED

Theorem MEM_MAP_SND_thm:
  ∀x x' xs.
    MEM (x, x') xs ⇒ MEM x' (MAP SND xs)
Proof
  Induct_on `xs` >> gvs []
  >> rpt strip_tac
  >> rw []
  >> first_x_assum $ drule_then assume_tac
  >> rw []
QED

Theorem FIND_FST_WITH_SND_thm:
  ∀l f g.
    FIND (f ∘ FST) l = NONE
    ⇒ FIND (f ∘ FST) (MAP (with_snd g) l) = NONE
Proof
  Induct_on `l` >> gvs [FIND_thm]
  >> rw []
  >> Cases_on `h` >> gvs [with_snd_def]
QED

Theorem FIND_FST_WITH_SND_SOME_thm:
  ∀l f g x.
    FIND (f ∘ FST) l = SOME x
    ⇒ FIND (f ∘ FST) (MAP (with_snd g) l)
        = SOME (with_snd g x)
Proof
  Induct_on `l` >> gvs [FIND_thm]
  >> rw []
  >> Cases_on `h` >> gvs [with_snd_def]
QED

Theorem MAP_FST_WITH_SND_thm:
  ∀l f g.
    MAP (f ∘ FST) (MAP (with_snd g) l)
    = MAP (f ∘ FST) l
Proof
  Induct_on `l` >> gvs []
  >> rw []
  >> Cases_on `h` >> gvs [with_snd_def]
QED

Theorem MAP_SND_MAP_WITH_FST_thm:
  ∀f l.
    MAP SND (MAP (with_fst f) l) = MAP SND l
Proof
  Induct_on `l` >> gvs []
  >> rw []
  >> Cases_on `h` >> gvs [with_fst_def]
QED

Theorem EVERY_MAP_WITH_FST_thm:
  ∀P f l.
    EVERY (P ∘ FST) (MAP (with_fst f) l)
    ⇔ EVERY (P ∘ f ∘ FST) l
Proof
  Induct_on `l` >> gvs []
  >> rw []
  >> Cases_on `h` >> gvs [with_fst_def]
QED

Theorem MAP_WITH_FST_WITH_SND_thm:
  ∀f g l.
    MAP (with_fst f) (MAP (with_snd g) l)
    = MAP (with_snd g) (MAP (with_fst f) l)
Proof
  Induct_on `l` >> gvs []
  >> rw []
  >> Induct_on `h` >> gvs [with_fst_def, with_snd_def]
QED

Theorem NOT_MEM_EVERY_thm:
  ∀x l. ¬MEM x l ⇒ EVERY (λy. y ≠ x) l
Proof
  Induct_on `l` >> gvs []
QED

val _ = export_theory()
