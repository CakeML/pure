
open HolKernel Parse boolLib bossLib term_tactic pairTheory listTheory;
open thunk_cexpTheory mlmapTheory mlstringTheory pred_setTheory var_setTheory;

val _ = new_theory "thunk_split_Forcing_Lam";

Theorem size_eq:
  ∀l. list_size cexp_size l = cexp8_size l
Proof
  Induct >> simp [list_size_def, cexp_size_def]
QED

Theorem size_eq2:
  ∀l. cexp6_size l = list_size cexp_size (MAP SND l) + list_size mlstring_size (MAP FST l)
Proof
  Induct >> simp [cexp_size_def, FORALL_PROD, list_size_def]
QED

Theorem size_eq_case:
  ∀l. cexp2_size l = list_size cexp_size (MAP (SND o SND) l)
                     + list_size mlstring_size (MAP FST l)
                     + list_size (list_size mlstring_size) (MAP (FST o SND) l)
Proof
  Induct >> simp [cexp_size_def, FORALL_PROD, list_size_def]
QED

Definition extract_names_def:
  extract_names (thunk_cexp$Var v) = insert_var empty_vars v ∧
  extract_names (thunk_cexp$Lam ns x) = delete_vars (extract_names x) ns ∧
  extract_names (Letrec xs y) =
    (let s = extract_names_list (extract_names y) (MAP SND xs) in
       delete_vars s (MAP FST xs)) ∧
  extract_names (Prim p xs) =
    extract_names_list (empty_vars) xs ∧
  extract_names (Monad mop xs) =
    extract_names_list (empty_vars) xs ∧
  extract_names (App x ys) =
    extract_names_list (extract_names x) ys ∧
  extract_names (Let NONE x y) =
    var_union (extract_names x) (extract_names y) ∧
  extract_names (Let (SOME n) x y) =
    var_union (extract_names x) (delete_var (extract_names y) n) ∧
  extract_names (Case n ys eopt) =
    (let s = case eopt of
       | NONE => empty_vars
       | SOME (a,e) => (extract_names e) in
       insert_var (extract_names_rows s ys) n) ∧
  extract_names (Box x) = extract_names x ∧
  extract_names (Delay x) = extract_names x ∧
  extract_names (Force x) = extract_names x ∧
  extract_names_list s [] = s ∧
  extract_names_list s (x::xs) =
    extract_names_list (var_union s (extract_names x)) xs ∧
  extract_names_rows s [] = s ∧
  extract_names_rows s ((_, vs, x)::xs) =
    extract_names_rows (var_union s (delete_vars (extract_names x) vs)) xs
Termination
  WF_REL_TAC `measure $ λx. case x of
              | INL x => cexp_size x
              | INR (INL x) => list_size cexp_size (SND x)
              | INR (INR x) => list_size cexp_size (MAP (SND o SND) (SND x))`
  \\ fs [pure_cexpTheory.cexp_size_eq] \\ rw [list_size_def]
  >~ [‘list_size cexp_size (MAP SND pes)’] >-
    (Induct_on ‘pes’ \\ fs [listTheory.list_size_def,FORALL_PROD]
     \\ rw [] \\ fs [cexp_size_def])
  >- simp [size_eq_case, combinTheory.o_DEF]
End

Definition thunk_names_def:
  thunk_names e = extract_names e
End

Definition find_forcing_def:
  (find_forcing (h::tl) (Let (SOME h2) (Force (Var h3)) e) =
   if h = h3
   then
     let (keeped, changed, bL, e, s, b1, b2, s2) = find_forcing tl e in
       if contains_var h s
       then (h::keeped, h2::changed, T::bL, e, s, T,
             b2 ∧ h ≠ h2 ∧ ¬contains_var h s2 ∧ ¬contains_var h2 s2, insert_var (insert_var s2 h) h2)
       else (keeped, h2::changed, T::bL, e, s, T,
             b2 ∧ h ≠ h2 ∧ ¬contains_var h s2 ∧ ¬contains_var h2 s2, insert_var (insert_var s2 h) h2)
   else
     let (keeped, changed, bL, e, s, b1, b2, s2) = find_forcing tl (Let (SOME h2) (Force (Var h3)) e) in
       (keeped, h::changed, F::bL, e, s, b1,
             b2 ∧ ¬contains_var h s2, insert_var s2 h)) ∧
  (find_forcing l e = ([], l, MAP (K F) l, e, thunk_names e, F, ALL_DISTINCT l, insert_vars empty_vars l))
End

Definition check_hypothesis_def:
  check_hypothesis b v s = (b ∧ ¬contains_var v s)
End

Definition my_function_def:
  (my_function s (Var v) = (s, Var v)) ∧
  (my_function s (App f g) =
     let (s, f) = my_function s f in
       let (s, g) = my_function_list s g in
         (s, App f g)) ∧
  (my_function s (Prim op l) =
   let (s, l) = my_function_list s l in
         (s, Prim op l)) ∧
  (my_function s (Monad mop l) =
   let (s, l) = my_function_list s l in
         (s, Monad mop l)) ∧
  (my_function s (Letrec f x) =
     let (s, x) = my_function s x in
       let (s, f) = my_function_bind s f in
         (s, Letrec f x)) ∧
  (my_function s (Lam vL x) =
    let (s, x) = my_function s x in (s, Lam vL x)) ∧
  (my_function s (Let (SOME v) (Lam vL x) y) =
     let (s, x) = my_function s x in
       let (s, y) = my_function s y in
         let (l1, l2, bL, e, s_freevars, b1, b2, s_vars) = find_forcing (REV vL []) x in
           if check_hypothesis (b1 ∧ b2) v s_vars
           then
             let (v2, s) = invent_var v s in
               (s, Let (SOME v2) (Lam (REV l1 (REV l2 [])) e)
                   (Let (SOME v) (Lam vL (App (Var v2)
                                          (REV (MAP Var l1)
                                           (MAP2 (λb v. if b then Force (Var v) else Var v) (REV bL []) vL))))
                    y))
           else (s, Let (SOME v) (Lam vL x) y)) ∧
  (my_function s (Let opt x y) =
     let (s, x) = my_function s x in
       let (s, y) = my_function s y in
           (s, Let opt x y)) ∧
  (my_function s (Case n ys eopt) =
   let (s, ys) = my_function_row s ys in
     let (s, eopt) = case eopt of
                     | NONE => (s, NONE)
                     | SOME (a, e) =>
                         let (s, e) = my_function s e in (s, SOME (a, e))
     in (s, Case n ys eopt)) ∧
  (my_function s (Force e) =
     let (s, e) = my_function s e in
       (s, Force e)) ∧
  (my_function s (Delay e) =
     let (s, e) = my_function s e in
       (s, Delay e)) ∧
  (my_function s (Box e) =
     let (s, e) = my_function s e in
       (s, Box e)) ∧
  (my_function_list s [] = (s, [])) ∧
  (my_function_list s (hd::tl) =
     let (s, hd) = my_function s hd in
       let (s, tl) = my_function_list s tl in
         (s, hd::tl)) ∧
  (my_function_row s [] = (s, [])) ∧
  (my_function_row s ((v, vs, e)::tl) =
     let (s, e) = my_function s e in
       let (s, tl) = my_function_row s tl in
         (s, (v, vs, e)::tl)) ∧
  (my_function_bind s [] = (s, [])) ∧
  (my_function_bind s ((v, e)::tl) =
     let (s, e) = my_function s e in
       let (s, tl) = my_function_bind s tl in
         (s, (v, e)::tl))
Termination
  WF_REL_TAC `measure $ λx. case x of
          | INL x => cexp_size (SND x)
          | INR (INL x) => list_size cexp_size (SND x)
          | INR (INR (INL x)) => list_size (cexp_size o SND o SND) (SND x)
          | INR (INR (INR x)) => list_size (cexp_size o SND) (SND x)`
  \\ fs [pure_cexpTheory.cexp_size_eq] \\ rw []
  \\ rename1 ‘list_size _ f’
  \\ Induct_on ‘f’ \\ fs [listTheory.list_size_def,FORALL_PROD]
  \\ rw [] \\ fs [cexp_size_def]
End

val _ = export_theory ();

