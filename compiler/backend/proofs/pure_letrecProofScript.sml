(*
   Verification of pure_letrec, i.e. simplification of Letrec.
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_exp_lemmasTheory mlmapTheory mlstringTheory
     (* from CakeML: *) mlmapTheory;
open pure_exp_relTheory pure_evalTheory;

val _ = new_theory "pure_letrecProof";

(*
  TODO: move the implementation to ../pure_letrecScript.sml once it's done.
*)

(*

  The motivation for these Letrec simplifications is that the parser
  will produce a giant Letrec holding all the top-level functions. It
  makes sense to split this up and clean it up as much as possible early.

  Plan for the Letrec simplifications:

    1. make a pass that ensures, for every Letrec xs y, that
       ALL_DISTINCT (MAP FST xs)

    2. split every Letrec according to top_sort_any, i.e. each Letrec becomes
       one or more nested Letrecs

    3. clean up pass:
        - remove any Letrec xs y that only bind variables that are not free in y
        - change any Letrec [(v,x)] y into Let v x y, when v not free in x

*)

Definition make_distinct_def:
  (* this could be written in a more efficient way, but perhaps this is good
     for the proofs, i.e. the implementation version might be different *)
  make_distinct [] = [] ∧
  make_distinct ((n:string,x)::xs) =
    if MEM n (MAP FST xs) then make_distinct xs else (n,x)::make_distinct xs
End

Definition distinct_def:
  distinct (Letrec xs y) = Letrec (make_distinct (MAP (λ(n,x). (n, distinct x)) xs)) y ∧
  distinct (Lam n x) = Lam n (distinct x) ∧
  distinct (Prim p xs) = Prim p (MAP distinct xs) ∧
  distinct (App x y) = App (distinct x) (distinct y) ∧
  distinct res = res
Termination
  WF_REL_TAC ‘measure exp_size’ \\ rw []
  \\ cheat
End

Theorem set_MAP_FST_make_distinct:
  ∀xs. set (MAP FST (make_distinct xs)) = set (MAP FST xs)
Proof
  Induct \\ fs [make_distinct_def,FORALL_PROD]
  \\ rw [] \\ fs [EXTENSION] \\ metis_tac []
QED

Theorem closed_distinct:
  closed x ⇒ closed (distinct x)
Proof
  cheat
QED

(* some infrastructure for the proofs *)

Inductive letrec_rel:
  (∀c n.
    letrec_rel c (Var n) (Var n))
  ∧
  (∀c n x y.
    letrec_rel c x y ⇒
    letrec_rel c (Lam n x) (Lam n y))
  ∧
  (∀c f g x y.
    letrec_rel c f g ∧ letrec_rel c x y ⇒
    letrec_rel c (App f x) (App g y))
  ∧
  (∀c n xs ys.
    LIST_REL (letrec_rel c) xs ys ⇒
    letrec_rel c (Prim n xs) (Prim n ys))
  ∧
  (∀c xs y xs1 y1 z.
    LIST_REL (letrec_rel c) (MAP SND xs) (MAP SND xs1) ∧
    MAP FST xs = MAP FST xs1 ∧ letrec_rel c y y1 ∧
    (c (Letrec xs1 y1) z ∨ Letrec xs1 y1 = z) ⇒
    letrec_rel c (Letrec xs y) z)
End

Theorem letrec_rel_subst:
  letrec_rel c x y ⇒ letrec_rel c (subst s e x) (subst s e y)
Proof
  cheat
QED

Theorem distinct_correct:
  closed x ⇒ x ≃ distinct x
Proof
  rw [] \\ irule eval_to_sim_thm \\ fs [closed_distinct]
  \\ qabbrev_tac ‘c = λx z. ∃xs y. x = Letrec ys y ∧ z = Letrec (make_distinct ys) y’
  \\ qexists_tac ‘letrec_rel c’
  \\ reverse conj_tac
  THEN1 cheat
  \\ last_x_assum kall_tac
  \\ simp [eval_to_sim_def]
  \\ rw [] \\ pop_assum kall_tac
  \\ qexists_tac ‘0’ \\ fs []
  \\ ntac 2 (pop_assum mp_tac)
  \\ qid_spec_tac ‘e2’
  \\ qid_spec_tac ‘e1’
  \\ qid_spec_tac ‘k’
  \\ fs [AND_IMP_INTRO]
  \\ ho_match_mp_tac eval_wh_to_ind \\ rw []
  THEN1
   (rename [‘Lam s x’]
    \\ fs [eval_wh_to_def]
    \\ qpat_x_assum ‘letrec_rel c (Lam s x) e2’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ rw []
    \\ fs [eval_wh_to_def]
    \\ fs [letrec_rel_subst])
  THEN1
   (rename [‘App x1 x2’]
    \\ qpat_x_assum ‘letrec_rel c _ _’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ rw [] \\ fs []
    \\ fs [eval_wh_to_def]
    \\ Cases_on ‘eval_wh_to k x1 = wh_Diverge’ THEN1 fs [] \\ fs []
    \\ ‘eval_wh_to k g ≠ wh_Diverge’ by
     (CCONTR_TAC \\ fs []
      \\ first_x_assum drule \\ fs []
      \\ Cases_on ‘eval_wh_to k x1’ \\ fs [])
    \\ fs []
    \\ first_x_assum drule \\ fs [] \\ rw []
    \\ Cases_on ‘eval_wh_to k x1’ \\ fs []
    \\ Cases_on ‘k’ \\ fs []
    \\ ‘letrec_rel c (bind s x2 e) (bind s y y')’ by cheat
    \\ last_x_assum drule \\ fs []
    \\ impl_tac THEN1 cheat (* closedness *)
    \\ Cases_on ‘eval_wh_to n (bind s x2 e)’ \\ fs [])
  THEN1
   (rename [‘Letrec f y’]
    \\ qpat_x_assum ‘letrec_rel c _ _’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ reverse (rw []) \\ fs []
    THEN1
     (Cases_on ‘k’ \\ fs [eval_wh_to_def]
      \\ ‘letrec_rel c (subst_funs f y) (subst_funs xs1 y1)’ by cheat
      \\ first_x_assum drule \\ fs []
      \\ impl_tac THEN1 cheat (* closedness *)
      \\ Cases_on ‘eval_wh_to n (subst_funs f y)’ \\ fs [])
    \\ ‘e2 = Letrec (make_distinct xs1) y1’ by (unabbrev_all_tac \\ gvs [])
    \\ gvs []
    \\ Cases_on ‘k’ \\ fs [eval_wh_to_def]
    \\ ‘letrec_rel c (subst_funs f y) (subst_funs (make_distinct xs1) y1)’ by cheat
    \\ first_x_assum drule \\ fs []
    \\ impl_tac THEN1 cheat (* closedness *)
    \\ Cases_on ‘eval_wh_to n (subst_funs f y)’ \\ fs [])
  \\ rename [‘Prim p xs’]
  \\ cheat (* straightforward cases? *)
QED

Definition valid_split_def:
  valid_split xs xs1 xs2 ⇔
    ALL_DISTINCT (MAP FST xs) ∧ ALL_DISTINCT (MAP FST xs1 ++ MAP FST xs2) ∧
    set xs = set xs1 UNION set xs2 ∧
    DISJOINT (set (MAP FST xs2)) (BIGUNION { freevars y | ∃n. MEM (n,y) xs1 })
End

Definition Lets_def:
  Lets [] b = b ∧
  Lets ((v,x)::xs) b = Let v x (Lets xs b)
End

Inductive letrec_split:
  (∀xs xs1 xs2 x.
     valid_split xs xs1 xs2 ⇒
     letrec_split
       (Letrec xs x)
       (Lets (MAP (λ(a,A). (a, Letrec xs A)) xs1)
          (Letrec xs2 x)))
End

Theorem letrec_rel_split_subst:
  letrec_rel letrec_split x y ⇒
  letrec_rel letrec_split (subst s e x) (subst s e y)
Proof
  cheat
QED

Theorem valid_split_FDIFF:
  valid_split ys ys1 ys2 ⇒
  FDIFF (FEMPTY |++ MAP (λ(g,x). (g,Letrec ys1 x)) ys1) (set (MAP FST ys2)) =
  FEMPTY |++ MAP (λ(g,x). (g,Letrec ys1 x)) ys1
Proof
  cheat
QED

Theorem letrec_split_correct:
  letrec_rel letrec_split x y ∧ closed x ∧ closed y ⇒ x ≃ y
Proof
  rw [] \\ irule eval_to_sim_thm \\ fs []
  \\ qexists_tac ‘letrec_rel letrec_split’ \\ fs []
  \\ simp [eval_to_sim_def]
  \\ rpt (pop_assum kall_tac)
  \\ qabbrev_tac ‘c = letrec_split’
  \\ gen_tac \\ gen_tac
  \\ qid_spec_tac ‘e1’
  \\ qid_spec_tac ‘k’
  \\ ho_match_mp_tac eval_wh_to_ind \\ rw []
  THEN1
   (rename [‘Lam s x’]
    \\ qpat_x_assum ‘letrec_rel c _ _’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ rw []
    \\ fs [eval_wh_to_def]
    \\ unabbrev_all_tac
    \\ fs [letrec_rel_split_subst])
  THEN1
   (rename [‘App x1 x2’]
    \\ qpat_x_assum ‘letrec_rel c _ _’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ rw [] \\ fs []
    \\ fs [eval_wh_to_def]
    \\ Cases_on ‘eval_wh_to k x1 = wh_Diverge’
    THEN1 (fs [] \\ res_tac \\ qexists_tac ‘ck’ \\ fs [])
    \\ fs []
    \\ first_x_assum drule \\ fs [] \\ rw []
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k x1)’ \\ fs []
    THEN1
     (fs [AllCaseEqs()] \\ qexists_tac ‘ck’ \\ fs []
      \\ Cases_on ‘eval_wh_to k x1’ \\ fs [])
    \\ Cases_on ‘eval_wh_to k x1’ \\ gvs []
    \\ rename [‘eval_wh_to (ck + k) g = wh_Closure _ e1’]
    \\ ‘letrec_rel c (bind s x2 e) (bind s y e1)’ by
        (fs [bind_single_def] \\ cheat)
    \\ Cases_on ‘k’ \\ fs []
    THEN1 (qexists_tac ‘0’ \\ fs [] \\ cheat (* true *))
    \\ fs [ADD1]
    \\ last_x_assum drule \\ fs []
    \\ impl_tac THEN1 cheat (* closedness *)
    \\ strip_tac
    \\ Cases_on ‘eval_wh_to n (bind s x2 e) = wh_Diverge’ \\ fs []
    THEN1
     (qexists_tac ‘ck'’ \\ fs [] \\ IF_CASES_TAC \\ fs []
      \\ cheat (* easy *))
    \\ qexists_tac ‘ck+ck'’
    \\ ‘eval_wh_to (ck + (n + 1) + ck') g = wh_Closure s e1’ by cheat (* easy *)
    \\ fs [] \\ Cases_on ‘eval_wh_to n (bind s x2 e)’ \\ fs []
    \\ ‘eval_wh_to (ck + (ck' + n)) (bind s y e1) =
        eval_wh_to (ck' + n) (bind s y e1)’ by cheat
    \\ fs [])
  THEN1
   (rename [‘Letrec f y’]
    \\ qpat_x_assum ‘letrec_rel c _ _’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ reverse (rw []) \\ fs []
    THEN1
     (Cases_on ‘k’ \\ fs [eval_wh_to_def]
      THEN1 (qexists_tac ‘0’ \\ fs []) \\ fs [ADD1]
      \\ ‘letrec_rel c (subst_funs f y) (subst_funs xs1 y1)’ by cheat
      \\ first_x_assum drule \\ fs []
      \\ impl_tac THEN1 cheat (* closedness *)
      \\ rw [])
    \\ unabbrev_all_tac
    \\ pop_assum mp_tac
    THEN1
     (simp [Once letrec_split_cases] \\ rw []
      \\ cheat (* crucial part *))
    \\ all_tac (* more here in case letrec_split gets more cases *))
  \\ rename [‘Prim p xs’]
  \\ cheat
QED

Theorem valid_split_thm:
  valid_split xs xs1 xs2 (* ∧ closed ... *) ⇒
  Letrec xs x ≃ Lets (MAP (λ(a,A). (a, Letrec xs A)) xs1) (Letrec xs2 x)
Proof
  cheat (* follows from letrec_split_correct *)
QED

(* This lemma would allow us to verify a top_sort_any application anywhere
   in the program. See proof idea below. *)
Theorem Letrec_Letrec:
  valid_split xs xs1 xs2 ⇒
  Letrec xs y ≅ Letrec xs1 (Letrec xs2 y)
Proof
  cheat
QED

(*

Proof idea based on two examples:

Example 1:

Let's assume that A is an expression where only a is free
also assume that B is an expressions where a and b are free.

   Letrec [(a,A);(b,B)] r
 ≃ (* due to something like valid_split_thm *)
   subst a (Letrec [(a,A);(b,B)] A) (Letrec [(b,B)] r)
 ≃ (* easy *)
   Let a (Letrec [(a,A);(b,B)] A) (Letrec [(b,B)] r)
 ≃ (* because b is not reachable from A *)
   Let a (Letrec [(a,A)] A) (Letrec [(b,B)] r)
 ≃ (* easy *)
   Letrec [(a,A)] (Letrec [(b,B)] r)

Example 2:

Now let's consider a slightly more interesting case: below A1 and A2
both have a1 and a2 free, and B has a1, a2, b free.

   Letrec [(a1,A1);(a2,A2);(b,B)] r
 ≃ (* due to something like valid_split_thm *)
   subst (a1 -> (Letrec [(a1,A1);(a2,A2);(b,B)] A1);
          a2 -> (Letrec [(a1,A1);(a2,A2);(b,B)] A2))
     (Letrec [(b,B)] r)
 ≃ (* easy *)
   Let a1 (Letrec [(a1,A1);(a2,A2);(b,B)] A1)
   Let a2 (Letrec [(a1,A1);(a2,A2);(b,B)] A2)
     (Letrec [(b,B)] r)
 ≃ (* because b is not reachable from A1 and A2 *)
   Let a1 (Letrec [(a1,A1);(a2,A2)] A1)
   Let a2 (Letrec [(a1,A1);(a2,A2)] A2)
     (Letrec [(b,B)] r)
 ≃ (* easy *)
   Letrec [(a1,A1);(a2,A2)] (Letrec [(b,B)] r)

*)

val _ = export_theory();
