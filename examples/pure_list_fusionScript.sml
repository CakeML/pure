
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory rich_listTheory stringTheory alistTheory
     optionTheory llistTheory BasicProvers pred_setTheory finite_mapTheory;
open pure_evalTheory pure_valueTheory pure_expTheory pure_exp_lemmasTheory
     pure_miscTheory pure_exp_relTheory pure_congruenceTheory
     pure_alpha_equivTheory pure_beta_equivTheory;

val _ = new_theory "pure_list_fusion";

Definition nil_def:
  nil = Prim (Cons "nil") []
End

Definition cons_def:
  cons xs = Prim (Cons "cons") xs
End

Definition dot_def:
  dot f g = Lam "x" (App f (App g (Var "x")))
End

Definition LAMREC_def:
  LAMREC f v b = Lam v (Letrec [ (f,Lam v b) ] b)
End

(* map f [] = []
   map f (x::xs) = f x::map f xs *)
Definition map_def:
   map =
   LAMREC "MAP" "f"
             (Lam "l"
               (Case (Var "l") "v" [
                    ("nil" ,         [],  nil );
                    ("cons", ["x";"xs"],  cons [App (Var "f") (Var "x" )
                                               ;App (App (Var "MAP") (Var "f")) (Var "xs")]
                    )
                   ])
             )
End

Definition map_f_def:
   map_f f =
   LAMREC "MAP_F" "l"
               (Case (Var "l") "v" [
                    ("nil" ,         [],  nil );
                    ("cons", ["x";"xs"],  cons [App f (Var "x")
                                               ;App (Var "MAP_F") (Var "xs")]
                    )
                   ])
End


Triviality app_bisimilarity_trans:
  ∀x y z b. (x ≃ y) b ∧ (y ≃ z) b ⇒ (x ≃ z) b
Proof
  rw[]
  \\ assume_tac transitive_app_bisimilarity
  \\ fs[relationTheory.transitive_def]
  \\ res_tac \\ fs[]
QED

Triviality app_bisimilarity_sym:
  ∀x y b. (x ≃ y) b ⇒ (y ≃ x) b
Proof
  rw[]
  \\ assume_tac symmetric_app_bisimilarity
  \\ fs[relationTheory.symmetric_def]
QED


(*
 we want to prove a naïve list fusion transformation:

  ∀ f g. MAP (dot f g) ≅ dot (MAP f) (MAP g)

 to do so, we need to define a bisimulation argument
 between the two expressions.

 We want to prove that the two functions consume thier
 input in the same way, producing observationally equivalent
 results.

 To help us with that, we define a function in HOL
 as model to show the behavior of map
 for the possible ways in which the co-datatype list
 can be consumed (either nil or cons)
*)

Definition next_list_def:
  next_list f input =
              if (¬closed input) then (INL Fail)
              else ( if eval input = Diverge then (INL Bottom)
                     else (case eval input of
                           | Constructor n vs =>
                               (if n = "nil" ∧ LENGTH vs = 0
                                then (INL nil)
                                else (if n = "cons" ∧ LENGTH vs = 2
                                then (INR (n
                                           ,App f (Proj n 0 input)
                                           ,Proj n 1 input       ))
                                else (INL Fail))
                               )
                           | _ => (INL Fail)))
End

(*
  then we state a lemma that says that, when two
  expressions are bisimilar to the same model, those
  are ≃-related.

  TODO: can we also make it work for ≅ ?
*)

Definition progress_def:
  progress exp next =
    ∀input.
        closed input ⇒
        ((App exp input) ≃
                 (case next input of
                  | INL final => final
                  | INR (n,x,rec_input) =>
                      Cons n [x; App exp rec_input])) T
End

Theorem progress_lemma:
  ∀ exp1 exp2 next b.
  progress exp1 next ∧ progress exp2 next ∧
  isClos (eval exp1) ∧ isClos (eval exp2) ⇒
  (exp1 ≃ exp2) b
Proof
  cheat
QED


Theorem progress_equivalence:
  ∀ exp1 exp2 model.
  (exp1 ≃ exp2) T ∧
  progress exp1 model
   ⇒ progress exp2 model
Proof
  cheat
QED

val eval_rewrites =
  [bind_def,subst_def,closed_def,freevars_equiv,
   FLOOKUP_UPDATE,FDIFF_def,DOMSUB_FUPDATE_THM,FUPDATE_LIST_THM];

Theorem progress_map_f:
  ∀ f. closed f ⇒ progress (App map f) (next_list f)
Proof
  rw[progress_def]
  \\ fs[closed_def, freevars_equiv]
  \\ rw[exp_eq_def,bind_def,subst_def] \\ rw[]
  \\ irule eval_IMP_app_bisimilarity
  \\ rw[closed_def, freevars_equiv]
  THEN1(
    rw[dot_def,map_def,nil_def,cons_def,LAMREC_def]
    \\ rw[expandCases_def,expandRows_def,expandLets_def]
  )
  THEN1(
    simp[next_list_def,closed_def, freevars_equiv]
    \\ rw[] \\ fs[Bottom_def]
    \\ FULL_CASE_TAC \\ fs[]
    \\ FULL_CASE_TAC \\ fs[]
    THEN1(
      rw[dot_def,map_def,nil_def,cons_def,LAMREC_def]
      \\ rw[expandCases_def,expandRows_def,expandLets_def, GSYM DELETE_DEF]
    )
    \\ rw[nil_def]
  )
  \\ simp[map_def,LAMREC_def,cons_def,nil_def]
  \\ simp[eval_thm]
  \\ simp eval_rewrites
  \\ simp[eval_thm]
  \\ simp[subst_funs_def]
  \\ simp eval_rewrites
  \\ simp[expandCases_def,expandRows_def,expandLets_def]
  \\ simp eval_rewrites
  \\ simp[eval_thm]
  \\ simp eval_rewrites
  \\ simp[eval_thm]
  \\ simp eval_rewrites
  \\ simp[eval_thm]
  \\ simp[is_eq_def]
  \\ Cases_on ‘eval input = Diverge’ \\ fs[]
  THEN1(
    simp[next_list_def,closed_def,eval_thm,freevars_equiv]
  )
  \\ FULL_CASE_TAC \\ fs[]
  \\ TRY(simp[next_list_def,closed_def,freevars_equiv,eval_thm])
  \\ rw[]\\fs[]
  \\ TRY(
    simp[next_list_def,closed_def,freevars_equiv,eval_thm]
    \\ fs[nil_def,eval_thm]
    \\ FULL_CASE_TAC \\ fs[]
    \\ FULL_CASE_TAC \\ fs[]
  )
  \\ simp eval_rewrites
  \\ simp[eval_thm]
  \\ simp eval_rewrites
  \\ simp[eval_thm]
  \\ simp[subst_funs_def]
  \\ simp eval_rewrites
  \\ simp[eval_thm]
  \\ simp eval_rewrites
  \\ simp[eval_thm]
  \\ simp eval_rewrites
  \\ simp[eval_thm]
  \\ simp[is_eq_def]
  \\ simp eval_rewrites
  \\ simp[eval_thm]
  \\ simp[is_eq_def,el_def]
  \\ Cases_on ‘EL 1 t = Diverge’ \\ fs[]
  \\  rw[] \\ fs[]
  \\ simp eval_rewrites
  \\ simp[eval_thm]
  \\ simp eval_rewrites
  \\ simp[eval_thm]
  \\ simp[subst_funs_def]
  \\ simp eval_rewrites
QED

Theorem progress_map_f_f:
  ∀ f. closed f ⇒ progress (map_f f) (next_list f)
Proof
  rw[progress_def]
  \\fs[closed_def,freevars_equiv]
  \\rw[exp_eq_def,bind_def,subst_def] \\ rw[]
  \\irule eval_IMP_app_bisimilarity
  \\rw[closed_def,freevars_equiv]
  THEN1(
    rw[dot_def,map_f_def,nil_def,cons_def,LAMREC_def]
    \\rw[expandCases_def,expandRows_def,expandLets_def]
  )
  THEN1(
    simp[next_list_def] \\ fs[closed_def,freevars_equiv]
    \\ rw[] \\ fs[Bottom_def]
    \\ FULL_CASE_TAC \\ fs[] \\ rw[] \\ fs[nil_def,map_f_def,LAMREC_def]
    \\ EVAL_TAC \\ fs[FILTER_FILTER]
  )
  \\ simp[map_f_def,LAMREC_def,cons_def,nil_def]
  \\ simp[eval_thm]
  \\ simp eval_rewrites
  \\ simp[eval_thm]
  \\ simp[subst_funs_def]
  \\ simp eval_rewrites
  \\ simp[eval_thm]
  \\ reverse (rw[FILTER_FILTER])
  THEN1 (
    pop_assum mp_tac
    \\ rw[FILTER_FILTER,expandCases_def,expandRows_def,expandLets_def]
  )
  \\ simp[expandCases_def,expandRows_def,expandLets_def]
  \\ simp eval_rewrites
  \\ simp[is_eq_def]
  \\ Cases_on ‘eval input = Diverge’ \\ fs[]
  THEN1 (
    simp[next_list_def,closed_def,freevars_equiv,eval_thm,
         bind1_def,subst1_def,is_eq_def]
    ) >>
  simp[next_list_def, closed_def, freevars_equiv] >>
  FULL_CASE_TAC >> gvs (eval_thm :: is_eq_def :: eval_rewrites) >>
  Cases_on `s = "nil"` >> gvs[nil_def, eval_thm]
  >- (Cases_on `t = []` >> gvs[nil_def, eval_thm]) >>
  Cases_on `s = "cons"` >> gvs[nil_def, eval_thm] >>
  Cases_on `LENGTH t = 2` >> gvs[nil_def, eval_thm] >> rw[]
  >- simp eval_rewrites
  >- (
    irule FALSITY >>
    gvs[subst_funs_def] >> gvs eval_rewrites >> gvs[eval_thm]
    ) >>
  simp[eval_thm,subst_funs_def]
  \\ simp eval_rewrites
  \\ simp[eval_thm,subst_funs_def]
  \\ simp eval_rewrites
QED

Theorem progress_compose_fg:
  ∀ f g. closed f ∧ closed g
  ⇒ progress (dot (App map f) (App map g)) (next_list (dot f g))
Proof
  rw[]
  \\ ‘∀ h. closed h ⇒ (App map h) ≃ (map_f h)’ by (
    rpt strip_tac
    \\ qspecl_then [‘App map h’,‘map_f h’,‘next_list h’]
             assume_tac progress_lemma
    \\ assume_tac progress_map_f
    \\ assume_tac progress_map_f_f
    \\ res_tac
    \\ ‘isClos (eval (App map h))’ by (
       cheat
    )
    \\ ‘isClos (eval (map_f h))’ by (
       cheat
    )
    \\ res_tac
  )
  \\ first_assum (qspec_then ‘f’ assume_tac)
  \\ first_assum (qspec_then ‘g’ assume_tac)
  \\ res_tac
  \\ ‘dot (App map f) (App map g) ≃ dot (map_f f) (map_f g)’ by (
    simp[dot_def]
    \\ simp[app_bisimilarity_eq]
    \\ rw[]
    \\ TRY (
      fs[closed_def,freevars_equiv]
      \\ simp[map_f_def,map_def,LAMREC_def,expandCases_def
             ,expandRows_def,expandLets_def,cons_def,nil_def]
      \\ FAIL_TAC "rollback"
    )
    \\ irule exp_eq_Lam_cong
    \\ irule exp_eq_App_cong
    \\ rw[]
    THEN1 (
      irule exp_eq_App_cong
      \\ rw[exp_eq_Var_cong]
      \\ imp_res_tac app_bisimilarity_eq
    )
    \\ imp_res_tac app_bisimilarity_eq
  )
  \\ irule progress_equivalence
  \\ qexists_tac ‘dot (map_f f) (map_f g)’
  \\ rw[app_bisimilarity_sym]
  \\ fs[dot_def,progress_def]
  \\ strip_tac
  \\ strip_tac
  \\ irule eval_IMP_app_bisimilarity
  \\ rw[]
  \\ TRY (
     fs[closed_def,freevars_equiv]
     \\ simp[map_f_def,map_def,LAMREC_def,expandCases_def,next_list_def
            ,expandRows_def,expandLets_def,cons_def,nil_def,closed_def]
     \\ rpt ( FULL_CASE_TAC \\ fs[Bottom_def] )
     \\ FAIL_TAC "rollback"
  )
  \\ simp [eval_thm]
  \\ simp eval_rewrites
  \\ ‘closed (map_f f) ∧ closed (map_f g)’ by (
    fs[closed_def,freevars_equiv]
    \\ simp[closed_def,freevars_equiv,map_f_def,LAMREC_def,expandCases_def
           ,expandRows_def,expandLets_def,cons_def,nil_def]
  )
  \\ simp[closed_subst] \\ fs[closed_def,freevars_equiv]
  \\ simp[eval_thm]
  \\ ntac 2
      (simp[closed_def,freevars_equiv,Once map_f_def,LAMREC_def,expandCases_def
           ,expandRows_def,expandLets_def,cons_def,nil_def])
  \\ ntac 6
      (simp [Once eval_thm,bind_def,subst_def,closed_def,freevars_equiv,subst_funs_def
          ,FLOOKUP_UPDATE,FDIFF_def,DOMSUB_FUPDATE_THM,FUPDATE_LIST_THM])
  \\ simp[is_eq_def]
  \\ simp [Once map_f_def,map_def,LAMREC_def,expandCases_def,next_list_def
          ,expandRows_def,expandLets_def,cons_def,nil_def,closed_def]
  \\ ntac 5
     ( simp [Once eval_thm,bind_def,subst_def,closed_def,freevars_equiv,subst_funs_def
            ,FLOOKUP_UPDATE,FDIFF_def,DOMSUB_FUPDATE_THM
            ,FUPDATE_LIST_THM,is_eq_def] )
  \\ Cases_on ‘eval input = Diverge’ \\ fs[eval_thm,is_eq_def]
  \\ ‘eval (map_f g) ≠ Diverge’ by (
    simp [Once map_f_def,map_def,LAMREC_def,expandCases_def,next_list_def
         ,expandRows_def,expandLets_def,cons_def,nil_def,closed_def,freevars_equiv]
    \\ simp [Once eval_thm,bind_def,subst_def,closed_def,freevars_equiv,subst_funs_def
            ,FLOOKUP_UPDATE,FDIFF_def,DOMSUB_FUPDATE_THM
            ,FUPDATE_LIST_THM,is_eq_def]
  ) \\ fs[]
  \\ Cases_on ‘dest_Closure (eval (map_f g))’ \\ fs[]
  THEN1 (
    Cases_on ‘eval input’ \\ fs[eval_thm]
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ simp [Once map_f_def,map_def,LAMREC_def,expandCases_def,next_list_def
            ,expandRows_def,expandLets_def,cons_def,nil_def,closed_def,freevars_equiv]
    \\ simp [Once eval_thm,bind_def,subst_def,closed_def,freevars_equiv,subst_funs_def
            ,FLOOKUP_UPDATE,FDIFF_def,DOMSUB_FUPDATE_THM
            ,FUPDATE_LIST_THM,is_eq_def]
  )
  \\ fs[dest_Closure_def]
  \\ Cases_on ‘eval (map_f g)’ \\ fs[]
  \\ pop_assum mp_tac
  \\ simp [Once map_f_def,map_def,LAMREC_def,expandCases_def,next_list_def
            ,expandRows_def,expandLets_def,cons_def,nil_def,closed_def,freevars_equiv]
  \\ ntac 2
     (simp [Once eval_thm,bind_def,subst_def,closed_def,freevars_equiv,subst_funs_def
           ,FLOOKUP_UPDATE,FDIFF_def,DOMSUB_FUPDATE_THM
           ,FUPDATE_LIST_THM,is_eq_def])
  \\ cheat
  (*go on with the symbolic evaluation...*)
QED


Theorem map_fusion:
 ∀ f g. closed f ∧ closed g ⇒
     (dot (App map f) (App map g)) ≃ (App map (dot f g))
Proof
  rw[]
  \\ ‘closed (dot f g)’ by (fs[dot_def,closed_def])
  \\ qspecl_then [‘App map (dot f g)’,
                  ‘dot (App map f) (App map g)’,
                  ‘next_list (dot f g)’]
          assume_tac progress_lemma
  \\ qspec_then ‘dot f g’ assume_tac progress_map_f
  \\ qspecl_then [‘f’,‘g’] assume_tac progress_compose_fg
  \\ ‘isClos (eval (dot (App map f) (App map g)))’ by (
     cheat
  )
  \\ ‘isClos (eval (App map (dot f g)))’ by (
     cheat
  )
  \\ fs[app_bisimilarity_sym]
QED




val _ = export_theory();
