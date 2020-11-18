
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory rich_listTheory stringTheory alistTheory optionTheory
     llistTheory pure_langTheory;

val _ = new_theory "list_fusion";

(*********** Some PureCake programs *************)

Definition nil_def:
  nil = Prim (Cons "nil") []
End

Definition cons_def:
  cons xs = Prim (Cons "cons") xs
End

Definition LAMREC_def:
  LAMREC f v b = Lam v (Letrec [ (f,v,b) ] b)
End

(* map f [] = []
   map f (x::xs) = f x::map f xs *)
Definition map_def:
   map =
   LAMREC "MAP" "f"
             (Lam "l"
               (Case (Var "l") "v" [
                    ("nil" ,         [],  nil );
                    ("cons", ["x";"xs"],  cons [App (Var "f"  ) (Var "x" )
                                               ;App (Var "MAP") (Var "xs")]
                    )
                   ])
             )
End

(* add1 [] = []
   add1 (x::xs) = [x]::add2 xs *)
Definition add1'_def:
  add1' = LAMREC "ADD1" "l"
                  (Case (Var "l") "v" [
                    ("nil" ,         [],  nil );
                    ("cons", ["x";"xs"],  cons [ cons [Var "x";nil]           ;
                                                 App (Var "ADD1") (Var "xs")  ]
                    )
                   ])
End

(* add2 [] = []
   add2 (x::xs) = [[x]]::add2 xs *)
Definition add2'_def:
  add2' = LAMREC "ADD2" "l"
                  (Case (Var "l") "v" [
                    ("nil" ,         [],  nil );
                    ("cons", ["x";"xs"],  cons [ cons [cons [Var "x";nil];nil] ;
                                                 App (Var "ADD2") (Var "xs")   ]
                    )
                   ])
End



Definition Apps_rev_def:
  Apps_rev [] = Fail                     ∧
  Apps_rev [x] = x                       ∧
  Apps_rev (x::xs) = App (Apps_rev xs) x
End

Definition Apps_def:
  Apps xs = Apps_rev (REVERSE xs)
End


(* Some lemmas, mostly to *)

Triviality LNTH_2:
  ∀ n ll. LNTH n ll =
        if n = 0 then LHD ll
        else OPTION_JOIN (OPTION_MAP (LNTH (n-1)) (LTL ll))
Proof
  rw[] \\ fs[LNTH] \\ Cases_on ‘n’ \\ fs[LNTH]
QED

Theorem freevars_subst_lemma_gen:
  ∀ n x e . freevars x = [] ⇒
            freevars (subst n x e) =
                 FILTER ($≠ n) (freevars e)
Proof
  ho_match_mp_tac subst_ind
  \\ rw []
  THEN1( fs[subst_def,freevars_def] )
  THEN1( fs[subst_def,freevars_def] )
  THEN1(
    fs[subst_def,freevars_def]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF]
    \\ Induct_on ‘xs’ \\ fs[]
    \\ rpt strip_tac \\ fs[FILTER_APPEND_DISTRIB]
  )
  THEN1(
    fs[subst_def]
    \\ fs[FILTER_APPEND_DISTRIB]
  )
  THEN1(
    fs[subst_def] \\ IF_CASES_TAC
    THEN1( fs[] \\ fs[rich_listTheory.FILTER_IDEM])
    \\ fs[rich_listTheory.FILTER_FILTER,AC CONJ_ASSOC CONJ_COMM]
  )
  THEN1(
    fs[subst_def] \\ IF_CASES_TAC
    THEN1 (
      fs[rich_listTheory.FILTER_FILTER] \\ AP_THM_TAC \\ AP_TERM_TAC
      \\ fs[FUN_EQ_THM]
      \\ metis_tac [] )
    \\ fs[] \\ fs[rich_listTheory.FILTER_FILTER] \\ fs[FILTER_APPEND_DISTRIB]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF,pairTheory.UNCURRY]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ fs[rich_listTheory.FILTER_FILTER,AC CONJ_ASSOC CONJ_COMM]
    \\ fs[rich_listTheory.FILTER_FLAT]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF,pairTheory.UNCURRY]
    \\ AP_TERM_TAC \\ fs[listTheory.MAP_EQ_f,pairTheory.FORALL_PROD]
    \\ fs[rich_listTheory.FILTER_FILTER,AC CONJ_ASSOC CONJ_COMM]
    \\ rpt strip_tac \\ IF_CASES_TAC
    THEN1 (
      fs[] \\ fs[rich_listTheory.FILTER_FILTER,AC CONJ_ASSOC CONJ_COMM]
      \\ AP_THM_TAC \\ AP_TERM_TAC
      \\ fs[FUN_EQ_THM] \\ metis_tac [] )
    \\ res_tac \\ fs[]
    \\ fs[rich_listTheory.FILTER_FILTER,AC CONJ_ASSOC CONJ_COMM]
  )
  THEN1(
   fs[subst_def] \\fs[FILTER_APPEND_DISTRIB]
   \\ fs[rich_listTheory.FILTER_FLAT]
   \\ fs[MAP_MAP_o,combinTheory.o_DEF,pairTheory.UNCURRY]
   \\ fs[rich_listTheory.FILTER_FILTER,AC CONJ_ASSOC CONJ_COMM]
   \\ AP_TERM_TAC \\ fs[listTheory.MAP_EQ_f,pairTheory.FORALL_PROD]
   \\ rpt strip_tac \\ reverse IF_CASES_TAC
   THEN1(
     AP_THM_TAC \\ AP_TERM_TAC
     \\ fs[FUN_EQ_THM] \\ metis_tac []
   )
   \\ res_tac \\ fs[] \\ rfs[]
   \\ fs[rich_listTheory.FILTER_FILTER,AC CONJ_ASSOC CONJ_COMM]
  )
QED

Theorem no_var_no_subst:
  ∀ n v e. ¬MEM n (freevars e) ⇒ subst n v e = e
Proof
  ho_match_mp_tac subst_ind
  \\ rw[]
  THEN1(fs[subst_def])
  THEN1(fs[subst_def] \\ Induct_on ‘xs’ \\ fs[])
  THEN1(res_tac \\ fs[subst_def])
  THEN1(fs[subst_def] \\ IF_CASES_TAC \\ fs[] \\ fs[MEM_FILTER])
  THEN1(
    fs[subst_def] \\ IF_CASES_TAC \\ fs[] \\ fs[MEM_FILTER]
    \\ Induct_on ‘f’ \\ fs[] \\ rpt strip_tac
    THEN1 (Cases_on ‘h’ \\ Cases_on ‘r’ \\ fs[] \\ IF_CASES_TAC \\ fs[] \\ fs[MEM_FILTER])
    \\ metis_tac [])
  THEN1(
    fs[subst_def] \\ fs[MEM_FILTER]
    \\ Induct_on ‘css’ \\ fs[] \\ rpt strip_tac
    THEN1 (Cases_on ‘h’ \\ Cases_on ‘r’ \\ fs[] \\ IF_CASES_TAC \\ fs[] \\ fs[MEM_FILTER])
    \\ metis_tac [])
QED

Theorem closed_no_subst:
  closed e ⇒ subst n v e = e
Proof
  fs[closed_def,no_var_no_subst]
QED

Theorem subst_swap:
   ∀ n1 x b. (n1 ≠ n2 ∧ closed x ∧ closed y) ⇒
   subst n1 y (subst n2 x b) = subst n2 x (subst n1 y b)
Proof
  ho_match_mp_tac subst_ind
  \\ rw[]
  THEN1 (
    fs[subst_def]
    \\ IF_CASES_TAC THEN1 (fs[subst_def,closed_no_subst])
    \\ IF_CASES_TAC \\ fs[subst_def,closed_no_subst])
  THEN1 (
    fs[subst_def]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF,pairTheory.UNCURRY]
    \\ Induct_on ‘xs’ \\ fs[]
    \\ rpt strip_tac \\ metis_tac[])
  THEN1 (
    fs[subst_def] \\ rw[] \\ fs[])
  THEN1 (
    fs[subst_def] \\ IF_CASES_TAC \\ fs[] \\ IF_CASES_TAC \\ fs[] \\ fs[])
  THEN1 (
    Cases_on ‘MEM n1 (MAP FST f)’ \\ fs[subst_def]
    THEN1 (
      IF_CASES_TAC \\ fs[subst_def]
      \\ fs[MAP_MAP_o,combinTheory.o_DEF,pairTheory.UNCURRY]
      \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs[]
    )
    \\ Cases_on ‘MEM n2 (MAP FST f)’ \\ fs[subst_def]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF,pairTheory.UNCURRY]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs[]
    \\ rw[] \\ fs[]
    \\ fs[MAP_EQ_f] \\ rpt strip_tac
    \\ IF_CASES_TAC \\ fs[]
    \\ IF_CASES_TAC \\ fs[]
    \\ Cases_on ‘x'’ \\ Cases_on ‘r’ \\ fs[] \\ res_tac \\ fs[]
  )
  THEN1 (
    fs[subst_def]
    \\ fs[MAP_MAP_o,combinTheory.o_DEF,pairTheory.UNCURRY]
    \\ rw[] \\ fs[]
    \\ fs[MAP_EQ_f] \\ rpt strip_tac
    \\ IF_CASES_TAC \\ fs[]
    \\ IF_CASES_TAC \\ fs[]
    \\ Cases_on ‘x'’ \\ Cases_on ‘r’ \\ fs[] \\ res_tac \\ fs[])
QED

(*used to control recursive steps during the proofs*)
Theorem eval_LAMREC3:
  v≠f (*∧ closed (LAMREC f v b)*) ⇒
  eval c (App (LAMREC f v b) y) =
      if closed (Lam v (Letrec [(f,v,b)] b))
       then eval c (App (Lam v ( subst f (LAMREC f v b) b) ) y)
       else Error
Proof
  rpt strip_tac
  \\ fs[Once LAMREC_def]
  \\ fs[eval_thm]
  \\ fs[bind_def]
  \\ rw[]
  \\ fs[subst_def]
  \\ fs[eval_thm]
  \\ fs[subst_funs_def]
  \\ fs[bind_def]
  \\ fs[eval_thm]
  \\ fs[subst_def]
  \\ fs[eval_Let]
  \\ fs[bind_def]
  \\ fs[LAMREC_def]
  \\ metis_tac [subst_swap]
QED

Theorem eval_LAMREC2:
  (*b has no other free variables except v and f*)
  (∀ k. MEM k (freevars b) ⇒ k = v ∨ k = f) ⇒
  eval c (LAMREC f v b) = if closed (Lam v (Letrec [(f,v,b)] b))
                           then eval c (Lam v ( Letrec [(f,v,b)] b ))
                           else Error
Proof
  rpt strip_tac
  \\ fs[Once LAMREC_def]
  \\ fs[eval_thm] \\ fs[closed_def,no_var_no_subst,freevars_subst_lemma_gen]
  \\ fs[FILTER_APPEND]
  \\ fs[FILTER_FILTER]
  \\ fs[AC CONJ_ASSOC CONJ_COMM]
  \\ rw[] \\ fs[FILTER_NEQ_NIL]
  \\ res_tac \\ fs[]
QED

Theorem subst_closed_iff:
  ∀ n e. closed x ∧ closed y ⇒
          (closed (subst n x e) ⇔ closed (subst n y e))
Proof
  rw[]
  \\ fs[closed_def]
  \\ imp_res_tac freevars_subst_lemma_gen
  \\ eq_tac \\ fs[]
QED

Theorem exp_rel_refl[simp]:
  ∀ e. exp_rel c e e
Proof
  strip_tac \\ fs[exp_rel_def,v_rel_refl]
QED


(*
Theorem eval_subst_imp_eq2:
  ∀ v x y e.
    closed x ∧ closed y ∧ (*alternatively, eval c  ≠ Error*)
    exp_rel c x y ⇒
    exp_rel c (subst v x e) (subst v y e)
Proof
  fs[exp_rel_def]
  \\ fs[v_rel_def]
  \\ fs[PULL_FORALL]
  \\ completeInduct_on ‘n’
  \\ fs[GSYM PULL_FORALL]
  \\ rpt strip_tac

  \\ qid_spec_tac ‘e’
  \\ qid_spec_tac ‘k’
  \\ qid_spec_tac ‘c’

  \\ rpt strip_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘e’
  \\ qid_spec_tac ‘k’
  \\ qid_spec_tac ‘c’
  \\ ho_match_mp_tac eval_to_ind
  \\ rw[]
  THEN1 (fs[subst_def] \\ rw[])
  THEN1 (cheat)
  THEN1 (
    fs[subst_def] \\ rw[]
    THEN1 (
      fs[exp_rel_def] \\ fs[eval_thm]
      \\ fs[v_rel_def]
      \\ strip_tac
      \\ Cases_on ‘n’ \\ fs[v_rel'_def]
    )
    \\ fs[exp_rel_def] \\ fs[eval_thm]
    \\ fs[v_rel_def]
    \\ strip_tac
    \\ Cases_on ‘n’ \\ fs[v_rel'_def]
    \\ DISJ2_TAC
    \\ strip_tac
    \\ fs[bind_def] \\ rw[]
    \\ Cases_on ‘x=y’ \\ fs[] \\ rw[subst_def]
    \\ cheat
  )
  \\ cheat
QED
*)
(*
Theorem eval_subst_imp_eq:
  ∀ y n x e.
    closed x ∧ closed y ∧ (*alternatively, eval c  ≠ Error*)
    eval c x = eval c y ⇒
    eval c (subst n x e) = eval c (subst n y e)
Proof
  strip_tac
  \\ ho_match_mp_tac subst_ind
  \\ rw[]
  THEN1 (fs[subst_def,eval_thm] \\ rw[])
  THEN1 (
    fs[subst_def,eval_thm]
    \\ Induct_on ‘xs’ \\ fs[]
    \\ rpt strip_tac
    \\ fs[eval_core] \\ AP_TERM_TAC
    \\ fs[MAP_MAP_o,combinTheory.o_DEF,pairTheory.UNCURRY]
    \\ fs[MAP_EQ_f] )
  THEN1 (
    fs[subst_def,eval_thm] \\ rw[]
    \\ Cases_on ‘dest_Closure (eval c (subst n y e))’ \\ fs[]
    \\ Cases_on ‘x'’ \\ rw[]
    \\ imp_res_tac dest_Closure_Closure_IMP
    \\ fs[bind_def]
    \\ qspecl_then [‘n’,‘e'’] assume_tac subst_closed_iff \\ rw[]
    \\ fs[bind_def]
    \\ Cases_on ‘n = q’
    THEN1 (
      ‘¬MEM n (freevars r)’ by (
         imp_res_tac dest_Closure_Closure_IMP
         \\ imp_res_tac subst_closure_not_MEM_freevars)
      \\ rfs[no_var_no_subst]
      ‘freevars (subst q x e') = []’ by (fs[closed_def,freevars_subst_lemma_gen])
      \\ IF_CASES_TAC \\ fs[]
    )
    \\ ‘freevars (subst n x e') = []’ by (
      imp_res_tac freevars_subst_lemma_gen \\ fs[]
    )
    \\ cheat
    \\ imp_res_tac dest_Closure_Closure_IMP
    \\ imp_res_tac subst_closure_App
    \\ Cases_on ‘closed (subst n x e')’
    \\ Cases_on ‘closed (subst n y e')’ (this follow from freevars e' = at most n
    \\ res_tac \\ fs[]
    \\ simp[eval_thm]
    \\ simp[bind_def]
    \\ simp[eval_thm]
 THEN1(
   fs[subst_def]
   \\ IF_CASES_TAC \\ fs[]
   \\ rw[] \\ fs[eval_thm]
   \\ CCONTR_TAC
   \\ once_rewrite_tac [eval_thm]
 )
QED
*)

Theorem eval_Case_value:
  closed x ∧ closed y ∧ eval c x = eval c y ⇒
      eval c (Case x nm css) = eval c (Case y nm css)
Proof
  cheat (*this is true, but requires equational reasoning in order to be proved*)
QED


(*evaluation of map, case []*)
Theorem eval_map_nil:
  ∀ f. closed f ⇒
       eval c (App (App map f) nil) = eval c nil
Proof
  rw[] \\ fs[map_def,cons_def,nil_def]
  \\ fs[LAMREC_def] \\ fs[eval_thm]
  \\ ntac 3 (
    fs[bind_def] \\ fs[closed_def]
    \\ fs[subst_def] \\ fs[eval_thm]
    \\ fs[subst_funs_def])
  \\ fs[expandCases_def,expandRows_def,expandLets_def] \\ fs[eval_thm]
  \\ fs[bind_def,closed_def]
  \\ fs[subst_def]
  \\ fs[eval_thm]
  \\ fs[is_eq_def,el_def,LNTH_2]
QED

(*
TODO: fix this
(*evaluation of map, case (x::xs)*)
Theorem eval_map_cons:
  ∀ f. closed f ∧ closed x ∧ closed y ⇒
   eval c (App (App map f) (cons [x;y])) = Constructor "cons" [
       eval c (App f   (Proj "cons" 0 (cons [x;y]))) ;  (*TODO, equational reason *)
       eval c (App map (Proj "cons" 1 (cons [x;y])))    (*this Proj away          *)
   ]
Proof
  rw[]
  \\ fs[map_def,cons_def,nil_def]
  \\ fs[LAMREC_def] \\ fs[eval_thm]
  \\ ntac 3
    (fs[bind_def] \\ fs[closed_def]
     \\ fs[subst_def] \\ fs[eval_thm] \\ fs[subst_funs_def])
  \\ fs[expandCases_def,expandRows_def,expandLets_def] \\ fs[eval_thm]
  \\ fs[bind_def,closed_def]
  \\ fs[subst_def]
  \\ fs[eval_thm]
  \\ fs[is_eq_def]

  \\ once_rewrite_tac [is_eq_def]
  \\ IF_CASES_TAC cheat
   \\ fs[]

  \\ fs[is_eq_def,el_def,LNTH_2]
  \\ fs[bind_def,closed_def]
  \\ fs[subst_def] \\ fs[eval_thm]
  \\ fs[bind_def,closed_def]
  \\ fs[no_var_no_subst]
  \\ fs[subst_def] \\ fs[eval_thm]
  \\ fs[no_var_no_subst]
  \\ IF_CASES_TAC THEN1 (
      fs[bind_def,closed_def,subst_def,eval_thm,subst_funs_def]
      \\ fs[no_var_no_subst] )
  \\ Cases_on ‘dest_Closure (eval c f)’ THEN1 (
      fs[bind_def,closed_def,subst_def,eval_thm,subst_funs_def]
      \\ fs[no_var_no_subst] )
  \\ Cases_on ‘x'’ \\  fs[]
  \\ fs[bind_def,closed_def,subst_def,eval_thm,subst_funs_def]
  \\ fs[no_var_no_subst]
QED
*)

Definition compose_def:
 compose f g = Lam "x" (App f (App g (Var "x")))
End

(*
   this equality requires the progress lemma
Theorem map_f_composition_eq:
  (* map f (map f l) = map (f o f) l *)
  closed f ∧ closed l ⇒
  eval c (Apps [map;f;Apps [map;f;l]])
 =
  eval c (Apps [map;compose f f;l])
Proof
  rw[]
  \\ fs[Apps_def,Apps_rev_def,compose_def]
  \\ fs[map_def,cons_def,nil_def,LAMREC_def]
  \\ fs[eval_thm,closed_def,subst_def,bind_def,subst_funs_def]
  \\ fs[expandCases_def,expandRows_def,expandLets_def]
  \\ fs[eval_thm,closed_def,subst_def,bind_def,subst_funs_def]
  \\ fs[no_var_no_subst,is_eq_def,el_def,LNTH_2]
  \\ fs[expandCases_def,expandRows_def,expandLets_def]
  \\ fs[eval_thm,closed_def,subst_def,bind_def,subst_funs_def]
  \\ fs[no_var_no_subst,is_eq_def,el_def,LNTH_2]
  \\ Cases_on ‘eval c l = Diverge’ \\ fs[] \\ fs[]

  \\ Cases_on ‘eval c l = Constructor "nil" []’ \\ fs[]
  \\ Cases_on ‘eval c l ≠ Constructor "cons" [b1;b2]’

  \\ Cases_on ‘eval c f = Diverge’ \\ fs[] \\ fs[]

  \\ cheat
QED
*)


Definition next_list_def:
  next_list (f:('a,'b) exp) c (input:('a,'b) exp) =
              if (¬closed input) then (INL Fail)
              else ( if eval c input = Diverge then (INL bottom)
                     else (case eval c input of
                           | Constructor n vs =>
                               (if n = "nil" ∧ LENGTH vs = 0
                                then (INL (nil:('a,'b) exp))
                                else if n = "cons" ∧ LENGTH vs = 2
                                then (INR (n
                                           ,App f (Proj n 0 input)
                                           ,Proj n 1 input       ))
                                else (INL Fail)
                               )
                           | _ => (INL Fail)))
End

Theorem progress_map_f:
  ∀ f. closed f ⇒ progress c (App map f) (next_list f c)
Proof
  rw[]
  \\ fs[progress_def]
  \\ rpt strip_tac \\ fs[exp_rel_def]
  \\ fs[eval_thm]
  \\ ‘eval c map ≠ Diverge’ by (fs[map_def,LAMREC_def,cons_def,nil_def,eval_thm]) \\ fs[]
  \\ fs[map_def,LAMREC_def,cons_def,nil_def]
  \\ fs[bind_def,subst_def,subst_funs_def,eval_thm,closed_def]
  (* These tactics no longer do anything:

     \\ fs[expandCases_def,expandRows_def,expandLets_def,eval_thm]
     \\ fs[bind_def,subst_def,subst_funs_def,eval_thm,closed_def]
     \\ fs[no_var_no_subst,is_eq_def,el_def,LNTH_2]
  *)
  \\ reverse IF_CASES_TAC THEN1 (fs[next_list_def,closed_def,v_rel_refl])
  \\ fs[eval_thm]
  \\ fs[expandCases_def,expandRows_def,expandLets_def,eval_thm]
  \\ fs[bind_def,subst_def,subst_funs_def,eval_thm,closed_def]
  \\ fs[no_var_no_subst,is_eq_def,el_def,LNTH_2]
  \\ Cases_on ‘eval c input = Diverge’
  THEN1 (fs[next_list_def,closed_def] \\ fs[eval_bottom] \\ fs[v_rel_refl])
  \\ fs[]
  \\ Cases_on ‘eval c input’
  \\ fs[next_list_def,eval_thm,v_rel_refl,closed_def]
  \\ cheat
  (* \\ Cases_on ‘eval c input’ \\ fs[] \\ Cases_on ‘a’ \\ fs[eval_thm,v_rel_refl] *)
  (* THEN1 ( *)
  (*   rw[] \\ fs[eval_thm,nil_def,v_rel_refl] \\ rw[] \\ fs[] \\ rw[] \\ fs[] *)

  (*   \\ Cases_on ‘s ≠ "nil" ∧ s ≠ "cons"’ \\ fs[eval_thm,v_rel_refl] *)
  (*   \\ rw[] \\ fs[eval_thm,v_rel_refl,nil_def] *)
  (*   THEN1 ( *)
  (*     rw[] *)
  (*     \\ IF_CASES_TAC \\ fs[eval_thm,nil_def,v_rel_refl] *)
  (*     \\ Cases_on ‘a'’ \\ fs[] *)
  (*     \\ Cases_on ‘ts’ \\ fs[] \\ rw[] *)
  (*     \\ Cases_on ‘eval c input’ \\ fs[eval_thm] *)
  (*     \\ cheat *)
  (*   ) *)
  (*   \\ cheat *)
  (* ) *)
  (* \\cheat *)
QED












(*used to prove eval_add1'_consx using equational reasoning*)
Triviality Proj_exp_rel_lemma:
  exp_rel c (Proj "cons" 1 (Cons "cons" [x; y])) y
Proof
  fs[exp_rel_def,eval_thm,el_def,LNTH_2,v_rel_refl]
QED

Definition add1'oadd1'_def:
  add1'oadd1' = (Lam "x" (App add1' (App add1' (Var "x"))))
End

Theorem exp_rel_add1'oadd1'_add2'_App:
  ∀ x. closed x ⇒ eval c (App add1'oadd1' x) = eval c (App add2' x)
Proof
  rpt strip_tac
  \\ fs[add1'oadd1'_def,add1'_def,add2'_def,cons_def,nil_def]
  \\ fs[eval_LAMREC3]
  \\ fs[closed_def,no_var_no_subst]
  \\ fs[eval_Let]
  \\ fs[bind_def]
  \\ fs[closed_def,no_var_no_subst]
  \\ fs[subst_def]
  \\ fs[LAMREC_def] \\ fs[no_var_no_subst] \\ fs[GSYM LAMREC_def]
  \\ fs[GSYM cons_def,GSYM nil_def]
  \\ fs[GSYM add1'_def,GSYM add2'_def]
  (*here looks good*)
  \\ fs[add1'_def,cons_def,nil_def]
  \\ fs[eval_thm] \\ fs[LAMREC_def]
  \\ fs[eval_thm]
  \\ fs[bind_def]
  \\ fs[closed_def,no_var_no_subst]
  \\ fs[subst_def]
  \\ fs[GSYM LAMREC_def]
  \\ fs[eval_thm]
  \\ fs[subst_funs_def]
  \\ fs[bind_def]
  \\ fs[closed_def,no_var_no_subst]
  \\ fs[subst_def]
  \\ fs[closed_def,no_var_no_subst]
  \\ fs[LAMREC_def] \\ fs[no_var_no_subst] \\ fs[GSYM LAMREC_def]
  \\ fs[GSYM eval_Case]
  \\ fs[GSYM cons_def,GSYM nil_def,GSYM add1'_def]
  (*here also looks good*)
  \\ Cases_on ‘x = nil’ \\ fs[]
  (*from here below, it's probably a good idea to use equational reasoning.*)

  \\ match_mp_tac EQ_TRANS
  \\ qexists_tac ‘ eval c
              (Case r "v"
                 [("nil",[],nil);
                  ("cons",["x"; "xs"],
                   cons [cons [Var "x"; nil]; App add1' (Var "xs")])])’
  \\ conj_tac
  THEN1 (
    match_mp_tac eval_Case_value
    \\ cheat
  )
  \\ cheat


  (* (* *)
  (*     eval c e1 = eval c e2 ⇒ *)
  (*       ∀brs. eval c (Case e1 brs) = eval c (Case e2 brs)   *) *)
  (* THEN1 ( *)
  (*    (*from theorem eval_add1'_nil: *)
  (*         eval c (App add1' nil) = eval c nil*) *)
  (*    fs [add1'_def,LAMREC_def,cons_def,nil_def] *)
  (*    \\ fs[eval_thm] *)
  (*    \\ ntac 4 ( *)
  (*      fs [bind_def,closed_def, subst_def, subst_funs_def] *)
  (*      \\ fs [eval_thm]) *)
  (*    \\ fs [expandCases_def,expandRows_def,expandLets_def]  \\ fs[eval_thm] *)
  (*    \\ fs [bind_def,closed_def, subst_def, subst_funs_def] \\ fs [eval_thm] *)
  (*    \\ fs [is_eq_def,el_def,LNTH_2] *)
  (*    (*additional stuff, because eval is OUTSIDE Case*) *)
  (*    \\ fs[bind_def] *)
  (*    \\ fs[closed_def] \\ fs[subst_def] *)
  (*    \\ fs[eval_thm] *)
  (*    \\ fs[bind_def] \\ fs[subst_funs_def] \\ fs[subst_def]    *)
  (*    \\ ntac 3 ( *)
  (*      fs[closed_def] *)
  (*      \\ fs[bind_def] \\ fs[eval_thm]) *)
  (*    \\ fs[closed_def] \\ fs[subst_def] *)
  (*    \\ ntac 2 ( *)
  (*      fs [is_eq_def,el_def,LNTH_2] *)
  (*      \\ fs[eval_thm] *)
  (*      \\ fs [expandCases_def,expandRows_def,expandLets_def]  \\ fs[eval_thm] *)
  (*      \\ fs [bind_def,closed_def, subst_def, subst_funs_def] \\ fs [eval_thm] ) *)
  (* ) *)






  (*   \\ Cases_on ‘x ≠ nil ∧ ∀ a b. x ≠ cons [a;b]’ \\ fs[] *)

  (*   \\  fs[add1'_def,LAMREC_def,cons_def,nil_def,eval_thm] *)

  (*   \\ fs[expandCases_def,expandRows_def,expandLets_def] \\ fs[eval_thm] *)
  (*   \\ fs[bind_def] \\ fs[closed_def,no_var_no_subst] \\ fs[subst_def] \\ fs[eval_thm] *)
  (*   \\ fs[is_eq_def,el_def,LNTH_2] *)
  (*   \\ fs[bind_def] \\ fs[closed_def,no_var_no_subst] \\ fs[subst_def] \\ fs[eval_thm] *)
  (*   \\ fs[subst_funs_def] *)
  (*   \\ fs[bind_def] \\ fs[closed_def,no_var_no_subst] \\ fs[subst_def] \\ fs[eval_thm] *)
  (*   \\ fs[expandCases_def,expandRows_def,expandLets_def] \\ fs[eval_thm] *)

QED



Theorem progress_lemma:
  progress c exp1 next ∧ progress c exp2 next ⇒
  ∀x. exp_rel c (App exp1 x) (App exp2 x)
Proof
  cheat
QED

(*because of the way exp_rel is defined over closures, this should hold*)
(*the opposite should follow from equational reasoning*)
Theorem App_Closure_lemma:
  ∀x. exp_rel c (App exp1 x) (App exp2 x) ⇒ exp_rel c exp1 exp2
Proof
  cheat
QED

Theorem exp_rel_add1'oadd1'_add2':
  exp_rel c add1'oadd1' add2'
Proof
  cheat
QED


Theorem deforestation:
  ∀ c l f g.
  closed f ∧ closed g ∧ closed l ∧
  f = Lam fn fb ∧ g = Lam gn ge
   ⇒
   exp_rel c
     (*(map f) (map g l)*)
     (*Apps map [f;Apps map [g;l]]*)
     (App (App map f) (App (App map g) l))
     (*map (f.g) l*)
     (App (App map (App (App dot f) g)) l)
Proof
  rw[]
  \\ fs[exp_rel_def,v_rel_def,v_rel'_def] \\ strip_tac
  \\ fs [eval_thm]
  \\ ‘eval c map ≠ Diverge’ by (cheat)
  \\ fs [map_def,eval_thm]
  \\ fs [bind_def]
  \\ fs [subst_def]
  \\ fs [eval_thm]
  \\ fs [closed_def]
  \\ fs [subst_def]
  \\ cheat
QED

val _ = export_theory();
