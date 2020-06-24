
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     ltreeTheory llistTheory;

val _ = new_theory "denotation_cons";


(* AST for a small functional language *)

Type vname = “:string”  (* variable name *)
Type fname = “:string”  (* function name *)

Datatype:
  op = If               (* if-expression                    *)
     | Lit num          (* literal number                   *)
     | Cons string      (* datatype constructor             *)
     | Proj num         (* reading a field of a constructor *)
End

Datatype:
  exp = Var vname                     (* variable                   *)
      | Prim op (exp list)            (* primitive operations       *)
      | App exp exp                   (* function application       *)
      | Fun (fname option) vname exp  (* lambda that optionally     *)
                                      (* binds its own name (fname) *)
End

(* some abbreviations *)
Overload Lam = “Fun NONE”         (* lambda without a function name *)
Overload Rec = “λf. Fun (SOME f)”      (* lambda with function name *)
Overload Let = “λs x y. App (Lam s y) x”          (* let-expression *)
Overload If = “λx y z. Prim If [x; y; z]”        (* It at exp level *)
Overload Lit = “λn. Prim (Lit n) []”            (* Lit at exp level *)
Overload Cons = “λs. Prim (Cons s)”            (* Cons at exp level *)
Overload Proj = “λi x. Prim (Proj i) [x]”      (* Proj at exp level *)

(* a call-by-name semantics in a denotational semantics style *)

(* would like to have:
Codatatype:
  v = Num num
    | Constructor string (v list)
    | Closure fname vname exp
    | Diverge
    | Error
End
*)

Datatype:
  v_prefix = Num' num
           | Constructor' string
           | Closure' (fname option) vname exp
           | Diverge'
           | Error'
End

Type v = “:v_prefix ltree”;

Overload Num = “λn. Branch (Num' n) LNIL”;
Overload Constructor = “λs ts. Branch (Constructor' s) ts”;
Overload Constructor = “λs ts. Branch (Constructor' s) (fromList ts)”;
Overload Closure = “λf s x. Branch (Closure' f s x) LNIL”;
Overload Diverge = “Branch Diverge' LNIL”;
Overload Error = “Branch Error' LNIL”;

Definition dest_Closure_def:
  dest_Closure x =
    case x of Closure f s x => SOME (f,s,x) | _ => NONE
End

Theorem dest_Closure_Closure[simp]:
  dest_Closure (Closure f s x) = SOME (f,s,x)
Proof
  fs [dest_Closure_def]
QED

Triviality exp_size_lemma:
  ∀xs a. MEM a xs ⇒ exp_size a < exp1_size xs
Proof
  Induct \\ rw [] \\ res_tac \\ fs [fetch "-" "exp_size_def"]
QED

Definition subst_def:
  subst name v (Var s) = (if name = s then v else Var s) ∧
  subst name v (Prim op xs) = Prim op (MAP (subst name v) xs) ∧
  subst name v (App x y) = App (subst name v x) (subst name v y) ∧
  subst name v (Fun f s x) =
    Fun f s (if s = name ∨ f = SOME name then x else subst name v x)
Termination
  WF_REL_TAC `measure (λ(n,v,x). exp_size x)` \\ rw []
  \\ imp_res_tac exp_size_lemma \\ fs []
End

Definition subst_opt_def[simp]:
  subst_opt NONE v x = x ∧
  subst_opt (SOME n) v x = subst n v x
End

Definition el_def:
  el i x =
    if x = Diverge then Diverge else
      case x of
      | Constructor s xs =>
          (case LNTH i xs of NONE => Error | SOME x => x)
      | _ => Error
End

Definition eval_op_def:
  (eval_op (Lit n) [] = Num n) ∧
  (eval_op (Cons s) xs = Constructor s xs) ∧
  (eval_op If [x1;x2;x3] =
    if x1 = Diverge then Diverge else
    if x1 = Num 1 then x2 else
    if x1 = Num 0 then x3 else Error) ∧
  (eval_op (Proj i) [x] = el i x) ∧
  (eval_op _ _ = Error)
End

Definition eval_to_def:
  eval_to k (Var s) = Error ∧
  eval_to k (Prim op xs) = eval_op op (MAP (eval_to k) xs) ∧
  eval_to k (Fun f s x) = Closure f s x ∧
  eval_to k (App x y) =
    (let v = eval_to k x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (f,s,body) =>
             if k = 0 then Diverge else
               eval_to (k-1) (subst s y (subst_opt f (Fun f s body) body)))
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λ(k,x). (k,exp_size x))` \\ rw []
  \\ imp_res_tac exp_size_lemma \\ fs []
End

(*
  limit (div,div,div,div,div,...) d = div

  limit (div,div,div,div,div,4,4,4,4,4,4,4,4,4,4,4,4,...) d = 4

  limit (1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,...) d = d
*)

Definition limit_def:
  limit (f:num->'a) default =
    (* if there is a value x that forever repeats from some
       index k onwards in sequence f, then return that x;
       in the other case we return the default value *)
    case (some x. ∃k. ∀n. k ≤ n ⇒ f n = x) of
    | SOME x => x
    | NONE => default
End

Definition v_lookup_def:
  v_lookup [] x =
    (case x of Branch a ts => (a,LLENGTH ts)) ∧
  v_lookup (n::path) x =
    (case x of Branch a ts => v_lookup path (THE (LNTH n ts)))
End

Definition v_limit_def:
  v_limit v_seq path =
    limit (λk. v_lookup path (v_seq k)) (Error', NONE)
End

Definition eval_def:
  eval x =
    gen_ltree (λpath. v_limit (λk. eval_to k x) path)
End

Theorem limit_const[simp]:
  limit (λk. x) d = x
Proof
  fs [limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  THEN1 (first_x_assum (qspec_then ‘k’ mp_tac) \\ fs [])
  \\ first_x_assum (qspec_then ‘x’ mp_tac) \\ fs []
QED

Theorem limit_eq_add:
  ∀k p x f.
    limit (λn. f (n + k)) p = x ⇒
    limit f p = x
Proof
  rw [limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  THEN1
   (first_x_assum (qspec_then ‘k'+k''’ mp_tac)
    \\ first_x_assum (qspec_then ‘k+k'+k''’ mp_tac)
    \\ fs [])
  THEN1
   (first_x_assum (qspecl_then [‘f (k+k')’,‘k'’] strip_assume_tac)
    \\ first_assum (qspecl_then [‘k+k'’] strip_assume_tac) \\ fs []
    \\ first_x_assum (qspecl_then [‘n+k’] strip_assume_tac)
    \\ rfs [] \\ rw [] \\ fs [])
  THEN1
   (last_x_assum (qspecl_then [‘x’,‘k+k'’] strip_assume_tac)
    \\ first_x_assum (qspecl_then [‘n-k’] strip_assume_tac) \\ fs []
    \\ rfs [])
QED

Theorem limit_if:
  ∀x y d. limit (λk. if k = 0 then x else y (k − 1)) d = limit y d
Proof
  rw [] \\ match_mp_tac limit_eq_add
  \\ qexists_tac ‘1’ \\ fs []
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
QED

Theorem v_limit_eq_add:
  ∀k p x f.
    v_limit (λn. f (n + k)) p = x ⇒
    v_limit f p = x
Proof
  rw [v_limit_def,FUN_EQ_THM]
  \\ match_mp_tac limit_eq_add
  \\ qexists_tac ‘k’ \\ fs []
QED

Theorem v_limit_if:
  v_limit (λk. if k = 0 then a else b (k − 1)) = v_limit b
Proof
  rw [v_limit_def,FUN_EQ_THM]
  \\ qspecl_then [‘v_lookup x a’,‘λk. v_lookup x (b k)’,‘(Error',NONE)’] mp_tac
       (GSYM limit_if)
  \\ fs [] \\ rw [] \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM] \\ rw []
QED

Theorem v_limit_SOME:
  v_limit f [] = (r,SOME m) ⇔ ∃k. ∀n. k ≤ n ⇒ v_lookup [] (f n) = (r,SOME m)
Proof
  fs [v_limit_def,limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw [v_lookup_def]
  \\ PairCases_on ‘x’ \\ fs []
  \\ eq_tac \\ rw []
  THEN1 metis_tac []
  \\ first_x_assum (qspec_then ‘k+k'’ mp_tac)
  \\ first_x_assum (qspec_then ‘k+k'’ mp_tac) \\ fs []
QED

Theorem limit_not_default:
  limit f d = x ∧ x ≠ d ⇒ ∃k. ∀n. k ≤ n ⇒ f n = x
Proof
  fs [limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ qexists_tac ‘k’ \\ fs []
QED

Theorem eval_op_toList:
  ∀op xs.
    EVERY (λx. ∀a ts. x = Branch a ts ⇒ ∃l. ts = fromList l) xs ⇒
    eval_op op xs = Branch a ts ⇒ ∃l. ts = fromList l
Proof
  ho_match_mp_tac eval_op_ind \\ rw []
  \\ fs [eval_op_def] \\ rw []
  \\ fs [AllCaseEqs(),el_def] \\ rw []
  \\ fs [LNTH_fromList]
  \\ cheat
QED

Theorem eval_to_toList:
  ∀k x a ts. eval_to k x = Branch a ts ⇒ ∃l. ts = fromList l
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  \\ fs [eval_to_def] \\ fs [AllCaseEqs()]
  \\ pop_assum mp_tac
  \\ match_mp_tac eval_op_toList
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem v_limit_Cons:
  v_limit (λk. eval_to k x) [] = (Constructor' s,r) ⇒
  ∃l. r = SOME l
Proof
  rw [v_limit_def]
  \\ drule limit_not_default \\ fs [] \\ rw []
  \\ first_x_assum (qspec_then ‘k’ mp_tac)
  \\ fs [v_lookup_def]
  \\ Cases_on ‘eval_to k x’ \\ fs [] \\ rw []
  \\ imp_res_tac eval_to_toList \\ fs []
QED

Theorem limit_eq_imp:
  limit f d = x ∧ (∀n. k ≤ n ⇒ f n = y) ⇒ x = y
Proof
  rw [] \\ fs [limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  THEN1 (rpt (first_x_assum (qspec_then ‘k+k'’ mp_tac)) \\ fs [])
  \\ first_x_assum (qspecl_then [‘y’,‘k’] mp_tac) \\ rw []
  \\ res_tac
QED

(*
Theorem eval_op_div:
  LIST_REL (λx y. x ≠ Diverge ⇒ x = y) xs ys ∧
  eval_op op xs ≠ Diverge ⇒
  eval_op op ys = eval_op op xs
Proof
  .. (* not true *)
QED

Theorem eval_to_determ_lemma:
  ∀n x k.
    eval_to n x ≠ Diverge ⇒
    eval_to (n+k) x = eval_to n x
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  \\ TRY (fs [eval_to_def] \\ NO_TAC)
  THEN1
   (fs [eval_to_def]
    \\ match_mp_tac eval_op_div \\ fs []
    \\ pop_assum kall_tac
    \\ Induct_on ‘xs’ \\ fs [])
  \\ Cases_on ‘eval_to n x = Diverge’ \\ fs []
  THEN1 fs [eval_to_def]
  \\ fs [eval_to_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ fs [AllCaseEqs(),dest_Closure_def]
  \\ rw [] \\ fs []
QED

Theorem eval_to_res_mono:
  eval_to k x ≠ Diverge ∧ k ≤ k1 ⇒ eval_to k1 x = eval_to k x
Proof
  metis_tac [LESS_EQ_EXISTS,eval_to_determ_lemma]
QED
*)

Theorem eval_op_div:
  ∀op xs ys.
    LIST_REL (λx y. x ≠ Diverge ⇒ v_lookup [] x = v_lookup [] y) xs ys ⇒
    eval_op op xs ≠ Diverge ∧
    eval_op op xs = Branch a ts ∧
    eval_op op ys = Branch a1 ts1 ⇒
      a1 = a ∧ LLENGTH ts1 = LLENGTH ts
Proof
  ho_match_mp_tac eval_op_ind \\ rw []
  \\ fs [eval_op_def] \\ rw [] \\ fs []
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
  \\ fs [AllCaseEqs(),el_def] \\ fs []
  \\ rw [] \\ fs [v_lookup_def]
  \\ fs [list_CASE_eq] \\ rw []
  \\ qspec_then ‘xs’ mp_tac fromList_fromSeq
  \\ qspec_then ‘xs'’ mp_tac fromList_fromSeq
  \\ rw [] \\ fs [LNTH_fromList]
  \\ cheat
QED

Theorem eval_to_res_mono_lemma:
  ∀k x n a ts a1 ts1.
    eval_to k x ≠ Diverge ∧
    eval_to k x = Branch a ts ∧
    eval_to (k+n) x = Branch a1 ts1 ⇒
      a1 = a ∧ LLENGTH ts1 = LLENGTH ts
Proof
  ho_match_mp_tac eval_to_ind \\ rpt conj_tac
  \\ rpt gen_tac
  \\ TRY (fs [eval_to_def] \\ rw [] \\ NO_TAC)
  THEN1
   (fs [eval_to_def] \\ strip_tac
    \\ rpt gen_tac
    \\ match_mp_tac eval_op_div
    \\ Induct_on ‘xs’ \\ fs []
    \\ reverse (rw []) THEN1 metis_tac []
    \\ first_x_assum (qspec_then ‘h’ mp_tac) \\ fs []
    \\ disch_then (qspec_then ‘n’ mp_tac)
    \\ Cases_on ‘eval_to k h’
    \\ Cases_on ‘eval_to (k+n) h’ \\ fs [v_lookup_def])
  \\ Cases_on ‘eval_to k x = Diverge’ \\ fs []
  THEN1 fs [eval_to_def]
  \\ cheat
QED

Theorem eval_to_res_mono:
  eval_to k x ≠ Diverge ∧
  eval_to k x = Branch a ts ∧
  eval_to k1 x = Branch a1 ts1 ∧
  k ≤ k1 ⇒
    a1 = a ∧ LLENGTH ts1 = LLENGTH ts
Proof
  fs [LESS_EQ_EXISTS] \\ rw []
  \\ metis_tac [eval_to_res_mono_lemma]
QED

Theorem eval_to_res_mono_LNIL:
  eval_to k x = Branch a LNIL ∧
  eval_to k x ≠ Diverge ∧
  k ≤ k1 ⇒
    eval_to k1 x = eval_to k x
Proof
  rw []
  \\ drule eval_to_res_mono
  \\ disch_then drule
  \\ Cases_on ‘eval_to k1 x’
  \\ disch_then drule
  \\ fs []
QED

Theorem eval_to_simple_mono:
  eval_to k1 x = Branch a LNIL ∧
  eval_to k x ≠ Diverge ∧
  k ≤ k1 ⇒
    eval_to k1 x = eval_to k x
Proof
  rw []
  \\ drule eval_to_res_mono
  \\ Cases_on ‘eval_to k x’
  \\ simp []
  \\ last_x_assum assume_tac
  \\ disch_then drule
  \\ fs []
QED

Theorem eval_to_div:
  eval_to k1 x = Diverge ∧ k ≤ k1 ⇒ eval_to k x = Diverge
Proof
  rw [] \\ CCONTR_TAC
  \\ drule eval_to_simple_mono
  \\ disch_then drule \\ fs []
QED

Theorem dest_Closure_eval_IMP:
  dest_Closure (eval x) = NONE ⇒
  dest_Closure (eval_to k x) = NONE
Proof
  rw []
  \\ simp [AllCaseEqs(),dest_Closure_def]
  \\ CCONTR_TAC \\ fs []
  \\ Cases_on ‘eval_to k x’ \\ fs []
  \\ Cases_on ‘a’ \\ fs []
  \\ Cases_on ‘ts’ \\ fs []
  \\ rename [‘Closure x1 x2 x3’]
  \\ qsuff_tac ‘eval x = Closure x1 x2 x3’
  THEN1 (strip_tac \\ fs [dest_Closure_def])
  \\ fs [eval_def,gen_ltree_LNIL,v_limit_SOME]
  \\ drule eval_to_res_mono_LNIL \\ fs [] \\ rw []
  \\ qexists_tac ‘k’ \\ fs [v_lookup_def]
QED

Theorem v_lookup_eq_SOME_0[simp]:
  v_lookup [] t = (h,SOME 0) ⇔ t = Branch h LNIL
Proof
  fs [v_lookup_def]
  \\ Cases_on ‘t’ \\ fs []
QED

Theorem eval_Lit:
  eval (Lit n) = Num n
Proof
  fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
  \\ fs [v_limit_def,v_lookup_def]
QED

Theorem eval_Var:
  eval (Var s) = Error (* free variables are not allowed *)
Proof
  fs [eval_def,eval_to_def,Once gen_ltree]
  \\ fs [v_limit_def,v_lookup_def]
QED

Theorem eval_Fun:
  eval (Fun f s x) = Closure f s x
Proof
  fs [eval_def,eval_to_def,Once gen_ltree]
  \\ fs [v_limit_def,v_lookup_def]
QED

Theorem eval_App:
  eval (App x y) =
    let v = eval x in
      if v = Diverge then Diverge else
        case dest_Closure v of
        | NONE => Error
        | SOME (f,s,body) =>
            eval (subst s y (subst_opt f (Fun f s body) body))
Proof
  fs [eval_def,eval_to_def]
  \\ IF_CASES_TAC \\ fs [gen_ltree_LNIL]
  THEN1 (fs [v_limit_SOME] \\ qexists_tac ‘k’ \\ fs [])
  \\ CASE_TAC
  THEN1
   (fs [v_limit_SOME]
    \\ fs [GSYM eval_def]
    \\ imp_res_tac dest_Closure_eval_IMP \\ fs []
    \\ fs [gen_ltree_LNIL]
    \\ fs [v_limit_SOME]
    \\ last_x_assum (qspec_then ‘0’ strip_assume_tac) \\ fs []
    \\ qexists_tac ‘k'’ \\ fs [] \\ rpt strip_tac
    \\ rw [] \\ imp_res_tac eval_to_div)
  \\ rename [‘_ = SOME y’] \\ PairCases_on ‘y’ \\ fs []
  \\ fs [dest_Closure_def,AllCaseEqs()]
  \\ fs [gen_ltree_LNIL]
  \\ fs [v_limit_SOME]
  \\ AP_TERM_TAC \\ fs [FUN_EQ_THM] \\ rw []
  \\ match_mp_tac v_limit_eq_add
  \\ fs [] \\ qexists_tac ‘k+1’ \\ fs []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ match_mp_tac v_limit_eq_add
  \\ fs [] \\ qexists_tac ‘k’ \\ fs []
QED

Theorem eval_Let:
  eval (Let s x y) = eval (subst s x y)
Proof
  fs [eval_App,eval_Fun,dest_Closure_def,subst_opt_def]
QED

Theorem eval_Cons:
  eval (Cons s xs) = Constructor s (MAP eval xs)
Proof
  fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
  \\ fs [v_limit_def,v_lookup_def,LGENLIST_EQ_fromList,LNTH_fromList]
  \\ fs [LIST_EQ_REWRITE]
  \\ fs [EL_MAP,eval_def,v_limit_def]
QED

Theorem gen_ltree_not_Error:
  gen_ltree (λpath. v_limit (λk. eval_to k x) path) = Branch a ts ∧
  a ≠ Error' ⇒
  ∃k. ∀n. k ≤ n ⇒ ∃ts. eval_to n x = Branch a ts
Proof
  once_rewrite_tac [gen_ltree] \\ fs [pairTheory.UNCURRY] \\ rw []
  \\ Cases_on ‘v_limit (λk. eval_to k x) []’
  \\ fs [v_limit_def]
  \\ drule limit_not_default \\ fs []
  \\ rpt strip_tac \\ qexists_tac ‘k’ \\ fs []
  \\ rpt strip_tac \\ first_x_assum drule
  \\ fs [] \\ Cases_on ‘eval_to n x’ \\ fs []
  \\ fs [v_lookup_def]
QED

Theorem eval_Proj:
  eval (Proj i x) = el i (eval x)
Proof
  fs [eval_def,eval_to_def,eval_op_def,el_def]
  \\ IF_CASES_TAC \\ fs [gen_ltree_LNIL]
  THEN1 (fs [v_limit_SOME] \\ qexists_tac ‘k’ \\ fs [])
  \\ fs [GSYM eval_def]
  \\ Cases_on ‘eval x’ \\ fs [eval_def]
  \\ Cases_on ‘ts’
  THEN1
   (Cases_on ‘a’ \\ fs []
    \\ fs [v_limit_SOME,gen_ltree_LNIL]
    \\ qexists_tac ‘k’ \\ fs [])
  \\ Cases_on ‘a’ \\ fs []
  \\ fs [v_limit_SOME,gen_ltree_LNIL]
  \\ pop_assum mp_tac
  THEN1
   (rw [] \\ drule gen_ltree_not_Error \\ fs []
    \\ strip_tac \\ qexists_tac ‘k’ \\ fs []
    \\ rpt strip_tac \\ res_tac \\ fs [])
  THEN1
   (simp [Once gen_ltree,pairTheory.UNCURRY]
    \\ Cases_on ‘v_limit (λk. eval_to k x) []’ \\ fs [] \\ rw []
    \\ imp_res_tac v_limit_Cons \\ rw []
    \\ fs [v_limit_SOME]
    \\ pop_assum (assume_tac o GSYM) \\ fs []
    \\ fs [LGENLIST_EQ_fromList,LNTH_fromList]
    \\ pop_assum kall_tac
    \\ reverse IF_CASES_TAC \\ fs []
    THEN1
     (fs [v_limit_SOME,gen_ltree_LNIL]
      \\ qexists_tac ‘k’ \\ fs [] \\ rpt strip_tac
      \\ first_x_assum drule \\ fs [v_lookup_def]
      \\ Cases_on ‘eval_to k'' x’ \\ fs []
      \\ qspec_then ‘ts’ mp_tac fromList_fromSeq \\ rw [] \\ fs []
      \\ rw [] \\ fs [LNTH_fromList])
    \\ AP_TERM_TAC \\ fs [FUN_EQ_THM]
    \\ rw [] \\ fs [v_lookup_def]
    \\ match_mp_tac v_limit_eq_add
    \\ qexists_tac ‘k’ \\ fs []
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ match_mp_tac v_limit_eq_add
    \\ qexists_tac ‘k’ \\ fs []
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ fs [v_limit_def,v_lookup_def]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ fs [FUN_EQ_THM] \\ rpt strip_tac
    \\ first_x_assum (qspec_then ‘k+n’ mp_tac) \\ fs []
    \\ Cases_on ‘eval_to (k + n) x’ \\ fs [] \\ rw []
    \\ qspec_then ‘ts’ mp_tac fromList_fromSeq \\ rw [] \\ fs []
    \\ rw [] \\ fs [LNTH_fromList])
  THEN1
   (rw [] \\ drule gen_ltree_not_Error \\ fs []
    \\ strip_tac \\ qexists_tac ‘k’ \\ fs []
    \\ rpt strip_tac \\ res_tac \\ fs [])
  THEN1
   (rw [] \\ drule gen_ltree_not_Error \\ fs []
    \\ strip_tac \\ last_assum (qspec_then ‘k’ mp_tac)
    \\ strip_tac
    \\ qexists_tac ‘k'’ \\ fs []
    \\ rpt strip_tac \\ ‘k ≤ k''’ by fs []
    \\ first_x_assum drule \\ strip_tac
    \\ fs [] \\ rw []
    \\ drule eval_to_div
    \\ disch_then (qspec_then ‘k'’ assume_tac)
    \\ rfs [])
  \\ rw []
  \\ first_x_assum (qspec_then ‘0’ strip_assume_tac) \\ fs []
  \\ qexists_tac ‘k'’ \\ fs [] \\ rw []
  THEN1 (strip_tac \\ imp_res_tac eval_to_div)
  \\ Cases_on ‘eval_to k'' x’ \\ fs []
  \\ Cases_on ‘a’ \\ fs []
  \\ Cases_on ‘LNTH i ts’ \\ fs [] \\ rw []
  \\ last_x_assum mp_tac
  \\ once_rewrite_tac [gen_ltree]
  \\ fs [] \\ Cases_on ‘v_limit (λk. eval_to k x) []’ \\ fs []
  \\ ‘eval_to k'' x ≠ Diverge’ by fs []
  \\ drule eval_to_res_mono \\ fs []
  \\ rpt strip_tac
  \\ fs [v_limit_def,v_lookup_def]
  \\ drule limit_eq_imp
  \\ disch_then (qspecl_then [‘Constructor' s,LLENGTH ts’,‘k''’] mp_tac)
  \\ impl_tac \\ fs []
  \\ rw [] \\ fs []
  \\ res_tac \\ fs []
  \\ Cases_on ‘eval_to n x’ \\ fs []
QED

Theorem eval_If:
  eval (If x y z) =
    (if eval x = Diverge then Diverge else
     if eval x = Num 0 then eval z else
     if eval x = Num 1 then eval y else Error)
Proof
  fs [eval_def,eval_to_def,eval_op_def]
  \\ IF_CASES_TAC \\ fs [gen_ltree_LNIL]
  THEN1 (fs [v_limit_SOME] \\ qexists_tac ‘k’ \\ fs [])
  \\ IF_CASES_TAC \\ fs [gen_ltree_LNIL]
  THEN1
   (fs [v_limit_SOME] \\ AP_TERM_TAC
    \\ fs [FUN_EQ_THM] \\ rw []
    \\ match_mp_tac v_limit_eq_add
    \\ qexists_tac ‘k’ \\ fs []
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ match_mp_tac v_limit_eq_add
    \\ qexists_tac ‘k’ \\ fs [])
  \\ IF_CASES_TAC \\ fs [gen_ltree_LNIL]
  THEN1
   (fs [v_limit_SOME] \\ AP_TERM_TAC
    \\ fs [FUN_EQ_THM] \\ rw []
    \\ match_mp_tac v_limit_eq_add
    \\ qexists_tac ‘k’ \\ fs []
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ match_mp_tac v_limit_eq_add
    \\ qexists_tac ‘k’ \\ fs [])
  \\ fs [v_limit_SOME]
  \\ last_x_assum (qspec_then ‘0’ mp_tac)
  \\ strip_tac \\ rename [‘0 ≤ k1’]
  \\ first_x_assum (qspec_then ‘k1’ mp_tac)
  \\ strip_tac \\ rename [‘_ ≤ k2’]
  \\ first_x_assum (qspec_then ‘k2’ mp_tac)
  \\ strip_tac \\ rename [‘_ ≤ k3’]
  \\ qexists_tac ‘k3’ \\ fs []
  \\ rpt strip_tac
  \\ rpt (IF_CASES_TAC \\ fs [])
  \\ ‘k1 ≤ k' ∧ k2 ≤ k' ∧ k3 ≤ k'’ by fs []
  THEN1 imp_res_tac eval_to_div
  \\ ‘eval_to k2 x ≠ Diverge ∧ eval_to k3 x ≠ Diverge’ by
        (CCONTR_TAC \\ fs [] \\ imp_res_tac eval_to_div)
  \\ metis_tac [eval_to_simple_mono]
QED

Theorem eval_Prim:
  eval (Prim op xs) = eval_op op (MAP eval xs)
Proof
  Cases_on ‘∃s. op = Cons s’
  THEN1 fs [eval_Cons,eval_op_def]
  \\ Cases_on ‘∃n. op = Lit n’
  THEN1
   (Cases_on ‘xs’ \\ fs [eval_Lit,eval_op_def]
    \\ fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
    \\ fs [v_limit_def,v_lookup_def])
  \\ Cases_on ‘op = If’
  THEN1
   (Cases_on ‘∃x1 x2 x3. xs = [x1;x2;x3]’
    THEN1 (rw [] \\ fs [eval_If,eval_op_def] \\ rw [] \\ fs [])
    \\ fs []
    \\ rpt
       (rename [‘xs ≠ _’] \\ Cases_on ‘xs’ \\ fs [] THEN1
         (fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
          \\ fs [v_limit_def,v_lookup_def])))
  \\ Cases_on ‘∃i. op = Proj i’
  THEN1
   (Cases_on ‘xs’ \\ fs [eval_op_def]
    THEN1
      (fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
       \\ fs [v_limit_def,v_lookup_def])
    \\ Cases_on ‘t’ \\ fs [eval_Proj,eval_op_def]
    \\ fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
    \\ fs [v_limit_def,v_lookup_def])
  \\ Cases_on ‘op’ \\ fs []
QED

Theorem eval_core:
  eval (Var s) = Error (* free variables are not allowed *) ∧
  eval (Prim op xs) = eval_op op (MAP eval xs) ∧
  eval (Fun f s x) = Closure f s x ∧
  eval (App x y) =
    (let v = eval x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (f,s,body) =>
             eval (subst s y (subst_opt f (Fun f s body) body)))
Proof
  fs [eval_Var,eval_Prim,eval_Fun,eval_App]
QED

Theorem eval_thm:
  eval (Lit n) = Num n ∧
  eval (Var s) = Error (* free variables are not allowed *) ∧
  eval (Cons s xs) = Constructor s (MAP eval xs) ∧
  eval (Proj i x) = el i (eval x) ∧
  eval (Let s x y) = eval (subst s x y) ∧
  eval (If x y z) =
    (if eval x = Diverge then Diverge else
     if eval x = Num 0 then eval z else
     if eval x = Num 1 then eval y else Error) ∧
  eval (Fun f s x) = Closure f s x ∧
  eval (App x y) =
    (let v = eval x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (f,s,body) =>
             eval (subst s y (subst_opt f (Fun f s body) body)))
Proof
  fs [eval_Var,eval_Cons,eval_App,eval_Fun,eval_Lit,eval_If,eval_Proj]
QED


(* prove that bottom diverges *)

Definition bottom_def:
  bottom =
    Let "bot"
      (Rec "bot" "n" (App (Var "bot") (Lit 0)))
      (App (Var "bot") (Lit 0))
End

Theorem eval_bottom:
  eval bottom = Diverge
Proof
  qsuff_tac ‘∀k. eval_to k bottom = Diverge’
  THEN1 fs [eval_def,v_limit_def,v_lookup_def,gen_ltree_LNIL]
  \\ fs [bottom_def,eval_to_def]
  \\ Cases \\ fs [subst_def]
  \\ Induct_on ‘n’ \\ fs []
  \\ simp [eval_to_def,subst_def,subst_opt_def,dest_Closure_def]
QED


(* example producing infinite list of zeros *)

Definition zeros_def:
  zeros =
    Let "z"
      (Rec "z" "n" (Cons "cons" [Var "n"; App (Var "z") (Var "n")]))
        (App (Var "z") (Lit 0))
End

Theorem eval_zeros:
  eval zeros = Constructor "cons" [Num 0; eval zeros]
Proof
  fs [Once zeros_def]
  \\ ntac 6 (simp [Once eval_thm,dest_Closure_def,subst_def])
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once eval_thm,dest_Closure_def,subst_def,zeros_def]
QED

val _ = export_theory();
