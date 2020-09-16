
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     ltreeTheory llistTheory;

val _ = new_theory "pure_lang";


(* AST for a small functional language *)

Type vname = “:string”  (* variable name *)
Type fname = “:string”  (* function name *)

Datatype:
  op = If               (* if-expression                    *)
     | Lit num          (* literal number                   *)
     | Cons string      (* datatype constructor             *)
     | IsEq string      (* compare cons tag                 *)
     | Proj string num  (* reading a field of a constructor *)
     | Add              (* primitive add operator           *)
End

Datatype:
  exp = Var vname                     (* variable                   *)
      | Prim op (exp list)            (* primitive operations       *)
      | App exp exp                   (* function application       *)
      | Lam vname exp                 (* lambda                     *)
      | Letrec ((fname # vname # exp) list) exp   (* mut. rec. funs *)
End

(* some abbreviations *)
Overload Let  = “λs x y. App (Lam s y) x”         (* let-expression *)
Overload If   = “λx y z. Prim If [x; y; z]”      (* If at exp level *)
Overload Lit  = “λn. Prim (Lit n) []”           (* Lit at exp level *)
Overload Cons = “λs. Prim (Cons s)”            (* Cons at exp level *)
Overload IsEq = “λs x. Prim (IsEq s) [x]”      (* IsEq at exp level *)
Overload Proj = “λs i x. Prim (Proj s i) [x]”  (* Proj at exp level *)
Overload Fail = “Prim (Lit ARB) [Prim (Lit ARB)[]]” (* causes Error *)

(* a call-by-name semantics in a denotational semantics style *)

(* would like to have:
Codatatype:
  v = Num num
    | Constructor string (v list)
    | Closure vname exp
    | Diverge
    | Error
End
*)

Datatype:
  v_prefix = Num' num
           | Constructor' string
           | Closure' vname exp
           | Diverge'
           | Error'
End

Type v = “:v_prefix ltree”;

Overload Num = “λn. Branch (Num' n) LNIL”;
Overload Constructor = “λs ts. Branch (Constructor' s) ts”;
Overload Constructor = “λs ts. Branch (Constructor' s) (fromList ts)”;
Overload Closure = “λs x. Branch (Closure' s x) LNIL”;
Overload Diverge = “Branch Diverge' LNIL”;
Overload Error = “Branch Error' LNIL”;

Definition dest_Closure_def:
  dest_Closure x =
    case x of Closure s x => SOME (s,x) | _ => NONE
End

Theorem dest_Closure_Closure[simp]:
  dest_Closure (Closure s x) = SOME (s,x)
Proof
  fs [dest_Closure_def]
QED

Triviality exp_size_lemma:
  (∀xs a. MEM a xs ⇒ exp_size a < exp4_size xs) ∧
  (∀xs x y a. MEM (x,y,a) xs ⇒ exp_size a < exp1_size xs)
Proof
  conj_tac \\ Induct \\ rw [] \\ res_tac \\ fs [fetch "-" "exp_size_def"]
QED

Definition subst_def:
  subst name v (Var s) = (if name = s then v else Var s) ∧
  subst name v (Prim op xs) = Prim op (MAP (subst name v) xs) ∧
  subst name v (App x y) = App (subst name v x) (subst name v y) ∧
  subst name v (Lam s x) = Lam s (if s = name then x else subst name v x) ∧
  subst name v (Letrec f x) =
    if MEM name (MAP FST f) then Letrec f x else
      Letrec (MAP (λ(g,m,z). (g,m,subst name v z)) f) (subst name v x)
Termination
  WF_REL_TAC `measure (λ(n,v,x). exp_size x)` \\ rw []
  \\ imp_res_tac exp_size_lemma \\ fs []
End

(*An expression is closed when every variable in it is bound.
  A variable (Var "x") is bound if there's a lambda abstraction
  above in the AST that captures it (Lam "x" ...).

  Alternatively, an expression is closed if a substitution fails
  (leaves the expression unaltered) for any possible variable
  identifier.                                                     *)
Definition closed_def:
  closed e = ∀n v. subst n v e = e
End

(*projection: given the constructor name s, and the index i,
  access the object x and retrieve the i-th element
  if present, otherwise returns Error. *)
Definition el_def:
  el s i x =
    if x = Diverge then Diverge else
      case x of
      | Constructor t xs =>
          if s = t then
            (case LNTH i xs of NONE => Error | SOME x => x)
          else Error
      | _ => Error
End

(*check whether the constructor x is labeled as s, if so
  return Num 1 (true), Num 0 otherwise *)
Definition is_eq_def:
  is_eq s x =
    if x = Diverge then Diverge else
      case x of
      | Constructor t (xs:v llist) => Num (if s = t then 1 else 0)
      | _ => Error
End


Definition getNum_def:
  getNum (Num n) = SOME n ∧
  getNum _       = NONE
End

Definition eval_op_def:
  (eval_op (Lit n) [] = Num n) ∧
  (eval_op (Cons s) xs = Constructor s xs) ∧
  (eval_op If [x1;x2;x3] =
    if x1 = Diverge then Diverge else
    if x1 = Num 1 then x2 else
    if x1 = Num 0 then x3 else Error) ∧
  (eval_op (IsEq s) [x] = is_eq s x) ∧
  (eval_op (Proj s i) [x] = el s i x) ∧
  (eval_op Add [a1;a2] =
     if a1 = Diverge then Diverge else
     if a2 = Diverge then Diverge else
   case (getNum a1,getNum a2) of
     | (SOME n1,SOME n2) => (Num (n1 + n2))
     | _               => Error )  ∧
  (eval_op _ _ = Error)
End

Definition bind_def:
  bind [] x = x ∧
  bind ((s,v)::ys) x =
    if closed v then subst s v (bind ys x) else Fail
End

Definition subst_funs_def:
  subst_funs f = bind (MAP (λ(g,n,x). (g,Lam n (Letrec f x))) f)
End

Definition eval_to_def:
  eval_to k (Var s) = Error ∧
  eval_to k (Prim op xs) = eval_op op (MAP (eval_to k) xs) ∧
  eval_to k (Lam s x) = Closure s x ∧
  eval_to k (App x y) =
    (let v = eval_to k x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (s,body) =>
             if k = 0 then Diverge else
               eval_to (k-1) (bind [(s,y)] body)) ∧
  eval_to k (Letrec f y) =
    if k = 0 then Diverge else
      eval_to (k-1) (subst_funs f y)
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λ(k,x). (k,exp_size x))` \\ rw []
  \\ imp_res_tac exp_size_lemma \\ fs []
End

(*
  limit (div,div,div,div,div,...) d = div

  limit (div,div,div,div,div,4,4,4,4,4,4,4,4,4,4,4,4,...) d = 4

  limit (1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,...) d = d

  limit is used to define eval in terms of ‘∀ k . eval_to k’
  eval_to is deterministic, hence, we wouldn't need "d" in
  limit (k -> v) d. But is convenient for the proofs.
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

(*v_lookup takes a list of indexes and an ltree, goes trough
  the tree following the indexes in the list until list = [],
  then it returns the value at the given node, together with the
  number of children at that node *)

(*LLENGTH returns the length of the lazy list llist, when it is
  finite (SOME n), otherwise NONE. supposedly, (a,LLENGTH ts) refers
  to the constructor/literal together with its cardinality.

  LNTH = "Lazy n-th element"                                        *)

Definition v_lookup_def:
  v_lookup [] x =
    (case x of Branch a ts => (a,LLENGTH ts)) ∧
  v_lookup (n::path) x =
    (case x of Branch a ts =>
       case LNTH n ts of
       | NONE => (Diverge',SOME 0)
       | SOME y => v_lookup path y)
End

 (*
   v_seq: num -> v_prefix ltree
   given a certain path, v_limit tries to look into a rose tree (v_seq k)
   with k any num.
  *)
Definition v_limit_def:
  v_limit v_seq path =
    limit (λk. v_lookup path (v_seq k)) (Error', NONE)
End

(*
   given an expression x, eval returns the denotational
   value associated to it. Since eval might produce
   infinite values as result, the resulting value needs
   to be "wrapped" into a lazy datatype. This is the role
   of gen_ltree. gen_ltree takes a function that, given
   any path over the resulting ltree, the function returns
   the values in that specific branch.
   In fact, eval has type : exp -> v_prefix ltree, instead
   of exp -> v_prefix. Also, a value is defined
   as an object of type :v_prefix ltree
*)
Definition eval_def:
  eval x =
    gen_ltree (λpath. v_limit (λk. eval_to k x) path)
End


(**** LEMMAS for limit/v_limit algebra *****)

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

Theorem v_limit_not_Error:
  v_limit f [] = (r,l) ∧ r ≠ Error' ⇒
  ∃k. ∀n. k ≤ n ⇒ v_lookup [] (f n) = (r,l)
Proof
  fs [v_limit_def,limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw [v_lookup_def]
  \\ metis_tac []
QED

Theorem limit_not_default:
  limit f d = x ∧ x ≠ d ⇒ ∃k. ∀n. k ≤ n ⇒ f n = x
Proof
  fs [limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ qexists_tac ‘k’ \\ fs []
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

(***********************************)

(* x and y : v_prefix ltree, v_cmp checks whether x and y are equal
   for the given path. If x or y diverge, then they ARE equal.
   v_cmp is a relation used to prove some lemmas over eval_to,
   ultimately, used to prove eval_thm
*)
Definition v_cmp_def:
  v_cmp path x y ⇔
    (v_lookup path x ≠ (Diverge',SOME 0) ⇒
     v_lookup path y = v_lookup path x)
End

Triviality v_cmp_refl[simp]:
  v_cmp path x x
Proof
  fs [v_cmp_def]
QED

Triviality v_cmp_Diverge[simp]:
  ∀path x. v_cmp path Diverge x
Proof
  Induct \\ fs [v_cmp_def,v_lookup_def]
QED

Theorem v_cmp_Diverge2:
  (∀path. v_cmp path x y) ∧ x ≠ Diverge ⇒ y ≠ Diverge
Proof
  rw [] \\ CCONTR_TAC \\ fs []
  \\ first_x_assum (qspec_then ‘[]’ mp_tac)
  \\ fs [v_cmp_def,v_lookup_def]
  \\ Cases_on ‘x’ \\ fs []
QED

Theorem v_cmp_LNIL_IMP:
  ∀x y.
    x ≠ Diverge' ⇒
    ((∀path. v_cmp path (Branch x LNIL) y) ⇔ y = Branch x LNIL)
Proof
  rw [] \\ eq_tac \\ rw []
  \\ first_x_assum (qspec_then ‘[]’ mp_tac)
  \\ fs [v_cmp_def,v_lookup_def]
  \\ Cases_on ‘y’ \\ fs []
QED

Theorem getNum_eq_same_length_args:
  ∀ ts ts' . LLENGTH ts = LLENGTH ts'
             ⇒ getNum (Branch q ts) = getNum (Branch q ts')
Proof
  Cases_on ‘q’ \\ Cases_on ‘ts’ \\ Cases_on ‘ts'’ \\ rw [getNum_def]
QED

Theorem v_cmp_getNum_eq:
  ∀x y.
    x ≠ Diverge ∧ y ≠ Diverge ⇒
    ((∀path. v_cmp path x y) ⇒ (getNum x) = (getNum y))
Proof
  rw []
  \\ first_x_assum (qspec_then ‘[]’ assume_tac)
  \\ Cases_on ‘x’
  \\ fs [v_cmp_def,v_lookup_def,ltree_CASE]
  \\ first_assum imp_res_tac
  \\ Cases_on ‘y’
  \\ fs [ltree_CASE]
  \\ rw []
  \\ imp_res_tac getNum_eq_same_length_args
  \\ rw [] 
QED

(*maybe needed later.*)
Triviality eval_strict_op_not_num_error:
  ∀ x y .  x ≠ Diverge ∧
           y ≠ Diverge ∧
           ( (∀ n . x ≠ Num n) ∨ (∀ n. y ≠ Num n) )
             ⇒ eval_op Add [x;y] = Error
Proof
  rw []
  THEN1 (*(∀ n . x ≠ Num n) case *)(
  rw [eval_op_def,getNum_def]
  \\ Cases_on ‘x’ \\ rw [ltree_CASE,llist_CASES,getNum_def]
  \\ rpt(   Cases_on ‘a’ \\ rw [ltree_CASE,llist_CASES,getNum_def]
         \\ Cases_on ‘ts’ \\ rw [ltree_CASE,llist_CASES,getNum_def])
  )(*(∀ n . y ≠ Num n) case *)
  \\ Cases_on ‘∀ n . x ≠ Num n’ \\ fs []
  THEN1 ((*(∀ n . x ≠ Num n) case, again *)
  rw [eval_op_def]
  \\ Cases_on ‘x’ \\ rw [ltree_CASE,llist_CASES,getNum_def]
  \\ rpt(   Cases_on ‘a’ \\ rw [ltree_CASE,llist_CASES,getNum_def]
         \\ Cases_on ‘ts’ \\ rw [ltree_CASE,llist_CASES,getNum_def])
  ) THEN1 ( (*∀ n . y ≠ Num n ∧ x = Num n1 *)
  rw [eval_op_def]
  \\ Cases_on ‘y’ \\ rw [ltree_CASE,llist_CASES,getNum_def]
  \\ rpt (   Cases_on ‘a’ \\ rw [ltree_CASE,llist_CASES,getNum_def]
          \\ Cases_on ‘ts’ \\ rw [ltree_CASE,llist_CASES,getNum_def])
  )
QED

Theorem eval_op_div:
  ∀op xs ys path.
    LIST_REL (λx y. ∀path. v_cmp path x y) xs ys ⇒
    v_cmp path (eval_op op xs) (eval_op op ys)
Proof
  ho_match_mp_tac eval_op_ind \\ rw []
  \\ TRY (fs [eval_op_def] \\ rw [] \\ fs [v_cmp_refl] \\ NO_TAC)
  THEN1 (*op = Cons s *)
   (fs [eval_op_def] \\ fs [v_cmp_def]
    \\ Cases_on ‘path’ \\ fs [v_lookup_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [LNTH_fromList]
    \\ rw [] \\ fs [LIST_REL_EL_EQN])
  THEN1 (*op = If *)
   (fs [eval_op_def]
    \\ Cases_on ‘x1 = Diverge’ \\ fs []
    \\ qspec_then ‘Num' 0’ assume_tac v_cmp_LNIL_IMP
    \\ qspec_then ‘Num' 1’ assume_tac v_cmp_LNIL_IMP
    \\ fs []
    \\ IF_CASES_TAC (*case x = 1 *)
       THEN1 (rw [] \\ imp_res_tac v_cmp_LNIL_IMP \\ fs [])
    \\ IF_CASES_TAC (*case x = 2 *)
       THEN1 (rw [] \\ imp_res_tac v_cmp_LNIL_IMP \\ fs [])
    (*case x ≠ 1 ∧ x ≠ 2 (Error) *)
    \\ Cases_on ‘y’ \\ fs []
    \\ Cases_on ‘ts’ \\ fs []
    \\ last_x_assum (qspec_then ‘[]’ mp_tac)
    \\ simp [Once v_cmp_def,v_lookup_def]
    \\ Cases_on ‘x1’ \\ fs [])
  THEN1 (*op = IsEq s *)
   (fs [eval_op_def]
    \\ Cases_on ‘x = Diverge’ \\ fs []
    \\ TRY (first_x_assum (qspec_then ‘[]’ mp_tac))
    \\ Cases_on ‘path’ \\ fs [v_cmp_def,v_lookup_def,is_eq_def]
    \\ rw [] \\ fs [] \\ fs [ltree_CASE_eq]
    \\ Cases_on ‘y’ \\ fs []
    \\ Cases_on ‘x’ \\ fs []
    \\ Cases_on ‘a’ \\ fs []
    \\ Cases_on ‘a’ \\ fs [])
  THEN1 (*op = Proj s i*)
   (fs [eval_op_def,el_def]
    \\ Cases_on ‘x = Diverge’ \\ fs []
    \\ imp_res_tac v_cmp_Diverge2 \\ fs []
    \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ simp []
    \\ ‘a' = a ∧ LLENGTH ts' = LLENGTH ts’ by
      (first_x_assum (qspec_then ‘[]’ mp_tac)
       \\ fs [v_cmp_def,v_lookup_def])
    \\ pop_assum mp_tac \\ simp []
    \\ pop_assum mp_tac \\ simp []
    \\ Cases_on ‘a’ \\ simp []
    \\ strip_tac \\ strip_tac
    \\ first_x_assum (qspec_then ‘i::path’ mp_tac)
    \\ simp [v_lookup_def,v_cmp_def]
    \\ pop_assum mp_tac \\ simp []
    \\ rpt (pop_assum kall_tac)
    \\ qspec_then ‘ts’ mp_tac fromList_fromSeq
    \\ qspec_then ‘ts'’ mp_tac fromList_fromSeq
    \\ rw [] \\ fs [LNTH_fromList]
    \\ rfs [] \\ rw [] \\ fs []   )
  THEN1 (*op = Add *)
   (fs []
    \\ Cases_on ‘a1 = Diverge’ THEN1 (fs [eval_op_def])
    \\ Cases_on ‘a2 = Diverge’ THEN1 (fs [eval_op_def])
    \\ ‘y  ≠ Diverge’ by (imp_res_tac v_cmp_Diverge2)
    \\ ‘y' ≠ Diverge’ by (imp_res_tac v_cmp_Diverge2)
    \\ qspec_then ‘a1’ (qspec_then ‘y’ assume_tac) v_cmp_getNum_eq
       \\ first_x_assum imp_res_tac 
    \\ qspec_then ‘a2’ (qspec_then ‘y'’ assume_tac) v_cmp_getNum_eq
       \\ first_x_assum imp_res_tac     
    \\ fs [eval_op_def])
QED

Theorem eval_to_res_mono_lemma:
  ∀k x n path. v_cmp path (eval_to k x) (eval_to (k+n) x)
Proof
  ho_match_mp_tac eval_to_ind \\ rpt conj_tac
  \\ rpt gen_tac
  \\ TRY (fs [eval_to_def] \\ rw [v_cmp_refl] \\ NO_TAC)
  THEN1
   (fs [eval_to_def] \\ strip_tac
    \\ rpt gen_tac
    \\ match_mp_tac eval_op_div
    \\ Induct_on ‘xs’ \\ fs [])
  \\ strip_tac
  \\ fs [eval_to_def]
  \\ Cases_on ‘eval_to k x = Diverge’ \\ fs []
  \\ fs [] \\ rpt strip_tac
  \\ ‘eval_to (k + n) x ≠ Diverge’ by
   (CCONTR_TAC
    \\ first_x_assum (qspecl_then [‘n’,‘[]’] mp_tac)
    \\ pop_assum mp_tac \\ simp []
    \\ fs [v_cmp_def] \\ fs [v_lookup_def]
    \\ Cases_on ‘eval_to k x’ \\ fs [])
  \\ fs []
  \\ ‘dest_Closure (eval_to (k + n) x) = dest_Closure (eval_to k x)’ by
   (Cases_on ‘eval_to k x’ \\ simp []
    \\ Cases_on ‘eval_to (k+n) x’ \\ simp []
    \\ first_x_assum (qspecl_then [‘n’,‘[]’] mp_tac)
    \\ simp [v_cmp_def] \\ simp [v_lookup_def]
    \\ simp [dest_Closure_def] \\ fs []
    \\ Cases_on ‘a’ \\ simp []
    \\ Cases_on ‘ts’ \\ Cases_on ‘ts'’ \\ simp []) \\ fs []
  \\ Cases_on ‘dest_Closure (eval_to k x)’ \\ fs [v_cmp_refl]
  \\ PairCases_on ‘x'’ \\ simp []
  \\ last_x_assum mp_tac \\ simp []
  \\ Cases_on ‘k = 0’ \\ simp []
QED

Theorem eval_to_res_mono:
  eval_to k x ≠ Diverge ∧
  eval_to k x = Branch a ts ∧
  eval_to k1 x = Branch a1 ts1 ∧
  k ≤ k1 ⇒
    a1 = a ∧ LLENGTH ts1 = LLENGTH ts
Proof
  fs [LESS_EQ_EXISTS] \\ strip_tac
  \\ BasicProvers.var_eq_tac
  \\ qspecl_then [‘k’,‘x’,‘p’,‘[]’] mp_tac eval_to_res_mono_lemma
  \\ simp [v_cmp_def,v_lookup_def] \\ fs []
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

Theorem eval_to_not_diverge_mono:
  ∀ k' k x . (k ≤ k' ∧ eval_to k x ≠ Diverge) ⇒ eval_to k' x ≠ Diverge
Proof
  rw []
  \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k' x’ 
  \\ qspecl_then
        [‘x’,‘ts'’,‘ts’,‘k'’,‘k’,‘a'’,‘a’]
        assume_tac (GEN_ALL eval_to_res_mono) \\ fs []
  \\ first_assum imp_res_tac \\ rw []
  \\ ‘eval_to k x ≠ Diverge’ by (fs [])
  \\ ‘a' = a ∧ LLENGTH ts' = LLENGTH ts’ by (fs [])
  \\ Cases_on ‘a’ \\ Cases_on ‘ts’ \\ Cases_on ‘ts'’ \\ fs []
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
  \\ rename [‘Closure x1 x2’]
  \\ qsuff_tac ‘eval x = Closure x1 x2’
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

Theorem eval_Lam:
  eval (Lam s x) = Closure s x
Proof
  fs [eval_def,eval_to_def,Once gen_ltree]
  \\ fs [v_limit_def,v_lookup_def]
QED

Theorem eval_Letrec:
  eval (Letrec f x) = eval (subst_funs f x)
Proof
  fs [eval_def,eval_to_def]
  \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM] \\ rw []
  \\ match_mp_tac v_limit_eq_add
  \\ fs [] \\ qexists_tac ‘1’ \\ fs []
QED

Theorem eval_App:
  eval (App x y) =
    let v = eval x in
      if v = Diverge then Diverge else
        case dest_Closure v of
        | NONE => Error
        | SOME (s,body) => eval (bind [(s,y)] body)
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
  eval (Let s x y) = eval (bind [(s,x)] y)
Proof
  fs [eval_App,eval_Lam,dest_Closure_def,bind_def]
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

Theorem eval_IsEq:
  eval (IsEq s x) = is_eq s (eval x)
Proof
  fs [eval_def,eval_to_def,eval_op_def,is_eq_def]
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
  \\ TRY
   (rw [] \\ drule gen_ltree_not_Error \\ fs []
    \\ strip_tac \\ qexists_tac ‘k’ \\ fs []
    \\ rpt strip_tac \\ res_tac \\ fs [] \\ NO_TAC)
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
  \\ Cases_on ‘eval_to k'' x’ \\ simp []
  \\ Cases_on ‘a’ \\ simp [] \\ fs []
  \\ last_x_assum mp_tac \\ simp []
  \\ once_rewrite_tac [gen_ltree]
  \\ fs [] \\ Cases_on ‘v_limit (λk. eval_to k x) []’ \\ fs []
  \\ CCONTR_TAC \\ fs [] \\ rw []
  \\ ‘eval_to k'' x ≠ Diverge’ by fs []
  \\ drule eval_to_res_mono \\ strip_tac \\ rfs []
  \\ first_x_assum drule \\ strip_tac
  \\ rfs [v_limit_def,v_lookup_def]
  \\ drule limit_eq_imp
  \\ disch_then (qspecl_then [‘Constructor' s',LLENGTH ts’,‘k''’] mp_tac)
  \\ impl_tac \\ fs []
  \\ fs [AllCaseEqs()]
  \\ ‘eval_to k'' x ≠ Diverge’ by fs []
  \\ drule eval_to_res_mono \\ strip_tac \\ rfs [] \\ rw []
  \\ Cases_on ‘eval_to n x’ \\ fs []
  \\ first_x_assum drule \\ fs []
QED

Theorem eval_Proj:
  eval (Proj s i x) = el s i (eval x)
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
    \\ reverse (Cases_on ‘s=s'’) \\ fs []
    \\ Cases_on ‘v_limit (λk. eval_to k x) []’ \\ fs [] \\ rw []
    \\ pop_assum (assume_tac o GSYM) \\ fs [LNTH_LGENLIST]
    \\ drule v_limit_not_Error
    \\ fs [] \\ strip_tac
    THEN1
     (fs [gen_ltree_LNIL]
      \\ match_mp_tac v_limit_eq_add
      \\ fs [v_limit_SOME]
      \\ qexists_tac ‘k’ \\ fs []
      \\ qexists_tac ‘0’ \\ fs []
      \\ fs [v_lookup_def] \\ gen_tac
      \\ fs [ltree_CASE_eq]
      \\ first_x_assum (qspec_then ‘k+n’ strip_assume_tac) \\ fs [])
    \\ Cases_on ‘r’ \\ fs []
    THEN1
     (AP_TERM_TAC \\ fs [FUN_EQ_THM]
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
      \\ qspec_then ‘ts’ mp_tac fromList_fromSeq \\ rw [] \\ fs [])
    \\ reverse IF_CASES_TAC \\ fs []
    THEN1
     (fs [gen_ltree_LNIL,v_limit_SOME]
      \\ qexists_tac ‘k’ \\ fs [] \\ rpt strip_tac
      \\ first_x_assum drule \\ fs [v_lookup_def]
      \\ rename [‘eval_to k3 x = Diverge’]
      \\ Cases_on ‘eval_to k3 x’ \\ fs []
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

Theorem getNum_NONE:
  (getNum x = NONE) = ∀n. x ≠ Num n
Proof
  Cases_on ‘x’
  \\ Cases_on ‘a’ \\ Cases_on ‘ts’ \\ fs [getNum_def]
QED

Theorem getNum_SOME:
  getNum x = SOME n ⇔ x = Num n
Proof
  Cases_on ‘x’
  \\ Cases_on ‘a’ \\ Cases_on ‘ts’ \\ fs [getNum_def]
QED

Theorem eval_to_no_div_not_equal:
  (k ≤ k')                    ∧
  (eval_to k x ≠ Diverge)     ∧
  (∀ n . eval_to k x ≠ Num n) ∧
  (eval_to k' x ≠ Diverge)
  ⇒ (∀ n . eval_to k' x ≠ Num n)
Proof
  rw []        
  \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k' x’
  \\ ‘eval_to k x ≠ Diverge’ by (fs [])
  \\ qspecl_then [‘k'’,‘ts'’,‘a'’] assume_tac (Q.GENL [‘k1’,‘ts1’,‘a1’] eval_to_res_mono)
  \\ first_x_assum imp_res_tac
  \\ first_x_assum (qspec_then ‘n:num’ assume_tac)
  \\ ‘a' = a
      ∧ LLENGTH ts' = LLENGTH ts
      ∧ Branch a ts ≠ Num n
      ⇒ Branch a' ts' ≠ Num n’ by
      (rw [] \\ fs [] \\ CCONTR_TAC \\ fs [])
  \\ first_x_assum imp_res_tac \\ fs []
QED

(*potentially, this can be generalized from Num n to Branch a LNIL*)
Theorem eval_to_forall_exists_swap:
  (∀n. ∃k. eval_to k x ≠ Num n ∧ eval_to k x ≠ Diverge)
       ⇒ (∃k. (∀n. eval_to k x ≠ Num n) ∧ eval_to k x ≠ Diverge)
Proof
  rw []
  \\ first_assum (qspec_then ‘n’ assume_tac) \\ fs []
  \\ qexists_tac ‘k’
  \\ CONJ_TAC 
  THEN1
    (  pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ CCONTR_TAC \\ fs []
    \\ last_x_assum (qspec_then ‘n’ assume_tac) \\ fs []
    \\ ‘eval_to k x ≠ Diverge’ by (fs [])
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘ts ≠ LNIL’ \\ fs []
    \\ Cases_on ‘k≤k'’
    THEN1 (qspec_then ‘k'’ imp_res_tac $ Q.GEN ‘k1’ eval_to_res_mono_LNIL \\ fs [])
    \\ first_x_assum (fn t => ‘k' ≤ k’ by fs [t])
    \\ qspecl_then [‘k’,‘k'’] imp_res_tac $ Q.GENL [‘k1’,‘k’] eval_to_simple_mono
    \\ fs [])
  \\ fs []
QED
        
Theorem eval_Add:
  eval (Prim Add [a1;a2]) =
    (if eval a1 = Diverge then Diverge else
     if eval a2 = Diverge then Diverge else
       case (getNum (eval a1),getNum (eval a2)) of
         | (SOME n1,SOME n2) => (Num (n1 + n2))
         | _                 => Error
    )
Proof
    fs [eval_def,eval_to_def,eval_op_def]
  \\ IF_CASES_TAC \\ fs [gen_ltree_LNIL]
  THEN1 (fs [v_limit_SOME] \\ qexists_tac ‘k’ \\ fs [])
  \\ IF_CASES_TAC \\ fs [gen_ltree_LNIL]
  THEN1
   (fs [v_limit_SOME]
   \\ qexists_tac ‘k’ \\ fs [])
  \\ BasicProvers.TOP_CASE_TAC
  THEN1
   (fs [gen_ltree_LNIL,v_limit_SOME,getNum_NONE]
    \\ last_x_assum (qspec_then ‘0’ strip_assume_tac) 
    \\ last_x_assum (qspec_then ‘0’ strip_assume_tac)
    \\ qexists_tac ‘MAX k' k''’
    \\ rpt (strip_tac)
    \\ rename [‘MAX k1 k2 ≤ k3’]
    \\ IF_CASES_TAC
    THEN1 (drule eval_to_div \\ fs[] \\ qexists_tac ‘k1’ \\ fs[])
    \\ IF_CASES_TAC
    THEN1 (drule eval_to_div \\ fs[] \\ qexists_tac ‘k2’ \\ fs[])
    \\ pop_assum kall_tac
    \\ drule eval_to_res_mono
    \\ Cases_on ‘eval_to k3 a1’ \\ qpat_x_assum ‘_≠_’ kall_tac
    \\ fs []
    \\ Cases_on ‘a’ \\ fs [getNum_def]
    \\ last_x_assum (qspecl_then [‘n’,‘k3’] strip_assume_tac)
    \\ Cases_on ‘eval_to k' a1’
    \\ disch_then drule \\ fs [] \\  rw []
    \\ Cases_on ‘ts’ \\ Cases_on ‘ts'’ \\ fs [getNum_def])
  \\ BasicProvers.TOP_CASE_TAC
  THEN1
   (fs [getNum_NONE,getNum_SOME,gen_ltree_LNIL,v_limit_SOME]
    \\ ‘∀n. ∃k. eval_to k a2 ≠ Num n ∧ eval_to k a2 ≠ Diverge’ by
      (fs [] \\ strip_tac
       \\ first_x_assum (qspec_then ‘n’ assume_tac)
       \\ last_x_assum kall_tac
       \\ last_x_assum (qspec_then ‘0’ assume_tac) \\ fs []
       \\ last_x_assum kall_tac
       \\ first_x_assum (qspec_then ‘k'’ assume_tac) \\ fs []
       \\ qspecl_then [‘k''’,‘k'’,‘a2’] imp_res_tac eval_to_not_diverge_mono 
       \\ qexists_tac ‘k''’ \\ fs []
      )
    \\ qspec_then ‘a2’ imp_res_tac (Q.GEN ‘x’ eval_to_forall_exists_swap)
    \\ last_x_assum (qspec_then ‘0’ strip_assume_tac)
    \\ last_x_assum (qspec_then ‘0’ strip_assume_tac)
    \\ last_x_assum kall_tac 
    \\ last_x_assum kall_tac
    \\ last_x_assum kall_tac
    \\ qexists_tac ‘MAX (MAX k' k'') k'''’
    \\ rpt (strip_tac)
    \\ rename [‘MAX (MAX k1 k2) k3 ≤ k4’] \\ fs []
    \\ qspecl_then [‘k4’,‘k2’,‘a1’] assume_tac eval_to_not_diverge_mono
    \\ first_x_assum imp_res_tac
    \\ qspecl_then [‘k4’,‘k3’,‘a2’] assume_tac eval_to_not_diverge_mono
    \\ first_x_assum imp_res_tac
    \\ fs [] \\ rw []
    \\ Cases_on ‘getNum (eval_to k4 a1)’ \\ fs [getNum_SOME]
    \\ ‘∀n. eval_to k4 a2 ≠ Num n’ by (
      qspecl_then [‘a2’,‘k4’,‘k1’] imp_res_tac (GEN_ALL eval_to_no_div_not_equal))
    \\ Cases_on ‘getNum (eval_to k4 a2)’ \\ fs [getNum_SOME])
  \\ fs [getNum_NONE,getNum_SOME,gen_ltree_LNIL,v_limit_SOME]
  \\ last_x_assum (qspec_then ‘k’ strip_assume_tac)
  \\ last_x_assum (qspec_then ‘k'’ strip_assume_tac)
  \\ last_x_assum (qspec_then ‘k'' ’ strip_assume_tac)
  \\ last_x_assum (qspec_then ‘k'''’ strip_assume_tac)
  \\ qpat_x_assum ‘_⇒_’ imp_res_tac
  \\ qpat_x_assum ‘_⇒_’ imp_res_tac
  \\ qexists_tac ‘MAX k'' k'''’
  \\ rpt (strip_tac)
  \\ rename [‘MAX k2 k3 ≤ k4’] \\ fs []
  (*  eval_to k2 a1 = Num x ⇒ eval_to k4 a1 = Num x   *)
  \\ Cases_on ‘eval_to k2 a1’ \\ Cases_on ‘ts’ \\ fs []
  \\ ‘eval_to k2 a1 ≠ Diverge’ by (fs[])
  \\ qspecl_then [‘a1’,‘k4’,‘k2’,‘a’] assume_tac (GEN_ALL eval_to_res_mono_LNIL)
  \\ first_x_assum imp_res_tac
  (*  eval_to k3 a2 = Num x' ⇒ eval_to k4 a2 = Num x'   *)
  \\ Cases_on ‘eval_to k3 a2’ \\ Cases_on ‘ts’ \\ fs []
  \\ ‘eval_to k3 a2 ≠ Diverge’ by (fs[])
  \\ qspecl_then [‘a2’,‘k4’,‘k3’,‘a'’] assume_tac (GEN_ALL eval_to_res_mono_LNIL)
  \\ first_x_assum imp_res_tac
  \\ fs [getNum_def,getNum_SOME]                      
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
  \\ Cases_on ‘∃s. op = IsEq s’
  THEN1
   (Cases_on ‘xs’ \\ fs [eval_op_def]
    \\ TRY (Cases_on ‘t’) \\ fs [eval_op_def,eval_IsEq]
    \\ fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
    \\ fs [v_limit_def,v_lookup_def])
  \\ Cases_on ‘∃s i. op = Proj s i’
  THEN1
   (Cases_on ‘xs’ \\ fs [eval_op_def]
    THEN1
      (fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
       \\ fs [v_limit_def,v_lookup_def])
    \\ Cases_on ‘t’ \\ fs [eval_Proj,eval_op_def]
    \\ fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
    \\ fs [v_limit_def,v_lookup_def])
  \\ Cases_on ‘op’ \\ fs []
  THEN1(
  Cases_on ‘∃ x y . xs = [x;y]’
   THEN1(
       rw []
       \\ simp [eval_Add]
       \\ Cases_on ‘eval a1 = Diverge’ \\ fs [eval_op_def]
    )THEN1(
       fs []
       \\ Cases_on ‘xs’ \\ fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
       \\ fs [v_limit_def,v_lookup_def]
       \\ Cases_on ‘t’  \\ fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
       \\ fs [v_limit_def,v_lookup_def]
       \\ Cases_on ‘t'’ \\ fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
       \\ fs [v_limit_def,v_lookup_def]
    )
  )
QED

Theorem eval_core:
  eval (Var s) = Error (* free variables are not allowed *) ∧
  eval (Prim op xs) = eval_op op (MAP eval xs) ∧
  eval (Lam s x) = Closure s x ∧
  eval (Letrec f x) = eval (subst_funs f x) ∧
  eval (App x y) =
    (let v = eval x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (s,body) => eval (bind [(s,y)] body))
Proof
  fs [eval_Var,eval_Prim,eval_Lam,eval_Letrec,eval_App]
QED

Theorem eval_thm:
  eval (Lit n) = Num n ∧
  eval (Var s) = Error (* free variables are not allowed *) ∧
  eval (Cons s xs) = Constructor s (MAP eval xs) ∧
  eval (IsEq s x) = is_eq s (eval x) ∧
  eval (Proj s i x) = el s i (eval x) ∧
  eval (Let s x y) = eval (bind [(s,x)] y) ∧
  eval (If x y z) =
    (if eval x = Diverge then Diverge else
     if eval x = Num 0 then eval z else
     if eval x = Num 1 then eval y else Error) ∧
  eval (Lam s x) = Closure s x ∧
  eval (Letrec f x) = eval (subst_funs f x) ∧
  eval (App x y) =
    (let v = eval x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (s,body) => eval (bind [(s,y)] body))
Proof
  fs [eval_Var,eval_Cons,eval_App,eval_Lam,eval_Lit,eval_If,eval_Proj,
      eval_IsEq,bind_def,eval_Letrec]
QED


(* prove that bottom diverges *)

Definition bottom_def:
  bottom =
    Letrec [("bot","n",App (Var "bot") (Lit 0))]
      (App (Var "bot") (Lit 0))
End

Theorem eval_bottom:
  eval bottom = Diverge
Proof
  qsuff_tac ‘∀k. eval_to k bottom = Diverge’
  THEN1 fs [eval_def,v_limit_def,v_lookup_def,gen_ltree_LNIL]
  \\ fs [bottom_def,eval_to_def]
  \\ Cases \\ fs [subst_def,subst_funs_def,bind_def,closed_def]
  \\ completeInduct_on ‘n’ \\ fs []
  \\ ntac 3 (simp [Once eval_to_def,subst_def,dest_Closure_def,
                   subst_funs_def,bind_def,closed_def])
  \\ Cases_on ‘n’ \\ fs []
  \\ ntac 5 (simp [Once eval_to_def,subst_def,dest_Closure_def,
                   subst_funs_def,bind_def,closed_def])
QED


(* example producing infinite list of zeros *)

Definition zeros_def:
  zeros =
    Letrec [("z","n",Cons "cons" [Var "n"; App (Var "z") (Var "n")])]
      (App (Var "z") (Lit 0))
End

Theorem eval_zeros:
  eval zeros = Constructor "cons" [Num 0; eval zeros]
Proof
  fs [Once zeros_def]
  \\ ntac 6 (simp [Once eval_thm,dest_Closure_def,subst_def,bind_def,
                   subst_funs_def,closed_def])
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ rewrite_tac [zeros_def]
  \\ ntac 2 (simp [Once eval_thm,dest_Closure_def,subst_def,bind_def,
                   subst_funs_def,closed_def])
QED


(* value and exp relation -- clocked *)

Definition v_rel'_def:
  (v_rel' 0 v1 v2 ⇔ T) ∧
  (v_rel' (SUC n) v1 v2 ⇔
     (v1 = v2) ∨
     (∃m xs ys.
        v1 = Constructor m xs ∧
        v2 = Constructor m ys ∧
        LIST_REL (v_rel' n) xs ys) ∨
     (∃s1 x1 s2 x2.
        v1 = Closure s1 x1 ∧
        v2 = Closure s2 x2 ∧
        ∀z. v_rel' n (eval (bind [(s1,z)] x1))
                     (eval (bind [(s2,z)] x2))))
End

Definition v_rel_def:
  v_rel x y = ∀n. v_rel' n x y
End

Definition exp_rel_def:
  exp_rel x y ⇔ v_rel (eval x) (eval y)
End

Theorem v_rel_Closure:
  (∀x y. exp_rel x y ⇒ exp_rel (bind [m,x] b) (bind [n,y] d)) ⇒
  v_rel (Closure m b) (Closure n d)
Proof
  rw [PULL_FORALL,exp_rel_def,v_rel_def] \\ fs []
  \\ rewrite_tac [eval_thm]
  \\ Cases_on ‘n'’
  \\ once_rewrite_tac [v_rel'_def] \\ fs [] \\ disj2_tac
  \\ rw [] \\ fs []
  \\ first_x_assum match_mp_tac
  \\ Cases \\ fs [v_rel'_def]
QED

Triviality LIST_REL_SYM:
  (∀x y. R x y ⇔ R y x) ⇒
  ∀xs ys. LIST_REL R xs ys ⇔ LIST_REL R ys xs
Proof
  strip_tac \\ Induct
  \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs [] \\ metis_tac []
QED

Triviality LIST_REL_TRANS:
  (∀x y z. R x y ∧ R y z ⇒ R x z) ⇒
  ∀xs ys zs. LIST_REL R xs ys ∧ LIST_REL R ys zs ⇒ LIST_REL R xs zs
Proof
  strip_tac \\ Induct
  \\ fs [] \\ rw [] \\ fs [] \\ rw [] \\ fs [] \\ metis_tac []
QED

Theorem v_rel_refl:
  ∀x. v_rel x x
Proof
  fs [v_rel_def,v_rel'_def] \\ rw []
  \\ Cases_on ‘n’ \\ fs [v_rel'_def]
QED

Theorem v_rel_sym:
  ∀x y. v_rel x y ⇔ v_rel y x
Proof
  qsuff_tac ‘∀n x y. v_rel' n x y ⇔ v_rel' n y x’
  THEN1 metis_tac [v_rel'_def,v_rel_def]
  \\ Induct_on ‘n’ \\ fs [v_rel'_def]
  \\ drule LIST_REL_SYM
  \\ metis_tac []
QED

Theorem v_rel_trans:
  ∀x y z. v_rel x y ∧ v_rel y z ⇒ v_rel x z
Proof
  qsuff_tac ‘∀n x y z. v_rel' n x y ∧ v_rel' n y z ⇒ v_rel' n x z’
  THEN1 metis_tac [v_rel_def]
  \\ Induct_on ‘n’ \\ fs [v_rel'_def]
  \\ drule LIST_REL_TRANS
  \\ strip_tac \\ rw []
  THEN1 (res_tac \\ fs [])
  \\ disj2_tac \\ rw []
  \\ metis_tac [v_rel'_def]
QED

(*
TODO:
 - add strictness primitive
*)

val _ = export_theory();
