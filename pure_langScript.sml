
open HolKernel Parse boolLib bossLib term_tactic;
open expTheory valueTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory;

val _ = new_theory "pure_lang";

Overload True  = “Constructor "True" []”;
Overload False = “Constructor "False" []”;

Definition dest_Closure_def:
  dest_Closure x =
    case x of Closure s x => SOME (s,x) | _ => NONE
End

Theorem dest_Closure_Closure[simp]:
  dest_Closure (Closure s x) = SOME (s,x)
Proof
  fs [dest_Closure_def]
QED

Theorem dest_Closure_Closure_IMP:
  dest_Closure v = SOME (s,x) ⇒ v = Closure s x
Proof
  rw [] \\ Cases_on ‘v’ \\ gs[dest_Closure_def]
QED

Triviality exp_size_lemma:
  (∀xs     a. MEM      a  xs ⇒ exp_size (K 0) (K 0) a < exp7_size (K 0) (K 0) xs) ∧
  (∀xs x y a. MEM (x,y,a) xs ⇒ exp_size (K 0) (K 0) a < exp3_size (K 0) (K 0) xs) ∧
  (∀xs x y a. MEM (x,y,a) xs ⇒ exp_size (K 0) (K 0) a < exp1_size (K 0) (K 0) xs)
Proof
  conj_tac \\ TRY conj_tac \\ Induct \\ rw [] \\ res_tac \\ fs [exp_size_def]
QED

Definition subst_def:
  subst name v (Var s) = (if name = s then v else Var s) ∧
  subst name v (Prim op xs) = Prim op (MAP (subst name v) xs) ∧
  subst name v (App x y) = App (subst name v x) (subst name v y) ∧
  subst name v (Lam s x) = Lam s (if s = name then x else subst name v x) ∧
  subst name v (Letrec f x) =
    (if MEM name (MAP FST f) then Letrec f x else
      Letrec (MAP (λ(g,m,z). (g,m, if name = m then z else subst name v z )) f)
             (subst name v x)) ∧
  subst name v (Case e vn css) =
    (Case (subst name v e)
          vn
          (MAP (λ(cn,ans, cb).
                 (cn,ans, if ¬MEM name (vn::ans) then subst name v cb else cb))
               css))
Termination
  WF_REL_TAC `measure (λ(n,v,x). exp_size (K 0) (K 0) x)` \\ rw []
  \\ imp_res_tac exp_size_lemma \\ fs []
End

Definition freevars_def[simp]:
  freevars (Var n)     = [n]                               ∧
  freevars (Prim _ es) = (FLAT (MAP freevars es))          ∧
  freevars (App e1 e2) = (freevars e1 ⧺ freevars e2)       ∧
  freevars (Lam n e)   = (FILTER ($≠ n) (freevars e))      ∧
  freevars (Letrec lcs e) =
    FILTER (\n. ¬ MEM n (MAP FST lcs))
           (freevars e ⧺
            FLAT (MAP (λ(fn,vn,e). FILTER (λ n.n ≠ vn) (freevars e)) lcs))  ∧
  freevars (Case exp nm css) =
    (freevars exp ⧺ FLAT (MAP (λ(_,vs,cs).FILTER (λ n. ¬MEM n (nm::vs)) (freevars cs))
                              css))
Termination
  WF_REL_TAC ‘measure (exp_size (K 0) (K 0))’ \\ fs[]
  \\ conj_tac \\ TRY conj_tac
  \\ TRY (Induct_on ‘lcs’)
  \\ TRY (Induct_on ‘css’)
  \\ TRY (Induct_on ‘es’)
  \\ rw [] \\ fs [exp_size_def] \\ res_tac \\ fs[]
  \\ pop_assum (assume_tac o SPEC_ALL) \\ fs[]
End

Definition closed_def:
  closed e = (freevars e = [])
End

(*projection: given the constructor name s, and the index i,
  access the object x and retrieve the i-th element
  if present, otherwise returns Error. *)
Definition el_def:
  el s i x =
    if x = Diverge then Diverge else
      case x of
      | Constructor t xs =>
          if s = t ∧ i < LENGTH xs then EL i xs
          else Error
      | _ => Error
End

Definition is_eq_def:
  is_eq c s n x =
    if x = Diverge then Diverge else
      case x of
        Constructor t xs =>
          if n = LENGTH xs then
            (if s = t then True else False)
          else Error
      | _ => Error
End

Definition getAtom_def:
  getAtom (Atom b) = SOME b ∧
  getAtom _        = NONE
End

Definition getAtoms_def:
  getAtoms [] = SOME [] ∧
  getAtoms (x::xs) = case (getAtom x,getAtoms xs) of
                     | (SOME n,SOME ns) => SOME (n::ns)
                     | _ => NONE
End

Definition eval_op_def:
  (eval_op c (Cons s) xs = Constructor s xs) ∧
  (eval_op c If [x1;x2;x3] =
    if x1 = Diverge then Diverge else
    if x1 = True  then x2 else
    if x1 = False then x3 else Error ) ∧
  (eval_op c (IsEq s n) [x] = is_eq c s n x) ∧
  (eval_op c (Proj s i) [x] = el s i x) ∧
  (eval_op c (AtomOp a) xs =
     if MEM Diverge xs then Diverge else
       case OPTION_BIND (getAtoms xs) (c.parAtomOp a) of
        | (SOME b) => Atom b
        | _        => Error )  ∧
  (eval_op c (Lit b) [] = Atom b) ∧
  (eval_op _ _ _ = Error)
End

Definition bind_def:
  bind [] x = x ∧
  bind ((s,v)::ys) x =
    if closed v then subst s v (bind ys x) else Fail
End

Definition subst_funs_def:
  subst_funs f = bind (MAP (λ(g,n,x). (g,Lam n (Letrec f x))) f)
End

Definition expandLets_def:
   expandLets i cn nm ([]) cs = cs ∧
   expandLets i cn nm (v::vs) cs = Let v (Proj cn i (Var nm))
                                         (expandLets (i+1) cn nm vs cs)
End

Definition expandRows_def:
   expandRows nm [] = Fail ∧
   expandRows nm ((cn,vs,cs)::css) = If (IsEq cn (LENGTH vs) (Var nm))
                                        (expandLets 0 cn nm vs cs)
                                        (expandRows nm css)
End

Definition expandCases_def:
   expandCases x nm css = (Let nm x (expandRows nm css))
End

(*EVAL “expandCases ARB "a" [("Nil",[],c1);("Cons",["x";"xs"],c2)] ”*)

Definition eval_to_def:
  eval_to c k (Var s) = Error ∧
  eval_to c k (Prim op xs) = eval_op c op (MAP (eval_to c k) xs) ∧
  eval_to c k (Lam s x) = Closure s x ∧
  eval_to c k (App x y) =
  (let v = eval_to c k x in
     if v = Diverge then Diverge else
       case dest_Closure v of
       | NONE => Error
       | SOME (s,body) =>
           if k = 0 then Diverge else
             eval_to c (k-1) (bind [(s,y)] body)) ∧
  eval_to c k (Letrec f y) =
    (if k = 0 then Diverge else
      eval_to c (k-1) (subst_funs f y)) ∧
  eval_to c k (Case x nm css) =
    (if k = 0 then Diverge else
       eval_to c (k-1) (expandCases x nm css))
Termination
  WF_REL_TAC `inv_image ($< LEX $< LEX $<) (λ(_,k,x).(0,k,(exp_size (K 0) (K 0) x)))`
  \\ rw []
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

 (*
   v_seq: num -> v
   given a certain path, v_limit tries to look into a value with k any num.
  *)
Definition v_limit_def:
  v_limit v_seq path =
    limit (λk. v_lookup path (v_seq k)) (Error', 0)
End

(*
   given an expression x, eval returns the denotational
   value associated to it. Since eval might produce
   infinite values as result, the resulting value needs
   to be "wrapped" into a lazy datatype. This is the role
   of gen_v. gen_v takes a function that, given
   any path over the resulting value, the function returns
   the values in that specific branch.
   This gives eval the type : conf -> exp -> v.
*)

Definition eval_def:
  eval c x =
    gen_v (λpath. v_limit (λk. eval_to c k x) path)
End

(* misc lemmas about bind, subst, closed *)

Theorem bind_bind:
  ∀xs ys s. bind xs (bind ys s) = bind (xs ++ ys) s
Proof
  Induct \\ fs [bind_def,FORALL_PROD] \\ rw []
QED

Theorem subst_ignore:
  ∀s x y. ~MEM s (freevars y) ⇒ subst s x y = y
Proof
  ho_match_mp_tac subst_ind \\ rw [] \\ fs [subst_def]
  THEN1 (Induct_on ‘xs’ \\ fs [])
  THEN1 (rw [] \\ fs [MEM_FILTER])
  THEN1
   (rw [] \\ fs [MEM_FILTER]
    \\ Induct_on ‘f’ \\ fs [FORALL_PROD]
    \\ rw [] \\ fs [AND_IMP_INTRO]
    THEN1 (first_x_assum match_mp_tac \\ metis_tac [])
    \\ fs [MEM_FILTER,EXISTS_PROD,MEM_MAP]
    \\ metis_tac [])
  \\ Induct_on ‘css’ \\ fs [FORALL_PROD,MEM_MAP] \\ rw []
  \\ fs [MEM_FILTER,EXISTS_PROD,MEM_MAP]
  \\ metis_tac []
QED

Theorem closed_subst[simp]:
  ∀s x y. closed y ⇒ subst s x y = y
Proof
  rw [] \\ match_mp_tac subst_ignore \\ fs [closed_def]
QED

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

Theorem limit_eq_add_rewrite:
  ∀k p f.
    limit (λn. f (n + k)) p = limit f p
Proof
  rw[] >>
  irule (GSYM limit_eq_add) >>
  qexists_tac `k` >> fs[]
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
  \\ qspecl_then [‘v_lookup x a’,‘λk. v_lookup x (b k)’,‘(Error',0)’] mp_tac
       (GSYM limit_if)
  \\ fs [] \\ rw [] \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM] \\ rw []
QED

Theorem v_limit_exists:
  ∀ f r m path.
    (∃k. ∀n. k ≤ n ⇒ v_lookup path (f n) = (r,m))
  ⇒ v_limit f path = (r,m)
Proof
  rw [] >> fs[v_limit_def,limit_def] >> rename1 `k1 ≤ _` >>
  DEEP_INTRO_TAC some_intro >> rw [v_lookup]
  >- (
    rename1 `k2 ≤ _` >>
    rpt (first_x_assum (qspec_then `k1 + k2` assume_tac)) >> fs[] >>
    Cases_on `f (k1 + k2)` >> fs[v_lookup]
    )
  >> (
    first_x_assum (qspecl_then [`(r,m)`,`k1`] assume_tac) >> fs[] >>
    rename1 `_ ≤ k2` >>
    first_x_assum drule >>
    Cases_on `f k2` >> fs[v_lookup]
    )
QED

Theorem v_limit_not_Error:
  v_limit f path = (r,l) ∧ r ≠ Error' ⇒
  ∃k. ∀n. k ≤ n ⇒ v_lookup path (f n) = (r,l)
Proof
  fs [v_limit_def,limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw [v_lookup_def]
  \\ metis_tac []
QED

Theorem v_limit_eqn:
  ∀ f path res.
    v_limit f path = res ⇔
    (∃k. ∀n. k ≤ n ⇒ v_lookup path (f n) = res) ∨
    (res = (Error',0) ∧ ∀ r k. ∃n. k ≤ n ∧ v_lookup path (f n) ≠ r)
Proof
  rw[v_limit_def, limit_def] >>
  DEEP_INTRO_TAC some_intro >> rw[] >> eq_tac >> rw[]
  >- (DISJ1_TAC >> goal_assum drule)
  >- (
    rename1 `k1 ≤ _` >>
    rpt (first_x_assum (qspec_then `k + k1` assume_tac)) >>
    gvs[]
    )
  >- (
    first_x_assum (qspecl_then [`x`,`k`] assume_tac) >> fs[] >>
    first_x_assum drule >> gvs[]
    )
  >- (
    first_x_assum (qspecl_then [`res`,`k`] assume_tac) >> fs[] >>
    first_x_assum drule >> gvs[]
    )
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

Theorem limit_intro:
  ∀ f d x. (∃k. ∀n. k ≤ n ⇒ f n = x) ⇒ limit f d = x
Proof
  rw[limit_def] >>
  DEEP_INTRO_TAC some_intro >> rw[]
  >- (
    first_x_assum (qspec_then `k + k'` assume_tac) >>
    first_x_assum (qspec_then `k + k'` assume_tac) >>
    fs[]
    )
  >- (
    first_x_assum (qspecl_then [`x`,`k`] assume_tac) >> fs[] >>
    first_x_assum drule >>
    fs[]
    )
QED

Theorem limit_intro_alt:
  ∀ f d x lim . limit f d = lim ∧ (∃k. ∀n. k ≤ n ⇒ f n = x) ⇒ lim = x
Proof
  rw[] >> irule limit_intro >>
  goal_assum drule
QED

Theorem limit_eq_IMP:
  ∀ f g d.
    (∃k. ∀n. k ≤ n ⇒ f n = g n)
  ⇒ limit f d = limit g d
Proof
  rw[limit_def] >>
  DEEP_INTRO_TAC some_intro >> rw[]
  >- (
    rename1 `k1 ≤ _` >>
    DEEP_INTRO_TAC some_intro >> rw[]
    >- (
      rename1 `k2 ≤ _` >>
      rpt (first_x_assum (qspec_then `k + k1 + k2` assume_tac)) >> gvs[]
      )
    >- (
      first_x_assum (qspecl_then [`x`,`k + k1`] assume_tac) >> fs[] >>
      rename1 `_ ≤ k3` >>
      rpt (first_x_assum (qspec_then `k3` assume_tac)) >> gvs[]
      )
    )
  >- (
    DEEP_INTRO_TAC some_intro >> rw[] >> rename1 `k1 ≤ _` >>
    first_x_assum (qspecl_then [`x`,`k + k1`] assume_tac) >> fs[] >>
    rename1 `_ ≤ k2` >>
    rpt (first_x_assum (qspec_then `k2` assume_tac)) >> gvs[]
    )
QED

Theorem limit_eq_add_IMP:
  ∀ f g c d.
    (∃k. ∀n. k ≤ n ⇒ f (n + c) = g n)
  ⇒ limit f d = limit g d
Proof
  rw[] >>
  qspecl_then [`c`,`d`,`f`] assume_tac (GSYM limit_eq_add_rewrite) >> fs[] >>
  irule limit_eq_IMP >> fs[] >>
  goal_assum drule
QED

Theorem v_limit_eq_IMP:
  ∀ f g path.
    (∃k. ∀n. k ≤ n ⇒ v_lookup path (f n) = v_lookup path (g n))
  ⇒ v_limit f path = v_limit g path
Proof
  rw[v_limit_def] >>
  irule limit_eq_IMP >>
  qexists_tac `k` >>
  fs[]
QED

(***********************************)

(*********** getAtom lemmas ***********)

Theorem getAtom_NONE:
  (getAtom x = NONE) = ∀n. x ≠ Atom n
Proof
  Cases_on ‘x’ >> fs[getAtom_def]
QED

Theorem getAtom_SOME:
  getAtom x = SOME n ⇔ x = Atom n
Proof
  Cases_on ‘x’ >> fs[getAtom_def]
QED

Theorem getAtoms_SOME:
  getAtoms xs = SOME ns ⇒ (∀x. MEM x xs ⇒ ∃n. x = Atom n)
Proof
  qspec_tac (‘ns’,‘ns’)
  \\ Induct_on ‘xs’ THEN1 (fs [])
  \\ strip_tac \\ strip_tac
  \\ disch_tac \\ rename [‘getAtoms (x::xs) = _’]
  \\ strip_tac
  \\ Cases_on ‘¬ (MEM x' (x::xs))’ THEN1 (fs [])
  \\ gvs[getAtoms_def]
  \\ Cases_on ‘getAtom x’ \\ fs []
  \\ Cases_on ‘getAtoms xs’ \\ fs [] \\ rename [‘x::xs = xx’]
  THEN1 (fs[getAtom_SOME])
  \\ last_assum (qspec_then ‘x''’ strip_assume_tac) \\ fs[]
QED

Theorem getAtoms_NOT_SOME_NONE:
  getAtoms xs = NONE ⇔ ∀ l. getAtoms xs ≠ SOME l
Proof
  eq_tac \\ fs[getAtoms_def]
  \\ disch_tac \\ CCONTR_TAC
  \\ Cases_on ‘getAtoms xs’ \\ fs[]
QED

Theorem getAtoms_NOT_NONE_SOME:
  getAtoms xs ≠ NONE ⇔ ∃ l. getAtoms xs = SOME l
Proof
  eq_tac \\ fs[getAtoms_def,getAtoms_NOT_SOME_NONE]
  \\ disch_tac \\ fs []
QED

(***********************************)

(* x and y : v_prefix ltree, v_cmp checks whether x and y are equal
   for the given path. If x or y diverge, then they ARE equal.
   v_cmp is a relation used to prove some lemmas over eval_to,
   ultimately, used to prove eval_thm
*)
Definition v_cmp_def:
  v_cmp path x y ⇔
    (v_lookup path x ≠ (Diverge',0) ⇒
     v_lookup path y = v_lookup path x)
End

Triviality v_cmp_refl[simp]:
  v_cmp path x x
Proof
  fs [v_cmp_def]
QED

Triviality LIST_REL_v_cmp_refl[simp]:
  ∀ xs. LIST_REL (λ x y.∀ path.v_cmp path x y) xs xs
Proof
  Induct \\ fs[]
QED

Triviality v_cmp_Diverge[simp]:
  ∀path x. v_cmp path Diverge x
Proof
  Induct \\ fs [v_cmp_def,v_lookup]
QED

Theorem v_cmp_Diverge2[simp]:
  (∀path. v_cmp path x y) ∧ x ≠ Diverge ⇒ y ≠ Diverge
Proof
  rw [] \\ CCONTR_TAC \\ fs []
  \\ first_x_assum (qspec_then ‘[]’ mp_tac)
  \\ fs [v_cmp_def,v_lookup]
  \\ Cases_on ‘x’ \\ fs []
QED

Theorem v_cmp_not_branching_IMP:
  ∀v y .
    v ≠ Diverge ∧ (∀ c vs. v = Constructor c vs ⇒ vs = []) ⇒
    ((∀path. v_cmp path v y) ⇔ y = v)
Proof
  rw [] \\ eq_tac \\ rw []
  \\ first_x_assum (qspec_then ‘[]’ mp_tac)
  \\ fs [v_cmp_def,v_lookup]
  \\ Cases_on `v` \\ Cases_on ‘y’ \\ fs []
QED

(*TODO: this might be used in order to simplify v_cmp_not_branching_IMP and
  the associated LIST_REL version*)
Definition isFinite_def:
  isFinite x = case x of
                | Diverge => F
                | Constructor _ [] => T
                | Constructor _ _ => F
                | _ => T
End

Theorem v_cmp_isFinite_IMP:
  ∀x y.
    (isFinite x ∧ (∀path. v_cmp path x y)) ⇒ y = x
Proof
  rw[] \\ Cases_on ‘x’ \\ fs[isFinite_def, v_cmp_not_branching_IMP]
  \\ qspec_then `Constructor s t` assume_tac v_cmp_not_branching_IMP \\ fs[]
  \\ Cases_on `t` \\ fs[]
QED

Theorem LIST_REL_v_cmp_isFinite:
  ∀xs ys.
    (∀x. MEM x xs ⇒ isFinite x) ⇒
    (LIST_REL (λx y.∀path. v_cmp path x y) xs ys ⇔ ys = xs)
Proof
  rw[] \\ eq_tac \\ fs [LIST_REL_EL_EQN, LIST_EQ_REWRITE] \\ rw[]
  \\ gvs[] \\ first_x_assum drule \\ strip_tac
  \\ irule v_cmp_isFinite_IMP
  \\ fs[MEM_EL]
  \\ first_x_assum irule
  \\ goal_assum drule \\ fs[]
QED

Theorem LIST_REL_not_diverge:
  ∀ xs ys.
  ¬MEM Diverge xs ∧
  LIST_REL (λx y. ∀path. v_cmp path x y) xs ys
  ⇒ ¬MEM Diverge ys
Proof
  Induct_on ‘xs’ \\ fs []
  \\ strip_tac
  \\ strip_tac
  \\ disch_tac
  \\ fs []
  \\ imp_res_tac v_cmp_Diverge2
QED

Theorem v_cmp_getAtom_eq:
  ∀x y.
    x ≠ Diverge ∧ y ≠ Diverge ⇒
    ((∀path. v_cmp path x y) ⇒ (getAtom x) = (getAtom y))
Proof
  rw []
  \\ first_x_assum (qspec_then ‘[]’ assume_tac)
  \\ Cases_on ‘x’
  \\ fs [v_cmp_def,v_lookup,ltree_CASE]
  \\ first_assum imp_res_tac
  \\ Cases_on ‘y’
  \\ fs [ltree_CASE]
  \\ rw [getAtom_def]
QED

Theorem LIST_REL_v_cmp_getAtom_eq:
  ∀xs ys.
    ¬MEM Diverge xs ∧ ¬MEM Diverge ys ∧
    (LIST_REL (λx y. ∀path. v_cmp path x y) xs ys)
    ⇒ getAtoms xs = getAtoms ys
Proof
  Induct \\ fs []
  \\ rpt strip_tac
  \\ Induct_on ‘ys’ \\ fs[]
  \\ rpt strip_tac
  \\ fs[getAtoms_def]
  \\ imp_res_tac v_cmp_getAtom_eq \\ fs []
  \\ last_x_assum (qspec_then ‘ys’ imp_res_tac)
  \\ fs []
QED

Theorem eval_op_div:
  ∀c op xs ys path.
    LIST_REL (λx y. ∀path. v_cmp path x y) xs ys ⇒
    v_cmp path (eval_op c op xs) (eval_op c op ys)
Proof
  ho_match_mp_tac eval_op_ind \\ rw []
  \\ TRY (fs [eval_op_def] \\ rw [] \\ fs [v_cmp_refl] \\ NO_TAC)
  >- ( (* op = Cons s *)
    fs[eval_op_def, v_cmp_def] >>
    Cases_on `path` >> fs[v_lookup] >>
    imp_res_tac LIST_REL_LENGTH >> fs[LIST_REL_EL_EQN, oEL_THM] >> rw[]
    )
  >- ( (* op = If *)
    fs[eval_op_def] >>
    rename1 `v_cmp path _ (
      if b = _ then _ else if _ then y1 else if _ then y2 else _)` >>
    Cases_on `x1 = Diverge` >> fs[] >>
    Cases_on `b = Diverge` >> fs[]
    >- (imp_res_tac v_cmp_Diverge2 >> fs[]) >>
    reverse (rw[]) >> fs[] >>
    last_x_assum (qspec_then `[]` mp_tac) >>
    simp[v_cmp_def, v_lookup]
    >- (Cases_on `x1` >> fs[])
    >- (Cases_on `x1` >> fs[])
    >> (Cases_on `b` >> fs[])
    )
  >- ( (* op = IsEq s *)
    fs[eval_op_def] >>
    Cases_on `x = Diverge` >> Cases_on `y = Diverge` >> fs[is_eq_def]
    >- (imp_res_tac v_cmp_Diverge2 >> fs[]) >>
    first_assum (qspec_then ‘[]’ assume_tac) >>
    Cases_on `x` >> Cases_on `y` >> fs[v_cmp_def, v_lookup]
    )
  >- ( (* op = Proj s i *)
    fs[eval_op_def, el_def] >>
    Cases_on `x = Diverge` >> Cases_on `y = Diverge` >> fs[is_eq_def]
    >- (imp_res_tac v_cmp_Diverge2 >> fs[]) >>
    first_assum (qspec_then ‘[]’ assume_tac) >>
    Cases_on `x` >> Cases_on `y` >> fs[v_cmp_def, v_lookup] >>
    gvs[] >> rw[] >>
    first_assum (qspec_then ‘i::path’ assume_tac) >>
    fs[v_lookup, oEL_THM] >> gvs[]
    )
  >- ( (* op = PrimOp *)
    fs[eval_op_def] >>
    Cases_on `MEM Diverge xs` >> fs[] >>
    imp_res_tac LIST_REL_not_diverge >> fs[] >>
    drule_all LIST_REL_v_cmp_getAtom_eq >> rw[]
    )
QED

Theorem eval_to_res_mono_lemma:
  ∀ c k x n path. v_cmp path (eval_to c k x) (eval_to c (k+n) x)
Proof
  ho_match_mp_tac eval_to_ind >> rw[]
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ TRY (fs [eval_to_def] \\ rw [v_cmp_refl] \\ NO_TAC)
  >- (
    fs[eval_to_def] >> rw[] >>
    irule eval_op_div >>
    Induct_on `xs` >> fs[]
    ) >>
  fs[eval_to_def, dest_Closure_def] >>
  first_x_assum (qspecl_then [`n`,`[]`] assume_tac) >>
  Cases_on `eval_to c k x` >> Cases_on `eval_to c (k + n) x` >>
  fs[v_cmp_def, v_lookup] >> gvs[] >>
  Cases_on `n = 0` >> fs[] >>
  Cases_on `k = 0` >> fs[] >>
  Cases_on `path` >> fs[v_lookup]
QED

Theorem eval_to_res_mono:
  eval_to c k x ≠ Diverge ∧
  k ≤ k1 ⇒
    v_lookup [] (eval_to c k x) = v_lookup [] (eval_to c k1 x)
Proof
  rw [LESS_EQ_EXISTS]
  \\ qspecl_then [‘c’,‘k’,‘x’,‘p’,‘[]’] assume_tac eval_to_res_mono_lemma
  \\ fs[v_cmp_def,v_lookup]
  \\ Cases_on `eval_to c k x` \\ Cases_on `eval_to c (k + p) x`
  \\ fs[]
QED

Theorem eval_to_res_mono_0:
  eval_to c k x ≠ Diverge ∧
  k ≤ k1 ∧
  SND (v_lookup [] (eval_to c k x)) = 0 ⇒
    eval_to c k1 x = eval_to c k x
Proof
  rpt strip_tac
  \\ drule eval_to_res_mono
  \\ disch_then drule
  \\ Cases_on `eval_to c k x` \\ Cases_on `eval_to c k1 x` \\  fs [v_lookup]
QED

Theorem eval_to_simple_mono:
  eval_to c k x ≠ Diverge ∧
  k ≤ k1 ∧
  SND (v_lookup [] (eval_to c k1 x)) = 0 ⇒
    eval_to c k1 x = eval_to c k x
Proof
  rpt strip_tac
  \\ drule eval_to_res_mono
  \\ disch_then drule \\ strip_tac
  \\ Cases_on ‘eval_to c k x’ \\ Cases_on `eval_to c k1 x` \\ gvs[v_lookup]
QED

Theorem eval_to_div:
  eval_to c k1 x = Diverge ∧ k ≤ k1 ⇒ eval_to c k x = Diverge
Proof
  rw [] \\ CCONTR_TAC
  \\ drule eval_to_simple_mono
  \\ disch_then drule
  \\ simp[v_lookup]
QED

Theorem eval_to_not_diverge_mono:
  ∀ k' k x . (k ≤ k' ∧ eval_to c k x ≠ Diverge) ⇒ eval_to c k' x ≠ Diverge
Proof
  rw []
  \\ drule eval_to_res_mono
  \\ disch_then drule
  \\ Cases_on ‘eval_to c k x’ \\ Cases_on ‘eval_to c k' x’ \\ fs[v_lookup]
QED

Theorem eval_to_not_diverge_not_eq_mono:
  ∀ k' k x c.
    (k ≤ k' ∧
     eval_to c k x ≠ Diverge ∧
     SND (v_lookup [] (eval_to c k x)) ≠ 0)
  ⇒ SND (v_lookup [] (eval_to c k' x)) ≠ 0
Proof
  rw[]
  \\ CCONTR_TAC \\ fs[]
  \\ imp_res_tac eval_to_simple_mono \\ fs[]
QED

Theorem LIST_MAP_eval_to_not_diverge_mono:
  ∀ k' k. (k ≤ k' ∧ ¬MEM Diverge (MAP (λa. eval_to c k a) es))
                  ⇒ ¬MEM Diverge (MAP (λa. eval_to c k' a) es)
Proof
  rw[] \\ Induct_on ‘es’ \\ fs[]
  \\ strip_tac \\ disch_tac \\ fs[]
  \\ imp_res_tac eval_to_not_diverge_mono
QED

Theorem dest_Closure_eval_IMP:
  dest_Closure (eval c x) = NONE ⇒
  dest_Closure (eval_to c k x) = NONE
Proof
  rw []
  \\ simp [AllCaseEqs(),dest_Closure_def]
  \\ CCONTR_TAC \\ fs []
  \\ Cases_on ‘eval_to c k x’ \\ fs []
  \\ rename [‘Closure x1 x2’]
  \\ qsuff_tac ‘eval c x = Closure x1 x2’
  THEN1 (strip_tac \\ fs [dest_Closure_def])
  \\ fs [eval_def, gen_v_Closure]
  \\ qexists_tac `0`
  \\ irule v_limit_exists
  \\ qexists_tac `k` \\ rw[]
  \\ `eval_to c k x ≠ Diverge` by fs[]
  \\ drule_all eval_to_res_mono \\ fs[]
  \\ Cases_on `eval_to c n x` >> fs[v_lookup]
QED

Theorem eval_Var:
  eval c (Var s) = Error (* free variables are not allowed *)
Proof
  fs [eval_def,eval_to_def, Once gen_v]
  \\ fs [v_limit_def,v_lookup]
QED

Theorem eval_Lam:
  eval c (Lam s x) = Closure s x
Proof
  fs [eval_def,eval_to_def,Once gen_v]
  \\ fs [v_limit_def,v_lookup]
QED

Theorem eval_Letrec:
  eval c (Letrec f x) = eval c (subst_funs f x)
Proof
  fs [eval_def,eval_to_def]
  \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM] \\ rw []
  \\ match_mp_tac v_limit_eq_add
  \\ fs [] \\ qexists_tac ‘1’ \\ fs []
QED

Theorem v_limit_if_Diverge_lemma:
  ∀ f g r.
    v_limit (λk. f k) [] = (Diverge', r)
  ⇒ v_limit (λk.
      if f k = (Diverge:(α,β) v) then (Diverge:(α,β) v) else g k) [] =
      (Diverge', r)
Proof
  rw[] >>
  drule v_limit_not_Error >> strip_tac >> rw[] >>
  irule v_limit_exists >>
  qexists_tac `k` >> strip_tac >> strip_tac >> fs[] >>
  first_x_assum drule >>
  rw[] >>
  Cases_on `f n` >> gvs[v_lookup]
QED

Theorem some_elim_eval_to_Diverge[local]:
  ∀ c x g path res.
    (∀k. ∃k'. k ≤ k' ∧ v_lookup path (eval_to c k' x) ≠ (Diverge', 0))
  ⇒ (∃k. ∀k'. k ≤ k' ⇒
      v_lookup path
        (if eval_to c k' x = (Diverge:(α,β) v)
         then (Diverge:(α,β) v) else g k') = res) =
    (∃k. ∀k'. k ≤ k' ⇒ v_lookup path (g k') = res)
Proof
  rw[] >> eq_tac >> rw[] >>
  last_x_assum (qspec_then `k` assume_tac) >> fs[] >>
  rename1 `_ ≤ k2` >>
  qexists_tac `k2` >> rw[] >> rename1 `_ ≤ k3` >>
  `k ≤ k3` by fs[] >>
  first_x_assum drule >> gvs[] >> rw[] >>
  `eval_to c k2 x ≠ Diverge` by (
    CCONTR_TAC >> Cases_on `path` >> gvs[v_lookup]) >>
  drule eval_to_not_diverge_mono >> disch_then drule >> fs[]
QED

Theorem v_limit_if_not_Diverge_lemma:
  ∀ c x g path.
    (∀r. v_limit (λk. eval_to c k x) path ≠ (Diverge', r))
  ⇒ v_limit (λk.
      if eval_to c k x = (Diverge:(α,β) v) then (Diverge:(α,β) v) else g k) path =
    v_limit (λk. g k) path
Proof
  rw[] >> fs[v_limit_def, limit_def] >>
  pop_assum mp_tac >>
  DEEP_INTRO_TAC some_intro >> strip_tac >> fs[]
  >- (
    qx_gen_tac `res1` >> rw[] >> rename1 `k1 ≤ _` >>
    DEEP_INTRO_TAC some_intro >> strip_tac
    >- (
      qx_gen_tac `res2` >> rw[] >> rename1 `k2 ≤ _` >>
      DEEP_INTRO_TAC some_intro >> strip_tac
      >- (
        qx_gen_tac `res3` >> rw[] >> rename1 `k3 ≤ _` >>
        qpat_x_assum `∀r. _ ≠ _` mp_tac >>
        rpt (first_x_assum (qspec_then `k1 + k2 + k3` assume_tac)) >> fs[] >>
        Cases_on `eval_to c (k1 + k2 + k3) x` >> Cases_on `path` >> gvs[v_lookup]
        )
      >- (
        rw[] >>
        first_x_assum (qspecl_then [`res2`,`k1 + k2`] assume_tac) >> fs[] >>
        rename1 `_ + _ ≤ k3` >>
        qpat_x_assum `∀r. _ ≠ _` mp_tac >>
        rpt (first_x_assum (qspec_then `k3` assume_tac)) >> gvs[] >>
        Cases_on `eval_to c k3 x` >> Cases_on `path` >> gvs[v_lookup]
        )
      )
    >- (
      rw[] >>
      DEEP_INTRO_TAC some_intro >> reverse (strip_tac) >- rw[] >>
      qx_gen_tac `res2` >> rw[] >> rename1 `k2 ≤ _` >>
      first_x_assum (qspecl_then [`res2`,`k1 + k2`] assume_tac) >> fs[] >>
      rename1 `_ + _ ≤ k3` >>
      qpat_x_assum `∀r. _ ≠ _` mp_tac >>
      rpt (first_x_assum (qspec_then `k3` assume_tac)) >> gvs[] >>
      Cases_on `eval_to c k3 x` >> Cases_on `path` >> gvs[v_lookup]
      )
    )
  >- (
    rw[] >>
    MK_COMB_TAC >> fs[] >> MK_COMB_TAC >> fs[] >>
    AP_TERM_TAC >> AP_TERM_TAC >>
    irule EQ_EXT >> rw[] >> rename1 `v_lookup _ _ = res` >>
    first_x_assum (qspec_then `(Diverge',0)` assume_tac) >>
    drule some_elim_eval_to_Diverge >> fs[]
    )
QED

Theorem eval_App:
  eval c (App x y) =
    let v = eval c x in
      if v = Diverge then Diverge else
        case dest_Closure v of
        | SOME (s,body) => eval c (bind [(s,y)] body)
        | NONE => Error
Proof
  fs [eval_def, eval_to_def] >>
  IF_CASES_TAC
  >- (
    fs[gen_v_Diverge] >> qexists_tac `r` >> fs[] >>
    qspecl_then [`λk. eval_to c k x`] assume_tac v_limit_if_Diverge_lemma >>
    fs[]
    ) >>
  CASE_TAC
  >- (
    fs[GSYM eval_def] >>
    drule dest_Closure_eval_IMP >> fs[] >> rw[] >>
    fs[eval_def, gen_v_Diverge, gen_v_Error] >>
    drule v_limit_if_not_Diverge_lemma >> fs[] >> rw[] >>
    fs[v_limit_def, v_lookup]
    ) >>
  rename1 `_ = SOME clos` >> PairCases_on `clos` >> fs[] >>
  fs[dest_Closure_def, GSYM eval_def] >>
  Cases_on `eval c x` >> gvs[] >>
  fs[eval_def, GSYM dest_Closure_def, gen_v_Closure] >>
  AP_TERM_TAC >> fs[FUN_EQ_THM] >> rw[] >>
  drule v_limit_not_Error >> strip_tac >> fs[] >>
  gvs[v_limit_def] >>
  irule limit_eq_add_IMP >> qexists_tac `1` >> fs[limit_def] >>
  qexists_tac `k` >> strip_tac >> strip_tac >>
  `eval_to c (n + 1) x = Closure clos0 clos1` by (
    CCONTR_TAC >>
    first_x_assum (qspec_then `n + 1` assume_tac) >> gvs[v_lookup] >>
    Cases_on `eval_to c (n + 1) x` >> gvs[]) >>
  fs[]
QED

Theorem eval_Let:
  eval c (Let s x y) = eval c (bind [(s,x)] y)
Proof
  fs [eval_App,eval_Lam,dest_Closure_def,bind_def]
QED

Theorem eval_Cons:
  eval c (Cons s xs) = Constructor s (MAP (eval c) xs)
Proof
  fs [eval_def,eval_to_def,Once gen_v,eval_op_def]
  \\ fs [v_limit_def,v_lookup]
  \\ fs [LIST_EQ_REWRITE, oEL_THM]
  \\ fs [EL_MAP,eval_def,v_limit_def]
QED

Theorem eval_Case:
  eval c (Case x nm css) = eval c (expandCases x nm css)
Proof
  fs[expandCases_def,eval_Let,bind_def]
  \\ IF_CASES_TAC
  \\ fs[eval_def,eval_to_def]
  \\ fs [v_limit_if]
  \\ fs [expandCases_def,bind_def,eval_to_def]
  \\ fs [eval_to_def]
  \\ fs [v_limit_if]
  \\ fs [bind_def]
QED

Theorem gen_v_not_Error:
  gen_v (λpath. v_limit (λk. eval_to c k x) path) ≠ Error ⇒
  ∃k. ∀n. k ≤ n ⇒ ∃v. eval_to c n x = v ∧ v ≠ Error
Proof
  once_rewrite_tac [gen_v] \\ fs [pairTheory.UNCURRY] \\ rw []
  \\ Cases_on ‘v_limit (λk. eval_to c k x) []’
  \\ fs [v_limit_def]
  \\ drule limit_not_default \\ fs []
  \\ Cases_on `q` \\ gvs[]
  \\ rpt strip_tac \\ qexists_tac ‘k’ \\ fs []
  \\ rpt strip_tac \\ first_x_assum drule
  \\ fs [] \\ Cases_on ‘eval_to c n x’ \\ fs []
  \\ fs [v_lookup]
QED

Theorem eval_IsEq:
  eval c (IsEq s n x) = is_eq c s n (eval c x)
Proof
  fs [eval_def,eval_to_def,eval_op_def,is_eq_def] >>
  IF_CASES_TAC
  >- (
    fs[gen_v_Diverge] >> qexists_tac `r` >> fs[] >>
    qspecl_then [`λk. eval_to c k x`] assume_tac v_limit_if_Diverge_lemma >>
    fs[]
    ) >>
  fs[GSYM eval_def] >>
  Cases_on `eval c x` >>
  fs[gen_v_Atom, gen_v_Closure, gen_v_Error, eval_def]
  >- (
    qexists_tac `r` >>
    drule v_limit_not_Error >> strip_tac >> fs[] >>
    irule v_limit_exists >>
    qexists_tac `k` >> strip_tac >> strip_tac >> fs[] >> rename1 `_ ≤ k1` >>
    first_x_assum drule >>
    Cases_on `eval_to c k1 x` >> gvs[v_lookup]
    )
  >- (
    pop_assum mp_tac >>
    simp[Once gen_v] >>
    CASE_TAC >> CASE_TAC >> fs[] >>
    strip_tac >> gvs[] >>
    rename1 `(Constructor' cons, len)` >>
    reverse (rw[]) >> fs[gen_v_nullary_Constructor, gen_v_Error]
    >- (
      qexists_tac `0` >>
      drule v_limit_not_Error >> strip_tac >> fs[] >>
      irule v_limit_exists >>
      qexists_tac `k` >> strip_tac >> strip_tac >> fs[] >> rename1 `_ ≤ n1` >>
      first_x_assum drule >>
      Cases_on `eval_to c n1 x` >> gvs[v_lookup]
      ) >>
    drule v_limit_not_Error >> strip_tac >> fs[] >>
    irule v_limit_exists >>
    qexists_tac `k` >> strip_tac >> strip_tac >> fs[] >>
    first_x_assum drule >> fs[] >>
    Cases_on `eval_to c n x` >> fs[v_lookup]
    )
  >- (
    qexists_tac `r` >>
    drule v_limit_not_Error >> strip_tac >> fs[] >>
    irule v_limit_exists >>
    qexists_tac `k` >> strip_tac >> strip_tac >> fs[] >> rename1 `_ ≤ k1` >>
    first_x_assum drule >>
    Cases_on `eval_to c k1 x` >> gvs[v_lookup]
    )
  >- (
    qexists_tac `r` >>
    pop_assum mp_tac >> simp[Once v_limit_eqn] >> rw[]
    >- (
      rename1 `k1 ≤ _` >>
      irule v_limit_exists >>
      qexists_tac `k1` >> strip_tac >> strip_tac >> fs[] >>
      rename1 `_ ≤ k2`  >>
      first_x_assum drule >> Cases_on `eval_to c k2 x` >> gvs[v_lookup]
      )
    >- (
      fs[v_limit_eqn, DISJ_EQ_IMP] >> rw[] >>
      first_assum (qspecl_then [`(Diverge',0)`,`k`] assume_tac) >> fs[] >>
      rename1 `_ ≤ k1` >>
      first_x_assum (qspec_then `k1` assume_tac) >> fs[] >>
      rename1 `_ ≤ k2` >>
      Cases_on `eval_to c k1 x = Diverge` >> fs[v_lookup] >>
      fs[GSYM v_lookup] >>
      drule eval_to_not_diverge_mono >> disch_then drule >> strip_tac >>
      Cases_on `eval_to c k2 x` >> gvs[v_lookup] >>
      rename1 `eval_to _ _ _ = Constructor cons vs` >>
      qexists_tac `k2` >> fs[] >>
      rw[] >>
      last_x_assum (
        qspecl_then [`(Constructor' cons, LENGTH vs)`,`k2`] assume_tac) >>
      fs[] >> rename1 `_ ≤ k3` >>
      imp_res_tac eval_to_res_mono >> pop_assum kall_tac >>
      pop_assum (qspecl_then [`x`,`c`] assume_tac) >> gvs[] >>
      Cases_on `eval_to c k3 x` >> gvs[v_lookup]
      )
    )
QED

Theorem eval_Proj:
  eval c (Proj s i x) = el s i (eval c x)
Proof
  fs [eval_def,eval_to_def,eval_op_def,el_def] >>
  IF_CASES_TAC
  >- (
    fs[gen_v_Diverge] >> qexists_tac `r` >> fs[] >>
    qspecl_then [`λk. eval_to c k x`] assume_tac v_limit_if_Diverge_lemma >>
    fs[]
    ) >>
  fs[GSYM eval_def] >>
  Cases_on `eval c x` >>
  fs[gen_v_Atom, gen_v_Closure, gen_v_Error, eval_def]
  >- (
    qexists_tac `r` >>
    drule v_limit_not_Error >> strip_tac >> fs[] >>
    irule v_limit_exists >>
    qexists_tac `k` >> strip_tac >> strip_tac >> fs[] >> rename1 `_ ≤ k1` >>
    first_x_assum drule >>
    Cases_on `eval_to c k1 x` >> gvs[v_lookup]
    )
  >- (
    rw[] >> fs[gen_v_Error] >>
    last_x_assum mp_tac >>
    simp[Once gen_v] >>
    CASE_TAC >> CASE_TAC >> fs[] >> rw[] >>
    rename1 `(Constructor' cons, len)` >> fs[LENGTH_GENLIST]
    >- (
      AP_TERM_TAC >> fs[FUN_EQ_THM] >> rw[] >>
      fs[v_limit_def, v_lookup, oEL_THM] >>
      irule limit_eq_IMP >>
      imp_res_tac limit_not_default >> fs[] >> rename1 `k ≤ _` >>
      qexists_tac `k` >> rw[v_lookup_Diverge] >>
      first_x_assum (qspec_then `n` assume_tac) >> gvs[] >>
      Cases_on `eval_to c n x` >> fs[]
      ) >>
    drule v_limit_not_Error >> strip_tac >> fs[] >>
    qexists_tac `0` >>
    irule v_limit_exists >>
    qexists_tac `k` >> strip_tac >> strip_tac >> fs[] >> rename1 `_ ≤ n1` >>
    first_x_assum drule >>
    Cases_on `eval_to c n1 x` >> gvs[v_lookup]
    )
  >- (
    qexists_tac `r` >>
    drule v_limit_not_Error >> strip_tac >> fs[] >>
    irule v_limit_exists >>
    qexists_tac `k` >> strip_tac >> strip_tac >> fs[] >> rename1 `_ ≤ k1` >>
    first_x_assum drule >>
    Cases_on `eval_to c k1 x` >> gvs[v_lookup]
    )
  >- (
    qexists_tac `r` >>
    fs[v_limit_eqn, DISJ_EQ_IMP, IMP_CONJ_THM] >> rw[]
    >- (
      first_x_assum irule >> rw[] >>
      first_x_assum (qspec_then `k` assume_tac) >> fs[] >>
      rename1 `_ ≤ k1` >> qexists_tac `k1` >>
      Cases_on `eval_to c k1 x` >> gvs[v_lookup]
      ) >>
    last_x_assum assume_tac >> last_x_assum mp_tac >>
    impl_tac
    >- (
      rw[] >>
      first_x_assum (qspec_then `k` assume_tac) >> fs[] >>
      rename1 `_ ≤ k1` >> qexists_tac `k1` >> fs[] >>
      Cases_on `eval_to c k1 x` >> gvs[v_lookup]
      ) >>
    rw[] >>
    first_assum (qspecl_then [`(Diverge',0)`,`k`] assume_tac) >> fs[] >>
    rename1 `_ ≤ k1` >>
    first_x_assum (qspec_then `k1` assume_tac) >> fs[] >>
    rename1 `_ ≤ k2` >>
    Cases_on `eval_to c k1 x = Diverge` >> fs[v_lookup] >> fs[GSYM v_lookup] >>
    drule eval_to_not_diverge_mono >> disch_then drule >> strip_tac >>
    Cases_on `eval_to c k2 x` >> gvs[v_lookup] >>
    rename1 `eval_to _ _ _ = Constructor cons vs` >>
    qexists_tac `k2` >> fs[] >>
    rw[] >>
    last_x_assum (
      qspecl_then [`(Constructor' cons, LENGTH vs)`,`k2`] assume_tac) >>
    fs[] >> rename1 `_ ≤ k3` >>
    imp_res_tac eval_to_res_mono >> pop_assum kall_tac >>
    pop_assum (qspecl_then [`x`,`c`] assume_tac) >> gvs[] >>
    Cases_on `eval_to c k3 x` >> gvs[v_lookup]
  )
QED

(************ getAtom NONE/SOME over eval/eval_to lemmas*********)

(*if eval_to does not diverge and is not equal to Num for some k, then
  eval_to is not equal to Num forall k                                *)
Theorem eval_to_not_div_not_eq_mono:
  ∀ n.(( eval_to c k (x:('a,'b) exp) ≠ Diverge ∧ eval_to c k x ≠ Atom n)
       ⇒ ∀ k'. eval_to c k' x ≠ Atom n)
Proof
  rw[] >> Cases_on `k ≤ k'`
  >- (
    imp_res_tac eval_to_not_diverge_mono >>
    drule_all eval_to_res_mono >>
    Cases_on `eval_to c k x` >> Cases_on `eval_to c k' x` >> gvs[v_lookup] >>
    rw[] >> fs[]
    ) >>
  fs[NOT_LESS_EQUAL] >> imp_res_tac LESS_IMP_LESS_OR_EQ >>
  CCONTR_TAC >> fs[] >>
  `eval_to c k' x ≠ Diverge` by fs[] >>
  drule_all eval_to_res_mono >> fs[] >>
  Cases_on `eval_to c k x` >> gvs[v_lookup]
QED

Theorem getAtom_eval_NONE:
  getAtom (eval c x) = NONE ⇒ (∀ k. ∃k'. k ≤ k' ∧ getAtom (eval_to c k' x) = NONE)
Proof
  rw[] >> fs[getAtom_NONE, eval_def, gen_v_Atom, v_limit_eqn] >>
  `∀k n r. ∃k'. k ≤ k' ∧ v_lookup [] (eval_to c k' x) ≠ (Atom' n, r)` by fs[] >>
  first_x_assum (qspec_then `k` assume_tac) >>
  qexists_tac `k` >> fs[] >> strip_tac >>
  first_x_assum (qspecl_then [`n`,`0`] assume_tac) >> fs[] >>
  Cases_on ‘eval_to c k' x = Diverge’
  THEN1 (imp_res_tac eval_to_div \\ fs[])
  \\ imp_res_tac eval_to_not_div_not_eq_mono
  \\ Cases_on `eval_to c k' x` \\ gvs[v_lookup]
QED

(*************eval/eval_to over exp list lemmas ***************)

Theorem eval_Diverge_IFF_eval_to_Diverge:
  MEM Diverge (MAP (eval c) es) ⇔ ∀ k. MEM Diverge (MAP (λa. eval_to c k a) es)
Proof
  eq_tac
  THEN1 (
    rw [MEM_MAP]
    \\ fs [eval_def, eval_to_def, gen_v_Diverge]
    \\ dxrule v_limit_not_Error \\ rw []
    \\ qexists_tac ‘y’ \\ fs []
    \\ Cases_on ‘k' ≤ k’ \\ fs []
    THEN1 (
      first_x_assum drule
      \\ simp [v_lookup_alt]
      \\ CASE_TAC \\ fs [v_to_prefix])
    \\ first_x_assum (qspec_then ‘k'’ mp_tac)
    \\ simp [v_lookup_alt]
    \\ CASE_TAC \\ rw [v_to_prefix]
    \\ ‘k ≤ k'’ by fs []
    \\ drule_all eval_to_div \\ rw [])
  THEN1 (
    Induct_on ‘es’ \\ rw []
    \\ fs [eval_def, gen_v_Diverge]
    \\ Cases_on ‘MEM Diverge (MAP (eval c) es)’ \\ fs []
    \\ ‘∀k'. k ≤ k' ⇒ eval_to c k' h = Diverge’
      by (imp_res_tac LIST_MAP_eval_to_not_diverge_mono
          \\ metis_tac [])
    \\ ntac 3 (last_x_assum kall_tac)
    \\ qexists_tac ‘0’
    \\ simp [v_limit_def, limit_def]
    \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
    THEN1 (
      first_x_assum (qspec_then ‘k + k'’ mp_tac)
      \\ first_x_assum (qspec_then ‘k + k'’ mp_tac)
      \\ simp [v_lookup_alt, v_to_prefix])
    \\ Q.LIST_EXISTS_TAC [‘Diverge', 0’, ‘k’]
    \\ rw [DISJ_EQ_IMP]
    \\ simp [v_lookup])
QED

Triviality eval_to_atom_mono_res:
  eval_to c k x = Atom n ⇒
    k ≤ k1 ⇒ eval_to c k1 x = eval_to c k x
Proof
  rpt strip_tac
  \\ ‘eval_to c k x ≠ Diverge’ by fs[]
  \\ drule_all eval_to_res_mono
  \\ simp [v_lookup]
  \\ CASE_TAC \\ fs []
QED

(* TODO Fix from here on: *)

Theorem getAtoms_eval_to_NONE:
   getAtoms (MAP (eval (c:(α,β) conf)) es) = NONE
   ⇒  getAtoms (MAP (λa. eval_to c k a) es) = NONE
Proof
  Induct_on `es` >> fs[] >> rw[getAtoms_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  Cases_on `eval_to c k h` >> gvs[getAtom_def] >>
  qsuff_tac `eval c h = Atom b` >- (CCONTR_TAC >> gvs[getAtom_def]) >>
  fs[eval_def, gen_v_Atom, v_limit_eqn] >>
  qexists_tac `0` >> qexists_tac `k` >> rw[] >>
  imp_res_tac eval_to_res_mono >>
  first_x_assum (qspecl_then [`h`,`c`] assume_tac) >> gvs[v_lookup]
QED

Theorem getAtoms_eval_to_SOME:
   (getAtoms (MAP (eval c) es) = SOME l
   ∧ ¬MEM Diverge (MAP (λa. eval_to c k a) es))
   ⇒  getAtoms (MAP (λa. eval_to c k a) es) = SOME l
Proof
  qid_spec_tac `l` >>
  Induct_on `es` >> fs[getAtoms_def] >> rw[] >>
  Cases_on `getAtoms (MAP (eval c) es)` >> gvs[]
  >- (BasicProvers.EVERY_CASE_TAC >> gvs[]) >>
  Cases_on `eval c h` >> gvs[getAtom_def] >>
  fs[eval_def, gen_v_Atom, v_limit_eqn] >>
  rename1 `k1 ≤ _` >>
  first_assum (qspec_then `k` assume_tac) >>
  Cases_on `k1 ≤ k` >> fs[]
  >- (Cases_on `eval_to c k h` >> gvs[getAtom_def, v_lookup]) >>
  fs[NOT_LESS_EQUAL] >>
  first_x_assum (qspec_then `k1` assume_tac) >> gvs[] >>
  drule eval_to_res_mono >> disch_then (qspec_then `k1` assume_tac) >> gvs[] >>
  Cases_on `eval_to c k h` >> gvs[v_lookup, getAtom_def]
QED

(*****************************************************)

Theorem eval_If:
  eval c (If x y z) = (
    if eval c x = Diverge then Diverge  else
    if eval c x = True    then eval c y else
    if eval c x = False   then eval c z else Error)
Proof
  IF_CASES_TAC
  >- (
    fs[eval_def, eval_to_def, gen_v_Diverge, v_limit_eqn] >>
    qexists_tac `0` >> qexists_tac `k` >> rw[] >>
    rename1 `_ ≤ k1` >> first_x_assum drule >>
    Cases_on `eval_to c k1 x` >> fs[eval_op_def, v_lookup]
    ) >>
  ntac 2 (
    IF_CASES_TAC
    >- (
      fs[eval_def, eval_to_def, eval_op_def] >>
      fs[gen_v_Diverge, gen_v_nullary_Constructor, v_limit_eqn] >>
      AP_TERM_TAC >> fs[FUN_EQ_THM] >> rw[] >>
      irule v_limit_eq_IMP >>
      qexists_tac `k` >> strip_tac >> strip_tac >> fs[] >>
      first_x_assum drule >>
      Cases_on `eval_to c n x` >> gvs[v_lookup]
      )
  ) >>
  fs[eval_def, eval_to_def] >>
  fs[eval_op_def, gen_v_Error, gen_v_Diverge, gen_v_nullary_Constructor] >>
  qexists_tac `0` >> fs[] >>
  fs[v_limit_eqn] >> DISJ1_TAC >>
  first_x_assum (qspecl_then [`0`,`k`] assume_tac) >> fs[] >>
  rename1 `_ ≤ lim` >>
  first_x_assum (qspec_then `lim` assume_tac) >> fs[] >> rename1 `_ ≤ k1` >>
  first_x_assum (qspec_then `lim` assume_tac) >> fs[] >> rename1 `_ ≤ k2` >>
  qexists_tac `k1 + k2` >> strip_tac >> strip_tac >> rename1 `_ ≤ k4` >>
  `eval_to c lim x ≠ Diverge` by (
    Cases_on `eval_to c lim x` >> gvs[v_lookup]) >>
  `eval_to c k2 x ≠ True` by (
    Cases_on `eval_to c k2 x` >> gvs[v_lookup]) >>
  `eval_to c k1 x ≠ False` by (
    Cases_on `eval_to c k1 x` >> gvs[v_lookup]) >>
  rw[] >> gvs[v_lookup] >> fs[GSYM v_lookup]
  >- (
    drule eval_to_div >> disch_then (qspec_then `lim` assume_tac) >>
    gvs[v_lookup]
    )
  >- (
    `eval_to c k2 x ≠ Diverge` by (
      CCONTR_TAC >> fs[] >> drule_all eval_to_div >> fs[]) >>
    drule eval_to_simple_mono >>
    disch_then (qspec_then `k4` assume_tac) >> gvs[v_lookup]
    )
  >- (
    `eval_to c k1 x ≠ Diverge` by (
      CCONTR_TAC >> fs[] >> drule_all eval_to_div >> fs[]) >>
    drule eval_to_simple_mono >>
    disch_then (qspec_then `k4` assume_tac) >> gvs[v_lookup]
    )
QED

Theorem eval_PrimOp:
  eval c (Prim (AtomOp (a:'a)) es) =
  (let xs = MAP (eval c) es in
   if MEM Diverge xs then Diverge else
      case OPTION_BIND (getAtoms xs) (c.parAtomOp a) of
       | (SOME n) => Atom n
       | _        => Error)
Proof
  fs[] >> rw[]
  >- (
    fs[eval_def, eval_to_def, gen_v_Diverge, v_limit_eqn, eval_op_def] >>
    qexists_tac `0` >> qexists_tac `k` >> rw[v_lookup] >>
    gvs[eval_Diverge_IFF_eval_to_Diverge]
    ) >>
  gvs[eval_Diverge_IFF_eval_to_Diverge] >>
  CASE_TAC >> fs[eval_def, eval_to_def, gen_v_Error, gen_v_Atom, eval_op_def]
  >- (
    imp_res_tac getAtoms_eval_to_NONE >>
    qexists_tac `0` >> fs[v_limit_eqn] >> DISJ1_TAC >>
    qexists_tac `k` >> rw[] >> gvs[v_lookup] >>
    drule LIST_MAP_eval_to_not_diverge_mono >> disch_then drule >> fs[]
    )
  >- (
    qexists_tac `0` >> fs[v_limit_eqn] >> DISJ1_TAC >>
    qexists_tac `k` >> strip_tac >> strip_tac >>
    drule LIST_MAP_eval_to_not_diverge_mono >> disch_then drule >> fs[] >>
    strip_tac >>
    CASE_TAC >> gvs[v_lookup] >>
    imp_res_tac getAtoms_eval_to_SOME >> fs[]
    )
  >- (
    qexists_tac `0` >> fs[v_limit_eqn] >>
    qexists_tac `k` >> strip_tac >> strip_tac >>
    drule LIST_MAP_eval_to_not_diverge_mono >> disch_then drule >> fs[] >>
    strip_tac >>
    CASE_TAC >> gvs[v_lookup] >>
    imp_res_tac getAtoms_eval_to_SOME >> fs[]
    )
QED

Theorem eval_Lit:
  eval c (Prim (Lit b) []) = Atom b ∧
  eval c (Prim (Lit b) (x::xs)) = Error
Proof
  fs[eval_def, eval_to_def, eval_op_def] >>
  once_rewrite_tac[gen_v] >> fs[] >>
  fs[v_limit_def, v_lookup]
QED

Theorem eval_Fail:
  eval c Fail = Error
Proof
  fs[eval_def, eval_to_def, eval_op_def] >>
  once_rewrite_tac[gen_v] >> fs[] >>
  fs[v_limit_def, v_lookup]
QED

Theorem eval_Prim:
  eval c (Prim op xs) = eval_op c op (MAP (eval c) xs)
Proof
  Cases_on `op`
  >- ( (* If *)
    Cases_on ‘∃x1 x2 x3. xs = [x1;x2;x3]’
    THEN1 (rw [] \\ fs [eval_If,eval_op_def] \\ rw [] \\ fs [])
    \\ fs []
    \\ rpt
       (rename [‘xs ≠ _’] \\ Cases_on ‘xs’ \\ fs [] THEN1
         (fs [eval_def,eval_to_def,Once gen_v,eval_op_def]
          \\ fs [v_limit_def,v_lookup]))
    )
  >- fs [eval_Cons,eval_op_def] (* Cons *)
  >- ( (* IsEq *)
    Cases_on ‘xs’ \\ fs [eval_op_def]
    \\ TRY (Cases_on ‘t’) \\ fs [eval_op_def,eval_IsEq]
    \\ fs [eval_def,eval_to_def,Once gen_v,eval_op_def]
    \\ fs [v_limit_def,v_lookup]
    )
  >- ( (* Proj *)
    Cases_on ‘xs’ \\ fs [eval_op_def]
    THEN1
      (fs [eval_def,eval_to_def,Once gen_v,eval_op_def]
       \\ fs [v_limit_def,v_lookup])
    \\ Cases_on ‘t’ \\ fs [eval_Proj,eval_op_def]
    \\ fs [eval_def,eval_to_def,Once gen_v,eval_op_def]
    \\ fs [v_limit_def,v_lookup]
    )
  >- fs[eval_PrimOp, eval_op_def] (* AtomOp *)
  >- (Cases_on `xs` >> fs[eval_Lit, eval_op_def]) (* Lit *)
QED

Theorem eval_core:
  eval c (Var s) = Error (* free variables are not allowed *) ∧
  eval c (Prim op xs) = eval_op c op (MAP (eval c) xs) ∧
  eval c (Lam s x) = Closure s x ∧
  eval c (Letrec f x) = eval c (subst_funs f x) ∧
  eval c (App x y) =
    (let v = eval c x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (s,body) => eval c (bind [(s,y)] body)) ∧
  eval c (Case x nm css) = eval c (expandCases x nm css)
Proof
  fs [eval_Var,eval_Prim,eval_Lam,eval_Letrec,eval_App,eval_Case]
QED

(*like eval_core, but extended with exp Overloads*)
Theorem eval_thm:
  eval c (Fail)  = Error ∧
  eval c (Var s) = Error (* free variables are not allowed *) ∧
  eval c (Cons s xs) = Constructor s (MAP (eval c) xs) ∧
  eval c (IsEq s n x) = is_eq c s n (eval c x) ∧
  eval c (Proj s i x) = el s i (eval c x) ∧
  eval c (Let s x y) = eval c (bind [(s,x)] y) ∧
  eval c (If x y z) = (
         if eval c x = Diverge then Diverge  else
         if eval c x = True    then eval c y else
         if eval c x = False   then eval c z else Error) ∧
  eval c (Lam s x) = Closure s x ∧
  eval c (Letrec f x) = eval c (subst_funs f x) ∧
  eval c (App x y) =
    (let v = eval c x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (s,body) => eval c (bind [(s,y)] body)) ∧
  eval c (Case x nm css) = eval c (expandCases x nm css)
Proof
  fs [eval_Fail,eval_Var,eval_Cons,eval_App,eval_Lam,eval_If,eval_Proj,
      eval_IsEq,bind_def,eval_Letrec,eval_Case]
QED

(* prove that bottom diverges.

   bot x = bot x;
   eval bot (λx.x);
*)

Definition bottom_def:
  bottom =
    Letrec [("bot","n",App (Var "bot") (Lam "x" (Var "x")))]
      (App (Var "bot") (Lam "x" (Var "x")))
End

Triviality subst_id_fun:
  (subst n v (Lam "x" (Var "x"))) = (Lam "x" (Var "x"))
Proof
  Cases_on ‘n’ \\ Cases_on ‘v’
  \\ fs [subst_def,subst_funs_def,bind_def,closed_def]
  \\ IF_CASES_TAC
  \\ fs [subst_def,subst_funs_def,bind_def,closed_def]
QED

Theorem eval_bottom:
  ∀c. eval c bottom = Diverge
Proof
  strip_tac
  \\ qsuff_tac ‘∀k. eval_to c k bottom = Diverge’
  THEN1 fs [eval_def,v_limit_def,v_lookup,gen_v_Diverge]
  \\ strip_tac
  \\ fs [bottom_def,eval_to_def]
  \\ completeInduct_on ‘k’
  \\ Cases_on ‘k’
  \\ fs [subst_def,subst_funs_def,bind_def,closed_def]
  \\ Cases_on ‘n’ THEN1 fs[eval_to_def]
  \\ first_assum (qspec_then ‘SUC n'’ assume_tac) \\ fs[]
  \\ simp[eval_to_def]
  \\ fs [subst_def,subst_funs_def,bind_def,closed_def]
  \\ simp[eval_to_def]
  \\ fs [subst_def,subst_funs_def,bind_def,closed_def]
QED

(* example producing infinite list of λx.x*)

Definition zeros_def:
  zeros =
    Letrec [("z","n",Cons "cons" [Var "n"; App (Var "z") (Var "n")])]
      (App (Var "z") (Lam "x" (Var "x")))
End

Theorem eval_zeros:
  ∀ c. eval c zeros = Constructor "cons" [Closure "x" (Var "x"); eval c zeros]
Proof
  strip_tac
  \\ fs [Once zeros_def]
  \\ ntac 6 (simp [Once eval_thm,dest_Closure_def,subst_def,bind_def,
                   subst_funs_def,closed_def])
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ rewrite_tac [zeros_def]
  \\ ntac 2 (simp [Once eval_thm,dest_Closure_def,subst_def,bind_def,
                   subst_funs_def,closed_def])
QED


(* value and exp relation -- clocked *)

(*TODO, there might not be the need to parametrize v_rel' over c*)
Definition v_rel'_def:
  (v_rel' c 0 v1 v2 ⇔ T) ∧
  (v_rel' c (SUC n) v1 v2 =
    case v1 of
    | Atom a => v2 = Atom a
    | Constructor m xs =>
        ∃ ys. v2 = Constructor m ys ∧ LIST_REL (v_rel' c n) xs ys
    | Closure s1 x1 =>
        ∃ s2 x2.
          v2 = Closure s2 x2 ∧
          ∀z. v_rel' c n (eval c (bind [(s1,z)] x1))
                         (eval c (bind [(s2,z)] x2))
    | Diverge => v2 = Diverge
    | Error => v2 = Error)
End

(* Coinductive definition:
Coinductive v_rel:
  (a1 = a2 ⇒
    v_rel c (Atom a1) (Atom a2)) ∧
  (m1 = m2 ∧ LIST_REL (v_rel c) xs ys ⇒
    v_rel c (Constructor m1 xs) (Constructor m2 ys)) ∧
  ((∀z. v_rel c (eval c (bind [(c1,z)] e1)) (eval c (bind [(c2,z)] e2))) ⇒
   v_rel c (Closure c1 e1) (Closure c2 e2)) ∧
  (v_rel c Diverge Diverge) ∧
  (v_rel c Error Error)
End
*)

Definition v_rel_def:
  v_rel c x y = ∀n. v_rel' c n x y
End

Definition exp_rel_def:
  exp_rel c x y ⇔ v_rel c (eval c x) (eval c y)
End

Triviality v_rel'_refl:
  ∀n x. v_rel' c n x x
Proof
  Induct >> Cases >> rw[v_rel'_def] >>
  fs[LIST_REL_EL_EQN]
QED

Theorem v_rel_Closure:
  (∀x y. exp_rel c x y ⇒ exp_rel c (bind [m,x] b) (bind [n,y] d)) ⇒
  v_rel c (Closure m b) (Closure n d)
Proof
  rw [PULL_FORALL,exp_rel_def,v_rel_def] \\ fs []
  \\ Cases_on `n'` \\ fs[v_rel'_def]
  \\ rw[]
  \\ first_x_assum irule
  \\ fs[v_rel'_refl]
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

Triviality v_rel'_sym:
  ∀n x y. v_rel' c n x y ⇔ v_rel' c n y x
Proof
  Induct >> rw[] >> fs[v_rel'_def] >>
  Cases_on `x` >> Cases_on `y` >> fs[] >>
  drule LIST_REL_SYM >>
  metis_tac[]
QED

Triviality v_rel'_trans:
  ∀n x y z. v_rel' c n x y ∧ v_rel' c n y z ⇒ v_rel' c n x z
Proof
  Induct >> rw[] >> fs[v_rel'_def] >>
  Cases_on `x` >> Cases_on `y` >> fs[] >>
  drule LIST_REL_TRANS >> strip_tac >> rw[] >>
  metis_tac[]
QED

Theorem v_rel_refl:
  ∀x. v_rel c x x
Proof
  metis_tac [v_rel'_refl,v_rel_def]
QED

Theorem v_rel_sym:
  ∀x y. v_rel c x y ⇔ v_rel c y x
Proof
  metis_tac [v_rel'_sym,v_rel_def]
QED

Theorem v_rel_trans:
  ∀x y z. v_rel c x y ∧ v_rel c y z ⇒ v_rel c x z
Proof
  metis_tac [v_rel'_trans,v_rel_def]
QED

Definition isClos_def:
  isClos (Closure _ _) = T ∧ isClos _ = F
End

Theorem isClos_Lam[simp]:
  isClos (eval c (Lam v x))
Proof
  fs [eval_thm,isClos_def]
QED

Theorem isClos_thm:
  isClos x = ∃n e. x = Closure n e
Proof
  Cases_on ‘x’ \\ fs [isClos_def]
  \\ Cases_on ‘a’ \\ fs [isClos_def]
  \\ Cases_on ‘ts’ \\ fs [isClos_def]
QED

Theorem exp_rel_extend:
  ∀c x y z.
    isClos (eval c x) ∧ isClos (eval c y) ⇒
    (exp_rel c x y ⇔ ∀a. exp_rel c (App x a) (App y a))
Proof
  rw [exp_rel_def,eval_App]
  \\ Cases_on ‘~isClos (eval c y)’ \\ fs []
  \\ fs [isClos_thm]
  \\ fs [v_rel_def]
  \\ eq_tac \\ rw []
  THEN1
   (rename [‘v_rel' _ k’]
    \\ first_x_assum (qspec_then ‘SUC k’ mp_tac)
    \\ fs [v_rel'_def] \\ rw [] \\ fs [])
  \\ rename [‘v_rel' _ k’]
  \\ Cases_on ‘k’ \\ fs [v_rel'_def]
QED

Theorem exp_rel_Cons:
  exp_rel c (Cons n xs) (Cons m ys) ⇔
  n = m ∧ LIST_REL (exp_rel c) xs ys
Proof
  fs [exp_rel_def,eval_Cons,v_rel_def,LIST_REL_EL_EQN]
  \\ eq_tac \\ rw []
  THEN1 (first_x_assum (qspec_then ‘SUC 0’ mp_tac) \\ fs [v_rel'_def] \\ rw [])
  THEN1
   (first_x_assum (qspec_then ‘SUC 0’ mp_tac) \\ fs [v_rel'_def]
    \\ fs [LIST_REL_EL_EQN] \\ rw [] \\ fs [MAP_EQ_EVERY2])
  THEN1
   (rename [‘v_rel' _ k’]
    \\ first_x_assum (qspec_then ‘SUC k’ mp_tac)
    \\ fs [v_rel'_def,MAP_EQ_EVERY2]
    \\ fs [LIST_REL_EL_EQN]
    \\ Cases_on ‘LENGTH xs = LENGTH ys’ \\ fs []
    \\ Cases_on ‘m = n’ \\ fs [EL_MAP]
    \\ rw [] \\ res_tac \\ fs []
    \\ Cases_on ‘k’ \\ fs [v_rel'_def])
  \\ rename [‘v_rel' _ k’]
  \\ Cases_on ‘k’ \\ fs [v_rel'_def]
  \\ fs [LIST_REL_EL_EQN]
  \\ rfs [] \\ rw [] \\ fs [EL_MAP]
QED

Definition progress_def:
  progress c exp next =
    ∀input.
       exp_rel c (App exp input)
                 (case next input of
                  | INL final => final
                  | INR (n,x,rec_input) =>
                      Cons n [x; App exp rec_input])
End

Theorem progress_lemma:
  progress c exp1 next ∧ progress c exp2 next ∧
  isClos (eval c exp1) ∧ isClos (eval c exp2) ⇒
  exp_rel c exp1 exp2
Proof
  fs [exp_rel_extend,progress_def] \\ rw []
  \\ rw [exp_rel_def,v_rel_def]
  \\ qid_spec_tac ‘a’
  \\ completeInduct_on ‘n’ \\ fs [] \\ strip_tac
  \\ first_assum (qspec_then ‘a’ mp_tac)
  \\ last_assum (qspec_then ‘a’ mp_tac)
  \\ rewrite_tac [exp_rel_def,v_rel_def]
  \\ Cases_on ‘next a’ \\ fs []
  THEN1 metis_tac [v_rel'_trans,v_rel'_sym]
  \\ PairCases_on ‘y’ \\ fs [] \\ rw []
  \\ qsuff_tac ‘v_rel' c n
       (eval c (Cons y0 [y1; App exp1 y2]))
       (eval c (Cons y0 [y1; App exp2 y2]))’
  THEN1 metis_tac [v_rel'_trans,v_rel'_sym]
  \\ once_rewrite_tac [eval_thm] \\ rewrite_tac [MAP]
  \\ Cases_on ‘n’ \\ fs [v_rel'_def,v_rel'_refl]
QED

val _ = export_theory();
