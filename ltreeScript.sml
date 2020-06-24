
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory llistTheory alistTheory optionTheory;

val _ = new_theory "ltree";

Type ltree_rep[local] = “:num list -> 'a # num option”;

Overload NOTHING[local] = “(ARB:'a, SOME (0:num))”;

Definition Branch_rep_def:
  Branch_rep (x:'a) (xs:('a ltree_rep) llist) =
    \path. case path of
           | [] => (x, LLENGTH xs)
           | (n::rest) => case LNTH n xs of SOME t => t rest | NONE => NOTHING
End

Definition dest_Branch_rep_def:
  dest_Branch_rep (l:'a ltree_rep) =
    let (x,len) = l [] in
      (x, LGENLIST (λn path. l (n::path)) len)
End

Theorem dest_Branch_rep_Branch_rep:
  dest_Branch_rep (Branch_rep x xs) = (x,xs)
Proof
  fs [Branch_rep_def,dest_Branch_rep_def]
  \\ qspec_then ‘xs’ strip_assume_tac fromList_fromSeq \\ fs []
  \\ fs [LGENLIST_EQ_fromSeq,FUN_EQ_THM,LGENLIST_EQ_fromList]
  \\ fs [LNTH_fromList]
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM GENLIST_ID]))
  \\ fs [GENLIST_FUN_EQ,FUN_EQ_THM]
QED

Definition ltree_rep_ok_def:
  ltree_rep_ok f ⇔
    ∀path x n.
      f path = (x, SOME n) ⇒
      ∀pos rest. f (path ++ pos::rest) ≠ NOTHING ⇒ pos < n
End

Theorem type_inhabited:
  ∃f. ltree_rep_ok f
Proof
  qexists_tac ‘λp. NOTHING’ \\ fs [ltree_rep_ok_def] \\ rw []
QED

val ltree_tydef = new_type_definition ("ltree", type_inhabited);

val repabs_fns = define_new_type_bijections
  { name = "ltree_absrep",
    ABS  = "ltree_abs",
    REP  = "ltree_rep",
    tyax = ltree_tydef};

val ltree_absrep = CONJUNCT1 repabs_fns
val ltree_repabs = CONJUNCT2 repabs_fns

val ltree_rep_ok_ltree_rep = prove(
  ``ltree_rep_ok (ltree_rep f)``,
  SRW_TAC [][ltree_repabs, ltree_absrep]);
val _ = BasicProvers.augment_srw_ss [rewrites [ltree_rep_ok_ltree_rep]]

val ltree_abs_11 = prove(
  ``ltree_rep_ok r1 /\ ltree_rep_ok r2 ==> ((ltree_abs r1 = ltree_abs r2) = (r1 = r2))``,
  SRW_TAC [][ltree_repabs, EQ_IMP_THM] THEN METIS_TAC []);

val ltree_rep_11 = prove(
  ``(ltree_rep t1 = ltree_rep t2) = (t1 = t2)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  POP_ASSUM (MP_TAC o AP_TERM ``ltree_abs``) THEN SRW_TAC [][ltree_absrep]);

val ltree_repabs' = #1 (EQ_IMP_RULE (SPEC_ALL ltree_repabs))

Theorem ltree_rep_ok_Branch_rep_every:
  ltree_rep_ok (Branch_rep a ts) = every ltree_rep_ok ts
Proof
  fs [Branch_rep_def,ltree_rep_ok_def]
  \\ rw [] \\ reverse (qspec_then ‘ts’ strip_assume_tac fromList_fromSeq)
  \\ rw [ltree_rep_ok_def]
  \\ eq_tac \\ rpt strip_tac
  THEN1
   (first_x_assum (qspecl_then [‘i::path’,‘x’,‘n’] mp_tac)
    \\ fs [] \\ disch_then drule \\ fs [])
  THEN1
   (Cases_on ‘path’ \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule \\ fs [])
  \\ fs [every_fromList_EVERY,LNTH_fromList]
  THEN1
   (rw [EVERY_EL,ltree_rep_ok_def]
    \\ first_x_assum (qspec_then ‘n::path’ mp_tac) \\ fs []
    \\ disch_then drule \\ fs [])
  \\ fs [EVERY_EL,ltree_rep_ok_def]
  \\ Cases_on ‘path’ \\ fs []
  \\ rw [] \\ fs [AllCaseEqs()]
  \\ res_tac \\ fs []
QED

Theorem ltree_rep_ok_Branch_rep:
  every ltree_rep_ok ts ⇒ ltree_rep_ok (Branch_rep a ts)
Proof
  fs [ltree_rep_ok_Branch_rep_every]
QED

Theorem ltree_rep_ok_Branch_rep_IMP:
  ltree_rep_ok (Branch_rep a ts) ⇒ every ltree_rep_ok ts
Proof
  fs [ltree_rep_ok_Branch_rep_every]
QED

Theorem every_ltree_rep_ok:
  ∀ts. every ltree_rep_ok (LMAP ltree_rep ts)
Proof
  rw [] \\ qspec_then ‘ts’ strip_assume_tac fromList_fromSeq
  \\ rw [LMAP_fromList,every_fromList_EVERY,EVERY_MEM,MEM_MAP]
  \\ fs [ltree_rep_ok_ltree_rep]
QED

Theorem LMAP_ltree_rep_11:
  LMAP ltree_rep ts1 = LMAP ltree_rep ts2 ⇔ ts1 = ts2
Proof
  rw []
  \\ qspec_then ‘ts1’ strip_assume_tac fromList_fromSeq \\ rw []
  \\ qspec_then ‘ts2’ strip_assume_tac fromList_fromSeq \\ rw []
  \\ fs [LMAP_fromList]
  \\ fs [Once FUN_EQ_THM,ltree_rep_11] \\ fs [FUN_EQ_THM]
  \\ rename [‘MAP _ l1 = MAP _ l2’]
  \\ qid_spec_tac ‘l1’
  \\ qid_spec_tac ‘l2’
  \\ Induct \\ Cases_on ‘l1’ \\ fs [ltree_rep_11]
QED

Theorem Branch_rep_11:
  ∀a1 a2 ts1 ts2. Branch_rep a1 ts1 = Branch_rep a2 ts2 ⇔ a1 = a2 ∧ ts1 = ts2
Proof
  fs [Branch_rep_def,FUN_EQ_THM]
  \\ rpt gen_tac \\ eq_tac \\ simp []
  \\ strip_tac
  \\ first_assum (qspec_then ‘[]’ assume_tac) \\ fs [] \\ rw []
  \\ reverse (qspec_then ‘ts1’ strip_assume_tac fromList_fromSeq) \\ rw []
  \\ reverse (qspec_then ‘ts2’ strip_assume_tac fromList_fromSeq) \\ rw []
  \\ fs [LLENGTH_fromSeq,LLENGTH_fromList]
  THEN1
   (fs [FUN_EQ_THM] \\ rw []
    \\ first_x_assum (qspec_then ‘x::x'’ mp_tac) \\ fs [])
  \\ fs [LNTH_fromList]
  \\ fs [LIST_EQ_REWRITE] \\ rw []
  \\ rw [FUN_EQ_THM]
  \\ first_x_assum (qspec_then ‘x::x'’ mp_tac) \\ fs []
QED

Theorem Branch_rep_exists:
  ltree_rep_ok f ⇒ ∃a ts. f = Branch_rep a ts
Proof
  fs [ltree_rep_ok_def] \\ rw []
  \\ Cases_on ‘f []’ \\ fs []
  \\ rename [‘_ = (a,ts)’]
  \\ qexists_tac ‘a’
  \\ qexists_tac ‘LGENLIST (\n path. f (n::path)) ts’
  \\ fs [Branch_rep_def,FUN_EQ_THM]
  \\ Cases \\ fs [LNTH_LGENLIST]
  \\ Cases_on ‘f (h::t)’ \\ fs []
  \\ Cases_on ‘ts’ \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ first_x_assum drule \\ fs []
  \\ disch_then (qspecl_then [‘h’,‘t’] mp_tac) \\ fs []
QED

Theorem LMAP_ltree_rep_ltree_abs:
  every ltree_rep_ok ts ⇒
  LMAP ltree_rep (LMAP ltree_abs ts) = ts
Proof
  rw [] \\ qspec_then ‘ts’ strip_assume_tac fromList_fromSeq
  \\ fs [LMAP_fromList,every_fromList_EVERY,MEM_MAP,
         LMAP_fromList,MAP_MAP_o]
  \\ rw [ltree_repabs,FUN_EQ_THM] \\ fs [ltree_repabs]
  \\ Induct_on ‘l’ \\ fs [ltree_repabs]
QED

val Branch = new_definition("Branch",
  “Branch a ts = ltree_abs (Branch_rep a (LMAP ltree_rep ts))”);

Theorem ltree_cases:
  ∀t. ∃a ts. t = Branch a ts
Proof
  fs [Branch] \\ fs [GSYM ltree_rep_11] \\ rw []
  \\ qspec_then ‘ts1’ assume_tac every_ltree_rep_ok
  \\ qabbrev_tac ‘f = ltree_rep t’
  \\ ‘ltree_rep_ok f’ by fs [Abbr‘f’]
  \\ drule Branch_rep_exists \\ rw []
  \\ qexists_tac ‘a’ \\ qexists_tac ‘LMAP ltree_abs ts’
  \\ imp_res_tac ltree_rep_ok_Branch_rep_IMP
  \\ fs [LMAP_ltree_rep_ltree_abs,ltree_repabs]
QED

Theorem Branch_11:
  ∀a1 a2 ts1 ts2. Branch a1 ts1 = Branch a2 ts2 ⇔ a1 = a2 ∧ ts1 = ts2
Proof
  rw [Branch] \\ eq_tac \\ strip_tac \\ fs []
  \\ qspec_then ‘ts1’ assume_tac every_ltree_rep_ok
  \\ drule ltree_rep_ok_Branch_rep
  \\ qspec_then ‘ts2’ assume_tac every_ltree_rep_ok
  \\ drule ltree_rep_ok_Branch_rep
  \\ strip_tac \\ strip_tac
  \\ fs [ltree_abs_11]
  \\ fs [LMAP_ltree_rep_11,Branch_rep_11]
QED

Definition ltree_CASE[nocompute]:
  ltree_CASE t f =
    let (a,ts) = dest_Branch_rep (ltree_rep t) in
      f a (LMAP ltree_abs ts)
End

Theorem ltree_CASE[compute]:
  ltree_CASE (Branch a ts) f = f a ts
Proof
  fs [ltree_CASE,Branch]
  \\ qspec_then ‘ts’ assume_tac every_ltree_rep_ok
  \\ drule ltree_rep_ok_Branch_rep
  \\ fs [ltree_repabs,dest_Branch_rep_Branch_rep]
  \\ fs [LMAP_MAP] \\ rw [] \\ AP_TERM_TAC
  \\ qspec_then ‘ts’ strip_assume_tac fromList_fromSeq
  \\ fs [LMAP_fromList,LMAP_fromSeq,FUN_EQ_THM,ltree_absrep]
  \\ rpt (pop_assum kall_tac)
  \\ Induct_on ‘l’ \\ fs [ltree_absrep]
QED

Theorem list_CASE_eq:
  ltree_CASE t f = v' ⇔ ∃a ts. t = Branch a ts ∧ f a ts = v'
Proof
  qspec_then ‘t’ strip_assume_tac ltree_cases \\ rw []
  \\ fs [Branch_11,ltree_CASE]
QED

Definition path_ok_def:
  path_ok path f ⇔
    ∀xs n ys k a.
      path = xs ++ n::ys ∧ f xs = (a,SOME k) ⇒ n < k
End

Definition make_ltree_rep_def:
  make_ltree_rep f =
    λpath. if path_ok path f then f path else NOTHING
End

Theorem ltree_rep_ok_make_ltree_rep:
  ∀f. ltree_rep_ok (make_ltree_rep f)
Proof
  fs [ltree_rep_ok_def,make_ltree_rep_def] \\ rw []
  THEN1
   (fs [AllCaseEqs()] \\ fs []
    \\ fs [path_ok_def] \\ metis_tac [])
  \\ fs [AllCaseEqs()] \\ fs []
  \\ CCONTR_TAC \\ fs [] \\ fs []
  \\ fs [path_ok_def] \\ rw []
  \\ first_x_assum (qspecl_then [‘xs’,‘n’,‘ys ⧺ pos::rest’] mp_tac)
  \\ fs []
QED

Definition gen_ltree_def[nocompute]:
  gen_ltree f = ltree_abs (make_ltree_rep f)
End

Theorem gen_ltree:
  gen_ltree f =
    let (a,len) = f [] in
      Branch a (LGENLIST (λn. gen_ltree (λpath. f (n::path))) len)
Proof
  fs [pairTheory.UNCURRY,gen_ltree_def,Branch]
  \\ fs [combinTheory.o_DEF]
  \\ qspec_then ‘f’ assume_tac ltree_rep_ok_make_ltree_rep
  \\ fs [REWRITE_RULE [ltree_rep_ok_make_ltree_rep]
          (Q.SPEC ‘make_ltree_rep f’ ltree_repabs)]
  \\ AP_TERM_TAC \\ Cases_on ‘f []’ \\ fs []
  \\ fs [Branch_rep_def,FUN_EQ_THM]
  \\ Cases \\ fs []
  THEN1 fs [make_ltree_rep_def,path_ok_def]
  \\ Cases_on ‘r’ \\ fs []
  \\ fs [LNTH_LGENLIST]
  THEN1
   (fs [make_ltree_rep_def]
    \\ AP_THM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ fs [path_ok_def]
    \\ rw [] \\ eq_tac \\ rw []
    THEN1
     (first_x_assum match_mp_tac
      \\ goal_assum (first_assum o mp_then.mp_then mp_then.Any mp_tac)
      \\ qexists_tac ‘ys’ \\ fs [])
    \\ Cases_on ‘xs’ \\ fs [] \\ rw []
    \\ metis_tac [])
  \\ fs [make_ltree_rep_def]
  \\ reverse (Cases_on ‘h < x’) \\ fs []
  THEN1 (rw [] \\ fs [path_ok_def] \\ metis_tac [APPEND])
  \\ AP_THM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ fs [path_ok_def]
  \\ rw [] \\ eq_tac \\ rw []
  THEN1
   (first_x_assum match_mp_tac
    \\ goal_assum (first_assum o mp_then.mp_then mp_then.Any mp_tac)
    \\ qexists_tac ‘ys’ \\ fs [])
  \\ Cases_on ‘xs’ \\ fs [] \\ rw []
  \\ metis_tac []
QED

Definition make_unfold_def:
  make_unfold f seed [] =
    (let (a,seeds) = f seed in (a,LLENGTH seeds)) ∧
  make_unfold f seed (n::path) =
    let (a,seeds) = f seed in
       make_unfold f (THE (LNTH n seeds)) path
End

Definition unfold_ltree_def:
  unfold_ltree f seed =
    gen_ltree (make_unfold f seed)
End

Theorem unfold_ltree:
  unfold_ltree f seed =
    let (a,seeds) = f seed in
      Branch a (LMAP (unfold_ltree f) seeds)
Proof
  fs [unfold_ltree_def]
  \\ once_rewrite_tac [gen_ltree]
  \\ simp [Once make_unfold_def]
  \\ Cases_on ‘f seed’
  \\ fs [Branch_11]
  \\ reverse (qspec_then ‘r’ strip_assume_tac fromList_fromSeq)
  \\ fs [LGENLIST_EQ_fromSeq]
  THEN1
   (fs [FUN_EQ_THM,unfold_ltree_def] \\ rw []
    \\ AP_TERM_TAC \\ fs [FUN_EQ_THM] \\ rw []
    \\ fs [make_unfold_def])
  \\ fs [LGENLIST_EQ_fromList,LMAP_fromList]
  \\ fs [LIST_EQ_REWRITE,EL_MAP] \\ rw []
  \\ rw [unfold_ltree_def] \\ rw []
  \\ AP_TERM_TAC \\ fs [FUN_EQ_THM] \\ rw []
  \\ fs [make_unfold_def,LNTH_fromList]
QED

Theorem gen_ltree_LNIL:
  gen_ltree f = Branch a LNIL ⇔ f [] = (a, SOME 0)
Proof
  simp [Once gen_ltree,pairTheory.UNCURRY]
  \\ Cases_on ‘f []’ \\ fs [Branch_11]
QED

val _ = TypeBase.export
  [TypeBasePure.mk_datatype_info
    {
     ax = TypeBasePure.ORIG TRUTH,
     induction = TypeBasePure.ORIG TRUTH,
     case_def = ltree_CASE,
     case_cong = TRUTH,
     case_eq = list_CASE_eq,
     nchotomy = ltree_cases,
     size = NONE,
     encode = NONE,
     lift = NONE,
     one_one = SOME Branch_11,
     distinct = NONE,
     fields = [],
     accessors = [],
     updates = [],
     destructors = [],
     recognizers = []
    }
  ]

val _ = export_theory();
