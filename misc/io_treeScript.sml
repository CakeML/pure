(*
  This file defines a type for potentially infinite interaction
  trees. We take inspiration from the itree type of Xia et al.'s
  POPL'20 paper titled "Interaction Trees".

  Interaction trees are interesting because they can both represent a
  program's observable I/O behaviour and also model of the I/O
  behaviour of the external world.

  Our version of the type for interaction trees, io, has the following
  constructors.  Here Ret ends an interaction tree with a return
  value; Div is internal silent divergence (an infinite run of Taus);
  Vis is a visible event that returns a value that the rest of the
  interaction tree can depend on.

    ('a,'e,'r) io  =
       Ret 'r                        --  termination with result 'r
    |  Div                           --  end in silent divergence
    |  Vis 'e ('a -> ('a,'e,'r) io)  --  visible event 'e with answer 'a,
                                         then continue based on answer

  The POPL paper includes a silent Tau action:

    |  Tau (('a,'e,'r) io)           --  a silent action, then continue

  We omit Tau since it makes reasoning about intereaction trees
  messy. It causes a mess because one then has to deal with equality
  up to deletion of finite runs of Tau actions, ugh. We model an
  infinite run of Taus using Div.

*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open arithmeticTheory listTheory llistTheory alistTheory optionTheory;
open mp_then pred_setTheory relationTheory pairTheory combinTheory;

val _ = new_theory "io_tree";


(* make type definition *)

Datatype:
  io_el = Event 'e | Return 'r | Stuck
End

Type io_rep[local] = ``:'a list -> ('e,'r) io_el``;
val f = ``(f: ('a,'e,'r) io_rep)``

Definition path_ok_def:
  path_ok path ^f <=>
    !xs y ys.
      path = xs ++ y::ys ==>
      f xs ≠ Stuck ∧ ∀z. f xs ≠ Return z (* a path cannot continue past a Stuck/Return *)
End

Definition io_rep_ok_def:
  io_rep_ok ^f <=>
    (* every bad path leads to the Return ARB element *)
    !path. ~path_ok path f ==> f path = Return ARB
End

Theorem type_inhabited[local]:
  ?f. io_rep_ok ^f
Proof
  qexists_tac `\p. Return ARB` \\ fs [io_rep_ok_def]
QED

val io_tydef = new_type_definition ("io", type_inhabited);

val repabs_fns = define_new_type_bijections
  { name = "io_absrep",
    ABS  = "io_abs",
    REP  = "io_rep",
    tyax = io_tydef};


(* prove basic theorems about rep and abs fucntions *)

val io_absrep = CONJUNCT1 repabs_fns
val io_repabs = CONJUNCT2 repabs_fns

Theorem io_rep_ok_io_rep[local,simp]:
  !t. io_rep_ok (io_rep t)
Proof
  fs [io_repabs, io_absrep]
QED

Theorem io_abs_11[local]:
  io_rep_ok r1 /\ io_rep_ok r2 ==> ((io_abs r1 = io_abs r2) = (r1 = r2))
Proof
  fs [io_repabs, EQ_IMP_THM] \\ metis_tac []
QED

Theorem io_rep_11[local]:
  (io_rep t1 = io_rep t2) = (t1 = t2)
Proof
  fs [EQ_IMP_THM] \\ metis_tac [io_absrep]
QED


(* define constructors *)

Definition Ret_rep_def:
  Ret_rep (x:'r) =
    \path. if path = [] then Return x else Return ARB
End

Definition Div_rep_def:
  Div_rep =
    \path. if path = [] then Stuck else Return ARB
End

Definition Vis_rep_def:
  Vis_rep e g =
    \path. case path of
           | [] => Event e
           | (a::rest) => g a rest
End

Definition Ret_def:
  Ret x = io_abs (Ret_rep x)
End

Definition Div_def:
  Div = io_abs Div_rep
End

Definition Vis_def:
  Vis e g = io_abs (Vis_rep e (io_rep o g))
End

Theorem io_rep_ok_Ret[local]:
  !x. io_rep_ok (Ret_rep x : ('a,'b,'c) io_rep)
Proof
  fs [io_rep_ok_def,Ret_rep_def]
  \\ rw [] \\ fs [path_ok_def]
QED

Theorem io_rep_ok_Div[local]:
  io_rep_ok (Div_rep : ('a,'b,'c) io_rep)
Proof
  fs [io_rep_ok_def,Div_rep_def]
  \\ rw [] \\ fs [path_ok_def]
QED

Theorem io_rep_ok_Vis[local]:
  !a g. (!a. io_rep_ok (g a)) ==> io_rep_ok (Vis_rep e g  : ('a,'b,'c) io_rep)
Proof
  fs [io_rep_ok_def,Vis_rep_def]
  \\ rw [] \\ CCONTR_TAC \\ fs [AllCaseEqs()]
  \\ Cases_on `path` \\ fs [] THEN1 fs [path_ok_def]
  \\ qpat_x_assum `~(path_ok _ _)` mp_tac \\ fs []
  \\ simp [path_ok_def] \\ rw []
  \\ Cases_on `path` \\ fs [] \\ rw []
  \\ CCONTR_TAC \\ fs []
  \\ rename [`xs ++ [y] ++ ys`] \\ fs []
  \\ first_x_assum (qspecl_then [`h`,`xs ⧺ [y] ⧺ ys`] mp_tac)
  \\ fs [] \\ rw [] \\ fs [path_ok_def]
  \\ metis_tac []
QED


(* prove injectivity *)

Theorem Ret_rep_11[local]:
  !x y. Ret_rep x = Ret_rep y <=> x = y
Proof
  fs [Ret_rep_def,FUN_EQ_THM]
  \\ rpt gen_tac \\ eq_tac \\ rw []
  \\ first_x_assum (qspec_then `[]` mp_tac) \\ fs []
QED

Theorem Ret_11:
  !x y. Ret x = Ret y <=> x = y
Proof
  rw [Ret_def] \\ eq_tac \\ strip_tac \\ fs []
  \\ metis_tac [io_rep_ok_Ret,io_abs_11,Ret_rep_11]
QED

Theorem Vis_rep_11[local]:
  !x y g g'. Vis_rep x g = Vis_rep y g' <=> x = y /\ g = g'
Proof
  fs [Vis_rep_def,Once FUN_EQ_THM]
  \\ rpt gen_tac \\ eq_tac \\ simp [] \\ strip_tac
  \\ first_assum (qspec_then `[]` assume_tac) \\ fs []
  \\ fs [FUN_EQ_THM] \\ rw []
  \\ rename [`g x1 x2 = _`]
  \\ first_x_assum (qspec_then `x1 :: x2` mp_tac) \\ fs []
QED

Theorem Vis_11:
  !x f y g. Vis x f = Vis y g <=> x = y /\ f = g
Proof
  rw [Vis_def] \\ eq_tac \\ strip_tac \\ fs []
  \\ qmatch_asmsub_abbrev_tac `_ x1 = _ x2`
  \\ `io_rep_ok x1 /\ io_rep_ok x2` by
      (unabbrev_all_tac \\ rw [] \\ match_mp_tac io_rep_ok_Vis \\ fs [])
  \\ fs [io_abs_11] \\ unabbrev_all_tac \\ fs [Vis_rep_11]
  \\ fs [FUN_EQ_THM,io_rep_11]
  \\ fs [GSYM io_rep_11] \\ fs [FUN_EQ_THM]
QED

Theorem io_11 = LIST_CONJ [Ret_11, Vis_11];


(* distinctness theorem *)

Theorem io_all_distinct[local]:
  !x e g. ALL_DISTINCT [Ret x; Div; Vis e g :('a,'b,'c) io]
Proof
  rw [Ret_def,Div_def,Vis_def]
  \\ assume_tac io_rep_ok_Div
  \\ qspec_then `x` assume_tac io_rep_ok_Ret
  \\ qspec_then `t` assume_tac io_rep_ok_io_rep
  \\ qspecl_then [`e`,`io_rep o g`] mp_tac io_rep_ok_Vis
  \\ impl_tac THEN1 fs []
  \\ rw [] \\ simp [io_abs_11]
  \\ rw [] \\ fs [FUN_EQ_THM]
  \\ qexists_tac `[]` \\ fs [Ret_rep_def,Div_rep_def,Vis_rep_def]
QED

Theorem io_distinct = io_all_distinct
  |> SIMP_RULE std_ss [ALL_DISTINCT,MEM,GSYM CONJ_ASSOC] |> SPEC_ALL;


(* prove cases theorem *)

Theorem rep_exists[local]:
  io_rep_ok f ⇒
    (∃x. f = Ret_rep x) ∨
    (f = Div_rep) ∨
    ∃a g. f = Vis_rep a g ∧ ∀v. io_rep_ok (g v)
Proof
  fs [io_rep_ok_def] \\ rw []
  \\ reverse (Cases_on `f []`)
  THEN1
   (disj2_tac \\ disj1_tac
    \\ fs [FUN_EQ_THM]
    \\ Cases \\ fs [Div_rep_def]
    \\ first_x_assum match_mp_tac
    \\ fs [path_ok_def]
    \\ qexists_tac `[]` \\ fs [])
  THEN1
   (disj1_tac
    \\ qexists_tac ‘r’ \\ fs []
    \\ fs [FUN_EQ_THM]
    \\ Cases \\ fs [Ret_rep_def]
    \\ first_x_assum match_mp_tac
    \\ fs [path_ok_def]
    \\ qexists_tac `[]` \\ fs [])
  \\ rpt disj2_tac
  \\ fs [Vis_rep_def,FUN_EQ_THM]
  \\ qexists_tac `e`
  \\ qexists_tac `\a path. f (a::path)`
  \\ rw [] THEN1 (Cases_on `x` \\ fs [])
  \\ first_x_assum match_mp_tac
  \\ fs [path_ok_def]
  \\ metis_tac [APPEND,APPEND_ASSOC]
QED

Theorem io_cases:
  ∀t. (∃x. t = Ret x) ∨ (t = Div) ∨ (∃a g. t = Vis a g)
Proof
  fs [GSYM io_rep_11,Ret_def,Div_def,Vis_def] \\ gen_tac
  \\ qabbrev_tac `f = io_rep t`
  \\ `io_rep_ok f` by fs [Abbr`f`]
  \\ drule rep_exists \\ strip_tac \\ fs [] \\ rw []
  \\ imp_res_tac io_repabs \\ fs []
  THEN1 metis_tac []
  \\ rpt disj2_tac
  \\ qexists_tac `a`
  \\ qexists_tac `io_abs o g`
  \\ qsuff_tac `io_rep o io_abs o g = g` THEN1 fs []
  \\ fs [o_DEF,Once FUN_EQ_THM]
  \\ metis_tac [io_repabs]
QED


(* io_CASE constant *)

Definition io_CASE[nocompute]:
  io_CASE (t:('a,'e,'r) io) ret div vis =
    case io_rep t [] of
    | Return r => ret r
    | Stuck    => div
    | Event e  => vis e (\a. (io_abs (\path. io_rep t (a::path))))
End

Theorem io_CASE[compute]:
  io_CASE (Ret r)   ret div vis = ret r ∧
  io_CASE Div       ret div vis = div ∧
  io_CASE (Vis a g) ret div vis = vis a g
Proof
  rw [io_CASE,Ret_def,Div_def,Vis_def]
  \\ qmatch_goalsub_abbrev_tac `io_rep (io_abs xx)`
  THEN1
   (`io_rep_ok xx` by fs [Abbr`xx`,io_rep_ok_Ret]
    \\ fs [io_repabs] \\ unabbrev_all_tac
    \\ fs [Ret_rep_def])
  THEN1
   (`io_rep_ok xx` by fs [Abbr`xx`,io_rep_ok_Div]
    \\ fs [io_repabs] \\ unabbrev_all_tac
    \\ fs [Div_rep_def])
  THEN1
   (`io_rep_ok xx` by
      (fs [Abbr`xx`] \\ match_mp_tac io_rep_ok_Vis \\ fs [])
    \\ fs [io_repabs] \\ unabbrev_all_tac
    \\ fs [Vis_rep_def]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [io_absrep]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
QED

Theorem io_CASE_eq:
  io_CASE t ret div vis = v ⇔
    (∃r. t = Ret r ∧ ret r = v) ∨
    (t = Div ∧ div = v) ∨
    (∃a g. t = Vis a g ∧ vis a g = v)
Proof
  qspec_then `t` strip_assume_tac io_cases \\ rw []
  \\ fs [io_CASE,io_11,io_distinct]
QED


(* io unfold *)

Datatype:
  io_next = Ret' 'r
          | Div'
          | Vis' 'e ('a -> 'seed)
End

Definition io_unfold_path_def:
  (io_unfold_path f seed [] =
     case f seed of
     | Ret' r   => Return r
     | Div'     => Stuck
     | Vis' e g => Event e) /\
  (io_unfold_path f seed (n::rest) =
     case f seed of
     | Ret' r   => Return ARB
     | Div'     => Return ARB
     | Vis' e g => io_unfold_path f (g n) rest)
End

Definition io_unfold:
  io_unfold f seed = io_abs (io_unfold_path f seed)
End

Theorem io_rep_abs_io_unfold_path[local]:
  io_rep (io_abs (io_unfold_path f s)) = io_unfold_path f s
Proof
  fs [GSYM io_repabs] \\ fs [io_rep_ok_def]
  \\ qid_spec_tac `s`
  \\ Induct_on `path` THEN1 fs [path_ok_def]
  \\ fs [io_unfold_path_def]
  \\ rw [] \\ Cases_on `f s` \\ fs [] \\ rw []
  \\ first_x_assum match_mp_tac
  \\ fs [path_ok_def]
  \\ Cases_on `xs` \\ fs [] \\ rw []
  \\ fs [io_unfold_path_def] \\ metis_tac []
QED

Theorem io_unfold:
  io_unfold f seed =
    case f seed of
    | Ret' r   => Ret r
    | Div'     => Div
    | Vis' e g => Vis e (io_unfold f o g)
Proof
  Cases_on `f seed` \\ fs []
  THEN1
   (fs [io_unfold,Ret_def] \\ AP_TERM_TAC \\ fs [FUN_EQ_THM]
    \\ Cases \\ fs [io_unfold_path_def,Ret_rep_def]
    \\ Cases_on `h` \\ fs [io_unfold_path_def,Ret_rep_def])
  THEN1
   (fs [io_unfold,Div_def] \\ AP_TERM_TAC \\ fs [FUN_EQ_THM]
    \\ Cases \\ fs [io_unfold_path_def,Div_rep_def]
    \\ Cases_on `h` \\ fs [io_unfold_path_def,Div_rep_def])
  \\ fs [io_unfold,Vis_def] \\ AP_TERM_TAC \\ fs [FUN_EQ_THM]
  \\ Cases \\ fs [io_unfold_path_def,Vis_rep_def]
  \\ fs [io_unfold_path_def,Vis_rep_def]
  \\ fs [io_unfold,io_rep_abs_io_unfold_path]
QED


(* io_unfold with errors - i.e. the environment can return an error *)

Definition io_unfold_err_path_def:
  (io_unfold_err_path f (rel, err_f, err) seed [] =
     case f seed of
     | Ret' r   => Return r
     | Div'     => Stuck
     | Vis' e g => Event e) ∧
  (io_unfold_err_path f (rel, err_f, err) seed (n::rest) =
     case f seed of
     | Ret' r   => Return ARB
     | Div'     => Return ARB
     | Vis' e g =>
        case n of
        | INL x => if rest = [] then Return (err_f e x) else Return ARB
        | INR y =>
            if rel e y then io_unfold_err_path f (rel, err_f, err) (g y) rest
            else if rest = [] then Return $ err e else Return ARB)
End

Definition io_unfold_err:
  io_unfold_err f err seed =
    io_abs (io_unfold_err_path f err seed)
End

Theorem io_rep_abs_io_unfold_err_path[local]:
  io_rep (io_abs (io_unfold_err_path f err s)) =
  io_unfold_err_path f err s
Proof
  gvs[GSYM io_repabs, io_rep_ok_def] >>
  qid_spec_tac `s` >> Induct_on `path` >- gvs[path_ok_def] >>
  PairCases_on `err` >> gvs[io_unfold_err_path_def] >> rw[] >>
  TOP_CASE_TAC >> fs []
  >- gvs[path_ok_def, APPEND_EQ_CONS, io_unfold_err_path_def] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  first_x_assum irule >>
  gvs [path_ok_def] >>
  gvs[path_ok_def, APPEND_EQ_CONS, io_unfold_err_path_def] >>
  metis_tac []
QED

Theorem io_unfold_err:
  io_unfold_err f (rel, err_f, err) seed =
    case f seed of
    | Ret' r   => Ret r
    | Div'     => Div
    | Vis' e g =>
        Vis e
          (λa. case a of
                  INL x => Ret $ err_f e x
                | INR y =>
                    if rel e y then io_unfold_err f (rel, err_f, err) (g y)
                    else Ret $ err e)
Proof
  CASE_TAC >> once_rewrite_tac [io_unfold_err] >>
  gvs[Ret_def, Div_def, Vis_def] >> AP_TERM_TAC >> simp[FUN_EQ_THM] >>
  Cases >> gvs[io_unfold_err_path_def, Ret_rep_def, Div_rep_def, Vis_rep_def] >>
  rpt TOP_CASE_TAC >> gvs[io_rep_abs_io_unfold_err_path] >>
  once_rewrite_tac [io_unfold_err] >> gvs [] >>
  once_rewrite_tac [GSYM io_unfold_err] >> gvs [] >>
  gvs[Ret_def, Div_def, Vis_def, Ret_rep_def, Div_rep_def, Vis_rep_def] >>
  DEP_REWRITE_TAC[iffLR io_repabs] >> simp[] >>
  gvs[io_rep_ok_def, path_ok_def, PULL_EXISTS]
QED


(* proving equivalences *)

Definition io_el_def:
  io_el t [] =
    io_CASE t (\r. Return r) Stuck (\e g. Event e) /\
  io_el t (a::ns) =
    io_CASE t (\r. Return ARB) (Return ARB) (\e g. io_el (g a) ns)
End

Theorem io_el_def:
  io_el (Ret r) []   = Return r /\
  io_el Div []       = Stuck /\
  io_el (Vis e g) [] = Event e /\
  io_el (Ret r) (a::ns)   = Return ARB /\
  io_el Div (a::ns)       = Return ARB /\
  io_el (Vis e g) (a::ns) = io_el (g a) ns
Proof
  fs [io_el_def,io_CASE]
QED

Theorem io_el_eqv:
  !t1 t2. t1 = t2 <=> !path. io_el t1 path = io_el t2 path
Proof
  rw [] \\ eq_tac \\ rw []
  \\ fs [GSYM io_rep_11,FUN_EQ_THM] \\ rw []
  \\ pop_assum mp_tac
  \\ qid_spec_tac `t1` \\ qid_spec_tac `t2`
  \\ Induct_on `x` \\ rw []
  \\ `io_rep_ok (io_rep t1) /\ io_rep_ok (io_rep t2)`
        by fs [io_rep_ok_io_rep]
  \\ qspec_then `t1` strip_assume_tac io_cases
  \\ qspec_then `t2` strip_assume_tac io_cases
  \\ rpt BasicProvers.var_eq_tac
  \\ TRY (first_x_assum (qspec_then `[]` mp_tac)
          \\ fs [io_el_def] \\ NO_TAC)
  \\ first_assum (qspec_then `[]` mp_tac)
  \\ rewrite_tac [io_el_def] \\ rw []
  \\ fs [Vis_def]
  \\ qmatch_abbrev_tac
      `io_rep (io_abs t1) _ = io_rep (io_abs t2) _`
  \\ `io_rep_ok t1 /\ io_rep_ok t2` by
   (rw [] \\ unabbrev_all_tac
    \\ TRY (match_mp_tac io_rep_ok_Vis) \\ fs [])
  \\ fs [io_repabs]
  \\ TRY (unabbrev_all_tac \\ fs [Vis_rep_def] \\ NO_TAC)
  \\ unabbrev_all_tac \\ fs [GSYM Vis_def]
  \\ fs [Vis_rep_def] \\ fs []
  \\ first_x_assum (qspecl_then [`g h`,`g' h`] mp_tac)
  \\ impl_tac THEN1
   (rw [] \\ first_x_assum (qspec_then `h::path` mp_tac) \\ fs [io_el_def])
  \\ fs [Vis_rep_def]
QED

Theorem io_bisimulation:
  ∀t1 t2.
    t1 = t2 <=>
    ∃R. R t1 t2 /\
        (∀x t. R (Ret x) t ==> t = Ret x) /\
        (∀t. R Div t ==> t = Div) /\
        (∀a f t. R (Vis a f) t ==> ∃b g. t = Vis a g /\ ∀s. R (f s) (g s))
Proof
  rw [] \\ eq_tac \\ rw []
  THEN1 (qexists_tac `(=)` \\ fs [io_11])
  \\ simp [io_el_eqv] \\ strip_tac
  \\ last_x_assum mp_tac \\ qid_spec_tac `t1` \\ qid_spec_tac `t2`
  \\ Induct_on `path` \\ rw []
  \\ qspec_then `t1` strip_assume_tac io_cases
  \\ qspec_then `t2` strip_assume_tac io_cases
  \\ fs [io_el_def]
  \\ res_tac \\ fs [io_11,io_distinct] \\ rw []
  \\ Cases_on `h` \\ fs [io_el_def]
QED


(* register with TypeBase *)

Theorem io_CASE_cong:
  ∀M M' ret div vis ret' div' vis'.
    M = M' /\
    (∀x. M' = Ret x ==> ret x = ret' x) /\
    (M' = Div ==> div = div') /\
    (∀a g. M' = Vis a g ==> vis a g = vis' a g) ==>
    io_CASE M ret div vis = io_CASE M' ret' div' vis'
Proof
  rw [] \\ qspec_then `M` strip_assume_tac io_cases
  \\ rw [] \\ fs [io_CASE]
QED

Theorem datatype_io:
  DATATYPE ((io
    (Ret : 'r -> ('a, 'e, 'r) io)
    (Div : ('a, 'e, 'r) io)
    (Vis : 'e -> ('a -> ('a, 'e, 'r) io) -> ('a, 'e, 'r) io)):bool)
Proof
  rw [boolTheory.DATATYPE_TAG_THM]
QED

val _ = TypeBase.export
  [TypeBasePure.mk_datatype_info
    { ax = TypeBasePure.ORIG TRUTH,
      induction = TypeBasePure.ORIG io_bisimulation,
      case_def = io_CASE,
      case_cong = io_CASE_cong,
      case_eq = io_CASE_eq,
      nchotomy = io_cases,
      size = NONE,
      encode = NONE,
      lift = NONE,
      one_one = SOME io_11,
      distinct = NONE,
      fields = [],
      accessors = [],
      updates = [],
      destructors = [],
      recognizers = [] } ]


(* tidy up theory exports *)

val _ = List.app Theory.delete_binding
  ["Ret_rep_def", "Ret_def",
   "Div_rep_def", "Div_def",
   "Vis_rep_def", "Vis_def",
   "path_ok_def", "io_rep_ok_def",
   "io_unfold_path_def", "io_unfold_path_ind",
   "io_unfold_err_path_def", "io_unfold_err_path_ind",
   "io_el_TY_DEF", "io_absrep", "io_next_TY_DEF"];

val _ = export_theory();
