
Theory pure_value
Ancestors
  arithmetic list mlstring alist option ltree llist quotient_llist
  pure_config pure_exp pure_misc
Libs
  term_tactic

Datatype:
  v_prefix = Atom' lit
           | Constructor' mlstring
           | Closure' vname exp
           | Diverge'
           | Error'
End

Definition v_rep_ok_def:
  v_rep_ok v ⇔
    ∀a ts.
      Branch a ts ∈ subtrees v ⇒
        case a of
          Constructor' s => LFINITE ts
        | _ => ts = LNIL
End

Theorem v_inhabited[local]:
  ∃f. v_rep_ok f
Proof
  qexists_tac ‘Branch Error' LNIL’
  \\ simp [v_rep_ok_def, subtrees]
QED

val v_tydef = new_type_definition ("v", v_inhabited);

val repabs_fns = define_new_type_bijections
  {name = "v_absrep",
   ABS  = "v_abs",
   REP  = "v_rep",
   tyax = v_tydef};

val v_absrep = CONJUNCT1 repabs_fns;
val v_repabs = CONJUNCT2 repabs_fns;

Theorem v_rep_ok_v_rep[local,simp]:
  ∀v. v_rep_ok (v_rep v)
Proof
  rw [v_repabs, v_absrep]
QED

Theorem v_abs_11[local]:
  v_rep_ok v1 ∧ v_rep_ok v2 ⇒
    (v_abs v1 = v_abs v2) = (v1 = v2)
Proof
  rw [v_repabs, EQ_IMP_THM] \\ fs []
QED

Theorem v_rep_11[local]:
  (v_rep v1 = v_rep v2) = (v1 = v2)
Proof
  metis_tac [v_absrep]
QED

(*
 * Define constructors.
 *)

Definition Atom_rep_def:
  Atom_rep = λb. Branch (Atom' b) LNIL
End

Definition Constructor_rep_def:
  Constructor_rep = λs ts. Branch (Constructor' s) (fromList ts)
End

Definition Closure_rep_def:
  Closure_rep = λs x. Branch (Closure' s x) LNIL
End

Definition Diverge_rep_def:
  Diverge_rep = Branch Diverge' LNIL
End

Definition Error_rep_def:
  Error_rep = Branch Error' LNIL
End

Definition Atom_def:
  Atom b = v_abs (Atom_rep b)
End

Definition Constructor_def:
  Constructor s ts = v_abs (Constructor_rep s (MAP v_rep ts))
End

Definition Closure_def:
  Closure s x = v_abs (Closure_rep s x)
End

Definition Diverge_def:
  Diverge = v_abs Diverge_rep
End

Definition Error_def:
  Error = v_abs Error_rep
End

Theorem v_rep_ok_Atom[local]:
  ∀b. v_rep_ok (Atom_rep b)
Proof
  rw [Atom_rep_def, v_rep_ok_def, subtrees]
QED

Theorem v_rep_ok_Constructor[local]:
  ∀s ts. v_rep_ok (Constructor_rep s (MAP v_rep ts))
Proof
  rw [v_rep_ok_def]
  \\ fs [subtrees, Constructor_rep_def, LFINITE_fromList]
  \\ ‘v_rep_ok x’
    by fs [LSET_fromList, MEM_MAP]
  \\ fs [v_rep_ok_def]
QED

Theorem v_rep_ok_Closure[local]:
  ∀s x. v_rep_ok (Closure_rep s x)
Proof
  rw [Closure_rep_def, v_rep_ok_def, subtrees]
QED

Theorem v_rep_ok_Diverge[local]:
  v_rep_ok Diverge_rep
Proof
  rw [Diverge_rep_def, v_rep_ok_def, subtrees]
QED

Theorem v_rep_ok_Error[local]:
  v_rep_ok Error_rep
Proof
  rw [Error_rep_def, v_rep_ok_def, subtrees]
QED

(*
 * Prove one-one theorems for constructors.
 *)

Theorem Atom_rep_11[local]:
  ∀x y. Atom_rep x = Atom_rep y ⇔ x = y
Proof
  rw [Atom_rep_def]
QED

Theorem Constructor_rep_11[local]:
  ∀s1 t1 s2 t2.
    Constructor_rep s1 t1 = Constructor_rep s2 t2 ⇔ s1 = s2 ∧ t1 = t2
Proof
  rw [Constructor_rep_def]
QED

Theorem Closure_rep_11[local]:
  ∀n1 x1 n2 x2.
    Closure_rep n1 x1 = Closure_rep n2 x2 ⇔ n1 = n2 ∧ x1 = x2
Proof
  rw [Closure_rep_def]
QED

Theorem Atom_11:
  ∀x y. Atom x = Atom y ⇔ x = y
Proof
  rw [Atom_def, v_rep_ok_Atom, Atom_rep_11, v_abs_11]
QED

Theorem Constructor_11:
  ∀s1 t1 s2 t2.
    Constructor s1 t1 = Constructor s2 t2 ⇔ s1 = s2 ∧ t1 = t2
Proof
  rw [Constructor_def]
  \\ eq_tac \\ strip_tac \\ fs []
  \\ qmatch_asmsub_abbrev_tac ‘_ x1 = _ x2’
  \\ ‘v_rep_ok x1 ∧ v_rep_ok x2’
    by (unabbrev_all_tac \\ rw []
        \\ irule v_rep_ok_Constructor)
  \\ unabbrev_all_tac
  \\ fs [v_abs_11, Constructor_rep_11]
  \\ ‘INJ v_rep (set t1 ∪ set t2) 𝕌(:v_prefix ltree)’
    by simp [pred_setTheory.INJ_DEF, v_rep_11]
  \\ drule INJ_MAP_EQ \\ fs []
QED

Theorem Closure_11:
  ∀n1 x1 n2 x2.
    Closure n1 x1 = Closure n2 x2 ⇔ n1 = n2 ∧ x1 = x2
Proof
  rw [Closure_def, v_rep_ok_Closure, Closure_rep_11, v_abs_11]
QED

Theorem v_11 = LIST_CONJ [Atom_11, Closure_11, Constructor_11];

(*
 * Prove distinctness for constructors.
 *)

Theorem v_distinct_lemma[local]:
  ALL_DISTINCT [Atom b; Closure n x; Constructor s t; Error; Diverge]
Proof
  rw [Atom_def, Closure_def, Constructor_def, Error_def, Diverge_def]
  \\ rw [v_rep_ok_Atom,
         v_rep_ok_Closure,
         v_rep_ok_Constructor,
         v_rep_ok_Diverge,
         v_rep_ok_Error,
         v_abs_11]
  \\ rw [Atom_rep_def,
         Closure_rep_def,
         Constructor_rep_def,
         Diverge_rep_def,
         Error_rep_def]
QED

Theorem v_distinct = SIMP_RULE list_ss [GSYM CONJ_ASSOC] v_distinct_lemma;

(*
 * Prove nchotomy and cases for constructors.
 *)

Theorem rep_exists[local]:
  v_rep_ok v ⇒
    (∃b. v = Atom_rep b) ∨
    (∃s t. v = Constructor_rep s t) ∨
    (∃n x. v = Closure_rep n x) ∨
    v = Diverge_rep ∨
    v = Error_rep
Proof
  rw [v_rep_ok_def]
  \\ Cases_on ‘v’
  \\ pop_assum (qspecl_then [‘a’, ‘ts’] mp_tac)
  \\ simp [subtrees, Atom_rep_def, Constructor_rep_def, Closure_rep_def,
     Diverge_rep_def, Error_rep_def]
  \\ Cases_on ‘a’ \\ fs []
  \\ metis_tac [to_fromList]
QED

val v_repabs_imp =
  v_repabs |> REWRITE_RULE [EQ_IMP_THM] |> SPEC_ALL |> CONJUNCT1 |> GSYM;

Theorem v_nchotomy:
  ∀v.
    (∃b. v = Atom b) ∨
    (∃s t. v = Constructor s t) ∨
    (∃n x. v = Closure n x) ∨
    v = Diverge ∨
    v = Error
Proof
  simp [GSYM v_rep_11, Atom_def, Constructor_def, Closure_def,
        Diverge_def, Error_def]
  \\ gen_tac
  \\ qabbrev_tac ‘x = v_rep v’
  \\ ‘v_rep_ok x’ by simp [Abbr ‘x’]
  \\ drule rep_exists
  \\ rw [] \\ fs []
  \\ TRY (metis_tac [v_repabs])
  \\ disj2_tac \\ disj1_tac
  \\ qexists_tac ‘s’
  \\ qexists_tac ‘MAP v_abs t’
  \\ simp [MAP_MAP_o, combinTheory.o_DEF]
  \\ imp_res_tac v_repabs
  \\ pop_assum (once_rewrite_tac o single o GSYM)
  \\ rpt AP_TERM_TAC
  \\ rw[LIST_EQ_REWRITE, EL_MAP]
  \\ irule v_repabs_imp
  \\ fs[v_rep_ok_def, subtrees_def]
  \\ rw[]
  \\ first_x_assum irule
  \\ qexists_tac `x::path`
  \\ fs[ltree_lookup_def, Constructor_rep_def, LNTH_fromList]
QED

Definition v_CASE[nocompute]:
  v_CASE v atom cons clos div err =
    case v_rep v of
      Branch (Atom' b) [||] => atom b
    | Branch (Constructor' s) ts => cons s (MAP v_abs (THE (toList ts)))
    | Branch (Closure' n x) [||] => clos n x
    | Branch Diverge' [||] => div
    | Branch Error' [||] => err
    | _ => ARB
End

Theorem v_CASE[compute,allow_rebind]:
  v_CASE (Atom b) atom cons clos div err = atom b ∧
  v_CASE (Constructor s t) atom cons clos div err = cons s t ∧
  v_CASE (Closure n x) atom cons clos div err = clos n x ∧
  v_CASE Diverge atom cons clos div err = div ∧
  v_CASE Error atom cons clos div err = err
Proof
  rw [v_CASE, Atom_def, Constructor_def, Closure_def, Diverge_def, Error_def]
  \\ qmatch_goalsub_abbrev_tac ‘v_rep (v_abs xx)’
  \\ ‘v_rep_ok xx’
    by rw [Abbr ‘xx’, v_rep_ok_Atom, v_rep_ok_Constructor, v_rep_ok_Closure,
           v_rep_ok_Diverge, v_rep_ok_Error]
  \\ fs [v_repabs, Abbr ‘xx’, Atom_rep_def, Constructor_rep_def,
         Closure_rep_def, Diverge_rep_def, Error_rep_def, from_toList,
         MAP_MAP_o, combinTheory.o_DEF, v_absrep]
QED

Theorem v_CASE_eq:
  v_CASE v atom cons clos div err = x ⇔
    (∃b. v = Atom b ∧ atom b = x) ∨
    (∃s t. v = Constructor s t ∧ cons s t = x) ∨
    (∃n y. v = Closure n y ∧ clos n y = x) ∨
    (v = Diverge ∧ div = x) ∨
    (v = Error ∧ err = x)
Proof
  qspec_then ‘v’ strip_assume_tac v_nchotomy \\ rw []
  \\ fs [v_CASE, v_11, v_distinct]
QED

Theorem v_CASE_elim:
  ∀f. f (v_CASE v atom cons clos div err) ⇔
    (∃b.   v = Atom b ∧ f (atom b)) ∨
    (∃s t. v = Constructor s t ∧ f (cons s t)) ∨
    (∃n y. v = Closure n y ∧ f (clos n y)) ∨
          (v = Diverge ∧ f div) ∨
          (v = Error ∧ f err)
Proof
  qspec_then `v` assume_tac v_nchotomy >> gvs[v_CASE, v_distinct, v_11]
QED

(*
 * Register with TypeBase.
 *)

Theorem v_CASE_cong:
  ∀M M' atom cons clos div err atom' cons' clos' div' err'.
    M = M' ∧
    (∀b. M' = Atom b ⇒ atom b = atom' b) ∧
    (∀s t. M' = Constructor s t ⇒ cons s t = cons' s t) ∧
    (∀n x. M' = Closure n x ⇒ clos n x = clos' n x) ∧
    (M' = Diverge ⇒ div = div') ∧
    (M' = Error ⇒ err = err') ⇒
      v_CASE M atom cons clos div err = v_CASE M' atom' cons' clos' div' err'
Proof
  rw []
  \\ qspec_then ‘M’ strip_assume_tac v_nchotomy
  \\ rw [] \\ fs [v_CASE]
QED

Theorem datatype_v:
  DATATYPE ((v
             (Atom : pure_config$lit -> v)
             (Constructor : mlstring -> v list -> v)
             (Closure : mlstring -> exp -> v)
             (Diverge : v)
             (Error : v)) : bool)
Proof
  rw [boolTheory.DATATYPE_TAG_THM]
QED

Theorem v_rep_ok_ltree_el:
  ∀ vtree subtree.
    v_rep_ok vtree ∧
    subtree ∈ subtrees vtree
  ⇒ v_rep_ok subtree
Proof
  rw[] >> fs[subtrees_def, v_rep_ok_def] >> rw[] >>
  rename1 `ltree_lookup vtree vpath` >> rename1 `ltree_lookup subtree spath` >>
  qspecl_then [`vpath`,`spath`,`vtree`] assume_tac ltree_lookup_APPEND >>
  gvs[optionTheory.OPTION_BIND_def] >>
  first_x_assum irule >>
  goal_assum drule
QED

Theorem v_prefix_ltree_bisimulation:
∀ t1 t2.
  t1 = t2 ∧ v_rep_ok t1 ⇔
    ∃R. R t1 t2 ∧ v_rep_ok t1 ∧ v_rep_ok t2 ∧
      ∀ a1 ts1 a2 ts2.
        R (Branch a1 ts1) (Branch a2 ts2) ∧
        v_rep_ok (Branch a1 ts1) ∧ v_rep_ok (Branch a2 ts2)
      ⇒ a1 = a2 ∧
        llist_rel R ts1 ts2
Proof
  rw[] >> eq_tac
  >- (rw[] >> qexists_tac `(=)` >> rw[llist_rel_equality]) >>
  rw[ltree_el_eqv] >> fs[] >>
  ntac 3 (last_x_assum mp_tac) >> qid_spec_tac `t1` >> qid_spec_tac `t2` >>
  Induct_on `path` >> rw[] >> rename1 `R s1 s2` >>
  Cases_on `s1` >> Cases_on `s2`
  >- (rw[ltree_el_def] >> fs[llist_rel_def] >> res_tac) >>
  fs[ltree_el_def] >>
  last_assum drule_all >> strip_tac >>
  gvs[llist_rel_def] >>
  Cases_on `LNTH h ts` >> Cases_on `LNTH h ts'` >> fs[] >>
  imp_res_tac LNTH_NONE_LLENGTH >> rgs[] >>
  imp_res_tac LNTH_LLENGTH_NONE >> rgs[] >>
  first_x_assum irule >> reverse (rw[])
  >- (
    first_x_assum irule >>
    goal_assum drule >> fs[]
    ) >>
  irule v_rep_ok_ltree_el >>
  rename1 `subtree ∈ _` >>
  rename1 `LNTH _ vtree = SOME subtree` >>
  qexists_tac `Branch a vtree` >> fs[subtrees_def] >>
  qexists_tac `[h]` >> fs[ltree_lookup_def]
QED

Theorem v_bisimulation:
  ∀v1 v2.
    v1 = v2 ⇔
    ∃R. R v1 v2 ∧
        ∀v3 v4. R v3 v4 ⇒
          (∃a. v3 = Atom a ∧ v4 = Atom a) ∨
          (∃s vs3 vs4.
            v3 = Constructor s vs3 ∧
            v4 = Constructor s vs4 ∧
            LIST_REL R vs3 vs4) ∨
          (∃s e. v3 = Closure s e ∧ v4 = Closure s e) ∨
          (v3 = Diverge ∧ v4 = Diverge) ∨
          (v3 = Error ∧ v4 = Error)
Proof
  rw[] >> eq_tac >> rw[]
  >- (qexists_tac `(=)` >> fs[v_nchotomy]) >>
  fs[Atom_def, Constructor_def, Closure_def, Diverge_def, Error_def] >>
  fs[Atom_rep_def, Constructor_rep_def, Closure_rep_def,
     Diverge_rep_def, Error_rep_def] >>
  rw[GSYM v_rep_11] >>
  qspecl_then [`v_rep v1`,`v_rep v2`] assume_tac v_prefix_ltree_bisimulation >>
  fs[] >> pop_assum kall_tac >>
  qexists_tac `λv1 v2. R (v_abs v1) (v_abs v2)` >> fs[v_absrep] >>
  rpt gen_tac >> strip_tac >>
  fs[GSYM v_rep_11] >>
  assume_tac v_rep_ok_Atom >>
  assume_tac v_rep_ok_Constructor >>
  assume_tac v_rep_ok_Closure >>
  assume_tac v_rep_ok_Diverge >>
  assume_tac v_rep_ok_Error >>
  fs[Atom_rep_def, Constructor_rep_def, Closure_rep_def,
     Diverge_rep_def, Error_rep_def] >>
  fs[v_repabs] >>
  first_assum drule >>
  strip_tac >> gvs[] >>
  fs[llist_rel_def, LIST_REL_EL_EQN, GSYM LMAP_fromList,
     LNTH_fromList, EL_MAP, v_absrep]
QED

val _ = TypeBase.export
  [TypeBasePure.mk_datatype_info
    { ax = TypeBasePure.ORIG TRUTH,
      induction = TypeBasePure.ORIG v_bisimulation,
      case_def = v_CASE,
      case_elim = v_CASE_elim,
      case_cong = v_CASE_cong,
      case_eq = v_CASE_eq,
      nchotomy = v_nchotomy,
      size = NONE,
      encode = NONE,
      lift = NONE,
      one_one = SOME v_11,
      distinct = SOME v_distinct,
      fields = [],
      accessors = [],
      updates = [],
      destructors = [],
      recognizers = [] } ]

Overload case = “v_CASE”;

(* v_lookup takes a list of indices and a value, and uses the indices one-by-one
   to recurse into the structure of the value. Note that only the `Constructor`
   node has sub-nodes.
   v_lookup returns the specified node, together with the number of children
   of that node. To achieve this, we define the `v_to_prefix` function, which
   removes child nodes *)

Definition v_to_prefix_def:
  v_to_prefix v = case v_rep v of Branch a ts => a
End

Theorem v_to_prefix:
  (∀a. v_to_prefix (Atom a) = Atom' a) ∧
  (∀c vs. v_to_prefix (Constructor c vs) = Constructor' c) ∧
  (∀x body. v_to_prefix (Closure x body) = Closure' x body) ∧
  v_to_prefix Diverge = Diverge' ∧
  v_to_prefix Error = Error'
Proof
  fs[Atom_def, Constructor_def, Closure_def, Diverge_def, Error_def] >>
  assume_tac v_rep_ok_Atom >>
  assume_tac v_rep_ok_Constructor >>
  assume_tac v_rep_ok_Closure >>
  assume_tac v_rep_ok_Diverge >>
  assume_tac v_rep_ok_Error >>
  fs[Atom_rep_def, Constructor_rep_def, Closure_rep_def,
     Diverge_rep_def, Error_rep_def] >>
  fs[v_to_prefix_def, v_repabs]
QED

Definition v_lookup_def:
  v_lookup path v =
    case ltree_lookup (v_rep v) path of
    | SOME (Branch a ts) => (a, THE (LLENGTH ts))
    | NONE => (Diverge', 0)
End

Theorem v_lookup_alt:
  (∀v. v_lookup [] v =
    (v_to_prefix v, case v of Constructor c vs => LENGTH vs | _ => 0)) ∧
  ∀n path. v_lookup (n::path) v =
    (case v of
    | Constructor c vs =>
      (case oEL n vs of
      | SOME v' => v_lookup path v'
      | NONE => (Diverge', 0))
    | _ => (Diverge', 0))
Proof
  assume_tac v_rep_ok_Atom >>
  assume_tac v_rep_ok_Constructor >>
  assume_tac v_rep_ok_Closure >>
  assume_tac v_rep_ok_Diverge >>
  assume_tac v_rep_ok_Error >>
  rw[v_lookup_def] >>
  Cases_on `v` >>
  fs[Atom_def, Constructor_def, Closure_def, Diverge_def, Error_def] >>
  fs[v_repabs] >>
  fs[Atom_rep_def, Constructor_rep_def, Closure_rep_def,
     Diverge_rep_def, Error_rep_def] >>
  fs[ltree_lookup_def, v_to_prefix_def] >>
  fs[GSYM LMAP_fromList, LNTH_fromList, oEL_THM] >>
  CASE_TAC >> fs[EL_MAP]
QED

Theorem v_lookup:
  (∀v. v_lookup [] v =
    case v of
    | Atom a => (Atom' a, 0)
    | Constructor c vs => (Constructor' c, LENGTH vs)
    | Closure x body => (Closure' x body, 0)
    | Diverge => (Diverge', 0)
    | Error => (Error', 0)) ∧
  ∀n path. v_lookup (n::path) v =
    (case v of
    | Constructor c vs =>
      (case oEL n vs of
      | SOME v' => v_lookup path v'
      | NONE => (Diverge', 0))
    | _ => (Diverge', 0))
Proof
  rw[v_lookup_alt] >>
  Cases_on `v` >> rw[v_lookup_alt, v_to_prefix]
QED

Theorem v_lookup_0:
  ∀ path v prefix len.
    v_lookup path v = (prefix, len) ∧
    (∀c. prefix ≠ Constructor' c)
  ⇒ len = 0
Proof
  Induct >> fs[v_lookup] >> rw[] >>
  Cases_on `v` >> fs[] >>
  Cases_on `oEL h t` >> fs[] >>
  first_x_assum irule >>
  goal_assum drule >> goal_assum drule
QED

Theorem v_lookup_Diverge:
  ∀ path. v_lookup path Diverge = (Diverge', 0)
Proof
  Cases >> fs[v_lookup]
QED

(* make_v_rep : (num list -> (α,β) vprefix # num) -> (α,β) vprefix ltree *)
(* Given a function which takes a path (:num list) and returns the corresponding
   node, produce the lazy tree of all nodes.
   make_v_rep must also produce ltrees which satisfy v_rep_ok *)
Definition make_v_rep_def:
  make_v_rep f = gen_ltree (
    λpath.
      case f path of
      | (Atom' a, _) => (Atom' a, SOME 0)
      | (Constructor' c, n) => (Constructor' c, SOME n)
      | (Closure' x body, _) => (Closure' x body, SOME 0)
      | (Diverge', _) => (Diverge', SOME 0)
      | (Error', _) => (Error', SOME 0))
End

Theorem v_rep_ok_make_v_rep[local]:
  ∀f. v_rep_ok (make_v_rep f)
Proof
  rw[v_rep_ok_def, subtrees_def, make_v_rep_def] >>
  drule ltree_lookup_SOME_gen_ltree >> rw[] >>
  Cases_on `f path` >> rename1 `(prefix, len_opt)` >> fs[] >>
  Cases_on `prefix` >> gvs[] >>
  fs[LFINITE_LLENGTH] >>
  qexists_tac `len_opt` >> fs[]
QED

(* gen_v : (num list -> vprefix # num) -> v *)
(* Generates a value of type v given a function generating v_prefix nodes when
   given a path *)
Definition gen_v_def:
  gen_v f = v_abs (make_v_rep f)
End

Theorem gen_v:
  ∀f. gen_v f =
    case f [] of
    | (Atom' a, len) => Atom a
    | (Constructor' c, len) =>
        Constructor c (GENLIST (λn. gen_v (λpath. f (n::path))) len)
    | (Closure' x body, len) => Closure x body
    | (Diverge', len) => Diverge
    | (Error', len) => Error
Proof
  rw[gen_v_def, GSYM v_rep_11] >>
  qspec_then `f` assume_tac v_rep_ok_make_v_rep >>
  fs[v_repabs] >>
  simp[make_v_rep_def, Once gen_ltree] >>
  Cases_on `f []` >> rename1 `f [] = (prefix, len)` >> fs[] >>
  assume_tac v_rep_ok_Atom >>
  assume_tac v_rep_ok_Constructor >>
  assume_tac v_rep_ok_Closure >>
  assume_tac v_rep_ok_Diverge >>
  assume_tac v_rep_ok_Error >>
  Cases_on `prefix` >>
  fs[Atom_def, Constructor_def, Closure_def, Diverge_def, Error_def] >>
  fs[v_repabs] >>
  fs[Atom_rep_def, Constructor_rep_def, Closure_rep_def,
     Diverge_rep_def, Error_rep_def] >>
  fs[MAP_GENLIST, combinTheory.o_DEF, LGENLIST_EQ_fromList] >>
  rw[GENLIST_FUN_EQ] >>
  qpat_abbrev_tac `tree = gen_ltree _` >>
  rw[GSYM v_repabs] >>
  irule v_rep_ok_ltree_el >>
  qexists_tac `make_v_rep f` >>
  assume_tac v_rep_ok_make_v_rep >> gvs[] >>
  fs[subtrees_def] >>
  qexists_tac `[n]` >>
  rw[make_v_rep_def, Once gen_ltree, ltree_lookup_def, LNTH_LGENLIST]
QED

Theorem gen_v_Atom:
  ∀ f a. gen_v f = Atom a ⇔ ∃r. f [] = (Atom' a, r)
Proof
  rw[] >>
  once_rewrite_tac[gen_v] >>
  CASE_TAC >> CASE_TAC >> fs[]
QED

Theorem gen_v_Constructor_IMP:
  ∀ f c vs. gen_v f = Constructor c vs ⇒ f [] = (Constructor' c, LENGTH vs)
Proof
  rpt gen_tac >>
  simp[Once gen_v] >>
  CASE_TAC >> CASE_TAC >> gvs[] >>
  rpt strip_tac >> rw[LENGTH_GENLIST]
QED

Theorem gen_v_nullary_Constructor:
  ∀ f v.
    gen_v f = Constructor c [] ⇔ f [] = (Constructor' c, 0)
Proof
  rw[] >>
  simp[Once gen_v] >>
  CASE_TAC >> CASE_TAC >> fs[] >>
  eq_tac >> rw[] >>
  Cases_on `r` >> fs[GENLIST]
QED

Theorem gen_v_Closure:
  ∀ f x body. gen_v f = Closure x body ⇔ ∃r. f [] = (Closure' x body, r)
Proof
  rw[] >>
  simp[Once gen_v] >>
  CASE_TAC >> CASE_TAC >> fs[]
QED

Theorem gen_v_Diverge:
  ∀ f. gen_v f = Diverge ⇔ ∃r. f [] = (Diverge', r)
Proof
  rw[] >>
  once_rewrite_tac[gen_v] >>
  CASE_TAC >> CASE_TAC >> fs[]
QED

Theorem gen_v_Error:
  ∀ f. gen_v f = Error ⇔ ∃r. f [] = (Error', r)
Proof
  rw[] >>
  once_rewrite_tac[gen_v] >>
  CASE_TAC >> CASE_TAC >> fs[]
QED

Definition freevars_v_def:
  freevars_v v name ⇔
    ∃path s x k.
      v_lookup path v = (Closure' s x, k) ∧ name ∈ freevars (Lam s x)
End

Theorem freevars_v_IN:
  name ∈ freevars_v v ⇔
    ∃path s x k.
      v_lookup path v = (Closure' s x, k) ∧ name ∈ freevars (Lam s x)
Proof
  rw[IN_DEF,freevars_v_def]
QED

Definition v_finite_def:
  v_finite v = ltree_finite(v_rep v)
End

Theorem v_finite:
  v_finite(Atom a) ∧
  v_finite(Closure x body) ∧
  v_finite(Error) ∧
  v_finite(Diverge) ∧
  v_finite(Constructor s l) = EVERY v_finite l
Proof
  rw[v_finite_def,Atom_def,Closure_def,Error_def,Diverge_def,Constructor_def,GSYM v_repabs_imp,
     v_rep_ok_Atom,v_rep_ok_Closure,v_rep_ok_Error,v_rep_ok_Diverge,v_rep_ok_Constructor] >>
  rw[Atom_rep_def,Closure_rep_def,Diverge_rep_def,Error_rep_def,Constructor_rep_def,
     ltree_finite_cases] >>
  simp[EVERY_MAP,GSYM v_finite_def] >>
  metis_tac[]
QED

Theorem v_finite_ind:
  (∀a. P(Atom a)) ∧
  (∀x body. P(Closure x body)) ∧
  (P Diverge) ∧
  (P Error) ∧
  (∀s vl. EVERY P vl ⇒ P (Constructor s vl))
  ⇒
  ∀t. v_finite t ⇒ P t
Proof
  strip_tac >>
  ‘∀x. ltree_finite x ⇒ ∀t. x = v_rep t ⇒ P (v_abs (v_rep t))’
   suffices_by(gvs[v_finite_def,PULL_FORALL,v_absrep]) >>
  ho_match_mp_tac ltree_finite_ind >>
  rw[v_absrep] >>
  rename1 ‘v_rep t’ >>
  Cases_on ‘t’ >> gvs[Constructor_def,GSYM v_repabs_imp,v_rep_ok_Constructor] >>
  gvs[Constructor_rep_def,EVERY_MAP] >>
  first_x_assum match_mp_tac >>
  match_mp_tac (MP_CANON EVERY_MONOTONIC) >>
  gvs[EVERY_EL] >> rw [] >>
  first_x_assum drule >> rw []
QED

Definition v_take_def:
  v_take (n:num) t =
    case t of
      Constructor s vl =>
        if n = 0 then Constructor s []
        else
          Constructor s (MAP (v_take (n-1)) vl)
    | v => v
End

Theorem v_take_finite:
  ∀n v. v_finite(v_take n v)
Proof
  Induct >> rw[v_finite,Once v_take_def] >>
  BasicProvers.TOP_CASE_TAC >> rw[v_finite] >>
  rw[EVERY_MEM,MEM_MAP] >> simp[]
QED

Theorem v_take_add:
  ∀n v x.
    v_take n v = v ⇒
    v_take (n + x) v = v
Proof
  ho_match_mp_tac v_take_ind >>
  ntac 3 strip_tac >>
  PURE_ONCE_REWRITE_TAC[v_take_def] >>
  rw[] >> BasicProvers.TOP_CASE_TAC >> gvs[] >>
  Cases_on ‘n = 0’ >> gvs[] >>
  CONV_TAC(RHS_CONV(PURE_ONCE_REWRITE_CONV [GSYM(cj 1 MAP_ID)])) >>
  qpat_x_assum ‘_ = _’ (mp_tac o CONV_RULE(RHS_CONV(PURE_ONCE_REWRITE_CONV [GSYM(cj 1 MAP_ID)]))) >>
  SIMP_TAC std_ss [MAP_EQ_f] >>
  rw[]
QED

Theorem v_take_finite[allow_rebind]:
  ∀v. v_finite v ⇔ ∃n. v_take n v = v
Proof
  simp[EQ_IMP_THM,FORALL_AND_THM] >>
  reverse conj_tac >- metis_tac[v_take_finite] >>
  ho_match_mp_tac v_finite_ind >> rw[] >>
  rw[Once v_take_def] >>
  Q.REFINE_EXISTS_TAC ‘SUC _’ >> rw[] >>
  pop_assum mp_tac >> Induct_on ‘vl’ >> rw[] >>
  res_tac >>
  rename1 ‘MAP (λa. v_take m a)’ >>
  qexists_tac ‘MAX n m’ >>
  rw[MAX_DEF,NOT_LESS]
  >- (imp_res_tac LESS_ADD >> gvs[v_take_add]) >>
  gvs[NOT_LESS] >>
  imp_res_tac LESS_EQUAL_ADD >>
  gvs[] >>
  CONV_TAC(RHS_CONV(PURE_ONCE_REWRITE_CONV [GSYM(cj 1 MAP_ID)])) >>
  pop_assum (mp_tac o CONV_RULE(RHS_CONV(PURE_ONCE_REWRITE_CONV [GSYM(cj 1 MAP_ID)]))) >>
  SIMP_TAC std_ss [MAP_EQ_f] >>
  rw[v_take_add]
QED

(* v_bisimulation in implication form. Much easier to apply that way. *)
Theorem v_coinduct:
  ∀R. (∀v3 v4. R v3 v4 ⇒
               (∃a. v3 = Atom a ∧ v4 = Atom a) ∨
               (∃s vs3 vs4.
                  v3 = Constructor s vs3 ∧
                  v4 = Constructor s vs4 ∧
                  LIST_REL R vs3 vs4) ∨
               (∃s e. v3 = Closure s e ∧ v4 = Closure s e) ∨
               (v3 = Diverge ∧ v4 = Diverge) ∨
               (v3 = Error ∧ v4 = Error)) ⇒
      ∀v1 v2. R v1 v2 ⇒ v1 = v2
Proof
  rw[] >> simp[Once v_bisimulation] >>
  goal_assum drule >>
  first_x_assum MATCH_ACCEPT_TAC
QED

Theorem v_take_lemma:
  ∀v1 v2. v1 = v2 ⇔ ∀n. v_take n v1 = v_take n v2
Proof
  simp[EQ_IMP_THM,FORALL_AND_THM] >>
  ho_match_mp_tac v_coinduct >>
  rw[] >>
  ‘∀n. v_take (SUC n) v1 = v_take (SUC n) v2’ by metis_tac[] >>
  last_x_assum kall_tac >>
  pop_assum(mp_tac o PURE_ONCE_REWRITE_RULE[v_take_def]) >>
  ntac 2 (BasicProvers.TOP_CASE_TAC) >> rw[] >>
  gvs[FORALL_AND_THM,MAP_EQ_EVERY2] >>
  gvs[LIST_REL_EL_EQN]
QED
