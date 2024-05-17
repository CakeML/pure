open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory miscTheory;
open listTheory alistTheory relationTheory set_relationTheory pred_setTheory;
open typeclass_typesTheory pure_tcexpTheory typeclass_texpTheory;
open typeclass_kindCheckTheory pure_configTheory pure_freshenTheory;
open monadsyntax;

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "option";

val _ = new_theory "typeclass_typing";

(*
  A type definition is an arity and a collection of constructor definitions.
  Each constructor definition is a name and a type scheme for its arguments
  (closed wrt the type definition arity).

  Like CakeML, use numbers to refer to types - known typedefs represented as
    : typedef list
  We could instead have:
    : (string # typedef) list     or     : string |-> typedef     etc.
  Unlike CakeML, we group constructors by their type (i.e. group siblings).

  E.g. the type definitions for Maybe and List might look like:
  [
    (1, [ ("Nothing", []) ; ("Just", [Var 0]) ]);
    (1, [ ("Nil", []) ; ("Cons", [Var 0; TypeCons 1 [Var 0]]) ])
  ]

  The exception definition is a list of constructors associated to (closed)
  argument types.

  Together, the exception definition and a collection of type definitions form
  our typing namespace.
*)
Type type_scheme[pp] = ``:num # type``;
Type pred_type_scheme[pp] = ``:num # PredType``;

Type type_kind_scheme[pp] = ``:Kind list # type``;
Type pred_type_kind_scheme[pp] = ``:Kind list # PredType``;

Type typedef[pp] = ``:Kind list # ((mlstring # type list) list)``;
Type typedefs[pp] = ``:typedef list``;
Type exndef[pp] = ``:(mlstring # type list) list``;

(* CakeML assumes the following initial namespace:
      Exceptions: 0 -> Bind, 1 -> Chr, 2 -> Div, 3 -> Subscript
      Types: 0 -> Bool, 1 -> List

   In Pure, we need only Subscript and List - Bool is built in and none of the
   others are used. Therefore, the Pure initial namespace should be:
      Exception: 0 -> Subscript
      Types: 0 -> List
*)
Definition initial_namespace_def:
  initial_namespace : exndef # typedefs = (
    [«Subscript»,[]],
    [[kindType],[(«[]»,[]);
      («::», [TypeVar 0; Cons (UserType 0) (TypeVar 0)])]]
  )
End

(* Constructor names and their arities defined by a namespace *)
Definition ns_cns_arities_def:
  ns_cns_arities (exndef : exndef, tdefs : typedefs) =
    set (MAP (λ(cn,ts). cn, LENGTH ts) exndef) INSERT
    {(«True», 0); («False», 0)} (* Booleans considered built-in *) INSERT
    set (MAP (λ(ar,cndefs). set (MAP (λ(cn,ts). cn, LENGTH ts) cndefs)) tdefs)
End

(* Check a set of constructor names/arities fits a namespace *)
Definition cns_arities_ok_def:
  cns_arities_ok ns cns_arities ⇔
  ∀cn_ars. cn_ars ∈ cns_arities ⇒
    (∃ar. cn_ars = {«»,ar}) (* all tuples allowed *) ∨
    (∃cn_ars'. cn_ars' ∈ ns_cns_arities ns ∧ cn_ars ⊆ cn_ars')
End

Definition typedefs_to_cdb_def:
  typedefs_to_cdb typedefs =
    (λc. OPTION_MAP (λtinfo. kind_arrows (FST tinfo) kindType)
        (LLOOKUP typedefs c))
End

Definition kind_ok_def:
  kind_ok typedefs ks k t ⇔
    kind_wf (typedefs_to_cdb typedefs) (LLOOKUP ks) k t
End

Definition type_ok_def:
  type_ok typedefs ks t = kind_ok typedefs ks kindType t
End

Definition pred_type_well_scoped_def:
  pred_type_well_scoped (Pred ps t) =
  (∀cl v. MEM (cl,v) ps ⇒
    collect_type_vars v ⊆ collect_type_vars t)
End

Definition pred_type_kind_ok_def:
  pred_type_kind_ok cldb (typedefs: typedefs) ks pt ⇔
    pred_kind_wf cldb (typedefs_to_cdb typedefs) (LLOOKUP ks) pt
End

Theorem kind_wf_IMP_freetyvars_ok:
  ∀k t. kind_wf cdb (LLOOKUP ks) k t ⇒
  freetyvars_ok (LENGTH ks) t
Proof
  ho_match_mp_tac kind_wf_ind >>
  gvs[freetyvars_ok_def,miscTheory.LLOOKUP_THM]
QED

Theorem kind_ok_IMP_freetyvars_ok:
  kind_ok typedefs ks k t ⇒ freetyvars_ok (LENGTH ks) t
Proof
  metis_tac[kind_wf_IMP_freetyvars_ok,kind_ok_def]
QED

Theorem type_ok_IMP_freetyvars_ok:
  type_ok typedefs ks t ⇒ freetyvars_ok (LENGTH ks) t
Proof
  metis_tac[kind_ok_IMP_freetyvars_ok,type_ok_def]
QED

Overload subst_db_scheme =
  ``λn ts (vars,scheme).
      (vars, subst_db (n + vars) (MAP (shift_db 0 vars) ts) scheme)``;
Overload shift_db_scheme =
  ``λskip shift (vars,scheme).
      (vars, shift_db (skip + vars) shift scheme)``;
Overload tshift_kind_scheme = ``λn (vars,scheme). (vars, shift_db (LENGTH
vars) n scheme)``;
Overload tshift_scheme_pred = ``λn (vars,scheme). (vars, shift_db_pred vars n scheme)``;
Overload tshift_kind_scheme_pred = ``λn (vars,scheme). (vars, shift_db_pred
(LENGTH vars) n scheme)``;

Overload tshift_env = ``λn. MAP (λ(x,scheme). (x, tshift_kind_scheme n scheme))``;
Overload tshift_env_pred = ``λn. MAP (λ(x,scheme). (x, tshift_kind_scheme_pred n scheme))``;

Overload type_kind_scheme_ok =
  ``λtdefs ks (varks,scheme). type_ok tdefs (varks ++ ks) scheme``

Overload pred_type_kind_scheme_ok =
  ``λclm tdefs ks (varks,scheme). pred_type_kind_ok clm tdefs (varks ++ ks) scheme``

(* Does a type specialise a type scheme in a given variable context/namespace? *)
Definition specialises_def:
  specialises tdefs db (vars, scheme) t =
    ∃subs.
      LIST_REL (λk sub. kind_ok tdefs db k sub) vars subs ∧
      tsubst subs scheme = t
End

(*
Theorem specialises_alt:
  specialises tdefs db (vars, scheme) t =
  ∃subs.
      LENGTH subs = LENGTH vars ∧
      (∀n. n < LENGTH subs ⇒
        kind_ok tdefs db (EL n vars) (EL n subs)) ∧
      tsubst subs scheme = t
Proof
  rw[specialises_def,EQ_IMP_THM] >>
  irule_at (Pos last) EQ_REFL >>
  gvs[LIST_REL_EVERY_ZIP,EVERY_EL,EL_ZIP]
QED
*)

Definition specialises_pred_def:
  specialises_pred tdefs db (vars, scheme) pt =
    ∃subs.
      LIST_REL (λk sub. kind_ok tdefs db k sub) vars subs ∧
      tsubst_pred subs scheme = pt
End

(* Our namespace is an exception definition and some datatype definitions *)
Definition namespace_ok_def:
  namespace_ok (exndef : exndef, typedefs : typedefs) ⇔
    (* No empty type definitions: *)
      EVERY (λ(ak,td). td ≠ []) typedefs ∧
    (* Unique, unreserved constructor names: *)
      ALL_DISTINCT
        (MAP implode (SET_TO_LIST (reserved_cns DELETE "Subscript")) ++
         MAP FST exndef ++ MAP FST (FLAT $ MAP SND typedefs)) ∧
    (* Every constructor type is closed wrt kinds and uses only defined
       types: *)
      EVERY (λ(ak,td).
        EVERY (λ(cn,argtys). EVERY (type_ok typedefs ak) argtys) td) typedefs ∧
    (* Every exception constructor type is closed and uses only defined types: *)
      EVERY (λ(cn,tys). EVERY (type_ok typedefs []) tys) exndef ∧
    (* Subscript is a valid exception *)
      MEM («Subscript»,[]) exndef
End

Overload append_ns = ``λ(ns:(exndef # ('a list))) ns'. (FST ns ++ FST ns', SND ns ++ SND ns')``;

Definition namespace_init_ok_def:
  namespace_init_ok ns ⇔
    namespace_ok ns ∧
    ∃ns'. ns = append_ns initial_namespace ns'
End

(******************** Typing judgements ********************)

(* Handle Locs separately *)
Inductive type_lit:
  type_lit (Int i) Integer ∧
  type_lit (Str s) String ∧
  (s1 ≠ ""⇒ type_lit (Msg s1 s2) Message)
End

Inductive type_atom_op:
[~Lit:]
  (type_lit l t ⇒ type_atom_op (Lit l) [] t)

[~IntOps_Int:]
  (MEM op [Add; Sub; Mul; Div; Mod] ⇒
    type_atom_op op [Integer;Integer] Integer)

[~IntOps_Bool:]
  (MEM op [Eq; Lt; Leq; Gt; Geq] ⇒
    type_atom_op op [Integer;Integer] Bool)

[~Len:]
  (type_atom_op Len [String] Integer)

[~Elem:]
  (type_atom_op Elem [String;Integer] Integer)

[~Concat:]
  (EVERY (λt. t = String) ts ⇒
    type_atom_op Concat ts String)

[~Implode:]
  (EVERY (λt. t = Integer) ts ⇒
    type_atom_op Implode ts String)

[~Substring1:]
  (type_atom_op Substring [String;Integer] String)

[~Substring2:]
  (type_atom_op Substring [String;Integer;Integer] String)

[~StrOps_Bool:]
  (MEM op [StrEq; StrLt; StrLeq; StrGt; StrGeq] ⇒
    type_atom_op op [String;String] Bool)

[~Message:]
  (s ≠ "" ⇒ type_atom_op (Message s) [String] Message)
End

(* Typing judgments for type constructors *)
Definition type_cons_def:
  type_cons (typedefs : typedefs) db (cname,carg_tys) (tyid,tyargs) ⇔
    ∃argks constructors schemes.
      (* There is some type definition: *)
        oEL tyid typedefs = SOME (argks, constructors) ∧
      (* Which declares the constructor: *)
        ALOOKUP constructors cname = SOME schemes ∧
      (* And we can specialise it appropriately: *)
        LIST_REL (kind_ok typedefs db) argks tyargs ∧
        MAP (tsubst tyargs) schemes = carg_tys
End

(* Typing judgments for exceptions *)
Definition type_exception_def:
  type_exception (exndef : exndef) (cname, carg_tys) ⇔
      ALOOKUP exndef cname = SOME carg_tys
End

Definition destruct_type_cons_def:
  destruct_type_cons (edef:exndef,tdefs: typedefs) db t cname carg_tys ⇔
  if t = Atom Exception
  then
    type_exception edef (cname,carg_tys)
  else
  ∃tc targs.
    split_ty_head t = SOME (tc,targs) ∧
    case tc of
    | INL tyid => type_cons tdefs db (cname,carg_tys) (tyid,targs)
    | INR (PrimT Bool) => MEM cname [«True»;«False»] ∧ carg_tys = []
    | INR (CompPrimT (Tuple n)) => cname = «» ∧ targs = carg_tys
    | _ => F
End

Definition get_PrimTys_def:
  get_PrimTys [] = SOME [] ∧
  get_PrimTys ((Atom $ PrimTy pty) :: rest) = OPTION_MAP (CONS pty) (get_PrimTys rest) ∧
  get_PrimTys _ = NONE
End

(* shows how the class constraint can be satisfied.
* e.g. Num a => Ord a, since Ord is a superclass of Num,
* (Monoid a, Monoid b) => Monoid (a, b), deal to instance declaration *)
Datatype:
  entailment = Entail (Kind list) ((mlstring # type) list) (mlstring # type)
End

Definition specialises_inst_def:
  specialises_inst tdefs (Entail ks ps p) (Entail ks' qs q) ⇔
    ∃subs.
      LIST_REL (λk sub. kind_ok tdefs ks' k sub) ks subs ∧
      LIST_REL (λ(c,t) (c',t'). c = c' ∧
        tsubst subs t = t') (p::ps) (q::qs)
End

Definition safeLam_def:
  safeLam _ [] e = e ∧
  safeLam a xs e = Lam a xs e
End

Definition safeApp_def:
  safeApp _ e [] = e ∧
  safeApp a e xs = pure_cexp$App a e xs
End

Theorem safeApp_simp[simp]:
  (∀v. (safeApp () x xs = Var () v) ⇔ xs = [] ∧ x = Var () v) ∧
  (∀cop ts. (safeApp () x xs = Prim () cop ts) ⇔
    xs = [] ∧ x = Prim () cop ts) ∧
  (∀t ts. (safeApp () x xs = App () t ts) ⇔
    (xs = [] ∧ x = App () t ts) ∨ (ts ≠ [] ∧ xs = ts ∧ x = t)) ∧
  (∀vs t. (safeApp () x xs = Lam () vs t) ⇔
    (xs = [] ∧ x = Lam () vs t)) ∧
  (∀vs t t'. (safeApp () x xs = Let () vs t t') ⇔
    (xs = [] ∧ x = Let () vs t t')) ∧
  (∀fns t'. (safeApp () x xs = Letrec () fns t') ⇔
    (xs = [] ∧ x = Letrec () fns t')) ∧
  (∀t c es ys. (safeApp () x xs = Case () t c es ys) ⇔
    (xs = [] ∧ x = Case () t c es ys)) ∧
  (∀t cv p e pes. (safeApp () x xs = NestedCase () t cv p e pes) ⇔
    (xs = [] ∧ x = NestedCase () t cv p e pes))
Proof
  Cases_on `xs` >>
  rw[safeApp_def] >>
  Cases_on `ts` >>
  rw[] >>
  metis_tac[]
QED

Theorem safeLam_simp[simp]:
  (∀v. (safeLam () xs x = Var () v) ⇔ xs = [] ∧ x = Var () v) ∧
  (∀cop ts. (safeLam () xs x = Prim () cop ts) ⇔
    xs = [] ∧ x = Prim () cop ts) ∧
  (∀t ts. (safeLam () xs x = App () t ts) ⇔
    (xs = [] ∧ x = App () t ts)) ∧
  (∀vs t. (safeLam () xs x = Lam () vs t) ⇔
    (xs = [] ∧ x = Lam () vs t) ∨ (vs ≠ [] ∧ xs = vs ∧ x = t)) ∧
  (∀vs t t'. (safeLam () xs x = Let () vs t t') ⇔
    (xs = [] ∧ x = Let () vs t t')) ∧
  (∀fns t'. (safeLam () xs x = Letrec () fns t') ⇔
    (xs = [] ∧ x = Letrec () fns t')) ∧
  (∀t c es ys. (safeLam () xs x = Case () t c es ys) ⇔
    (xs = [] ∧ x = Case () t c es ys)) ∧
  (∀t cv p e pes. (safeLam () xs x = NestedCase () t cv p e pes) ⇔
    (xs = [] ∧ x = NestedCase () t cv p e pes))
Proof
  Cases_on `xs` >>
  rw[safeLam_def] >>
  Cases_on `vs` >>
  rw[] >>
  iff_tac >> rw[]
QED

(* if s is a super class of c then `Entail [k] [(s,TypeVar 0)] (c,TypeVar 0)`
* will be in the set ie *)
(* This should be equivalent to `entail` after turning all the super classes
* and instance declarations to ie *)
Inductive has_dict:
[~lie:]
  p ∈ lie ⇒ has_dict tdefs db ie lie p
[~ie:]
  it ∈ ie ∧ specialises_inst tdefs it (Entail db cstrs p) ∧
  has_dicts tdefs db ie lie cstrs ⇒
    has_dict tdefs db ie lie p
[~dicts:]
  (∀p. MEM p ps ⇒ has_dict tdefs db ie lie p) ⇒
    has_dicts tdefs db ie lie ps
End

Theorem has_dicts_simp = cj 2 has_dict_cases;

Inductive construct_dict:
[~lie:]
  FLOOKUP lie d = SOME p ⇒
    construct_dict tdefs db ie lie p (pure_cexp$Var () d)
[~ie:]
  FLOOKUP ie d = SOME it ∧
  specialises_inst tdefs it (Entail db cstrs p) ∧
  construct_dicts tdefs db ie lie cstrs ds ∧
  de = (safeApp () (pure_cexp$Var () d) ds) ⇒
    construct_dict tdefs db ie lie p de
      
[~dicts:]
  (LIST_REL (construct_dict tdefs db ie lie) ps ds) ⇒
    construct_dicts tdefs db ie lie ps ds
End

Theorem construct_dicts_simp = cj 2 construct_dict_cases;

Theorem has_dict_EXISTS_construct_dict:
  (∀p. has_dict tdefs db (FRANGE ie) (FRANGE lie) p ⇒
    ∃d . construct_dict tdefs db ie lie p d) ∧
  ∀ps. has_dicts tdefs db (FRANGE ie) (FRANGE lie) ps ⇒
    ∃ds. construct_dicts tdefs db ie lie ps ds
Proof
  ho_match_mp_tac has_dict_ind >>
  rw[]
  >- (
    irule_at (Pos hd) construct_dict_lie >>
    metis_tac[finite_mapTheory.FRANGE_FLOOKUP]
  )
  >- (
    irule_at (Pos hd) construct_dict_ie >>
    metis_tac[finite_mapTheory.FRANGE_FLOOKUP]
  ) >>
  irule_at (Pos hd) construct_dict_dicts >>
  pop_assum mp_tac >>
  Induct_on `ps` >>
  rw[] >>
  pop_assum $ strip_assume_tac o SRULE[DISJ_IMP_THM,FORALL_AND_THM] >>
  last_x_assum drule >>
  metis_tac[]
QED

Theorem construct_dict_IMP_has_dict:
  (∀p d. construct_dict tdefs db ie lie p d ⇒
    has_dict tdefs db (FRANGE ie) (FRANGE lie) p) ∧
  (∀ps ds. construct_dicts tdefs db ie lie ps ds ⇒
    has_dicts tdefs db (FRANGE ie) (FRANGE lie) ps)
Proof
  ho_match_mp_tac construct_dict_ind >>
  rw[]
  >- (
    irule has_dict_lie >>
    metis_tac[finite_mapTheory.FRANGE_FLOOKUP]
  )
  >- (
    irule has_dict_ie >>
    metis_tac[finite_mapTheory.FRANGE_FLOOKUP]
  ) >>
  irule has_dict_dicts >>
  rw[] >>
  gvs[LIST_REL_EVERY_ZIP,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
  first_x_assum drule >>
  pairarg_tac >>
  gvs[] >>
  drule EL_ZIP >>
  rw[] >>
  first_x_assum drule >>
  rw[] >>
  first_x_assum irule
QED

Definition LIST_REL3_def:
  LIST_REL3 R [] [] [] = T ∧
  LIST_REL3 R (a::as) (b::bs) (c::cs) = (R a b c ∧ LIST_REL3 R as bs cs) ∧
  LIST_REL3 R _ _ _ = F
End

Theorem LIST_REL3_EL:
  ∀R as bs cs.
  LIST_REL3 R as bs cs ⇔
    (LENGTH bs = LENGTH as ∧ LENGTH cs = LENGTH as ∧
     (∀n. n < LENGTH as ⇒ R (EL n as) (EL n bs) (EL n cs)))
Proof
  ho_match_mp_tac LIST_REL3_ind >>
  reverse $ rw[LIST_REL3_def]
  >- (strip_tac >> gvs[]) >>
  rw[EQ_IMP_THM] >>
  gvs[]
  >- (
    simp[Once $ oneline EL] >>
    CASE_TAC >>
    simp[]
  )
  >- (first_x_assum $ qspec_then `0` mp_tac >> simp[]) >>
  first_x_assum $ qspec_then `SUC n` mp_tac >> fs[]
QED

Theorem LIST_REL3_strongind:
  ∀R P.
    P [] [] [] ∧
    (∀a b c as bs cs.
      R a b c ∧ LIST_REL3 R as bs cs ∧ P as bs cs ⇒
        P (a::as) (b::bs) (c::cs)) ⇒
    ∀as bs cs. LIST_REL3 R as bs cs ⇒ P as bs cs
Proof
  rpt gen_tac >>
  strip_tac >>
  `∀R' as bs cs. LIST_REL3 R' as bs cs ⇒ R' = R ⇒
    (P as bs cs) ∧ LIST_REL3 R as bs cs`
    suffices_by rw[] >>
  ho_match_mp_tac LIST_REL3_ind >>
  rw[LIST_REL3_def] >>
  gvs[]
QED

Theorem LIST_REL3_induct:
  ∀R P.
    P [] [] [] ∧
    (∀a b c as bs cs.
      R a b c ∧ P as bs cs ⇒
        P (a::as) (b::bs) (c::cs)) ⇒
    ∀as bs cs. LIST_REL3 R as bs cs ⇒ P as bs cs
Proof
  rpt gen_tac >>
  strip_tac >>
  `∀R' as bs cs. LIST_REL3 R' as bs cs ⇒ R' = R ⇒ P as bs cs`
    suffices_by rw[] >>
  ho_match_mp_tac LIST_REL3_ind >>
  rw[LIST_REL3_def] >>
  gvs[]
QED

Theorem LIST_REL3_mono[mono]:
  (∀x y z. R1 x y z ⇒ R2 x y z) ⇒
    LIST_REL3 R1 l1 l2 l3 ⇒ LIST_REL3 R2 l1 l2 l3
Proof
  strip_tac >>
  `∀R l1 l2 l3. LIST_REL3 R l1 l2 l3 ⇒ R = R1 ⇒ LIST_REL3 R2 l1 l2 l3`
    suffices_by rw[] >>
  ho_match_mp_tac LIST_REL3_ind >>
  rw[LIST_REL3_def] >>
  gvs[]
QED

Theorem LIST_REL3_cases:
  LIST_REL3 R as bs cs ⇔
    (as = [] ∧ bs = [] ∧ cs = []) ∨
    (∃x xs y ys z zs.
      as = x::xs ∧ bs = y::ys ∧ cs = z::zs ∧
      R x y z ∧ LIST_REL3 R xs ys zs)
Proof
  Cases_on `as` >>
  Cases_on `bs` >>
  Cases_on `cs` >>
  simp[LIST_REL3_def]
QED

Theorem LIST_REL3_simp:
  (LIST_REL3 R [] bs cs ⇔ (bs = [] ∧ cs = [])) ∧
  (LIST_REL3 R (x::xs) bs cs ⇔
    (∃y ys z zs.
      bs = y::ys ∧ cs = z::zs ∧
      R x y z ∧ LIST_REL3 R xs ys zs))
Proof
  Cases_on `bs` >>
  Cases_on `cs` >>
  simp[LIST_REL3_def]
QED

Inductive type_cepat:
[~Var:]
  type_cepat ns db (cepatVar v) t [(v,t)]

[~UScore:]
  type_cepat ns db cepatUScore t []

[~Cons:]
  destruct_type_cons ns db t c ts ∧
  LIST_REL3 (type_cepat ns db) pats ts vtss ⇒
    type_cepat ns db (cepatCons c pats) t (FLAT vtss)
End

Inductive exhaustive_cepat:
[~Var:]
  cepatVar v ∈ s ⇒
    exhaustive_cepat ns db t s

[~UScore:]
  cepatUScore ∈ s ⇒
    exhaustive_cepat ns db t s

[~Cons:]
  (∀c ts. destruct_type_cons ns db t c ts ⇒
    ∃(pss:cepat list set).
      exhaustive_cepatl ns db ts pss ∧ IMAGE (cepatCons c) pss ⊆ s) ⇒
  exhaustive_cepat ns db t s

[~Nil:]
  [] ∈ pss ⇒
    exhaustive_cepatl ns db [] pss

[~List:]
  exhaustive_cepat ns db t hs ∧
  exhaustive_cepatl ns db ts tls ∧
  IMAGE (UNCURRY CONS) (hs × tls) ⊆ pss ⇒
    exhaustive_cepatl ns db (t::ts) pss
End

Theorem exhaustive_cepat_monotone:
  (∀t s. exhaustive_cepat ns db t s ⇒
    ∀s'. s ⊆ s' ⇒ exhaustive_cepat ns db t s') ∧

  (∀ts s. exhaustive_cepatl ns db ts s ⇒
    ∀s'. s ⊆ s' ⇒ exhaustive_cepatl ns db ts s')
Proof
  ho_match_mp_tac exhaustive_cepat_ind >>
  rw[SUBSET_DEF]
  >- metis_tac[exhaustive_cepat_Var]
  >- metis_tac[exhaustive_cepat_UScore]
  >- (
    irule exhaustive_cepat_Cons >>
    fs[SUBSET_DEF,PULL_EXISTS] >>
    metis_tac[])
  >- metis_tac[exhaustive_cepat_Nil]
  >- (
    irule exhaustive_cepat_List >>
    fs[SUBSET_DEF,PULL_EXISTS] >>
    metis_tac[])
QED

Overload Monad = ``Cons (Atom $ CompPrimTy $ M)``;

(*
  The main typing relation.
  type_elaborate_texp :
      (ns: exndef # typedefs)     -- type definitions for exceptions and datatypes
   -> (clk: class -> Kind option) -- a map from class to its corresponding kind
   -> (ie: entailment set)        -- instance environment
   -> (lie: (class # type) set)   -- local instance environment
   -> (db: Kind list)             -- deBruijn indices in scope
                                  --   (kind of each index)
   -> (st: type list)             -- store typing
   -> (env: (string # (Kind list # PredType)) list)
                                  -- term variables associated to type schemes
   -> texp -> texp              -- expression, elaborated expression,
   -> type                        -- and its type
*)
(* It does four things:
* 1. checks the type of the expression
* 2. removes the user's type annotatoin
* 3. elaborates the class constraints for the variable
* 4. elaborates the poly type in every let binding
*)
Inductive type_elaborate_texp:
(* remove the user type annotation after class constraint elaboration *)
[~UserAnnot:]
  type_elaborate_texp ns (clk:mlstring -> Kind option) ie lie db st env e e' t ⇒
    type_elaborate_texp ns clk ie lie db st env (UserAnnot t e) e' t

[~Var:]
  (ALOOKUP env x = SOME s ∧
   specialises_pred (SND ns) db s (Pred ps t) ∧
   has_dicts (SND ns) db ie lie ps ⇒
      type_elaborate_texp ns clk ie lie db st env (Var _ x) (Var ps x) t)

[~Pred:]
  type_elaborate_texp ns clk ie (lie ∪ set ps) db st env e e' t ∧
  pred_type_kind_ok clk (SND ns) db (Pred ps t) ∧
  (* enforces all variables in the predicates to be well scoped:
   * rejects `Read a, Show a => String -> String` *)
  pred_type_well_scoped (Pred ps t) ⇒
    pred_type_elaborate_texp ns clk ie lie db st env e e' (Pred ps t)

[~App:]
  type_elaborate_texp ns clk ie lie db st env e e' (Functions arg_tys ret_ty) ∧
  es ≠ [] ∧
  LIST_REL3 (type_elaborate_texp ns clk ie lie db st env) es es' arg_tys ⇒
    type_elaborate_texp ns clk ie lie db st env (App e es) (App e' es') ret_ty

[~Let:]
  pred_type_elaborate_texp ns clk ie lie (new ++ db) (MAP (tshift n) st)
    (tshift_env_pred n env) e1 e1' pt1 ∧
  type_elaborate_texp ns clk ie lie db st ((x,new,pt1)::env) e2 e2' t2 ⇒
     type_elaborate_texp ns clk ie lie db st env (Let (x,NONE) e1 e2)
        (Let (x,SOME (new,pt1)) e1' e2') t2

(* The poly type of the let binding is annotated by the user *)
[~LetSOME:]
  LENGTH new = n ∧
  type_elaborate_texp ns clk ie lie db st env (Let (x,NONE) e1 e2)
    (Let (x,SOME (new,pt)) e1' e2') t2 ⇒
      type_elaborate_texp ns clk ie lie db st env (Let (x,SONE (n,pt)) e1 e2)
        (Let (x,SOME (new,pt)) e1' e2') t2

[~Lam:]
  ty = Functions args_tys ret_ty ∧
  EVERY (type_ok (SND ns) db) args_tys ∧
  args_tys ≠ [] ∧
  (* forcing the length of vs to be the same as arg_tys and
  * handle user annotations in vs with args_tys *)
  LIST_REL (λot t'.
    case ot of
    | NONE => T
    | SOME t => t = t') (MAP SND vs) arg_tys ∧
  type_elaborate_texp ns clk ie lie db st
    (REVERSE (ZIP (MAP FST vs, MAP (λat. ([],Pred [] at)) arg_tys)) ++ env)
    e e' ret_ty ⇒
      type_elaborate_texp ns clk ie lie db st env (Lam vs e) (Lam vs e') ty

[~Letrec:]
   LIST_REL3
    (λ((fn,ot),body) ((fn',ot'),body') (varks,scheme).
      fn = fn' ∧
      ot' = SOME (varks,scheme) ∧
      (case ot of
      | NONE => T
      | SOME t => t = (LENGTH varks,scheme)) ∧
      pred_type_elaborate_texp ns clk ie lie (varks ++ db)
        (MAP (tshift $ LENGTH varks) st)
        (tshift_env_pred (LENGTH varks) $
          REVERSE (ZIP (MAP (FST o FST) fns', kind_schemes)) ++ env)
          body body' scheme)
    fns fns' kind_schemes ∧
   fns ≠ [] ∧
   type_elaborate_texp ns clk ie lie db st (REVERSE (ZIP (MAP (FST o FST) fns', kind_schemes)) ++ env) e e' t ⇒
      type_elaborate_texp ns clk ie lie db st env (Letrec fns e) (Letrec fns' e') t

[~Cons:]
  LIST_REL3 (type_elaborate_texp ns clk ie lie db st env) es es' carg_ts ∧
  type_cons (SND ns) db (cname,carg_ts) (tyid,tyargs) ∧
  ty = tcons_to_type (INL tyid) tyargs ⇒
     type_elaborate_texp ns clk ie lie db st env
       (Prim (Cons cname) es) (Prim (Cons cname) es') ty

[~Tuple:]
  LIST_REL3 (type_elaborate_texp ns clk ie lie db st env) es es' ts ∧
  (t = cons_types (Atom $ CompPrimTy $ Tuple (LENGTH ts)) ts) ⇒
     type_elaborate_texp ns clk ie lie db st env (Prim (Cons «») es) (Prim (Cons «») es') t

[~Ret:]
  type_elaborate_texp ns clk ie lie db st env e e' t ⇒
     type_elaborate_texp ns clk ie lie db st env
        (Prim (Cons «Ret») [e]) (Prim (Cons «Ret») [e']) (Monad t)

[~Bind:]
  type_elaborate_texp ns clk ie lie db st env e1 e1' (Monad t1) ∧
  type_elaborate_texp ns clk ie lie db st env e2 e2' (Functions [t1] (Monad t2)) ⇒
     type_elaborate_texp ns clk ie lie db st env
        (Prim (Cons «Bind») [e1;e2]) (Prim (Cons «Bind») [e1';e2']) (Monad t2)

[~Raise:]
  type_elaborate_texp ns clk ie lie db st env e e' (Atom Exception) ∧
  type_ok (SND ns) db t ⇒
     type_elaborate_texp ns clk ie lie db st env
        (Prim (Cons «Raise») [e]) (Prim (Cons «Raise») [e']) (Monad t)

[~Handle:]
  type_elaborate_texp ns clk ie lie db st env e1 e1' (Monad t) ∧
  type_elaborate_texp ns clk ie lie db st env e2 e2' (Functions [Atom Exception] (Monad t)) ⇒
     type_elaborate_texp ns clk ie lie db st env
        (Prim (Cons «Handle») [e1;e2]) (Prim (Cons «Handle») [e1';e2']) (Monad t)

[~Act:]
  type_elaborate_texp ns clk ie lie db st env e e' (Atom $ PrimTy Message) ⇒
     type_elaborate_texp ns clk ie lie db st env
      (Prim (Cons «Act») [e]) (Prim (Cons «Act») [e']) (Monad $ Atom $ PrimTy String)

[~Alloc:]
  type_elaborate_texp ns clk ie lie db st env e1 e1' (Atom $ PrimTy Integer) ∧
   type_elaborate_texp ns clk ie lie db st env e2 e2' t ⇒
      type_elaborate_texp ns clk ie lie db st env
        (Prim (Cons «Alloc») [e1;e2]) (Prim (Cons «Alloc») [e1';e2'])
        (Monad $ Cons (Atom $ CompPrimTy Array) t)

[~Length:]
  type_elaborate_texp ns clk ie lie db st env e e' (Cons (Atom $ CompPrimTy Array) t) ⇒
     type_elaborate_texp ns clk ie lie db st env
       (Prim (Cons «Length») [e]) (Prim (Cons «Length») [e'])
       (Monad $ Atom $ PrimTy Integer)

[~Deref:]
   type_elaborate_texp ns clk ie lie db st env e1 e1' (Cons (Atom $ CompPrimTy Array) t) ∧
   type_elaborate_texp ns clk ie lie db st env e2 e2' (Atom $ PrimTy Integer) ⇒
      type_elaborate_texp ns clk ie lie db st env
        (Prim (Cons «Deref») [e1;e2]) (Prim (Cons «Deref») [e1';e2']) (Monad t)

[~Update:]
   type_elaborate_texp ns clk ie lie db st env e1 e1' (Cons (Atom $ CompPrimTy Array) t) ∧
   type_elaborate_texp ns clk ie lie db st env e2 e2' (Atom $ PrimTy Integer) ∧
   type_elaborate_texp ns clk ie lie db st env e3 e3' t ⇒
      type_elaborate_texp ns clk ie lie db st env
        (Prim (Cons «Update») [e1;e2;e3]) (Prim (Cons «Update») [e1';e2';e3']) (Monad Unit)

[~Exception:]
   LIST_REL3 (type_elaborate_texp ns clk ie lie db st env) es es' carg_ts ∧
   type_exception (FST ns) (cname,carg_ts) ⇒
      type_elaborate_texp ns clk ie lie db st env
        (Prim (Cons cname) es) (Prim (Cons cname) es') (Atom Exception)

[~True:]
  type_elaborate_texp ns clk ie lie db st env (Prim (Cons «True») []) (Prim (Cons «True») []) (Atom $ PrimTy Bool)

[~False:]
  type_elaborate_texp ns clk ie lie db st env (Prim (Cons «False») []) (Prim (Cons «False») []) (Atom $ PrimTy Bool)

[~Loc:]
  oEL n st = SOME t ⇒
     type_elaborate_texp ns clk ie lie db st env
        (Prim (AtomOp $ Lit (Loc n)) []) (Prim (AtomOp $ Lit (Loc n)) [])
        (Cons (Atom $ CompPrimTy Array) t)

[~AtomOp:]
   LIST_REL3 (type_elaborate_texp ns clk ie lie db st env) es es' ts ∧
   get_PrimTys ts = SOME pts ∧
   type_atom_op aop pts primt ⇒
      type_elaborate_texp ns clk ie lie db st env
        (Prim (AtomOp aop) es) (Prim (AtomOp aop) es') (Atom $ PrimTy primt)

[~Seq:]
  type_elaborate_texp ns clk ie lie db st env e1 e1' t1 ∧
  type_elaborate_texp ns clk ie lie db st env e2 e2' t2 ⇒
     type_elaborate_texp ns clk ie lie db st env
        (Prim Seq [e1; e2]) (Prim Seq [e1';e2']) t2

[~NestedCase:]
  type_elaborate_texp ns clk ie lie db st env e e' vt ∧
  (* expression for each pattern type check *)
  LIST_REL
    (λ(p,e) (p',e').
      p' = p ∧
      ∃vts. type_cepat ns db p vt vts ∧
      type_elaborate_texp ns clk ie lie db st
        (REVERSE (MAP (λ(v,t). (v,[],Pred [] t)) vts) ++
          ((v,[],Pred [] vt)::env))
        e e' t)
    ((p,e1)::pes) ((p,e1')::pes') ∧
  (* exhaust all cases *)
  exhaustive_cepat ns db vt (p INSERT (IMAGE FST $ set pes)) ∧
  ¬MEM v (FLAT (MAP (cepat_vars_l ∘ FST) ((p,e)::pes))) ⇒
  type_elaborate_texp ns clk ie lie db st env
    (NestedCase e v p e1 pes) (NestedCase e' v p e1' pes') t
End

Definition type_elaborate_bindings_def:
   type_elaborate_bindings ns clk ie lie db st env fns fns' =
     LIST_REL
      (λ((fn,ot),body) ((fn',ot'),body').
        fn = fn' ∧
        (case ot' of
        | SOME (varks,scheme) =>
            pred_type_elaborate_texp ns clk ie lie (varks ++ db)
              (MAP (tshift $ LENGTH varks) st)
              (tshift_env_pred (LENGTH varks) env)
               body body' scheme ∧
          (case ot of
          | NONE => T
          | SOME t => t = (LENGTH varks,scheme))
        | _ => F)) fns fns'
End

Definition get_names_namespace_def:
  get_names_namespace (ns: exndef # typedefs) =
    (MAP FST $ FST ns) ++ FLAT (MAP (MAP FST o SND) $ SND ns)
End

Triviality MAX_SET_LE:
  FINITE s ∧ (∀y. y ∈ s ⇒ y ≤ x) ⇒
  MAX_SET s ≤ x
Proof
  strip_tac >>
  simp[GSYM GREATER_EQ] >>
  ho_match_mp_tac MAX_SET_ELIM >>
  simp[GREATER_EQ]
QED

Triviality MAX_SET_LT:
  FINITE s ∧ (∀y. y ∈ s ⇒ y < x) ∧ 0 < x ⇒
  MAX_SET s < x
Proof
  strip_tac >>
  simp[GSYM GREATER_DEF] >>
  ho_match_mp_tac MAX_SET_ELIM >>
  simp[GREATER_DEF]
QED

Definition lambda_vars_def:
  lambda_vars (Var _ _) = {} ∧
  lambda_vars (Prim _ es) = lambda_varsl es ∧
  lambda_vars (App f es) = lambda_vars f ∪ lambda_varsl es ∧
  lambda_vars (Lam vs e) = set (MAP FST vs) ∪ lambda_vars e ∧
  lambda_vars (Let v e e') =
    FST v INSERT lambda_vars e ∪ lambda_vars e' ∧
  lambda_vars (Letrec fns e') =
    set (MAP (FST o FST) fns) ∪
    lambda_varsl (MAP SND fns) ∪
    lambda_vars e' ∧
  lambda_vars (UserAnnot _ e) = lambda_vars e ∧
  lambda_vars (NestedCase g gv p e pes) =
    gv INSERT lambda_vars g ∪ cepat_vars p ∪ lambda_vars e ∪
    BIGUNION (set (MAP (cepat_vars o FST) pes)) ∪
    lambda_varsl (MAP SND pes) ∧
  lambda_varsl [] = {} ∧
  lambda_varsl (e::es) = lambda_vars e ∪ lambda_varsl es
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (λe. case e of
    | INR es => (MAX_SET (set (MAP (texp_size (K 1)) es)),LENGTH es + 1)
    | INL e => (texp_size (K 1) e,0))` >>
  rw[]
  >- (
    irule MAX_SET_LT >>
    rw[MEM_MAP] >>
    irule LESS_TRANS >>
    drule_then (irule_at (Pos hd)) $ cj 3 texp_size_lemma >>
    simp[]
  )
  >- (
    simp[GSYM LE_LT] >>
    irule in_max_set >>
    simp[]
  )
  >- (
    irule MAX_SET_LT >>
    rw[MEM_MAP] >>
    irule LESS_TRANS >>
    Cases_on `y''` >>
    simp[] >>
    drule_then (irule_at (Pos hd)) $ cj 2 texp_size_lemma >>
    simp[]
  )
  >- (
    irule MAX_SET_LT >>
    rw[MEM_MAP] >>
    irule LESS_TRANS >>
    Cases_on `y''` >>
    simp[] >>
    drule_then (irule_at (Pos hd)) $ cj 1 texp_size_lemma >>
    simp[]
  )
  >- (
    irule MAX_SET_LT >>
    rw[MEM_MAP] >>
    irule LESS_TRANS >>
    drule_then (irule_at (Pos hd)) $ cj 3 texp_size_lemma >>
    simp[]
  )
  >- (
    simp[GSYM LE_LT] >>
    irule MAX_SET_LE >>
    rw[MEM_MAP,PULL_EXISTS] >>
    irule in_max_set >>
    simp[MEM_MAP] >>
    metis_tac[]
  )
End

Theorem lambda_varsl_def:
  lambda_varsl es = BIGUNION (set (MAP lambda_vars es))
Proof
  Induct_on `es` >>
  simp[lambda_vars_def]
QED

Theorem lambda_vars_FINITE[simp]:
  (∀(e:'a texp). FINITE (lambda_vars e)) ∧
  ∀(es:'a texp list). FINITE (lambda_varsl es)
Proof
  ho_match_mp_tac lambda_vars_ind >>
  rw[lambda_vars_def,lambda_varsl_def,MEM_MAP,PULL_EXISTS,
    GSYM pure_cexpTheory.cepat_vars_l_correct]
QED

(*
* Dictionary construction given that we have the elaborated expression.
* texp_construct_dict:
*     ns: namespace                       all constructors
* ->  db: Kind list                       deBruijn indices in scope
* ->  ie: (mlstring |-> entailment)   instance environment
* -> lie: (mlstring |-> (class # type))       local instance environment
* -> env: mlstring set                    term variables in scope
* ->  ps: texp                           elaborated expression
* ->  ds:'a cexp                          translated cexp expression
*)
(* we need to record the variables/constructors to avoid name collision *)
Inductive texp_construct_dict:
[~Var:]
  construct_dicts (SND ns) db (ie:mlstring |-> entailment) lie ps ds ∧
  te = safeApp () (Var () x) ds ⇒
    texp_construct_dict ns ie lie db env (Var ps x) te

[~Pred:]
  (* enforce all variables in vs are fresh *)
  set vs ∩
    (FDOM lie ∪ FDOM ie ∪ env ∪
      set (get_names_namespace ns) ∪ lambda_vars e) = ∅ ∧
  LENGTH vs = LENGTH ps ∧
  texp_construct_dict ns ie (lie |++ ZIP (vs,ps)) db env e de ∧
  te = safeLam () vs de ⇒
    pred_texp_construct_dict ns ie lie db env (Pred ps t) e te

[~Let:]
  pred_texp_construct_dict ns ie lie (new ++ db) env pt e1 de1 ∧
  texp_construct_dict ns ie lie db (x INSERT env) e2 de2 ⇒
    texp_construct_dict ns ie lie db env
      (typeclass_texp$Let (x,SOME (new,pt)) e1 e2)
      (pure_cexp$Let () x de1 de2)

[~Letrec:]
  LIST_REL
    (λ((x,ot),e) (y,de).
      x = y ∧
      ∃new pt. ot = SOME (new,pt) ∧
        pred_texp_construct_dict ns ie lie (new ++ db)
          (env ∪ set (MAP (FST o FST) fns)) pt e de)
    fns dfns ∧
  texp_construct_dict ns ie lie db (env ∪ set (MAP (FST o FST) fns)) e2 de2 ∧
  fns ≠ [] ⇒
    texp_construct_dict ns ie lie db env
      (typeclass_texp$Letrec fns e2) (pure_cexp$Letrec () dfns de2)

[~Prim:]
  LIST_REL (texp_construct_dict ns ie lie db env) es des ⇒
    texp_construct_dict ns ie lie db env (Prim c es) (Prim () c des)

[~Lam:]
  texp_construct_dict ns ie lie db
    (set (MAP FST xs) ∪ env) e de ∧
  te = Lam () (MAP FST xs) de ⇒
      texp_construct_dict ns ie lie db env (Lam xs e) te

[~App:]
  texp_construct_dict ns ie lie db env e1 de1 ∧
  LIST_REL (texp_construct_dict ns ie lie db env) es des ⇒
    texp_construct_dict ns ie lie db env (App e1 es) (App () de1 des)

[~NestedCase:]
  texp_construct_dict ns ie lie db env e e' ∧
  LIST_REL (λ(p,e) (p',e'). p = p' ∧
      texp_construct_dict ns ie lie db (v INSERT env ∪ pure_cexp$cepat_vars p) e e')
    ((p,e1)::pes) ((p,e1')::pes') ⇒
  texp_construct_dict ns ie lie db env (NestedCase e v p e1 pes)
    (NestedCase () e' v p e1' pes')
End

(********************)
(* Prove that if we can type_elaborate, then we can do dictionary
* construction on the output *)

Triviality INFINITE_mlstring:
  INFINITE 𝕌(:mlstring)
Proof
  strip_assume_tac mlstringTheory.explode_BIJ >>
  strip_tac >>
  drule_all pred_setTheory.FINITE_BIJ >>
  simp[INFINITE_LIST_UNIV]
QED

Triviality DISTINCT_SUBSET:
  s ∩ u = {} ∧ v ⊆ u ⇒ s ∩ v = {}
Proof
  rw[] >>
  irule $ iffLR pred_setTheory.SUBSET_EMPTY >>
  irule pred_setTheory.SUBSET_TRANS >>
  drule_then (irule_at $ Pos last) $ iffRL pred_setTheory.SUBSET_EMPTY >>
  simp[] >>
  irule pred_setTheory.SUBSET_TRANS >>
  first_x_assum $ irule_at (Pos last) >>
  simp[]
QED

Triviality INFINITE_INTER_FINITE_EMPTY:
  ∀s. FINITE s ⇒ INFINITE (u:'a set) ⇒
    ∃v. INFINITE v ∧ v ⊆ u ∧ v ∩ s = ∅
Proof
  ho_match_mp_tac pred_setTheory.FINITE_INDUCT >>
  rw[]
  >- (qexists `u` >> simp[]) >>
  gvs[] >>
  qexists `v DIFF {e}` >>
  simp[pred_setTheory.DIFF_INTER] >>
  reverse $ conj_tac
  >- (
    conj_tac
    >- (
      irule pred_setTheory.SUBSET_TRANS >>
      irule_at (Pos hd) pred_setTheory.DIFF_SUBSET >>
      simp[]
    ) >>
    simp[Once pred_setTheory.INTER_COMM] >>
    simp[Once $ GSYM pred_setTheory.DIFF_INTER] >>
    simp[pred_setTheory.DIFF_INTER] >>
    simp[Once pred_setTheory.INTER_COMM]
  ) >>
  strip_tac >>
  `v ⊆ e INSERT (v DIFF {e})` by
    simp[pred_setTheory.SUBSET_DEF,
      pred_setTheory.INSERT_DEF,pred_setTheory.DIFF_DEF] >>
  qpat_x_assum `INFINITE v` mp_tac >>
  simp[] >>
  irule pred_setTheory.SUBSET_FINITE >>
  first_x_assum $ irule_at (Pos last) >>
  simp[]
QED

Triviality INFINITE_TAKE_N:
  INFINITE v ⇒ ∃s. s ⊆ v ∧ FINITE s ∧ CARD s = n
Proof
  Induct_on `n` >>
  rw[]
  >- (qexists `{}` >> simp[]) >>
  gvs[] >>
  drule_all_then strip_assume_tac pred_setTheory.IN_INFINITE_NOT_FINITE >>
  qexists `x INSERT s` >>
  simp[]
QED

Triviality EXISTS_fresh_vars_list:
  FINITE s ⇒
  ∃vs. LENGTH (vs:mlstring list) = n ∧ set vs ∩ s = {} ∧ ALL_DISTINCT vs
Proof
  strip_tac >>
  assume_tac INFINITE_mlstring >>
  drule_all_then strip_assume_tac INFINITE_INTER_FINITE_EMPTY >>
  drule_then (qspec_then `n` strip_assume_tac) INFINITE_TAKE_N >>
  qexists `SET_TO_LIST s'` >>
  simp[SET_TO_LIST_CARD,SET_TO_LIST_INV] >>
  irule $ iffLR pred_setTheory.SUBSET_EMPTY >>
  irule pred_setTheory.SUBSET_TRANS >>
  drule_then (irule_at $ Pos last) $ iffRL pred_setTheory.SUBSET_EMPTY >>
  simp[] >>
  irule pred_setTheory.SUBSET_TRANS >>
  first_x_assum $ irule_at (Pos last) >>
  simp[]
QED

Triviality DISTINCT_FRANGE:
  set (MAP FST l) ∩ FDOM m = {} ∧ ALL_DISTINCT (MAP FST l) ⇒
    FRANGE m ∪ set (MAP SND l) = FRANGE (m |++ l)
Proof
  Induct_on `l` >>
  rw[finite_mapTheory.FUPDATE_LIST_THM] >>
  Cases_on `h` >>
  gvs[finite_mapTheory.FUPDATE_FUPDATE_LIST_COMMUTES] >>
  simp[Once pred_setTheory.UNION_COMM,pred_setTheory.INSERT_UNION_EQ] >>
  AP_TERM_TAC >>
  simp[pred_setTheory.UNION_COMM] >>
  irule EQ_TRANS >>
  last_x_assum $ irule_at (Pos hd) >>
  conj_tac
  >- (
    irule $ iffLR pred_setTheory.SUBSET_EMPTY >>
    irule pred_setTheory.SUBSET_TRANS >>
    drule_then (irule_at $ Pos last) $ iffRL pred_setTheory.SUBSET_EMPTY >>
    simp[]
  ) >>
  simp[pred_setTheory.SET_EQ_SUBSET,
    finite_mapTheory.FRANGE_DOMSUB_SUBSET] >>
  rw[finite_mapTheory.FRANGE_DEF,pred_setTheory.SUBSET_DEF,
    pred_setTheory.EXTENSION,PULL_EXISTS] >>
  first_assum $ irule_at (Pos hd) >>
  `q ∉ FDOM (m |++ l)` suffices_by (
      rw[]
      >- (strip_tac >> gvs[]) >>
      AP_THM_TAC >> AP_TERM_TAC >>
      drule_then irule finite_mapTheory.DOMSUB_NOT_IN_DOM
    ) >>
  strip_tac >>
  gvs[MEM_MAP,finite_mapTheory.FDOM_FUPDATE_LIST,
    pred_setTheory.INSERT_INTER]
QED

Triviality DISTINCT_FRANGE_ZIP:
  LENGTH vs = LENGTH ps ∧
  set vs ∩ FDOM m = {} ∧ ALL_DISTINCT vs ⇒
    FRANGE m ∪ set ps = FRANGE (m |++ ZIP (vs,ps))
Proof
  strip_tac >>
  qspecl_then [`m`,`ZIP (vs,ps)`] assume_tac $ GEN_ALL DISTINCT_FRANGE >>
  gvs[MAP_ZIP]
QED

Theorem MAP_FST_tshift_env_pred[simp]:
  MAP FST (tshift_env_pred n env) = MAP FST env
Proof
  Induct_on `env` >>
  rw[] >>
  simp[ELIM_UNCURRY]
QED

Theorem type_cepat_cepat_vars:
  ∀p t vts. type_cepat ns db p t vts ⇒
    set (MAP FST vts) = cepat_vars p
Proof
  ho_match_mp_tac type_cepat_ind >>
  rw[pure_cexpTheory.cepat_vars_def] >>
  pop_assum mp_tac >>
  qid_spec_tac `vtss` >>
  qid_spec_tac `ts` >>
  qid_spec_tac `pats` >>
  ho_match_mp_tac LIST_REL3_induct >>
  rw[]
QED

Theorem type_elaborate_texp_IMP_texp_construct_dict:
  (∀lie db st env e e' pt.
    pred_type_elaborate_texp ns clk ie lie db st env e e' pt ⇒
    ∀lie_map.
      ie = FRANGE ie_map ∧
      lie = FRANGE lie_map ⇒
      ∃d. pred_texp_construct_dict ns
        ie_map lie_map db (set $ MAP FST env) pt e' d) ∧

  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    ∀lie_map.
      ie = FRANGE ie_map ∧
      lie = FRANGE lie_map ⇒
      ∃d. texp_construct_dict ns
        ie_map lie_map db (set $ MAP FST env) e' d)
Proof
  ho_match_mp_tac type_elaborate_texp_ind >>
  rw[]
  >- (
    irule_at (Pos hd) texp_construct_dict_Var >>
    metis_tac[has_dict_EXISTS_construct_dict]
  )
  >- (
    irule_at (Pos hd) texp_construct_dict_Pred >>
    qmatch_goalsub_abbrev_tac `set _ ∩ fs = _` >>
    `FINITE fs` by simp[Abbr`fs`] >>
    drule_then (qspec_then `LENGTH ps` strip_assume_tac)
      EXISTS_fresh_vars_list >>
    first_assum $ irule_at (Pos hd) >>
    simp[] >>
    first_x_assum irule >>
    irule DISTINCT_FRANGE_ZIP >>
    simp[Abbr`fs`] >>
    drule_then irule DISTINCT_SUBSET >>
    metis_tac[pred_setTheory.SUBSET_UNION,pred_setTheory.UNION_ASSOC]
  )
  >- (
    irule_at (Pos hd) texp_construct_dict_App >>
    simp[GSYM PULL_EXISTS] >>
    pop_assum mp_tac >>
    qid_spec_tac `arg_tys` >>
    qid_spec_tac `es'` >>
    qid_spec_tac `es` >>
    ho_match_mp_tac LIST_REL3_induct >>
    rw[] >>
    first_x_assum $ irule_at $ Pos last >>
    first_x_assum irule >>
    simp[]
  )
  >- (
    irule_at (Pos hd) texp_construct_dict_Let >>
    simp[GSYM PULL_EXISTS]
  )
  >- (
    irule_at (Pos hd) texp_construct_dict_Lam >>
    drule_then assume_tac $ cj 1 $ iffLR LIST_REL_EVERY_ZIP >>
    fs[rich_listTheory.MAP_REVERSE,MAP_ZIP]
  )
  >- (
    irule_at (Pos hd) texp_construct_dict_Letrec >>
    drule_then assume_tac $ cj 1 $ iffLR LIST_REL3_EL >>
    drule_then assume_tac $ cj 2 $ iffLR LIST_REL3_EL >>
    gvs[rich_listTheory.MAP_REVERSE,MAP_ZIP] >>
    simp[GSYM PULL_EXISTS] >>
    reverse conj_tac
    >- (
      reverse conj_tac
      >- (strip_tac >> gvs[]) >>
      simp[Once pred_setTheory.UNION_COMM] >>
      metis_tac[]
    ) >>
    qpat_x_assum `LIST_REL3 _ _ _ _` mp_tac >>
    qpat_abbrev_tac `l = set (MAP (FST o FST) fns')` >>
    pop_assum $ assume_tac o REWRITE_RULE[markerTheory.Abbrev_def] >>
    strip_tac >>
    drule $ cj 2 $ iffLR pred_setTheory.SET_EQ_SUBSET >>
    pop_assum mp_tac >>
    qid_spec_tac `kind_schemes` >>
    qid_spec_tac `fns'` >>
    qid_spec_tac `fns` >>
    ho_match_mp_tac LIST_REL3_induct >>
    rw[ELIM_UNCURRY] >>
    gvs[pred_setTheory.UNION_COMM,PULL_EXISTS] >>
    first_x_assum $ irule_at (Pos last) >>
    simp[Once LAMBDA_PROD,GSYM PEXISTS_THM] >>
    irule_at (Pos hd) $ GSYM PAIR >>
    simp[]
  )
  >- (
    irule_at (Pos hd) texp_construct_dict_Prim >>
    pop_assum mp_tac >>
    qid_spec_tac `carg_ts` >>
    qid_spec_tac `es'` >>
    qid_spec_tac `es` >>
    ho_match_mp_tac LIST_REL3_induct >>
    rw[GSYM PULL_EXISTS]
  )
  >- (
    irule_at (Pos hd) texp_construct_dict_Prim >>
    pop_assum mp_tac >>
    qid_spec_tac `ts` >>
    qid_spec_tac `es'` >>
    qid_spec_tac `es` >>
    ho_match_mp_tac LIST_REL3_induct >>
    rw[GSYM PULL_EXISTS]
  )
  >> TRY (
    irule_at (Pos hd) texp_construct_dict_Prim >>
    pop_assum $ qspec_then `lie_map` mp_tac >>
    rw[GSYM PULL_EXISTS]
  )
  >- (
    irule_at (Pos hd) texp_construct_dict_Prim >>
    pop_assum mp_tac >>
    qid_spec_tac `carg_ts` >>
    qid_spec_tac `es'` >>
    qid_spec_tac `es` >>
    ho_match_mp_tac LIST_REL3_induct >>
    rw[GSYM PULL_EXISTS]
  )
  >- (
    irule_at (Pos hd) texp_construct_dict_Prim >>
    simp[LIST_REL_rules]
  )
  >- (
    irule_at (Pos hd) texp_construct_dict_Prim >>
    simp[LIST_REL_rules]
  )
  >- (
    irule_at (Pos hd) texp_construct_dict_Prim >>
    simp[LIST_REL_rules]
  )
  >- (
    irule_at (Pos hd) texp_construct_dict_Prim >>
    pop_assum mp_tac >>
    qid_spec_tac `ts` >>
    qid_spec_tac `es'` >>
    qid_spec_tac `es` >>
    ho_match_mp_tac LIST_REL3_induct >>
    rw[GSYM PULL_EXISTS]
  ) >>
  irule_at (Pos hd) texp_construct_dict_NestedCase >>
  simp[GSYM PULL_EXISTS] >>
  conj_tac
  >- (
    last_x_assum $ qspec_then `lie_map` kall_tac >>
    last_x_assum $ qspec_then `lie_map` mp_tac >>
    drule type_cepat_cepat_vars >>
    rw[rich_listTheory.MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF] >>
    pop_assum $ mp_tac o SRULE[LAMBDA_PROD,miscTheory.FST_pair] >>
    metis_tac[UNION_COMM,INSERT_UNION_EQ]
  ) >>
  pop_assum mp_tac >>
  qid_spec_tac `pes'` >>
  qid_spec_tac `pes` >>
  ho_match_mp_tac LIST_REL_ind >>
  rw[PULL_EXISTS] >>
  first_x_assum $ irule_at (Pos last) >>
  fs[rich_listTheory.MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
  drule_then assume_tac type_cepat_cepat_vars >>
  fs[UNION_COMM,INSERT_UNION_EQ,ETA_AX] >>
  simp[LAMBDA_PROD,GSYM PEXISTS_THM]
QED

(********************)
(* ``class Ord a => Num a where
*     f :: a -> a -> a``,
* would be an entry Num |-> ([Ord],[(f,forall a. a -> a -> a)]),
* note that we only have `a` as the type variable
* in the type of `f` *)
Type class_env[pp] = ``:(mlstring # (* class name *)
  (Kind # (* the kind of the parameter *)
  (mlstring list # (* list of super classes *)
  ((mlstring # pred_type_kind_scheme) list)))) list``; (* types of each method *)

Definition ce_to_clk_def:
  ce_to_clk (ce:class_env) = λc. OPTION_MAP FST (ALOOKUP ce c)
End

Definition class_env_kind_ok_def:
  class_env_kind_ok tdefs (ce:class_env) ⇔
    let clk = ce_to_clk ce in
    (∀c k supers methods. MEM (c,k,supers,methods) ce ⇒
      EVERY (pred_type_kind_scheme_ok clk tdefs [k]) (MAP SND methods) ∧
      EVERY (λs. clk s = SOME k) supers)
End

(* classname, method name, implementation *)
Type default_impl[pp] = ``:mlstring # ('a texp)``;
Type default_impls[pp] = ``:'a default_impl list``;

Definition type_elaborate_default_impl_def:
  type_elaborate_default_impl ce ns clk ie st env meth e e' ⇔
    ∃cl k s methods ks ps t.
      ALOOKUP (ce:class_env) cl = SOME (k,s,methods) ∧
      ALOOKUP methods meth = SOME (ks,Pred ps t) ∧
      pred_type_elaborate_texp ns clk ie EMPTY (k::ks) st env e e'
        (Pred ((cl,TypeVar 0)::ps) t)
End

Definition type_elaborate_default_impls_def:
  type_elaborate_default_impls ce ns clk ie st env defaults
    (defaults': Kind list default_impls) ⇔
  LIST_REL (λ(meth,e) (meth',e'). meth = meth' ∧
    type_elaborate_default_impl ce ns clk ie st env meth e e'
    ) defaults defaults'
End

Definition default_impl_construct_dict_def:
  default_impl_construct_dict ns ie env cl k (ks,Pred ps t) e e' ⇔
    pred_texp_construct_dict ns ie FEMPTY (k::ks) env
      (Pred ((cl,TypeVar 0)::ps) t) e e'
End

Definition default_impls_construct_dict_def:
  default_impls_construct_dict ns ce ie env
    default_name_map defaults defaults' ⇔
  LIST_REL (λ(meth,e) (name,e').
    ∃cl k supers meths pt.
      ALOOKUP default_name_map meth = SOME name ∧
      ALOOKUP ce cl = SOME (k,supers,meths) ∧
      ALOOKUP meths meth = SOME pt ∧
      default_impl_construct_dict ns ie env cl k pt e e')
    (defaults:Kind list default_impls) defaults'
End

Theorem default_impls_construct_dict_names:
  ∀defaults defaults'.
    default_impls_construct_dict ns ce ie env
      default_name_map defaults defaults' ⇒
    set (MAP FST defaults') ⊆ set (MAP SND default_name_map)
Proof
  simp[default_impls_construct_dict_def] >>
  ho_match_mp_tac LIST_REL_ind >>
  rw[default_impls_construct_dict_def,MEM_MAP,ELIM_UNCURRY] >>
  rev_drule ALOOKUP_MEM >>
  simp[LAMBDA_PROD,GSYM PEXISTS_THM] >>
  metis_tac[]
QED

Type instance_env[pp] = ``:((mlstring # 'a # type) #
  (((mlstring # type) list) # ((mlstring # 'a texp) list))) list``;

Definition translate_predicate_def:
  translate_predicate cl_to_tyid p = do
    pid <- FLOOKUP cl_to_tyid (FST p);
    return $ Cons (UserType pid) (SND p)
  od
End

Definition translate_predicates_def:
  translate_predicates cl_to_tyid [] = SOME [] ∧
  translate_predicates cl_to_tyid (p::ps) = do
    p' <- translate_predicate cl_to_tyid p;
    ps' <- translate_predicates cl_to_tyid ps;
    return $ p'::ps'
  od
End

Definition translate_pred_type_def:
  translate_pred_type cl_to_tyid (Pred ps t) = do
    args <- translate_predicates cl_to_tyid ps;
    return $ Functions args t
  od
End

Definition translate_pred_type_scheme_def:
  translate_pred_type_scheme cl_to_tyid pt = do
    t <- translate_pred_type cl_to_tyid (SND pt);
    return (FST pt,t)
  od
End

Definition translate_superclasses_def:
  translate_superclasses cl_to_tyid [] = SOME [] ∧
  translate_superclasses cl_to_tyid (c::cs) = do
    sid <- FLOOKUP cl_to_tyid c;
    cs' <- translate_superclasses cl_to_tyid cs;
    SOME $ ([]:Kind list,typeclass_types$Cons (UserType sid) (TypeVar 0))::cs';
  od
End

Type tcexp_typedef[pp] = ``:Kind list # ((mlstring # type_kind_scheme list) list)``;
Type tcexp_typedefs[pp] = ``:tcexp_typedef list``;
Type tcexp_namespace[pp] = ``:exndef # tcexp_typedefs``;

Definition namespace_to_tcexp_namespace_def:
  namespace_to_tcexp_namespace (ns:exndef # typedefs) =
    ((FST ns,MAP (I ## MAP (I ## MAP ($, []))) (SND ns))):tcexp_namespace
End

(* a distinct type id and a distinct constructor name will be
* generated for each class *)
(* create a data type for a type class *)
Definition class_to_datatype_def:
  class_to_datatype (cenv:class_env) cl_to_tyid cname (c,k,supers,methods) = do
    method_tys <- OPT_MMAP (translate_pred_type_scheme cl_to_tyid)
      (MAP SND methods);
    sup_tys <- translate_superclasses cl_to_tyid supers;
    return $ (([k],[(cname,sup_tys ++ method_tys)]):tcexp_typedef)
  od
End

Definition class_env_to_ns_def:
  class_env_to_ns (cenv:class_env) cl_to_tyid cons [] = SOME [] ∧
  class_env_to_ns (cenv:class_env) cl_to_tyid (con::cons) (cl::rest) = do
    dt <- class_to_datatype cenv cl_to_tyid con cl;
    ns <- class_env_to_ns cenv cl_to_tyid cons rest;
    return $ (dt::ns)
  od
End

Definition get_method_type_def:
  get_method_type cl k (ks,Pred ps t) = (k::ks,Pred ((cl,TypeVar 0)::ps) t)
End

Definition class_env_to_env_def:
  class_env_to_env (cenv:class_env) = LIST_BIND cenv
    (λ(cl,k,_,methods).
      MAP (I ## get_method_type cl k) methods)
End

Theorem class_env_to_env_FST_methods_name:
  MAP FST (class_env_to_env ce) = FLAT (MAP (MAP FST ∘ SND ∘ SND ∘ SND) ce)
Proof
  simp[class_env_to_env_def,LIST_BIND_def,MAP_FLAT,MAP_MAP_o] >>
  AP_TERM_TAC >>
  AP_THM_TAC >>
  AP_TERM_TAC >>
  simp[ELIM_UNCURRY,get_method_type_def,FUN_EQ_THM]
QED

Definition translate_entailment_def:
  translate_entailment cl_to_tyid (Entail ks ps q) = do
    pts <- translate_predicates cl_to_tyid ps;
    qt <- translate_predicate cl_to_tyid q;
    return $ (ks,Functions pts qt)
  od
End

Definition translate_env_def:
  translate_env cl_to_tyid [] = SOME [] ∧
  translate_env cl_to_tyid ((name,pt)::env) = do
    pt' <- translate_pred_type_scheme cl_to_tyid pt;
    env' <- translate_env cl_to_tyid env;
    SOME $ (name,pt')::env'
  od
End

(* ie: mlstring |-> entailment *)
Definition translate_ie_alist_def:
  translate_ie_alist cl_to_tyid [] = return [] ∧
  translate_ie_alist cl_to_tyid ((name,ent)::ie) = do
    t <- translate_entailment cl_to_tyid ent;
    ie' <- translate_ie_alist cl_to_tyid ie;
    return $ (name,t)::ie'
  od
End

(* lie: mlstring |-> (class # type) *)
Definition translate_lie_alist_def:
  translate_lie_alist cl_to_tyid [] = return [] ∧
  translate_lie_alist cl_to_tyid ((name,cl,t)::lie) = do
    cid <- FLOOKUP cl_to_tyid cl;
    lie' <- translate_lie_alist cl_to_tyid lie;
    return $ (name,[],Cons (UserType cid) t)::lie';
  od
End

Definition class_to_entailments_def:
  class_to_entailments (class,k,supers,_) =
    MAP (λs. Entail [k] [class,TypeVar 0] (s,TypeVar 0)) supers
End

Definition class_env_to_ie_def:
  class_env_to_ie (clenv:class_env) = LIST_BIND clenv class_to_entailments
End

Definition select_nth_cepat_def:
  select_nth_cepat 0 m var = cepatVar var::REPLICATE m cepatUScore ∧
  select_nth_cepat (SUC n) m var = cepatUScore::select_nth_cepat n m var
End

Definition nth_from_dict_def:
  nth_from_dict cons len n = Lam () [«x»]
    (NestedCase () (pure_cexp$Var () «x») «x»
      (cepatCons cons (select_nth_cepat n (len - 1 - n) «y»))
        (Var () «y»)
      [])
End

Definition translate_methods_aux_def:
  translate_methods_aux con len n [] = [] ∧
  translate_methods_aux con len n (meth::meths) =
    (meth,nth_from_dict con len n)::
      translate_methods_aux con len (SUC n) meths
End

Definition class_env_construct_dict_def:
  class_env_construct_dict cons sup_vs [] = [] ∧
  class_env_construct_dict (con::cons) sup_vs ((cl,k,supers,meths)::ce) =
  let len = LENGTH supers + LENGTH meths in
  (translate_methods_aux con len 0
    (TAKE (LENGTH supers) sup_vs ++ MAP FST meths)) ++
    class_env_construct_dict cons (DROP (LENGTH supers) sup_vs) ce
End

Definition instance_kind_check_def:
  instance_kind_check tdefs clk ((class,n,t),cstrs,impls) ((class',varks,t'),cstrs',impls') ⇔
    class = class' ∧ t = t' ∧ cstrs = cstrs' ∧
    LENGTH varks = n ∧
    ∃k. clk class = SOME k ∧ kind_ok tdefs varks k t ∧
    EVERY (λ(c,t).
      clk c = SOME k ∧ kind_ok tdefs varks k t) cstrs
End

Definition instance_env_kind_check_def:
  instance_env_kind_check tdefs clk (inst_env:num instance_env) (inst_env':
  Kind list instance_env) ⇔
     LIST_REL (instance_kind_check tdefs clk) inst_env inst_env'
End

Definition instance_to_entailment_def:
  instance_to_entailment ((class,varks,t),cstrs,meths) =
    Entail varks cstrs (class,t)
End

Definition instance_env_to_ie_def:
  instance_env_to_ie (inst_env: (Kind list) instance_env) =
    MAP instance_to_entailment inst_env
End

Definition impl_construct_dict_def:
  impl_construct_dict ns ie env vs cstrs ks pt e e' ⇔
  pred_texp_construct_dict ns ie (FEMPTY |++ ZIP (vs,cstrs)) ks env
    pt e (safeLam () vs e')
End

Definition type_elaborate_impls_def:
  type_elaborate_impls ns clk ie st env varks cstrs inst_t meths impls impls' ⇔
    (LIST_REL (λimpl impl'.
       FST impl = FST impl' ∧
       ∃meth_ks pt.
         ALOOKUP meths (FST impl) = SOME (meth_ks,pt) ∧
         pred_type_elaborate_texp ns clk ie (set cstrs) (varks ++ meth_ks)
           st env (SND impl) (SND impl')
           (tsubst_pred [inst_t] $ shift_db_pred 1n (LENGTH varks) pt))
       impls impls')
End

Definition type_elaborate_inst_env_def:
  type_elaborate_inst_env ns (ce:class_env) clk ie st env
      (inst_env:num instance_env) (inst_env':Kind list instance_env) ⇔
  LIST_REL (λinst ((c,varks,t),cstrs,impls').
    ∃k supers meths.
    ALOOKUP ce c = SOME (k,supers,meths) ∧
    type_elaborate_impls ns clk ie st env varks cstrs t meths (SND $ SND inst) impls')
    inst_env inst_env'
End

(* default_name maps a method name to a translated name *)
(* inst_v is for referencing the dict itself *)
Definition instance_construct_dict_def:
  instance_construct_dict ns ie env
    cons supers meths defaults
    inst_v varks cstrs inst_t impls trans_inst ⇔
  ∃vs supers' impls'.
  trans_inst = safeLam () vs (Prim () (Cons cons) $ supers' ++ impls') ∧
  construct_dicts (SND ns) varks ie (FEMPTY |++ ZIP (vs,cstrs))
    (MAP (λsuper. (super,inst_t)) supers) supers' ∧
  LIST_REL (λ(name,(meth_ks,pt)) e'.
      case ALOOKUP impls name of
      | SOME e =>
          impl_construct_dict ns ie env vs cstrs (varks++meth_ks)
            (tsubst_pred [inst_t] $
              shift_db_pred 1n (LENGTH varks) pt) e e'
      | NONE => ∃default_name.
          ALOOKUP defaults name = SOME default_name ∧
          e' = App () (Var () default_name) [Var () inst_v])
     meths impls'
End

Definition instance_env_construct_dict_def:
  instance_env_construct_dict ns ce ie env cl_cons default_name_map
    inst_vs (inst_env:Kind list instance_env) inst_env' ⇔
  LIST_REL3 (λinst_v ((cl,varks,inst_t),cstrs,impls) (v,e).
    v = inst_v ∧
    ∃k supers meths cons.
    ALOOKUP ce cl = SOME (k,supers,meths) ∧
    ALOOKUP cl_cons cl = SOME cons ∧
    instance_construct_dict ns ie env
      cons supers meths default_name_map
      inst_v varks cstrs inst_t impls e
  ) inst_vs inst_env inst_env'
End

Definition type_elaborate_prog_def:
  type_elaborate_prog ns ce st defaults inst_env fns
    defaults' inst_env' fns' ⇔
  ∃clk env fns_type_scheme ie.
    clk = ce_to_clk ce ∧
    instance_env_kind_check (SND ns) clk inst_env inst_env' ∧
    ie = set (class_env_to_ie ce ++ instance_env_to_ie inst_env') ∧
    OPT_MMAP (SND ∘ FST) fns' = SOME fns_type_scheme ∧
    env =
      REVERSE (ZIP (MAP (FST ∘ FST) fns,fns_type_scheme)) ++
      class_env_to_env ce ∧
     EVERY (λscheme.
        ∃varks ty. scheme = (varks,ty) ∧
        pred_type_kind_ok clk (SND ns) varks ty) fns_type_scheme ∧
   type_elaborate_default_impls ce ns clk ie st env defaults defaults' ∧
   type_elaborate_bindings ns clk ie ∅ [] st env fns fns' ∧
   type_elaborate_inst_env ns ce clk ie st env inst_env inst_env'
End

Definition prog_construct_dict_def:
  prog_construct_dict ns ce defaults inst_env fns
    translated_ns output_bindings ⇔
  ∃cl_cons cl_ns cl_to_tyid default_name_map env ie inst_vs sup_vs
     translated_ce translated_defaults translated_fns translated_inst_env.
   output_bindings =
     translated_fns ++ translated_defaults ++
     translated_inst_env ++ translated_ce ∧
   LENGTH sup_vs = LENGTH (class_env_to_ie ce) ∧
   LENGTH inst_vs = LENGTH inst_env ∧
   ALL_DISTINCT sup_vs ∧
   ALL_DISTINCT inst_vs ∧
   ALL_DISTINCT $ MAP FST $ class_env_to_env ce ∧
   ALL_DISTINCT $ MAP SND default_name_map ∧
   set sup_vs ∩ set inst_vs ∩
    set (MAP FST $ class_env_to_env ce) ∩ set (MAP SND default_name_map) ∩
    (set (MAP (FST o FST) fns) ∪ lambda_varsl (MAP SND fns)) = ∅ ∧
   ie = FEMPTY |++
     (ZIP (sup_vs,class_env_to_ie ce) ++
      ZIP (inst_vs,instance_env_to_ie inst_env)) ∧
   env = set (MAP (FST ∘ FST) fns ++ MAP FST (class_env_to_env ce)) ∧
   cl_to_tyid = FEMPTY |++
     ZIP (MAP FST ce,GENLIST (λn. n + LENGTH (SND ns)) (LENGTH ce)) ∧
   MAP FST cl_cons = MAP FST ce ∧
   class_env_to_ns ce cl_to_tyid (MAP SND cl_cons) ce = SOME
  cl_ns ∧
   translated_ns =
     append_ns (namespace_to_tcexp_namespace ns) ([],cl_ns) ∧
   translated_ce = class_env_construct_dict (MAP SND cl_cons) sup_vs ce ∧
   instance_env_construct_dict ns ce ie env cl_cons default_name_map
     inst_vs inst_env translated_inst_env ∧
   default_impls_construct_dict ns ce ie env default_name_map defaults
     translated_defaults ∧
   LIST_REL
     (λ((x,ot),e) (y,de).
          x = y ∧
          case ot of
          | SOME (new,pt) =>
            pred_texp_construct_dict ns ie FEMPTY new env pt e
              de
          | NONE => F)
      fns translated_fns
End

Theorem subst_db_Functions:
  subst_db skip ts (Functions args ret) =
  Functions (MAP (subst_db skip ts) args)
    (subst_db skip ts ret)
Proof
  Induct_on `args` >>
  rw[Functions_def,subst_db_def]
QED

Theorem shift_db_Functions:
  shift_db skip n (Functions args ret) =
  Functions (MAP (shift_db skip n) args)
    (shift_db skip n ret)
Proof
  Induct_on `args` >>
  rw[Functions_def,shift_db_def]
QED

Theorem Functions_Functions:
  Functions args_ty (Functions args_ty2 ret_ty) =
    Functions (args_ty ++ args_ty2) ret_ty
Proof
  Induct_on `args_ty` >>
  simp[Functions_def]
QED

Theorem collect_type_vars_Functions:
  collect_type_vars (Functions args ret) =
    BIGUNION (set (MAP collect_type_vars args)) ∪ collect_type_vars ret
Proof
  Induct_on `args` >>
  rw[Functions_def,collect_type_vars_def] >>
  metis_tac[UNION_COMM,UNION_ASSOC]
QED

Theorem subst_db_empty:
  subst_db skip [] t = t
Proof
  Induct_on `t` >>
  simp[subst_db_def] >>
  Cases_on `a` >>
  simp[subst_db_def]
QED

Theorem has_dicts_empty:
  has_dicts tdefs db ie lie []
Proof
  irule has_dict_dicts >>
  simp[]
QED

Theorem kind_wf_simp[simp]:
  (∀t1 t2. kind_wf cdb vdb k (Cons t1 t2) ⇔
    ∃k1 k2. k1 = kindArrow k2 k ∧
    kind_wf cdb vdb k1 t1 ∧ kind_wf cdb vdb k2 t2) ∧
  (∀t. kind_wf cdb vdb k (Atom (PrimTy t)) ⇔ k = kindType) ∧
  (kind_wf cdb vdb k (Atom Exception) ⇔ k = kindType) ∧
  (∀v. kind_wf cdb vdb k (TypeVar v) ⇔ vdb v = SOME k) ∧
  (∀v. kind_wf cdb vdb k (UserType v) ⇔ cdb v = SOME k) ∧
  (kind_wf cdb vdb k (Atom (CompPrimTy Function)) ⇔
    k = kindArrow kindType (kindArrow kindType kindType)) ∧
  (kind_wf cdb vdb k (Atom (CompPrimTy Array)) ⇔
    k = kindArrow kindType kindType) ∧
  (kind_wf cdb vdb k (Atom (CompPrimTy M)) ⇔
    k = kindArrow kindType kindType) ∧
  (∀n. kind_wf cdb vdb k (Atom (CompPrimTy (Tuple n))) ⇔
    k = kind_arrows (GENLIST (K kindType) n) kindType)
Proof
  rpt (simp[Once kind_wf_cases])
QED

Theorem kind_wf_Functions:
   kind_wf cdb vdb k (Functions args ret) ⇔
    (kind_wf cdb vdb k ret ∧ args = []) ∨
    (k = kindType ∧ kind_wf cdb vdb kindType ret ∧
      ∀arg. MEM arg args ⇒ kind_wf cdb vdb kindType arg)
Proof
  Induct_on `args` >>
  rw[Functions_def,EQ_IMP_THM] >>
  gvs[]
QED

(* Monoid [mappend;mempty], Foldable [foldMap] *)
Definition test_class_env_def:
  test_class_env:class_env = [
    («Semigroup»,
      (kindType,[],[(
        «mappend»,
        [],Pred [] (Functions [TypeVar 0;TypeVar 0] (TypeVar 0)))]));
    («Monoid»,
      (kindType,[«Semigroup»],[(
        «mempty»,[],Pred [] (TypeVar 0))]));
    («Foldable»,
      (kindArrow kindType kindType,[],[
       (* Monoid m => (a -> m) -> t a -> m *)
       («foldMap»,[kindType;kindType],
          Pred [(«Monoid»,TypeVar 2)] $
          Functions [Functions [TypeVar 1] (TypeVar 2);
            Cons (TypeVar 0) (TypeVar 1)] (TypeVar 2));
       («toList»,[kindType], Pred [] $
          Functions [Cons (TypeVar 0) (TypeVar 1)] (Cons (UserType 0)
          (TypeVar 1)))]))]
End

Definition test_defaults_def:
  test_defaults:'a default_impls = [«toList»,
    App (Var [] «foldMap») [Lam [«x»,NONE] $
      (Prim (Cons «::») [Var [] «x»;Prim (Cons «[]») []])
    ]
  ]
End

Definition test_defaults_elaborated_def:
  test_defaults_elaborated:Kind list default_impls = [«toList»,
    App (Var [«Foldable»,TypeVar 0;«Monoid»,Cons (UserType 0) (TypeVar 1)] «foldMap») [Lam [«x»,NONE] $
      (Prim (Cons «::») [Var [] «x»;Prim (Cons «[]») []])
    ]
  ]
End
Overload Tup = ``λn. Atom $ CompPrimTy $ Tuple n``;

Definition test_instance_env_def:
  test_instance_env = [
    ((«Semigroup»,0n,Atom $ PrimTy Integer),[],
      [«mappend»,typeclass_texp$Lam [«x»,NONE;«y»,NONE]
        (Prim (AtomOp Add) [Var [] «x»;Var [] «y»])]);
    ((«Monoid»,0,Atom $ PrimTy Integer),[],
      [«mempty»,Prim (AtomOp (Lit (Int 0))) []]);
    ((«Foldable»,0,UserType 0),[],
      [«foldMap»,typeclass_texp$Lam [«f»,NONE;«t»,NONE] $
          typeclass_texp$NestedCase (Var [] «t») «t»
            (cepatCons «::» [cepatVar «h»;cepatVar «tl»])
              (App (Var [] «mappend») [
                App (Var [] «f») [Var [] «h»];
                App (Var [] «foldMap») [Var [] «f»;Var [] «tl»]])
            [cepatUScore,Var [] «mempty»]]);
    ((«Semigroup»,1,Cons (UserType 0) (TypeVar 0)),[],
      [«mappend»,Var [] «append»]);
    ((«Monoid»,1,Cons (UserType 0) (TypeVar 0)),[],
      [«mempty»,Prim (Cons «[]») []]);
    ((«Monoid»,2,
      Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1)),
      [«Monoid»,TypeVar 0;«Monoid»,TypeVar 1],
      [«mempty»,Prim (Cons «»)
        [Var [] «mempty»;Var [] «mempty»]]);
    ((«Semigroup»,2,
      Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1)),
      [«Semigroup»,TypeVar 0;«Semigroup»,TypeVar 1],
      [«mappend»,Lam [«x»,NONE;«y»,NONE] $
          typeclass_texp$NestedCase
            (Prim (Cons «») [Var [] «x»;Var [] «y»]) «p»
            (cepatCons «» [
              cepatCons «» [cepatVar «x1»;cepatVar «x2»];
              cepatCons «» [cepatVar «y1»;cepatVar «y2»]])
              (Prim (Cons «») [
                App (Var [] «mappend»)
                  [Var [] «x1»;Var [] «y1»];
                App (Var [] «mappend»)
                  [Var [] «x2»;Var [] «y2»]])
            []])
  ]
End

Definition test_instance_env_elaborated_def:
  test_instance_env_elaborated = [
    ((«Semigroup»,[],Atom $ PrimTy Integer),[],
      [«mappend»,typeclass_texp$Lam [«x»,NONE;«y»,NONE]
        (Prim (AtomOp Add) [Var [] «x»;Var [] «y»])]);
    ((«Monoid»,[],Atom $ PrimTy Integer),[],
      [«mempty»,Prim (AtomOp (Lit (Int 0))) []]);
    ((«Foldable»,[],UserType 0),[],
      [«foldMap»,typeclass_texp$Lam [«f»,NONE;«t»,NONE] $
          typeclass_texp$NestedCase (Var [] «t») «t»
            (cepatCons «::» [cepatVar «h»;cepatVar «tl»])
              (App (Var [(«Semigroup»,TypeVar 1)] «mappend») [
                App (Var [] «f») [Var [] «h»];
                App (Var [
                    («Foldable»,UserType 0);
                    («Monoid»,TypeVar 1)] «foldMap»)
                  [Var [] «f»;Var [] «tl»]])
            [cepatUScore,Var [(«Monoid»,TypeVar 1)] «mempty»]]);
    ((«Semigroup»,[kindType],Cons (UserType 0) (TypeVar 0)),[],
      [«mappend»,Var [] «append»]);
    ((«Monoid»,[kindType],Cons (UserType 0) (TypeVar 0)),[],
      [«mempty»,Prim (Cons «[]») []]);
    ((«Monoid»,[kindType;kindType],
      Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1)),
      [«Monoid»,TypeVar 0;«Monoid»,TypeVar 1],
      [«mempty»,Prim (Cons «»)
        [Var [«Monoid»,TypeVar 0] «mempty»;
         Var [«Monoid»,TypeVar 1] «mempty»]]);
    ((«Semigroup»,[kindType;kindType],
      Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1)),
      [«Semigroup»,TypeVar 0;«Semigroup»,TypeVar 1],
      [«mappend»,Lam [«x»,NONE;«y»,NONE] $
          typeclass_texp$NestedCase
            (Prim (Cons «») [Var [] «x»;Var [] «y»]) «p»
            (cepatCons «» [
              cepatCons «» [cepatVar «x1»;cepatVar «x2»];
              cepatCons «» [cepatVar «y1»;cepatVar «y2»]])
              (Prim (Cons «») [
                App (Var [«Semigroup»,TypeVar 0] «mappend»)
                  [Var [] «x1»;Var [] «y1»];
                App (Var [«Semigroup»,TypeVar 1] «mappend»)
                  [Var [] «x2»;Var [] «y2»]])
            []])
  ]
End

Definition test_prog_def:
  test_prog = [
    («append»,NONE),Lam [«l»,NONE;«r»,NONE] $
    NestedCase (Var [] «l») «l»
      (cepatCons «::» [cepatVar «h»; cepatVar «tl»])
        (Prim (Cons «::») [Var [] «h»;
          App (Var [] «append») [Var [] «tl»; Var [] «r»]])
      [cepatCons «[]» [],Var [] «r»];

    («test»,NONE),
      Letrec [(«fold»,NONE),
        App (Var [] «foldMap») [Lam [«x»,NONE] (Var [] «x»)]] $
      App (Var [] «fold») [App (Var [] «fold»)
        [App (Var [] «toList») [Prim (Cons «::») [
          Prim (Cons «::») [
            Prim (Cons «») [
              Prim (AtomOp $ Lit (Int 1)) [];
              Prim (AtomOp $ Lit (Int 1)) []];
            Prim (Cons «[]») []];
          Prim (Cons «[]») []]]]]
  ]
End

Definition test_prog_elaborated_def:
  test_prog_elaborated = [
    («append»,SOME ([kindType],
      Pred [] $ Functions [
        Cons (UserType 0) (TypeVar 0);
        Cons (UserType 0) (TypeVar 0)] $
        Cons (UserType 0) (TypeVar 0))),
    Lam [«l»,NONE;«r»,NONE] $
      NestedCase (Var [] «l») «l»
      (cepatCons «::» [cepatVar «h»; cepatVar «tl»])
        (Prim (Cons «::») [Var [] «h»;
          App (Var [] «append») [Var [] «tl»; Var [] «r»]])
      [cepatCons «[]» [],Var [] «r»];

    («test»,
      SOME ([],Pred [] $
        Cons (Cons (Tup 2) (Atom $ PrimTy Integer))
          (Atom $ PrimTy Integer))),
      typeclass_texp$Letrec [(«fold»,
        SOME (
          [kindArrow kindType kindType;kindType],
          Pred [(«Foldable»,TypeVar 0);(«Monoid»,TypeVar 1)] $
            Functions [Cons (TypeVar 0) (TypeVar 1)] (TypeVar 1))),
        typeclass_texp$App
          (Var [(«Foldable»,TypeVar 0);(«Monoid»,TypeVar 1)] «foldMap»)
          [Lam [«x»,NONE] (Var [] «x»)]] $
      typeclass_texp$App
        (Var [
          «Foldable»,UserType 0;
          «Monoid»,
            Cons (Cons (Tup 2) (Atom $ PrimTy Integer)) $
              Atom $ PrimTy Integer]
          «fold») [
        typeclass_texp$App
          (Var [
            «Foldable»,UserType 0;
            «Monoid»,
              Cons (UserType 0) $
                Cons (Cons (Tup 2) $ Atom $ PrimTy Integer) $
                  Atom $ PrimTy Integer]
            «fold»)
          [App (Var [«Foldable»,UserType 0] «toList»)
            [Prim (Cons «::») [
              Prim (Cons «::») [
                Prim (Cons «») [
                  Prim (AtomOp $ Lit (Int 1)) [];
                  Prim (AtomOp $ Lit (Int 1)) []];
                Prim (Cons «[]») []];
              Prim (Cons «[]») []]
            ]
          ]
        ]
  ]
End

Triviality UNIQUE_MEMBER_SUBSET_SING:
  (∀x. x ∈ s ⇒ x = y) ⇔ s ⊆ {y}
Proof
  rw[EQ_IMP_THM,SUBSET_DEF]
QED

Theorem test_instance_env_type_check:
  ie = set (class_env_to_ie test_class_env ++
    instance_env_to_ie test_instance_env_elaborated) ∧
  env = [
    «test»,[],Pred [] $
      Cons (Cons (Tup 2) (Atom $ PrimTy Integer))
        (Atom $ PrimTy Integer);
    «append»,[kindType],Pred [] $
      Functions [
        Cons (UserType 0) (TypeVar 0);
        Cons (UserType 0) (TypeVar 0)] $
        Cons (UserType 0) (TypeVar 0)] ++
    class_env_to_env test_class_env ⇒
  type_elaborate_inst_env initial_namespace test_class_env
    (ce_to_clk test_class_env) ie st env
    test_instance_env test_instance_env_elaborated
Proof
  rw[type_elaborate_inst_env_def] >>
  CONV_TAC (RATOR_CONV $ SCONV[test_instance_env_def]) >>
  CONV_TAC (RAND_CONV $ SCONV[test_instance_env_elaborated_def]) >>
  rw[]
  >- (
    simp[Once test_class_env_def,type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- simp[pred_type_well_scoped_def] >>
    conj_tac >-
      simp[pred_type_kind_ok_def,pred_kind_wf_def,
        Functions_def,subst_db_def,shift_db_def] >>
    irule type_elaborate_texp_Lam >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    simp[type_ok_def,kind_ok_def,kind_wf_Prim,PULL_EXISTS] >>
    irule_at (Pos hd) type_elaborate_texp_AtomOp >>
    simp[LIST_REL3_simp,PULL_EXISTS] >>
    irule_at (Pos last) type_atom_op_IntOps_Int >>
    simp[] >>
    rpt (irule_at Any type_elaborate_texp_Var) >>
    simp[has_dicts_simp,specialises_pred_def,subst_db_pred_def,
      subst_db_empty] >>
    simp[oneline get_PrimTys_def,AllCaseEqs()])
  >- (
    simp[Once test_class_env_def,type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- simp[pred_type_well_scoped_def] >>
    conj_tac >-
      simp[pred_type_kind_ok_def,pred_kind_wf_def,
        Functions_def,subst_db_def,shift_db_def] >>
    irule_at (Pos hd) type_elaborate_texp_AtomOp >>
    irule_at (Pos last) type_atom_op_Lit >>
    simp[type_lit_rules,get_PrimTys_def,LIST_REL3_simp]
  )
  >- (
    simp[Once test_class_env_def,type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- (
      simp[pred_type_well_scoped_def] >>
      simp[collect_type_vars_def,Functions_def]) >>
    simp[] >>
    conj_tac >- (
      simp[pred_type_kind_ok_def,pred_kind_wf_def,
        Functions_def,subst_db_def,shift_db_def,
        LLOOKUP_THM] >>
      simp[typedefs_to_cdb_def,initial_namespace_def,
        LLOOKUP_THM,kind_arrows_def,
        test_class_env_def,ce_to_clk_def]) >>
    irule type_elaborate_texp_Lam >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    rw[type_ok_def,kind_ok_def,PULL_EXISTS,LLOOKUP_THM] >>
    rw[GSYM PULL_EXISTS]
    >- simp[Functions_def,LLOOKUP_THM]
    >- simp[LLOOKUP_THM,typedefs_to_cdb_def,
        initial_namespace_def,kind_arrows_def] >>
    qrefinel [`Functions args_t ret_t`,`Cons (UserType 0) (TypeVar 0)`] >>
    irule_at (Pos hd) type_elaborate_texp_NestedCase >>
    irule_at (Pos hd) type_elaborate_texp_Var >>
    simp[has_dicts_empty,specialises_pred_def,subst_db_pred_def,
      PULL_EXISTS] >>
    irule_at (Pos hd) type_cepat_Cons >>
    simp[Once initial_namespace_def,destruct_type_cons_def,
      subst_db_def,split_ty_head_def,split_ty_head_aux_def,
      type_cons_def,LLOOKUP_THM,kind_ok_def,LIST_REL3_simp,
      PULL_EXISTS] >>
    rpt (irule_at Any type_cepat_Var) >>
    rpt (irule_at Any type_cepat_UScore) >>
    irule_at Any type_elaborate_texp_Var >>
    simp[Once class_env_to_env_def,Once test_class_env_def] >>
    simp[specialises_pred_def,get_method_type_def,subst_db_pred_def] >>
    simp[PULL_EXISTS,subst_db_def,kind_ok_def,LLOOKUP_THM,has_dicts_simp] >>
    irule_at (Pos last) exhaustive_cepat_UScore >>
    rw[GSYM PULL_EXISTS]
    >- (irule has_dict_lie >> simp[]) >>
    irule_at (Pos hd) type_elaborate_texp_App >>
    irule_at (Pos hd) type_elaborate_texp_Var >>
    simp[Once class_env_to_env_def,Once test_class_env_def] >>
    simp[specialises_pred_def,get_method_type_def,has_dicts_simp] >>
    simp[PULL_EXISTS,subst_db_def,subst_db_pred_def,
    subst_db_Functions,kind_ok_def,LLOOKUP_THM,LIST_REL3_simp] >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    rw[GSYM PULL_EXISTS]
    >- (
      irule has_dict_ie >>
      qexistsl [
        `[(«Monoid»,TypeVar 1)]`,
        `Entail [kindType] [(«Monoid»,TypeVar 0)] («Semigroup»,TypeVar 0)`] >>
      simp[Once class_env_to_ie_def,Once test_class_env_def,
        class_to_entailments_def] >>
      simp[specialises_inst_def,PULL_EXISTS,subst_db_def] >>
      simp[kind_ok_def,LLOOKUP_THM,has_dicts_simp] >>
      irule has_dict_lie >>
      simp[]) >>
    rpt (irule_at Any type_elaborate_texp_App) >>
    simp[LIST_REL3_simp] >>
    rpt (irule_at Any type_elaborate_texp_Var) >>
    simp[specialises_pred_def,PULL_EXISTS,subst_db_pred_def,
      subst_db_Functions,subst_db_empty,has_dicts_empty,
      has_dicts_simp,LIST_REL3_simp] >>
    simp[Once class_env_to_env_def,Once test_class_env_def] >>
    irule_at (Pos hd) $ iffLR FUN_EQ_THM >>
    qrefine `[_]` >>
    simp[subst_db_empty] >>
    irule_at (Pos hd) EQ_REFL >>
    simp[get_method_type_def,subst_db_Functions,PULL_EXISTS,kind_ok_def,
      specialises_pred_def,subst_db_def,subst_db_pred_def,LLOOKUP_THM,
      Functions_Functions] >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    simp[Once typedefs_to_cdb_def,Once initial_namespace_def,LLOOKUP_THM] >>
    simp[Once initial_namespace_def,kind_arrows_def] >>
    rw[]
    >- (
      irule has_dict_ie >>
      simp[instance_env_to_ie_def,instance_to_entailment_def,
        test_instance_env_elaborated_def] >>
      qexistsl [`[]`,`Entail [] [] («Foldable»,UserType 0)`] >>
      simp[has_dicts_empty,specialises_inst_def,subst_db_def,MEM_MAP]
    ) >>
    irule has_dict_lie >>
    simp[]
  )
  >- (
    simp[Once test_class_env_def,type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- simp[pred_type_well_scoped_def] >>
    conj_tac >- (
      simp[pred_type_kind_ok_def,pred_kind_wf_def,
        Functions_def,subst_db_def,shift_db_def,LLOOKUP_THM] >>
      simp[typedefs_to_cdb_def,initial_namespace_def,
        LLOOKUP_THM,kind_arrows_def]) >>
    irule type_elaborate_texp_Var >>
    simp[has_dicts_empty,specialises_pred_def,subst_db_pred_def,
      subst_db_def,subst_db_Functions,PULL_EXISTS] >>
    simp[Functions_def,kind_ok_def,LLOOKUP_THM]
  )
  >- (
    simp[Once test_class_env_def,type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- simp[pred_type_well_scoped_def] >>
    conj_tac >- (
      simp[pred_type_kind_ok_def,pred_kind_wf_def,
        kind_wf_Functions,subst_db_def,shift_db_def] >>
      simp[typedefs_to_cdb_def,initial_namespace_def,
        LLOOKUP_THM,kind_arrows_def]) >>
    irule type_elaborate_texp_Cons >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    qexistsl [`0`,`[TypeVar 0]`] >>
    simp[type_cons_def,tcons_to_type_def,cons_types_def,
      type_ok_def,kind_ok_def,LIST_REL3_simp] >>
    simp[LLOOKUP_THM,initial_namespace_def]
  )
  >- (
    simp[Once test_class_env_def,type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- simp[pred_type_well_scoped_def] >>
    simp[pred_type_kind_ok_def,pred_kind_wf_def,
      kind_wf_Functions,subst_db_def,shift_db_def,
      LLOOKUP_THM,kind_arrows_def] >>
    irule type_elaborate_texp_Tuple >>
    simp[LIST_REL3_simp,PULL_EXISTS,cons_types_def] >>
    rpt (irule_at Any type_elaborate_texp_Var) >>
    simp[has_dicts_simp,test_class_env_def,
      class_env_to_env_def,specialises_pred_def,
      subst_db_pred_def,subst_db_Functions,
      subst_db_def,get_method_type_def,PULL_EXISTS] >>
    simp[kind_ok_def,LLOOKUP_THM] >>
    rpt (irule_at Any has_dict_lie) >>
    simp[]
  )
  >- (
    simp[Once test_class_env_def,type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- simp[pred_type_well_scoped_def] >>
    simp[pred_type_kind_ok_def,pred_kind_wf_def,
      kind_wf_Functions,subst_db_def,shift_db_def,
      LLOOKUP_THM,kind_arrows_def] >>
    irule type_elaborate_texp_Lam >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    simp[type_ok_def,kind_ok_def,PULL_EXISTS,
      kind_arrows_def,LLOOKUP_THM] >>
    irule_at (Pos hd) type_elaborate_texp_NestedCase >>
    simp[] >>
    rpt (irule_at Any type_elaborate_texp_Tuple) >>
    simp[cons_types_def,LIST_REL3_simp,PULL_EXISTS] >>
    rpt (
      irule_at Any type_cepat_Cons >>
      simp[LIST_REL3_simp,PULL_EXISTS]
    ) >>
    rpt (irule_at Any type_cepat_Var) >>
    qrefinel [
      `Cons (Cons (Tup 2) (TypeVar a)) (TypeVar b)`,
      `Cons (Cons (Tup 2) (TypeVar a)) (TypeVar b)`] >>
    simp[destruct_type_cons_def,split_ty_head_def,
      split_ty_head_aux_def,initial_namespace_def] >>
    rpt (irule_at Any type_elaborate_texp_App) >>
    simp[LIST_REL3_simp,PULL_EXISTS] >>
    rpt (irule_at Any type_elaborate_texp_Var) >>
    simp[class_env_to_env_def,test_class_env_def,get_method_type_def,
      has_dicts_simp] >>
    simp[specialises_pred_def,subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def,PULL_EXISTS,
      subst_db_def,shift_db_def,subst_db_empty] >>
    rpt (irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL) >>
    simp[kind_ok_def,LLOOKUP_THM] >>
    rpt (irule_at Any has_dict_lie) >>
    simp[] >>
    irule_at Any exhaustive_cepat_Cons >>
    simp[PULL_EXISTS,destruct_type_cons_def,
      split_ty_head_def,split_ty_head_aux_def] >>
    qexists `{[cepatCons «» [cepatVar «x1»; cepatVar «x2»];
      cepatCons «» [cepatVar «y1»; cepatVar «y2»]]}` >>
    rpt (irule_at Any exhaustive_cepat_List) >>
    irule_at Any exhaustive_cepat_Nil >>
    simp[] >>
    irule_at (Pos last) $ cj 1 $ iffLR SET_EQ_SUBSET >>
    simp[IMAGE_DEF,Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] >>
    simp[FORALL_AND_THM,GSYM CONJ_ASSOC] >>
    simp[LAMBDA_PROD,GSYM PEXISTS_THM,GSYM PFORALL_THM] >>
    ntac 2 (
      irule_at (Pat `_ ∈ _`) $ iffRL IN_SING >> simp[]) >>
    irule_at (Pat `_ ⊆ _`) $ cj 1 $ iffLR SET_EQ_SUBSET >>
    simp[EXTENSION,EQ_IMP_THM,PULL_EXISTS,FORALL_AND_THM] >>
    simp[GSYM CONJ_ASSOC] >>
    irule_at (Pat `_ ∈ _`) $ iffRL IN_SING >> simp[] >>
    ntac 2 $ irule_at
      (Pat `exhaustive_cepat _ _ _ {cepatCons «» [_;_]}`)
      exhaustive_cepat_Cons >>
    simp[PULL_EXISTS,destruct_type_cons_def,
      split_ty_head_def,split_ty_head_aux_def] >>
    rpt (irule_at Any $ cj 1 $ iffLR SET_EQ_SUBSET) >>
    simp[IMAGE_DEF,EXTENSION,PULL_EXISTS,EQ_IMP_THM] >>
    simp[FORALL_AND_THM,GSYM CONJ_ASSOC] >>
    simp[LAMBDA_PROD,GSYM PEXISTS_THM,GSYM PFORALL_THM] >>
    rpt (irule_at (Pat `_ ∈ _`) $ iffRL IN_SING >> simp[]) >>
    rpt (irule_at Any exhaustive_cepat_List) >>
    rpt (irule_at Any exhaustive_cepat_Nil) >>
    simp[] >>
    rpt (irule_at (Pat `_ ∈ _`) $ iffRL IN_SING >> simp[]) >>
    rpt $ irule_at (Pat `_ ⊆ _`) $ cj 1 $ iffLR SET_EQ_SUBSET >>
    simp[EXTENSION,PULL_EXISTS,EQ_IMP_THM] >>
    simp[FORALL_AND_THM,LAMBDA_PROD,
      GSYM PFORALL_THM,GSYM PEXISTS_THM] >>
    rpt (irule_at Any exhaustive_cepat_Var) >>
    rpt (irule_at (Pat `_ ∈ _`) $ iffRL IN_SING >> simp[])
  )
QED

Theorem test_defaults_type_check:
  ie = set (class_env_to_ie test_class_env ++
    instance_env_to_ie test_instance_env_elaborated) ∧
  env = [
    «test»,[],Pred [] $
      Cons (Cons (Tup 2) (Atom $ PrimTy Integer))
        (Atom $ PrimTy Integer);
    «append»,[kindType],Pred [] $
      Functions [
        Cons (UserType 0) (TypeVar 0);
        Cons (UserType 0) (TypeVar 0)] $
        Cons (UserType 0) (TypeVar 0)] ++
    class_env_to_env test_class_env ⇒

  type_elaborate_default_impls test_class_env initial_namespace
    (ce_to_clk test_class_env) ie st env
    test_defaults test_defaults_elaborated
Proof
  rw[test_defaults_def,test_defaults_elaborated_def,
    type_elaborate_default_impls_def,type_elaborate_default_impl_def] >>
  simp[Once test_class_env_def] >>
  qexists `«Foldable»` >> simp[] >>
  irule type_elaborate_texp_Pred >>
  simp[pred_type_well_scoped_def,pred_type_kind_ok_def,
    pred_kind_wf_def,collect_type_vars_def,Once Functions_def] >>
  simp[Once Functions_def,LLOOKUP_THM] >>
  simp[Once Functions_def,LLOOKUP_THM,
    Once typedefs_to_cdb_def,Once initial_namespace_def] >>
  simp[Once initial_namespace_def,Once test_class_env_def,
    kind_arrows_def,ce_to_clk_def] >>
  irule type_elaborate_texp_App >>
  simp[LIST_REL3_simp,PULL_EXISTS,Functions_Functions] >>
  irule_at (Pos last) type_elaborate_texp_Var >>
  simp[Once class_env_to_env_def,Once test_class_env_def,
    get_method_type_def,has_dicts_simp,LIST_REL3_simp,
    PULL_EXISTS,specialises_pred_def,subst_db_pred_def,kind_ok_def,
    subst_db_Functions,subst_db_def] >>
  irule_at (Pos last) type_elaborate_texp_Lam >>
  irule_at (Pat `type_elaborate_texp`) type_elaborate_texp_Cons >>
  simp[LIST_REL3_simp,PULL_EXISTS] >>
  irule_at (Pat `type_elaborate_texp`) type_elaborate_texp_Var >>
  simp[has_dicts_empty,specialises_pred_def,subst_db_pred_def,
    subst_db_def] >>
  irule_at (Pat `type_elaborate_texp`) type_elaborate_texp_Cons >>
  simp[LIST_REL3_simp,PULL_EXISTS,type_cons_def] >>
  qexistsl [`0`,`0`] >>
  simp[LLOOKUP_THM,initial_namespace_def,PULL_EXISTS,typedefs_to_cdb_def,
    tcons_to_type_def,cons_types_def,subst_db_def,subst_db_empty,
    kind_arrows_def] >>
  irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
  rw[kind_ok_def,type_ok_def,LLOOKUP_THM]
  >- (irule has_dict_lie >> simp[]) >>
  irule has_dict_ie >>
  CONV_TAC (RESORT_EXISTS_CONV rev) >>
  qexists `Entail [kindType] [] («Monoid»,Cons (UserType 0) (TypeVar 0))`>>
  simp[instance_env_to_ie_def,instance_to_entailment_def,has_dicts_simp,
    test_instance_env_elaborated_def,PULL_EXISTS,kind_ok_def,
    specialises_inst_def,subst_db_def,LLOOKUP_THM]
QED

Theorem test_prog_type_check:
  ie = set (class_env_to_ie test_class_env ++
    instance_env_to_ie test_instance_env_elaborated) ∧
  OPT_MMAP (SND o FST) test_prog_elaborated = SOME fns_type_scheme ∧
  env = REVERSE (ZIP (MAP (FST o FST) test_prog,fns_type_scheme)) ++
    class_env_to_env test_class_env ⇒
  type_elaborate_bindings initial_namespace (ce_to_clk test_class_env) ie
    EMPTY [] st env
    test_prog test_prog_elaborated
Proof
  rw[type_elaborate_bindings_def,test_prog_def,test_prog_elaborated_def]
  >- (
    irule type_elaborate_texp_Pred >>
    simp[pred_type_well_scoped_def,pred_type_kind_ok_def,pred_kind_wf_def] >>
    conj_tac
    >- simp[Functions_def,LLOOKUP_THM,
        typedefs_to_cdb_def,kind_arrows_def,
        initial_namespace_def] >>
    irule type_elaborate_texp_Lam >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    simp[PULL_EXISTS,type_ok_def,kind_ok_def, LLOOKUP_THM] >>
    rw[GSYM PULL_EXISTS]
    >- simp[typedefs_to_cdb_def,kind_arrows_def,
      LLOOKUP_THM,initial_namespace_def] >>
    irule_at (Pos hd) type_elaborate_texp_NestedCase >>
    qexists `Cons (UserType 0) (TypeVar 0)` >>
    irule_at (Pos hd) type_elaborate_texp_Var >>
    simp[has_dicts_empty,specialises_pred_def,subst_db_pred_def,
      subst_db_empty,PULL_EXISTS] >>
    irule_at (Pos hd) type_cepat_Cons >>
    simp[Once initial_namespace_def,destruct_type_cons_def,
      split_ty_head_def,split_ty_head_aux_def,type_cons_def,
      LIST_REL3_simp,LLOOKUP_THM,kind_ok_def,PULL_EXISTS,
      subst_db_def] >>
    rpt $ irule_at Any type_cepat_Var >>
    irule_at Any type_cepat_Cons >>
    simp[Once initial_namespace_def,destruct_type_cons_def,
      split_ty_head_def,split_ty_head_aux_def,type_cons_def,
      LLOOKUP_THM,kind_ok_def,LIST_REL3_simp] >>
    irule_at (Pat `exhaustive_cepat`) exhaustive_cepat_Cons >>
    rw[Once $ GSYM PULL_EXISTS]
    >- (
      gvs[initial_namespace_def,destruct_type_cons_def,
        split_ty_head_def,split_ty_head_aux_def,type_cons_def,
        LLOOKUP_THM,PULL_EXISTS,AllCaseEqs()]
      >- (
        irule_at (Pos hd) exhaustive_cepat_Nil >>
        simp[SUBSET_SING,LEFT_AND_OVER_OR,EXISTS_OR_THM] >>
        qexists `{[]}` >>
        simp[]) >>
      rpt (irule_at (Pat `exhaustive_cepatl`) exhaustive_cepat_List) >>
      irule_at Any exhaustive_cepat_Nil >>
      simp[IMAGE_DEF,ELIM_UNCURRY,SUBSET_DEF,PULL_EXISTS] >>
      simp[LAMBDA_PROD,GSYM PFORALL_THM] >>
      rpt (irule_at Any exhaustive_cepat_Var) >>
      simp[UNIQUE_MEMBER_SUBSET_SING] >>
      irule_at (Pos last) SUBSET_REFL >>
      irule_at (Pos hd) $ iffRL IN_SING >>
      simp[] >>
      irule_at (Pos hd) $ iffRL IN_SING >>
      simp[] >>
      irule_at (Pos hd) $ iffRL IN_SING >>
      simp[IMP_CONJ_THM,FORALL_AND_THM] >>
      simp[UNIQUE_MEMBER_SUBSET_SING] >>
      irule_at (Pos last) SUBSET_REFL >>
      simp[]
    ) >>
    irule_at Any type_elaborate_texp_Var >>
    simp[specialises_pred_def,subst_db_pred_def,subst_db_empty,
      has_dicts_empty] >>
    irule type_elaborate_texp_Cons >>
    CONV_TAC (RESORT_EXISTS_CONV rev) >>
    qexistsl [`0`,`[TypeVar 0]`] >>
    simp[tcons_to_type_def,type_cons_def,cons_types_def,
      LLOOKUP_THM,subst_db_def,type_ok_def,kind_ok_def,
      LIST_REL3_simp,PULL_EXISTS] >>
    rw[initial_namespace_def]
    >- (
      irule type_elaborate_texp_Var >>
      simp[has_dicts_empty,specialises_pred_def,subst_db_pred_def,subst_db_def]) >>
    irule type_elaborate_texp_App >>
    simp[LIST_REL3_simp,PULL_EXISTS] >>
    rpt (irule_at Any type_elaborate_texp_Var) >>
    simp[has_dicts_simp,specialises_pred_def,subst_db_pred_def,
      shift_db_pred_def,shift_db_Functions,shift_db_def,
      subst_db_Functions,subst_db_def,PULL_EXISTS] >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    simp[kind_ok_def,LLOOKUP_THM]
  ) >>
  irule type_elaborate_texp_Pred >>
  rw[pred_type_well_scoped_def,pred_type_kind_ok_def,
    pred_kind_wf_def,kind_arrows_def] >>
  irule type_elaborate_texp_Letrec >>
  simp[LIST_REL3_simp,PULL_EXISTS] >>
  rw[LAMBDA_PROD,GSYM PEXISTS_THM]
  >- (
    irule type_elaborate_texp_Pred >>
    rw[pred_type_kind_ok_def,pred_kind_wf_def,pred_type_well_scoped_def] >>
    simp[collect_type_vars_Functions,collect_type_vars_def]
    >- simp[Functions_def,LLOOKUP_THM]
    >- simp[Functions_def,LLOOKUP_THM,ce_to_clk_def,test_class_env_def]
    >- simp[Functions_def,LLOOKUP_THM,ce_to_clk_def,test_class_env_def] >>
    irule type_elaborate_texp_App >>
    simp[LIST_REL3_simp,PULL_EXISTS,Functions_Functions] >>
    irule_at Any type_elaborate_texp_Var >>
    simp[Once class_env_to_env_def,Once test_class_env_def,
      specialises_pred_def,subst_db_pred_def,get_method_type_def,
      shift_db_pred_def,subst_db_Functions,shift_db_Functions,
      subst_db_def,shift_db_def,PULL_EXISTS] >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    rw[kind_ok_def,LLOOKUP_THM,has_dicts_simp]
    >- (irule has_dict_lie >> simp[])
    >- (irule has_dict_lie >> simp[])
    >- (
      irule type_elaborate_texp_Lam >>
      irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
      simp[type_ok_def,kind_ok_def,PULL_EXISTS,LLOOKUP_THM] >>
      irule_at (Pos hd) type_elaborate_texp_Var >>
      simp[has_dicts_empty,specialises_pred_def,subst_db_pred_def,subst_db_empty]
    )
  ) >>
  irule type_elaborate_texp_App >>
  simp[LIST_REL3_simp] >>
  rpt (irule_at Any type_elaborate_texp_App >> simp[LIST_REL3_simp]) >>
  rpt (irule_at Any type_elaborate_texp_Var) >>
  simp[has_dicts_simp,specialises_pred_def,subst_db_pred_def,
    subst_db_def,subst_db_Functions,PULL_EXISTS,kind_ok_def] >>
  rpt $ irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
  simp[GSYM PULL_EXISTS,DISJ_IMP_THM,FORALL_AND_THM,GSYM CONJ_ASSOC,
    kind_arrows_def] >>
  conj_asm1_tac
  >- (
    irule has_dict_ie >>
    qexistsl [`[]`,`Entail [] [] («Foldable»,UserType 0)`] >>
    simp[instance_env_to_ie_def,test_instance_env_elaborated_def,
      instance_to_entailment_def,has_dicts_empty,
      specialises_inst_def,subst_db_empty]
  ) >>
  `∀(ns:typedefs) db lie. has_dict ns db
    (set (class_env_to_ie test_class_env) ∪
     set (instance_env_to_ie test_instance_env_elaborated)) lie
    («Monoid»,Atom (PrimTy Integer))`
  by (
    rpt strip_tac >>
    irule has_dict_ie >>
    qexistsl [`[]`,`Entail [] [] («Monoid»,Atom (PrimTy Integer))`] >>
    simp[instance_env_to_ie_def,test_instance_env_elaborated_def,
      instance_to_entailment_def,has_dicts_empty,
      specialises_inst_def,subst_db_empty]
  ) >>
  conj_asm1_tac
  >- (
    irule has_dict_ie >>
    CONV_TAC $ RESORT_EXISTS_CONV rev >>
    qexists `Entail [kindType; kindType]
         [(«Monoid»,TypeVar 0); («Monoid»,TypeVar 1)]
         («Monoid»,Cons (Cons (Tup 2) (TypeVar 0)) (TypeVar 1))` >>
    simp[Once instance_env_to_ie_def,
      Once test_instance_env_elaborated_def,
      instance_to_entailment_def,has_dicts_simp,kind_ok_def,
      specialises_inst_def,subst_db_def,PULL_EXISTS] >>
    simp[LAMBDA_PROD,GSYM PEXISTS_THM,GSYM PFORALL_THM]
  ) >>
  conj_asm1_tac
  >- simp[typedefs_to_cdb_def,initial_namespace_def,
      kind_arrows_def,LLOOKUP_THM] >>
  rw[]
  >- (
    irule has_dict_ie >>
    qexistsl [`[]`,`Entail [kindType] [] («Monoid»,Cons (UserType 0) (TypeVar 0))`] >>
    simp[instance_env_to_ie_def,test_instance_env_elaborated_def,
      instance_to_entailment_def,has_dicts_empty,subst_db_def,
      specialises_inst_def,PULL_EXISTS,kind_ok_def,
      kind_arrows_def]
  ) >>
  simp[Once class_env_to_env_def,Once test_class_env_def,
    subst_db_def,get_method_type_def,
    specialises_pred_def,subst_db_pred_def,PULL_EXISTS,
    shift_db_pred_def,subst_db_Functions,shift_db_Functions,
    shift_db_def] >>
  irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
  simp[kind_ok_def,LLOOKUP_THM,kind_arrows_def] >>
  ntac 2 (
    irule_at Any type_elaborate_texp_Cons >>
    simp[LIST_REL3_simp,PULL_EXISTS]) >>
  irule_at Any type_elaborate_texp_Tuple >>
  rpt (
    irule_at Any type_elaborate_texp_Cons >>
    simp[LIST_REL3_simp,PULL_EXISTS]) >>
  simp[initial_namespace_def,typedefs_to_cdb_def,kind_arrows_def,
    type_cons_def,tcons_to_type_def,cons_types_def,subst_db_def,
    LIST_REL3_simp,PULL_EXISTS,LLOOKUP_THM,kind_ok_def] >>
  irule type_elaborate_texp_AtomOp >>
  simp[LIST_REL3_simp,get_PrimTys_def] >>
  irule type_atom_op_Lit >>
  simp[type_lit_rules]
QED

Theorem test_whole_prog_type_check:
  type_elaborate_prog initial_namespace test_class_env st
    test_defaults test_instance_env test_prog
    test_defaults_elaborated test_instance_env_elaborated
    test_prog_elaborated
Proof
  simp[type_elaborate_prog_def] >>
  irule_at Any test_prog_type_check >>
  irule_at Any test_instance_env_type_check >>
  irule_at Any test_defaults_type_check >>
  simp[test_prog_elaborated_def,test_prog_def] >>
  simp[instance_env_kind_check_def,pred_type_kind_ok_def,
    pred_kind_wf_def,Functions_def,LLOOKUP_THM] >>
  rw[test_instance_env_def,test_instance_env_elaborated_def,
    test_class_env_def,ce_to_clk_def,LLOOKUP_THM,
    instance_kind_check_def,kind_ok_def,kind_arrows_def,
    initial_namespace_def,typedefs_to_cdb_def]
QED

Definition test_cl_cons_def:
  test_cl_cons = [
    «Semigroup»,«SemigroupDict»;
    «Monoid»,«MonoidDict»;
    «Foldable»,«FoldableDict»
  ]
End

Definition test_sup_vs_def:
  test_sup_vs = [«getSemigroup»]
End

Definition test_inst_vs_def:
  test_inst_vs = [
    «semigroupInt»;
    «monoidInt»;
    «foldableList»;
    «semigroupList»;
    «monoidList»;
    «monoidTuple»;
    «semigroupTuple»
  ]
End

Definition test_default_name_map_def:
  test_default_name_map = [«toList»,«default_toList»]
End

Definition test_cl_to_tyid_def:
  test_cl_to_tyid = FEMPTY |++
    ZIP (MAP FST test_class_env,
      GENLIST (λn. n + LENGTH (SND initial_namespace))
        (LENGTH test_class_env))
End

Theorem test_cl_to_tyid = EVAL ``test_cl_to_tyid``;

Theorem test_class_env_to_ns =
  EVAL ``class_env_to_ns test_class_env test_cl_to_tyid
    (MAP SND test_cl_cons) test_class_env``;

Definition test_namespace_translated_def:
  test_namespace_translated =
    append_ns
      (namespace_to_tcexp_namespace initial_namespace)
      ([],THE $ class_env_to_ns
          test_class_env test_cl_to_tyid
          (MAP SND test_cl_cons) test_class_env)
End

Theorem test_namespace_translated =
  EVAL ``test_namespace_translated``;

Definition test_class_env_translated_def:
  test_class_env_translated =
    class_env_construct_dict (MAP SND test_cl_cons) test_sup_vs
      test_class_env
End

Theorem test_class_env_translated =
  EVAL ``test_class_env_translated``;

Definition test_ie_map_def:
  test_ie_map = FEMPTY |++
   (ZIP (test_sup_vs,class_env_to_ie test_class_env) ++
    ZIP (test_inst_vs,
      instance_env_to_ie test_instance_env_elaborated))
End

Theorem test_ie_map = EVAL ``test_ie_map``;

Definition test_env_def:
  test_env =
    set (MAP (FST ∘ FST) test_prog_elaborated ++
      MAP FST (class_env_to_env test_class_env))
End

Theorem test_class_env_to_env =
  EVAL ``class_env_to_env test_class_env``;

Theorem test_env = EVAL ``test_env``;

Definition test_defaults_translated_def:
  test_defaults_translated = [«default_toList»,
    Lam () [«y»] $
      App ()
        (App () (Var () «foldMap») [Var () «y»;Var () «monoidList»])
        [Lam () [«x»] $
          (Prim () (Cons «::») [Var () «x»;Prim () (Cons «[]») []])]
  ]
End

Theorem test_defaults_construct_dict:
  default_impls_construct_dict initial_namespace test_class_env
    test_ie_map test_env test_default_name_map test_defaults_elaborated
    test_defaults_translated
Proof
  simp[default_impls_construct_dict_def] >>
  simp[test_defaults_elaborated_def,test_defaults_translated_def,
    test_default_name_map_def] >>
  qexists `«Foldable»` >>
  simp[Once test_class_env_def] >>
  simp[default_impl_construct_dict_def] >>
  irule texp_construct_dict_Pred >>
  CONV_TAC (RESORT_EXISTS_CONV rev) >>
  qrefine `[v]` >>
  simp[test_ie_map,test_env,get_names_namespace_def,
    initial_namespace_def,lambda_vars_def] >>
  conj_tac >- EVAL_TAC >>
  irule texp_construct_dict_App >>
  rw[]
  >- (
    irule texp_construct_dict_Lam >>
    simp[] >>
    irule texp_construct_dict_Prim >>
    rw[]
    >- (
      irule texp_construct_dict_Var >>
      simp[construct_dicts_simp]
    ) >>
    irule texp_construct_dict_Prim >>
    simp[]
  ) >>
  irule texp_construct_dict_Var >>
  rw[construct_dicts_simp,PULL_EXISTS]
  >- (
    irule construct_dict_lie >>
    simp[alistTheory.FLOOKUP_FUPDATE_LIST]
  ) >>
  irule construct_dict_ie >>
  simp[construct_dicts_simp,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[specialises_inst_def,PULL_EXISTS,subst_db_def,
    kind_ok_def,LLOOKUP_THM]
QED

Definition test_prog_translated_def:
    test_prog_translated = [
    («append»,
      Lam () [«l»;«r»] $
        NestedCase () (Var () «l») «l»
        (cepatCons «::» [cepatVar «h»; cepatVar «tl»])
          (Prim () (Cons «::») [Var () «h»;
            App () (Var () «append») [Var () «tl»; Var () «r»]])
        [cepatCons «[]» [],Var () «r»]);

    («test»,
      Letrec () [«fold»,
        Lam () [«f0»;«m1»] $ App ()
          (App () (Var () «foldMap»)
            [Var () «f0»;Var () «m1»])
          [Lam () [«x»] (Var () «x»)]] $
      App ()
        (App () (Var () «fold») [
          Var () «foldableList»;
          App () (Var () «monoidTuple»)
            [Var () «monoidInt»;Var () «monoidInt»]]) [
        App ()
          (App () (Var () «fold») [
              Var () «foldableList»;
              Var () «monoidList»])
          [App () (App () (Var () «toList») [Var () «foldableList»])
            [Prim () (Cons «::») [
              Prim () (Cons «::») [
                Prim () (Cons «») [
                  Prim () (AtomOp $ Lit (Int 1)) [];
                  Prim () (AtomOp $ Lit (Int 1)) []];
                Prim () (Cons «[]») []];
              Prim () (Cons «[]») []]
            ]
          ]
        ])
  ]
End

Theorem test_prog_construct_dict:
  LIST_REL (λ((x,ot),e) (y,de).
    x = y ∧
    case ot of
    | NONE => F
    | SOME (new,pt) =>
      pred_texp_construct_dict initial_namespace
        test_ie_map FEMPTY new test_env pt e de)
    test_prog_elaborated test_prog_translated
Proof
  rw[test_prog_elaborated_def,test_prog_translated_def]
  >- (
    irule texp_construct_dict_Pred >>
    simp[] >>
    irule texp_construct_dict_Lam >>
    simp[] >>
    irule texp_construct_dict_NestedCase >>
    simp[] >>
    rpt (irule_at Any texp_construct_dict_Var) >>
    simp[construct_dicts_simp] >>
    irule texp_construct_dict_Prim >>
    simp[] >>
    irule_at Any texp_construct_dict_App >>
    simp[] >>
    rpt (irule_at Any texp_construct_dict_Var) >>
    simp[construct_dicts_simp]
  ) >>
  irule texp_construct_dict_Pred >>
  simp[] >>
  irule texp_construct_dict_Letrec >>
  rw[]
  >- (
    irule texp_construct_dict_Pred >>
    simp[PULL_EXISTS,RIGHT_AND_OVER_OR,EXISTS_OR_THM] >>
    conj_tac >- (
      simp[get_names_namespace_def,initial_namespace_def,
        lambda_vars_def,test_env,test_ie_map,
        finite_mapTheory.FDOM_FUPDATE_LIST] >>
      EVAL_TAC
    ) >>
    irule texp_construct_dict_App >>
    simp[] >>
    irule_at Any texp_construct_dict_Lam >>
    simp[] >>
    irule_at Any texp_construct_dict_Var >>
    simp[construct_dicts_simp] >>
    irule texp_construct_dict_Var >>
    rw[construct_dicts_simp] >>
    irule construct_dict_lie >>
    simp[alistTheory.FLOOKUP_FUPDATE_LIST]
  ) >>
  rpt (irule_at Any texp_construct_dict_App >> simp[]) >>
  rpt (irule_at Any texp_construct_dict_Prim >> simp[]) >>
  rpt (irule_at Any texp_construct_dict_Var) >>
  simp[construct_dicts_simp] >>
  rpt (irule_at Any construct_dict_ie) >>
  simp[test_ie_map,construct_dicts_simp,
      finite_mapTheory.FLOOKUP_UPDATE,subst_db_def,PULL_EXISTS,
      specialises_inst_def,kind_ok_def,kind_arrows_def] >>
  simp[LAMBDA_PROD,GSYM PEXISTS_THM] >>
  irule construct_dict_ie >>
  simp[finite_mapTheory.FLOOKUP_UPDATE,construct_dicts_simp,
    specialises_inst_def,subst_db_def,PULL_EXISTS]
QED
                  

Definition test_instance_env_translated_def:
  test_instance_env_translated = [
    («semigroupInt», Prim () (Cons «SemigroupDict»)
      [Lam () [«x»;«y»]
        (Prim () (AtomOp Add) [Var () «x»;Var () «y»])]);
    («monoidInt»,Prim () (Cons «MonoidDict»)
      [Var () «semigroupInt»;Prim () (AtomOp (Lit (Int 0))) []]);
    («foldableList»,Prim () (Cons «FoldableDict»)
      [Lam () [«m»;«f»;«t»] (
        NestedCase () (Var () «t») «t»
          (cepatCons «::» [cepatVar «h»;cepatVar «tl»])
            (App ()
              (App () (Var ()  «mappend»)
                [(App () (Var () «getSemigroup») [Var () «m»])]) [
              App () (Var () «f») [Var () «h»];
              App () (
                App () (Var () «foldMap») [
                  (Var () «foldableList»);
                  (Var () «m»)
                ])
                [Var () «f»;Var () «tl»]])
          [cepatUScore,App () (Var () «mempty») [Var () «m»]]);
       App () (Var () «default_toList») [Var () «foldableList»]]);
    («semigroupList»,Prim () (Cons «SemigroupDict») [Var () «append»]);
    («monoidList»,Prim () (Cons «MonoidDict»)
      [Var () «semigroupList»;Prim () (Cons «[]») []]);
    («monoidTuple»,Lam () [«m1»;«m2»] $ Prim () (Cons «MonoidDict») [
      App () (Var () «semigroupTuple») [
        App () (Var () «getSemigroup») [Var () «m1»];
        App () (Var () «getSemigroup») [Var () «m2»]];
      Prim () (Cons «») [
        App () (Var () «mempty») [Var () «m1»];
        App () (Var () «mempty») [Var () «m2»]]]);
    («semigroupTuple»,Lam () [«s1»;«s2»] $ Prim () (Cons «SemigroupDict») [
      NestedCase ()
        (Prim () (Cons «») [Var () «x»;Var () «y»]) «p»
        (cepatCons «» [
          cepatCons «» [cepatVar «x1»;cepatVar «x2»];
          cepatCons «» [cepatVar «y1»;cepatVar «y2»]])
          (Prim () (Cons «») [
            App ()
              (App () (Var () «mappend») [Var () «s1»])
              [Var () «x1»;Var () «y1»];
            App ()
              (App () (Var () «mappend») [Var () «s2»])
              [Var () «x2»;Var () «y2»]])
        []])
  ]
End

Theorem test_instance_env_construct_dict:
  instance_env_construct_dict initial_namespace test_class_env
    test_ie_map test_env test_cl_cons test_default_name_map
    test_inst_vs test_instance_env_elaborated
    test_instance_env_translated
Proof
  simp[instance_env_construct_dict_def,test_inst_vs_def,LIST_REL3_def,
    test_instance_env_elaborated_def,test_instance_env_translated_def,
    test_class_env_def,test_cl_cons_def,test_default_name_map_def] >>
  rw[instance_construct_dict_def,construct_dicts_simp,PULL_EXISTS] >>
  cheat
QED

val _ = export_theory();
