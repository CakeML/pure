open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory miscTheory;
open listTheory alistTheory relationTheory set_relationTheory pred_setTheory;
open typeclass_typesTheory pure_cexpTheory typeclass_texpTheory;
open typeclass_kindCheckTheory pure_configTheory;
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

(* a type that is not well scoped is ambiguous
* (cannot figure out what type we should instantiate the type class to) *)
(* an example is the type forall a. String -> String *)
(* This is reason why we reject a program ``read . show`` without
* any type annotation *)
Definition pred_type_well_scoped_def:
  pred_type_well_scoped (Pred ps t) =
  (∀cl v. MEM (cl,v) ps ⇒
    collect_type_vars v ⊆ collect_type_vars t)
End

Definition pred_type_kind_ok_def:
  pred_type_kind_ok cldb (typedefs: typedefs) ks pt ⇔
    pred_kind_wf cldb (typedefs_to_cdb typedefs) (LLOOKUP ks) pt
End

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
Overload subst_db_kind_scheme =
  ``λn ts (vars,scheme).
      (vars, subst_db (n + LENGTH vars) (MAP (shift_db 0 (LENGTH vars)) ts) scheme)``;
Overload shift_db_scheme =
  ``λskip shift (vars,scheme).
      (vars, shift_db (skip + vars) shift scheme)``;
Overload shift_db_kind_scheme =
  ``λskip shift (vars,scheme).
      (vars, shift_db (skip + LENGTH vars) shift scheme)``;
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
    split_ty_cons t = SOME (tc,targs) ∧
    case tc of
    | INL tyid => type_cons tdefs db (cname,carg_tys) (tyid,targs)
    | INR (PrimT Bool) => MEM cname [«True»;«False»] ∧ carg_tys = []
    | INR (CompPrimT (Tuple n)) =>
        cname = «» ∧ targs = carg_tys
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

Theorem SmartLam_EQ_Lam_cases:
  ∀vs t. (SmartLam b xs x = Lam a vs t) ⇔
  ((xs = [] ∧ x = Lam a vs t) ∨
  (a = b ∧ xs ≠ [] ∧ xs = vs ∧ x = t ∧ ∀c h tl e. t ≠ Lam c (h::tl) e) ∨
  (a = b ∧ xs ≠ [] ∧ ∃c ys. ys ≠ [] ∧ x = Lam c ys t ∧ xs ++ ys = vs))
Proof
  Cases_on `xs` >>
  rw[SmartLam_def,AllCaseEqs()] >>
  Cases_on `x` >>
  gvs[dest_Lam_def] >>
  rw[EQ_IMP_THM] >>
  Cases_on `l` >>
  fs[]
QED

Theorem SmartLam_EQ_simp[simp]:
  (∀v. (SmartLam b xs x = Var a v) ⇔ xs = [] ∧ x = Var a v) ∧
  (∀cop ts. (SmartLam b xs x = Prim a cop ts) ⇔
    xs = [] ∧ x = Prim a cop ts) ∧
  (∀vs t. (SmartLam b [] x = Lam a vs t) ⇔ x = Lam a vs t) ∧
  (∀t ts. (SmartLam b xs x = App a t ts) ⇔
    (xs = [] ∧ x = App a t ts)) ∧
  (∀vs t t'. (SmartLam b xs x = Let a vs t t') ⇔
    (xs = [] ∧ x = Let a vs t t')) ∧
  (∀fns t'. (SmartLam b xs x = Letrec a fns t') ⇔
    (xs = [] ∧ x = Letrec a fns t')) ∧
  (∀t c es ys. (SmartLam b xs x = Case a t c es ys) ⇔
    (xs = [] ∧ x = Case a t c es ys)) ∧
  (∀t cv p e pes. (SmartLam b xs x = NestedCase a t cv p e pes) ⇔
    (xs = [] ∧ x = NestedCase a t cv p e pes))
Proof
  Cases_on `xs` >>
  rw[SmartLam_def,AllCaseEqs()]
QED

Theorem SmartApp_Var_simp[simp]:
  (∀v. (SmartApp () (Var () x) xs = Var () v) ⇔ xs = [] ∧ x = v) ∧
  (∀v h tl. (SmartApp () (Var () x) xs = App () (Var () v) (h::tl) ⇔
    xs = (h::tl) ∧ x = v))
Proof
  Cases_on `xs` >>
  rw[SmartApp_def,dest_App_def] >>
  metis_tac[]
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

Theorem has_dicts_empty:
  has_dicts tdefs db ie lie []
Proof
  simp[has_dicts_simp]
QED

Inductive construct_dict:
[~lie:]
  FLOOKUP lie d = SOME p ⇒
    construct_dict tdefs db ie lie p (pure_cexp$Var () d)
[~ie:]
  FLOOKUP ie d = SOME it ∧
  specialises_inst tdefs it (Entail db cstrs p) ∧
  construct_dicts tdefs db ie lie cstrs ds ∧
  de = (SmartApp () (pure_cexp$Var () d) ds) ⇒
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

(* type that we can apply case on *)
Definition destructable_type_def:
  destructable_type t ⇔
  t = Atom Exception ∨
  case head_ty_cons t of
  | SOME (INL tyid) => T
  | SOME (INR (PrimT Bool)) => T
  | SOME (INR (CompPrimT (Tuple n))) => T
  | SOME _ => F
  | NONE => F
End

(* These unsafe versions are only for exhaustiveness check,
* and the reason to introduce them is to remove the argument db
* in the exhastive_cepat *)
(* type_cons but do not check if the type arguments are kind_ok *)
Definition unsafe_type_cons_def:
  unsafe_type_cons tdefs (cname,carg_tys) (tyid,tyargs) ⇔
  ∃argks constructors schemes.
    LLOOKUP tdefs tyid = SOME (argks,constructors) ∧
    ALOOKUP constructors cname = SOME schemes ∧
    LENGTH tyargs = LENGTH argks ∧
    MAP (tsubst tyargs) schemes = carg_tys
End

Theorem unsafe_type_cons_carg_tys_unique:
  unsafe_type_cons tdefs (cname,carg_tys) (tyid,tyargs) ∧
  unsafe_type_cons tdefs (cname,carg_tys') (tyid,tyargs) ⇒
  carg_tys = carg_tys'
Proof
  rw[oneline unsafe_type_cons_def] >>
  gvs[]
QED

Theorem type_cons_IMP_unsafe_type_cons:
  type_cons tdefs db (cname,carg_tys) (tyid,tyargs) ⇒
  unsafe_type_cons tdefs (cname,carg_tys) (tyid,tyargs)
Proof
  rw[type_cons_def,unsafe_type_cons_def] >>
  gvs[LIST_REL_EL_EQN] >>
  metis_tac[]
QED

Theorem type_cons_carg_tys_unique:
  type_cons tdefs db (cname,carg_tys) (tyid,tyargs) ∧
  type_cons tdefs db (cname,carg_tys') (tyid,tyargs) ⇒
  carg_tys = carg_tys'
Proof
  rw[type_cons_def] >>
  gvs[]
QED

(* destruct_type_cons but do not check if the type arguments are kind_ok *)
Definition unsafe_destruct_type_cons_def:
  unsafe_destruct_type_cons (edefs,tdefs) t cname carg_tys ⇔
  if t = Atom Exception then type_exception edefs (cname,carg_tys)
  else
    ∃tc targs.
    split_ty_cons t = SOME (tc,targs) ∧
    (case tc of
    | INL tyid => unsafe_type_cons tdefs (cname,carg_tys) (tyid,targs)
    | INR (PrimT Bool) => MEM cname [«True»; «False»] ∧ carg_tys = []
    | INR (CompPrimT (Tuple n)) =>
        cname = «» ∧ targs = carg_tys
    | _ => F)
End

Theorem destruct_type_cons_IMP_unsafe_type_cons:
  destruct_type_cons ns db t cname carg_tys ⇒
  unsafe_destruct_type_cons ns t cname carg_tys
Proof
  rw[oneline destruct_type_cons_def,oneline unsafe_destruct_type_cons_def] >>
  every_case_tac >> gvs[] >>
  every_case_tac >>
  metis_tac[type_cons_IMP_unsafe_type_cons]
QED

Theorem unsafe_destruct_type_cons_unique:
  unsafe_destruct_type_cons ns t cname carg_tys ∧
  unsafe_destruct_type_cons ns t cname carg_tys' ⇒
  carg_tys = carg_tys'
Proof
  rw[oneline unsafe_destruct_type_cons_def] >>
  pop_assum mp_tac >>
  every_case_tac >> gvs[type_exception_def] >>
  every_case_tac >> gvs[] >>
  metis_tac[unsafe_type_cons_carg_tys_unique]
QED

Theorem destruct_type_cons_unique:
  destruct_type_cons ns db t cname carg_tys ∧
  destruct_type_cons ns db t cname carg_tys' ⇒
  carg_tys = carg_tys'
Proof
  rw[oneline destruct_type_cons_def] >>
  pop_assum mp_tac >>
  every_case_tac >> gvs[type_exception_def] >>
  every_case_tac >> gvs[] >>
  metis_tac[type_cons_carg_tys_unique]
QED

Inductive exhaustive_cepat:
[~Var:]
  cepatVar v ∈ s ⇒
    exhaustive_cepat ns t s

[~UScore:]
  cepatUScore ∈ s ⇒
    exhaustive_cepat ns t s

[~Cons:]
  destructable_type t ∧
  (∀c ts. unsafe_destruct_type_cons ns t c ts ⇒
    ∃(pss:cepat list set).
      exhaustive_cepatl ns ts pss ∧ IMAGE (cepatCons c) pss ⊆ s) ⇒
  exhaustive_cepat ns t s

[~Nil:]
  [] ∈ pss ⇒
    exhaustive_cepatl ns [] pss

[~List:]
  exhaustive_cepat ns t hs ∧
  exhaustive_cepatl ns ts tls ∧
  IMAGE (UNCURRY CONS) (hs × tls) ⊆ pss ⇒
    exhaustive_cepatl ns (t::ts) pss
End

Theorem exhaustive_cepat_monotone:
  (∀t s. exhaustive_cepat ns t s ⇒
    ∀s'. s ⊆ s' ⇒ exhaustive_cepat ns t s') ∧

  (∀ts s. exhaustive_cepatl ns ts s ⇒
    ∀s'. s ⊆ s' ⇒ exhaustive_cepatl ns ts s')
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
  pred_type_elaborate_texp ns clk ie lie (new ++ db) (MAP (tshift (LENGTH new)) st)
    (tshift_env_pred (LENGTH new) env) e1 e1' pt1 ∧
  type_elaborate_texp ns clk ie lie db st ((x,new,pt1)::env) e2 e2' t2 ⇒
     type_elaborate_texp ns clk ie lie db st env (Let (x,NONE) e1 e2)
        (Let (x,SOME (new,pt1)) e1' e2') t2

(* The poly type of the let binding is annotated by the user *)
[~LetSOME:]
  LENGTH new = n ∧
  type_elaborate_texp ns clk ie lie db st env (Let (x,NONE) e1 e2)
    (Let (x,SOME (new,pt)) e1' e2') t2 ⇒
      type_elaborate_texp ns clk ie lie db st env (Let (x,SOME (n,pt)) e1 e2)
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
    | SOME t => t = t') (MAP SND vs) args_tys ∧
  type_elaborate_texp ns clk ie lie db st
    (REVERSE (ZIP (MAP FST vs, MAP (λat. ([],Pred [] at)) args_tys)) ++ env)
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
  (* Note: since there is at least one pattern, t must be type_ok,
  *  we don't need to add the premise that t is type_ok *)
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
  exhaustive_cepat ns vt (p INSERT (IMAGE FST $ set pes)) ∧
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
  te = SmartApp () (Var () x) ds ⇒
    texp_construct_dict ns ie lie db env (Var ps x) te

[~Pred:]
  (* enforce all variables in vs are fresh *)
  set vs ∩
    (FDOM lie ∪ FDOM ie ∪ env ∪
      set (get_names_namespace ns) ∪ lambda_vars e) = ∅ ∧
  LENGTH vs = LENGTH ps ∧
  texp_construct_dict ns ie (lie |++ ZIP (vs,ps)) db env e de ∧
  te = SmartLam () vs de ⇒
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
      EVERY (pred_type_kind_scheme_ok clk tdefs [k] o SND) methods ∧
      EVERY (λs. clk s = SOME k) supers)
End

(* the type of the method is unambiguous if the pred type is well-scoped and
* the class variable is used *)
(* an example of ambiguity type:
* class C a where
*   f :: b -> b -- a is not used *)
Definition method_unambiguous_def:
  method_unambiguous (ks,Pred ps t) ⇔
    (pred_type_well_scoped (Pred ps t) ∧ LENGTH ks ∈ collect_type_vars t)
End

Definition class_env_methods_unambiguous_def:
  class_env_methods_unambiguous ce ⇔
  ∀c k supers methods. MEM (c,k,supers,methods) ce ⇒
    EVERY (method_unambiguous o SND) methods
End

(* classname, method name, implementation *)
Type default_impl[pp] = ``:mlstring # ('a texp)``;
Type default_impls[pp] = ``:'a default_impl list``;

Definition type_elaborate_default_impl_def:
  type_elaborate_default_impl ce ns clk ie st env meth e e' ⇔
    ∃cl k s methods ks ps t.
      ALOOKUP (ce:class_env) cl = SOME (k,s,methods) ∧
      ALOOKUP methods meth = SOME (ks,Pred ps t) ∧
      pred_type_elaborate_texp ns clk ie EMPTY (SNOC k ks) st env e e'
        (Pred ((cl,TypeVar $ LENGTH ks)::ps) t)
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
    pred_texp_construct_dict ns ie FEMPTY (SNOC k ks) env
      (Pred ((cl,TypeVar $ LENGTH ks)::ps) t) e e'
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
  get_method_type cl k (ks,Pred ps t) = (SNOC k ks,Pred ((cl,TypeVar $ LENGTH ks)::ps) t)
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
  impl_construct_dict ns ie env vs cstrs ks (Pred ps t) e e' ⇔
  pred_texp_construct_dict ns ie FEMPTY ks env
    (Pred (cstrs ++ ps) t) e (SmartLam () vs e')
End

Definition type_elaborate_impls_def:
  type_elaborate_impls ns clk ie st env varks cstrs inst_t meths impls impls' ⇔
    (LIST_REL (λimpl impl'.
       FST impl = FST impl' ∧
       ∃meth_ks pt.
         ALOOKUP meths (FST impl) = SOME (meth_ks,pt) ∧
         pred_type_elaborate_texp ns clk ie (set cstrs) (meth_ks ++ varks)
           st env (SND impl) (SND impl')
           (subst_db_pred (LENGTH meth_ks) [inst_t] pt))
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
  trans_inst = SmartLam () vs (Prim () (Cons cons) $ supers' ++ impls') ∧
  construct_dicts (SND ns) varks ie (FEMPTY |++ ZIP (vs,cstrs))
    (MAP (λsuper. (super,inst_t)) supers) supers' ∧
  LIST_REL (λ(name,(meth_ks,pt)) e'.
      case ALOOKUP impls name of
      | SOME e =>
          impl_construct_dict ns ie env vs cstrs (meth_ks ++ varks)
            (subst_db_pred (LENGTH meth_ks) [inst_t] pt) e e'
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
   (* distinctness of variable names *)
   LENGTH sup_vs = LENGTH (class_env_to_ie ce) ∧
   LENGTH inst_vs = LENGTH inst_env ∧
   ALL_DISTINCT sup_vs ∧
   ALL_DISTINCT inst_vs ∧
   ALL_DISTINCT $ MAP FST $ class_env_to_env ce ∧
   ALL_DISTINCT $ MAP SND default_name_map ∧
   set sup_vs ∩ set inst_vs ∩
    set (MAP FST $ class_env_to_env ce) ∩ set (MAP SND default_name_map) ∩
    (set (MAP (FST o FST) fns) ∪ lambda_varsl (MAP SND fns)) = ∅ ∧
   (* set the the instance environment *)
   ie = FEMPTY |++
     (ZIP (sup_vs,class_env_to_ie ce) ++
      ZIP (inst_vs,instance_env_to_ie inst_env)) ∧
   (* set up the variable environment
   * (every method name declared in class env is in env) *)
   env = set (MAP (FST ∘ FST) fns ++ MAP FST (class_env_to_env ce)) ∧
   (* create the map from class name to the type id in the
   * translated namespace *)
   cl_to_tyid = FEMPTY |++
     ZIP (MAP FST ce,GENLIST (λn. n + LENGTH (SND ns)) (LENGTH ce)) ∧
   (* an alist from class name to the data constructor name for
   * dictionary for the class *)
   MAP FST cl_cons = MAP FST ce ∧
   (* translate the namespace *)
   class_env_to_ns ce cl_to_tyid (MAP SND cl_cons) ce = SOME
  cl_ns ∧
   translated_ns =
     append_ns (namespace_to_tcexp_namespace ns) ([],cl_ns) ∧
   (* translate getting super classes and the method calls
   * by doing case analysis *)
   translated_ce = class_env_construct_dict (MAP SND cl_cons) sup_vs ce ∧
   (* translate all the dictionaries to let bindings *)
   instance_env_construct_dict ns ce ie env cl_cons default_name_map
     inst_vs inst_env translated_inst_env ∧
   (* translate defaults method *)
   default_impls_construct_dict ns ce ie env default_name_map defaults
     translated_defaults ∧
   (* translate the let bindings *)
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

val _ = export_theory();
