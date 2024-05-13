open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory;
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

(* if s is a super class of c then `Entail [k] [(s,TypeVar 0)] (c,TypeVar 0)`
* will be in the set ie *)
(* This should be equivalent to `entail` after turning all the super classes
* and instance declarations to ie *)
Definition safeLam_def:
  safeLam _ [] e = e ∧
  safeLam a xs e = Lam a xs e
End

Definition safeApp_def:
  safeApp _ e [] = e ∧
  safeApp a e xs = pure_cexp$App a e xs
End

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

Inductive construct_dict:
[~lie:]
  FLOOKUP lie d = SOME p ⇒
    construct_dict tdefs db ie lie p (pure_cexp$Var _ d)
[~ie:]
  FLOOKUP ie d = SOME it ∧
  specialises_inst tdefs it (Entail db cstrs p) ∧
  construct_dicts tdefs db ie lie cstrs ds ⇒
    construct_dict tdefs db ie lie p
      (safeApp _ (pure_cexp$Var _ d) ds)
[~dicts:]
  (LIST_REL (construct_dict tdefs db ie lie) ps ds) ⇒
    construct_dicts tdefs db ie lie ps ds
End

Theorem has_dict_EXISTS_construct_dict:
  (∀p. has_dict tdefs db (FRANGE ie) (FRANGE lie) p ⇒
    ∃(d: 'a cexp) . construct_dict tdefs db ie lie p d) ∧
  ∀ps. has_dicts tdefs db (FRANGE ie) (FRANGE lie) ps ⇒
    ∃(ds: 'a cexp list). construct_dicts tdefs db ie lie ps ds
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
  (∀p (d:'a cexp). construct_dict tdefs db ie lie p d ⇒
    has_dict tdefs db (FRANGE ie) (FRANGE lie) p) ∧
  (∀ps (ds:'a cexp list). construct_dicts tdefs db ie lie ps ds ⇒
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
      exhaustive_cepatl ns db ts pss ∧ IMAGE (cepat c) pss ⊆ s) ⇒
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

Overload Monad = ``Cons (Atom $ CompPrimTy $ M)``;

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
      type_elaborate_texp ns clk ie lie db st env (Lam vs e) (Lam vs e')
        (Functions args_tys ret_ty)

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
   EVERY (pred_type_kind_scheme_ok clk (SND ns) db) kind_schemes ∧ fns ≠ [] ∧
   type_elaborate_texp ns clk ie lie db st (REVERSE (ZIP (MAP (FST o FST) fns', kind_schemes)) ++ env) e e' t ⇒
      type_elaborate_texp ns clk ie lie db st env (Letrec fns e) (Letrec fns' e') t

[~Cons:]
  LIST_REL3 (type_elaborate_texp ns clk ie lie db st env) es es' carg_ts ∧
  EVERY (type_ok (SND ns) db) tyargs ∧
  type_cons (SND ns) db (cname,carg_ts) (tyid,tyargs) ⇒
     type_elaborate_texp ns clk ie lie db st env
       (Prim (Cons cname) es) (Prim (Cons cname) es')
       (tcons_to_type (INL tyid) tyargs)

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

Inductive type_elaborate_bindings:
   LIST_REL3
    (λ((fn,ot),body) ((fn',ot'),body') (varks,scheme).
      fn = fn' ∧
      ot' = SOME (varks,scheme) ∧
      (case ot of
      | NONE => T
      | SOME t => t = (LENGTH varks,scheme)) ∧
      pred_type_elaborate_texp ns clk ie lie (varks ++ db)
        (MAP (tshift $ LENGTH varks) st)
        (tshift_env_pred (LENGTH varks) env)
          body body' scheme)
      fns fns' kind_schemes ⇒
    type_elaborate_bindings ns clk ie lie db st env fns fns' kind_schemes
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

Definition get_names_namespace_def:
  get_names_namespace (ns: exndef # typedefs) =
    (MAP FST $ FST ns) ++ FLAT (MAP (MAP FST o SND) $ SND ns)
End

(* we need to record the variables/constructors to avoid name collision *)
Inductive texp_construct_dict:
[~Var:]
  construct_dicts (SND ns) db (ie:mlstring |-> entailment) lie ps ds ⇒
    texp_construct_dict ns ie lie db env (Var ps x)
      (safeApp _ (pure_cexp$Var _ x) ds)

[~Pred:]
  (* enforce all variables in vs are fresh *)
  set vs ∩ (FDOM lie ∪ FDOM ie ∪ env ∪ set (get_names_namespace ns)) = ∅ ∧
  LENGTH vs = LENGTH ps ∧
  texp_construct_dict ns ie (lie |++ ZIP (vs,ps)) db env e de ⇒
    pred_texp_construct_dict ns ie lie db env (Pred ps t) e (safeLam _ vs de)

[~Let:]
  pred_texp_construct_dict ns ie lie (new ++ db) env pt e1 de1 ∧
  texp_construct_dict ns ie lie db (x INSERT env) e2 de2 ⇒
    texp_construct_dict ns ie lie db env
      (typeclass_texp$Let (x,SOME (new,pt)) e1 e2)
      (pure_cexp$Let _ x de1 de2)

[~Letrec:]
  LIST_REL
    (λ((x,ot),e) (y,de).
      x = y ∧ ∃new pt. ot = SOME (new,pt) ∧
      pred_texp_construct_dict ns ie lie (new ++ db)
        (env ∪ set (MAP (FST o FST) fns)) pt e de)
    fns dfns ∧
  texp_construct_dict ns ie lie db (env ∪ set (MAP (FST o FST) fns)) e2 de2 ∧
  fns ≠ [] ⇒
    texp_construct_dict ns ie lie db env
      (typeclass_texp$Letrec fns e) (pure_cexp$Letrec _ dfns de)

[~Prim:]
  LIST_REL (texp_construct_dict ns ie lie db env) es des ⇒
    texp_construct_dict ns ie lie db env (Prim c es) (Prim _ c des)

[~Lam:]
  texp_construct_dict ns ie lie db
    (set (MAP FST xs) ∪ env) e de ⇒
      texp_construct_dict ns ie lie db env (Lam xs e) (Lam _ (MAP FST xs) de)

[~App:]
  texp_construct_dict ns ie lie db env e1 de1 ∧
  LIST_REL (texp_construct_dict ns ie lie db env) es des ⇒
    texp_construct_dict ns ie lie db env (App e1 es) (App _ de1 des)

[~NestedCase:]
  texp_construct_dict ns ie lie db env e e' ∧
  LIST_REL (λ(p,e) (p',e'). p = p' ∧
      texp_construct_dict ns ie lie db (v INSERT env ∪ pure_cexp$cepat_vars p) e e')
    ((p,e1)::pes) ((p,e1')::pes') ⇒
  texp_construct_dict ns ie lie db env (NestedCase e v p e1 pes)
    (NestedCase _ e' v p e1' pes')
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
  pairarg_tac >> rw[]
QED

Triviality MAP_FST_REVERSE_MAP_PRED_SND[simp]:
  MAP FST (REVERSE (MAP (λ(v,t). (v,[],Pred [] t)) vts)) =
    REVERSE (MAP FST vts)
Proof
  Induct_on `vts` >>
  rw[] >>
  pairarg_tac >> rw[]
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
      ∃(d:'a cexp). pred_texp_construct_dict ns
        ie_map lie_map db (set $ MAP FST env) pt e' d) ∧

  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    ∀lie_map.
      ie = FRANGE ie_map ∧
      lie = FRANGE lie_map ⇒
      ∃(d:'a cexp). texp_construct_dict ns
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
    rw[pairTheory.LAMBDA_PROD,GSYM pairTheory.PEXISTS_THM] >>
    pairarg_tac >> gvs[] >>
    pairarg_tac >> gvs[] >>
    pairarg_tac >>
    gvs[pred_setTheory.UNION_COMM] >>
    rw[GSYM PULL_EXISTS] >>
    metis_tac[]
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
    simp[Once pred_setTheory.UNION_COMM,
      pred_setTheory.INSERT_UNION_EQ]
  ) >>
  pop_assum mp_tac >>
  qid_spec_tac `pes'` >>
  qid_spec_tac `pes` >>
  ho_match_mp_tac LIST_REL_ind >>
  rw[] >>
  first_x_assum $ irule_at (Pos last) >>
  pairarg_tac >> fs[] >>
  pairarg_tac >> fs[pairTheory.LAMBDA_PROD,GSYM PEXISTS_THM] >>
  drule_then assume_tac type_cepat_cepat_vars >>
  fs[] >>
  metis_tac[pred_setTheory.UNION_COMM,pred_setTheory.INSERT_UNION_EQ]
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
Type default_impl[pp] = ``:mlstring # mlstring # ('a texp)``;
Type default_impls[pp] = ``:'a default_impl list``;

Definition type_elaborate_default_impl_def:
  type_elaborate_default_impl ce ns clk ie st env cl meth e e' ⇔
    ∃k s methods ks ps t.
      ALOOKUP (ce:class_env) cl = SOME (k,s,methods) ∧
      ALOOKUP methods meth = SOME (ks,Pred ps t) ∧
      pred_type_elaborate_texp ns clk ie EMPTY (k::ks) st env e e'
        (Pred ((cl,TypeVar 0)::ps) t)
End

Definition type_elaborate_default_impls_def:
  type_elaborate_default_impls ce ns clk ie st env defaults
    (defaults': Kind list default_impls) ⇔
  LIST_REL (λ(cl,meth,e) (cl',meth',e'). cl = cl' ∧ meth = meth' ∧
    type_elaborate_default_impl ce ns clk ie st env cl meth e e'
    ) defaults defaults'
End

Definition default_impl_construct_dict:
  default_impl_construct_dict ns ie env cl k (ks,Pred ps t) e e' ⇔
    pred_texp_construct_dict ns ie FEMPTY (k::ks) env
      (Pred ((cl,TypeVar 0)::ps) t) e e' 
End

Definition default_impls_construct_dict:
  default_impls_construct_dict ns ce ie env
    default_name_map defaults defaults' ⇔
  LIST_REL (λ(cl,meth,e) (name,e').
    ∃k supers meths pt.
      ALOOKUP default_name_map meth = SOME name ∧
      ALOOKUP ce cl = SOME (k,supers,meths) ∧
      ALOOKUP meths meth = SOME pt ∧
      default_impl_construct_dict ns ie env cl k pt e e')
    (defaults:Kind list default_impls) defaults'
End

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

Inductive instance_kind_check:
  LENGTH varks = n ∧
  clk class = SOME k ∧ kind_ok tdefs varks k t ∧
  EVERY (λ(c,t). ∃k. clk c = SOME k ∧ kind_ok tdefs varks k t) cstrs ⇒
    instance_kind_check tdefs clk
      ((class,n,t),cstrs,impls) ((class,varks,t),cstrs,impls')
End

Definition instance_env_kind_check_def:
  instance_env_kind_check tdefs clk (inst_env:num instance_env) inst_env' ⇔
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

Inductive type_elaborate_inst_env:
  LIST_REL (λ(_,_,impls) ((c,varks,t),cstrs,impls').
    ∃k supers meths. ALOOKUP ce c = SOME (k,supers,meths) ∧
    type_elaborate_impls ns clk ie st env varks cstrs t meths impls impls') 
    inst_env inst_env'⇒
    type_elaborate_inst_env ns (ce:class_env) clk ie st env
      (inst_env:num instance_env) (inst_env':Kind list instance_env)
End

Inductive instance_construct_dict:
  LIST_REL (λ(name,(meth_ks,pt)) e'.
    case ALOOKUP impls name of
    | SOME e =>
        impl_construct_dict ns ie env vs cstrs (varks++meth_ks)
          (tsubst_pred [inst_t] $ shift_db_pred 1n (LENGTH varks) pt) e e'
    | NONE => ∃default_name.
        ALOOKUP defaults name = SOME default_name ∧
        e' = App _ (Var _ default_name) [Var _ inst_v]) meths impls' ⇒
    instance_construct_dict ns ie env
      cl k cons meths defaults
      (* default_name maps a method name to a translated name *)
      inst_v varks cstrs inst_t impls
      (* inst_v is for referencing the dict itself *)
      (safeLam _ vs ((pure_cexp$Prim _ (Cons cons) impls')))
End

Inductive instance_env_construct_dict:
  LIST_REL3 (λinst_v ((cl,varks,inst_t),cstrs,impls) (v,e).
    v = inst_v ∧
    ∃k supers meths.
    ALOOKUP ce cl = SOME (k,supers,meths) ∧
    ALOOKUP clcons cl = SOME cons ∧
    instance_construct_dict ns ie env
      cl k cons meths default_name_map
      inst_v varks cstrs inst_t impls e
  ) inst_vs inst_env inst_env' ⇒
  instance_env_construct_dict ns ce ie env cl_cons default_name_map
    inst_vs (inst_env:Kind list instance_env) inst_env'
End

Inductive type_elaborate_prog:
  clk = ce_to_clk ce ∧
  instance_env_kind_check (SND ns) clk inst_env inst_env' ∧ 
  ie = set (class_env_to_ie ce ++ instance_env_to_ie inst_env') ∧
  env = REVERSE (ZIP (MAP (FST o FST) fns,fn_kind_schemes)) ++
    class_env_to_env ce ∧
  EVERY (pred_type_kind_scheme_ok clk (SND ns) []) fn_kind_schemes ∧ 
  type_elaborate_default_impls ce ns clk ie st env defaults defaults' ∧
  type_elaborate_bindings ns clk ie EMPTY [] st env fns fns' fn_kind_schemes ∧
  type_elaborate_inst_env ns ce clk ie st env inst_env inst_env' ⇒
    type_elaborate_prog ns ce st defaults inst_env fns defaults' inst_env' fns'
End

Inductive prog_construct_dict:
  LENGTH sup_vs = LENGTH $ class_env_to_ie ce ∧
  LENGTH inst_vs = LENGTH inst_env ∧
  ALL_DISTINCT (sup_vs ++ inst_vs ++ MAP FST (class_env_to_env ce) ++
    MAP (FST o FST) fns ++ MAP FST translated_defaults) ∧
  (ie:mlstring |-> entailment) = FEMPTY |++ (
    ZIP (sup_vs,class_env_to_ie ce) ++
    ZIP (inst_vs,instance_env_to_ie inst_env)) ∧
  env = set (MAP (FST o FST) fns ++ (MAP FST $ class_env_to_env ce)) ∧
  cl_to_tyid = FEMPTY |++
    ZIP (MAP FST ce,GENLIST (λn. n + LENGTH (SND ns)) (LENGTH ce)) ∧
  MAP FST cl_cons = MAP FST ce ∧
  class_env_to_ns cenv cl_to_tyid (MAP SND cl_cons) cenv = SOME cl_ns ∧
  translated_ns = append_ns (namespace_to_tcexp_namespace ns) ([],cl_ns) ∧
  class_env_construct_dict (MAP SND cl_cons) sup_vs ce = translated_ce ∧
  instance_env_construct_dict ns ce ie env cl_cons
    default_name_map inst_vs inst_env inst_env' ∧
  default_impls_construct_dict ns ce ie env default_name_map
    defaults translated_defaults ∧
  LIST_REL
    (λ((x,ot),e) (y,de).
      x = y ∧ ∃new pt. ot = SOME (new,pt) ∧
      pred_texp_construct_dict ns ie FEMPTY (new ++ db) env pt e de)
    fns translated_fns ⇒
    prog_construct_dict (ns:exndef # typedefs) ce st defaults inst_env fns translated_ns
      (translated_fns ++ translated_defaults ++ translated_inst_env
         ++ translated_ce)
End

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
      (kindArrow kindType kindType,[],[(
       (* Monoid m => (a -> m) -> t a -> m *)
        «foldMap»,[kindType;kindType],
          Pred [(«Monoid»,TypeVar 2)] $
          Functions [Functions [TypeVar 1] (TypeVar 2);
            Cons (TypeVar 0) (TypeVar 1)] (TypeVar 2))]))]
End

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
(*    ((«Semigroup»,2,Atom $ CompPrimTy $ Tuple 2 [TypeVar 0;TypeVar 1]),
      [«Semigroup»,TypeVar 0;«Semigroup»,TypeVar 1],
      [«mappend»,typeclass_texp$Lam [«x»,NONE;«y»,NONE]
        (NestedCase (Var [] «x») «x»
          (cepatCons «» [cepatVar «x1»;cepatVar «x2»])
          (NestedCase (Var [] «y») «y»
            (cepatCons «» [cepatVar «y1»;cepatVar «y2»])
            (Prim (Cons «») [
              App (Var [] «mappend») [Var [] «x1»;Var [] «y1»];
              App (Var [] «mappend») [Var [] «x2»;Var [] «y2»]])
            [])
          [])]);
    ((«Monoid»,2,Atom $ CompPrimTy $ Tuple 2 [TypeVar 0;TypeVar 1]),
      [«Monoid»,TypeVar 0;«Monoid»,TypeVar 1],
      [«mempty»,Prim (Cons «») [Var [] «mempty»,Var [] «mempty»]]); *)
    ((«Semigroup»,1,Cons (UserType 0) (TypeVar 0)),[],
      [«mappend»,Var [] «concat»]);
    ((«Monoid»,1,Cons (UserType 0) (TypeVar 0)),[],
      [«mempty»,Prim (Cons «[]») []])]
End

Definition test_instance_env_kind_def:
  test_instance_env_kind = [
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
(*    ((«Semigroup»,2,Atom $ CompPrimTy $ Tuple 2 [TypeVar 0;TypeVar 1]),
      [«Semigroup»,TypeVar 0;«Semigroup»,TypeVar 1],
      [«mappend»,typeclass_texp$Lam [«x»,NONE;«y»,NONE]
        (NestedCase (Var [] «x») «x»
          (cepatCons «» [cepatVar «x1»;cepatVar «x2»])
          (NestedCase (Var [] «y») «y»
            (cepatCons «» [cepatVar «y1»;cepatVar «y2»])
            (Prim (Cons «») [
              App (Var [] «mappend») [Var [] «x1»;Var [] «y1»];
              App (Var [] «mappend») [Var [] «x2»;Var [] «y2»]])
            [])
          [])]);
    ((«Monoid»,2,Atom $ CompPrimTy $ Tuple 2 [TypeVar 0;TypeVar 1]),
      [«Monoid»,TypeVar 0;«Monoid»,TypeVar 1],
      [«mempty»,Prim (Cons «») [Var [] «mempty»,Var [] «mempty»]]); *)
    ((«Semigroup»,[kindType],Cons (UserType 0) (TypeVar 0)),[],
      [«mappend»,Var [] «concat»]);
    ((«Monoid»,[kindType],Cons (UserType 0) (TypeVar 0)),[],
      [«mempty»,Prim (Cons «[]») []])]
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

Theorem test_instance_env_type_check:
  ie = set (class_env_to_ie test_class_env ++
    instance_env_to_ie test_instance_env_kind) ∧
  env = [«concat»,[kindType],Pred [] $
    Functions [
      Cons (UserType 0) (TypeVar 0);
      Cons (UserType 0) (TypeVar 0)] $
      Cons (UserType 0) (TypeVar 0)] ++
    class_env_to_env test_class_env ⇒
  type_elaborate_inst_env initial_namespace test_class_env
    (ce_to_clk test_class_env) ie [] env
    test_instance_env test_instance_env_kind
Proof
  rw[] >>
  irule type_elaborate_inst_env_rules >>
  rw[test_instance_env_kind_def,test_instance_env_def]
  >- (
    simp[Once test_class_env_def] >>
    rw[type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- simp[pred_type_well_scoped_def] >>
    conj_tac >- (
      simp[pred_type_kind_ok_def,pred_kind_wf_def,
        Functions_def,subst_db_def,shift_db_def] >>
      rpt (irule_at Any kind_wf_Cons) >>
      rpt (irule_at Any kind_wf_TyConsFunction) >>
      rpt (irule_at Any kind_wf_Prim)) >>
    irule type_elaborate_texp_Lam >>
    simp[type_ok_def,kind_ok_def,kind_wf_Prim,PULL_EXISTS] >>
    irule_at (Pos hd) type_elaborate_texp_AtomOp >>
    irule_at (Pos last) type_atom_op_IntOps_Int >>
    qexists `[Atom (PrimTy Integer);Atom (PrimTy Integer)]` >>
    simp[LIST_REL3_def,get_PrimTys_def] >>
    ntac 2 $ irule_at (Pos last) type_elaborate_texp_Var >>
    rpt (irule_at Any has_dict_dicts) >>
    simp[specialises_pred_def,subst_db_pred_def,subst_db_empty])
  >- (
    simp[Once test_class_env_def] >>
    rw[type_elaborate_impls_def] >>
    simp[subst_db_def,shift_db_def,
      subst_db_Functions,shift_db_Functions,
      subst_db_pred_def,shift_db_pred_def] >>
    irule type_elaborate_texp_Pred >>
    conj_tac >- simp[pred_type_well_scoped_def] >>
    conj_tac >- (
      simp[pred_type_kind_ok_def,pred_kind_wf_def,
        Functions_def,subst_db_def,shift_db_def] >>
      rpt (irule_at Any kind_wf_Cons) >>
      rpt (irule_at Any kind_wf_TyConsFunction) >>
      rpt (irule_at Any kind_wf_Prim)) >>
    irule_at (Pos hd) type_elaborate_texp_AtomOp >>
    irule_at (Pos last) type_atom_op_Lit >>
    simp[type_lit_rules] >>
    irule_at (Pos last) $ cj 1 get_PrimTys_def >>
    simp[LIST_REL3_def]
  )
  >- (
    simp[Once test_class_env_def] >>
    rw[type_elaborate_impls_def] >>
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
        Functions_def,subst_db_def,shift_db_def] >>
      simp[ce_to_clk_def,test_class_env_def] >>
      rpt (irule_at Any kind_wf_Cons) >>
      rpt (irule_at Any kind_wf_TyConsFunction) >>
      rpt (irule_at Any kind_wf_VarTypeCons) >>
      simp[miscTheory.LLOOKUP_THM] >>
      irule kind_wf_TyConsINL >>
      simp[typedefs_to_cdb_def,initial_namespace_def,
        miscTheory.LLOOKUP_THM,kind_arrows_def]
    ) >>
    irule type_elaborate_texp_Lam >>
    rw[type_ok_def,kind_ok_def]
    >- (
      simp[Functions_def] >>
      rpt (irule_at Any kind_wf_Cons) >>
      rpt (irule_at Any kind_wf_TyConsFunction) >>
      rpt (irule_at Any kind_wf_VarTypeCons) >>
      simp[miscTheory.LLOOKUP_THM]
    )
    >- (
      rpt (irule_at Any kind_wf_Cons) >>
      rpt (irule_at Any kind_wf_VarTypeCons) >>
      simp[miscTheory.LLOOKUP_THM] >>
      irule kind_wf_TyConsINL >>
      simp[typedefs_to_cdb_def,initial_namespace_def,
        miscTheory.LLOOKUP_THM,kind_arrows_def]
     ) >>
     simp[PULL_EXISTS] >>
     qrefinel [`Functions args_t ret_t`,`Cons (UserType 0) (TypeVar 0)`] >>
     irule_at (Pos hd) type_elaborate_texp_NestedCase >>
     irule_at (Pos hd) type_elaborate_texp_Var >>
     simp[has_dicts_empty,specialises_pred_def,subst_db_pred_def,
       PULL_EXISTS] >>
     irule_at (Pos hd) type_cepat_Cons>>
     simp[initial_namespace_def,destruct_type_cons_def,
      subst_db_def,split_ty_head_def,split_ty_head_aux_def,
      type_cons_def,miscTheory.LLOOKUP_THM] >>
     simp[kind_ok_def] >>
     irule_at (Pos hd) kind_wf_VarTypeCons >>
     simp[miscTheory.LLOOKUP_THM] >>
     qrefine `[_;_]` >>
     simp[LIST_REL3_def] >>
     irule_at (Pos hd) type_cepat_Var >>
     irule_at (Pos hd) type_cepat_Var >>
     irule_at Any type_cepat_UScore >>
     irule_at Any type_elaborate_texp_Var >>
     simp[Once class_env_to_env_def,Once test_class_env_def] >>
     simp[specialises_pred_def,get_method_type_def,subst_db_pred_def] >>
     simp[PULL_EXISTS,subst_db_def,kind_ok_def] >>
     irule_at (Pos last) exhaustive_cepat_UScore >>
     rw[GSYM PULL_EXISTS]
     >- (
       irule_at (Pos hd) kind_wf_VarTypeCons >>
       simp[miscTheory.LLOOKUP_THM])
     >- (
       irule_at (Pos hd) has_dict_dicts >>
       simp[] >>
       irule has_dict_lie >>
       simp[]) >>
     irule_at (Pos hd) type_elaborate_texp_App >>
     irule_at (Pos hd) type_elaborate_texp_Var >>
     simp[Once class_env_to_env_def,Once test_class_env_def] >>
     simp[specialises_pred_def,get_method_type_def] >>
     simp[PULL_EXISTS,subst_db_def,subst_db_pred_def,
      subst_db_Functions] >>
     rw[GSYM PULL_EXISTS]
     >- (
       simp[kind_ok_def] >>
       irule kind_wf_VarTypeCons >>
       simp[miscTheory.LLOOKUP_THM]) >>
     irule_at (Pos hd) EQ_REFL >>
     rw[GSYM PULL_EXISTS]
     >- (
      irule has_dict_dicts >>
      simp[] >>
      irule has_dict_ie >>
      qexistsl [
        `[(«Monoid»,TypeVar 1)]`,
        `Entail [kindType] [(«Monoid»,TypeVar 0)] («Semigroup»,TypeVar 0)`] >>
      simp[Once class_env_to_ie_def,Once test_class_env_def,
        class_to_entailments_def] >>
      simp[specialises_inst_def,PULL_EXISTS] >>
      qexists `TypeVar 1` >>
      simp[kind_ok_def] >>
      irule_at (Pos hd) kind_wf_VarTypeCons >>
      simp[miscTheory.LLOOKUP_THM,subst_db_def] >>
      irule has_dict_dicts >>
      simp[] >>
      irule has_dict_lie >>
      simp[]) >>
     simp[LIST_REL3_def] >>
     irule_at (Pos hd) type_elaborate_texp_App >>
     irule_at (Pos hd) type_elaborate_texp_Var >>
     simp[specialises_pred_def,PULL_EXISTS,subst_db_pred_def,
      subst_db_Functions,subst_db_empty,has_dicts_empty] >>
     irule_at (Pos hd) EQ_REFL >>
     qrefine `[arg_t]` >>
     simp[subst_db_empty,LIST_REL3_def] >>
     irule_at (Pos hd) type_elaborate_texp_Var >>
     simp[specialises_pred_def,subst_db_def,subst_db_pred_def,
      has_dicts_empty] >>
     irule type_elaborate_texp_App >>
     simp[] >>
     qrefine `[at0;at1]` >>
     simp[LIST_REL3_def] >>
     rpt (
      irule_at (Pos hd) type_elaborate_texp_Var >>
      simp[specialises_pred_def,subst_db_pred_def,subst_db_def,
        subst_db_empty,has_dicts_empty]) >>
     simp[Once class_env_to_env_def,Once test_class_env_def] >>
     simp[get_method_type_def,specialises_pred_def,
       subst_db_pred_def,subst_db_def,PULL_EXISTS] >>
    simp[kind_ok_def,subst_db_Functions,subst_db_def] >>
    irule_at Any kind_wf_TyConsINL >>
    simp[Once typedefs_to_cdb_def,miscTheory.LLOOKUP_THM,kind_arrows_def] >>
    rpt (irule_at Any kind_wf_VarTypeCons) >>
    simp[miscTheory.LLOOKUP_THM] >>
    irule has_dict_dicts >>
    rw[]
    >- (
      irule has_dict_ie >>
      simp[instance_env_to_ie_def,instance_to_entailment_def] >>
      qexistsl [`[]`,`Entail [] [] («Foldable»,UserType 0)`] >>
      simp[has_dicts_empty,specialises_inst_def,subst_db_empty]
    ) >>
    irule has_dict_lie >>
    simp[]
  )
QED

Definition test_prog_def:
  test_prog = [
    («concat»,NONE),Lam [«l»,NONE;«r»,NONE] $
    NestedCase (Var [] «l») «l»
      (cepatCons «::» [cepatVar «h»; cepatVar «tl»])
        (Prim (Cons «::») [Var [] «h»;
          App (Var [] «concat») [Var [] «tl»; Var [] «r»]])
      [cepatCons «[]» [],Var [] «r»];

    («test»,NONE),
      Letrec [(«fold»,NONE),
        App (Var [] «foldMap») [Lam [«x»,NONE] (Var [] «x»)]] $
      App (Var [] «fold») [App (Var [] «fold»)
        [Prim (Cons «::») [
          Prim (Cons «::») [
            Prim (AtomOp $ Lit (Int 1)) [];
            Prim (Cons «[]») []];
          Prim (Cons «[]») []]]]
  ]
End

(* translation of predicated types to types without predicates,
* as a witness to the tpying rules of tcexp *)
Theorem texp_construct_dict_IMP_type_tcexp:
  acyclic
    (λp. ∃s x. FLOOKUP ce (SND p) = SOME (s,x) ∧ MEM (FST p) s) ∧
  ce_in_ie ce ie ∧
  class_kind_ok ce clk ∧
  FRANGE ie_map = ie ⇒
  (∀lie db st env e e' pt.
    pred_type_elaborate_texp ns clk ie lie db st env e e' pt ⇒
    ∀lie_map d. 
      FRANGE lie_map = lie ∧
      pred_texp_construct_dict (set $ get_names_namespace ns)
        ie_map lie_map (IMAGE FST $ set env) pt e' (d:'a cexp) ⇒
    ∃ie_env dt.
      ie_to_env ce ie_map = SOME ie_env ∧
      translate_pred_type ce pt = SOME dt ∧
      type_tcexp ns db st
        (translate_env ce env ++ lie_to_env ce lie_map ++ ie_env)
        (tcexp_of d) dt) ∧

  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    ∀lie_map d.
      lie = FRANGE lie_map ∧
      texp_construct_dict (set $ get_names_namespace ns)
        ie_map lie_map (IMAGE FST $ set env) e' (d:'a cexp) ⇒
     ∃ie_env. ie_to_env ce ie_map = SOME ie_env ∧
       type_tcexp ns db st
         (translate_env ce env ++ lie_to_env ce lie_map ++ ie_env) 
         (tcexp_of d) t)
Proof
  strip_tac >>
  ho_match_mp_tac type_elaborate_texp_ind >>
QED

val _ = export_theory();
