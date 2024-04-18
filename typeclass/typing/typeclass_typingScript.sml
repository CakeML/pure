open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory relationTheory set_relationTheory pred_setTheory;
open typeclass_typesTheory pure_tcexpTheory typeclass_texpTheory
typeclass_kindCheckTheory pure_configTheory;
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

(* we use kind instead of just arities *)
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
  typedefs_to_cdb (typedefs:typedefs) =
    (λc. OPTION_MAP (λtinfo. kind_arrows (FST tinfo) kindType)
        (LLOOKUP typedefs c))
End

Definition kind_ok_def:
  kind_ok (typedefs: typedefs) ks k t ⇔
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

Type type_scheme[pp] = ``:num # type``;
Type pred_type_scheme[pp] = ``:num # PredType``;

Type type_kind_scheme[pp] = ``:Kind list # type``;
Type pred_type_kind_scheme[pp] = ``:Kind list # PredType``;

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

Overload append_ns = ``λ (ns:(exndef # typedefs)) ns'. (FST ns ++ FST ns', SND ns ++ SND ns')``;

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

Definition get_constructors_def:
  get_constructors (edef:exndef,tdefs: typedefs) t ⇔
  if t = Atom Exception
  then SOME $ MAP (I ## LENGTH) edef
  else do
    (tc,targs) <- split_ty_head t;
    case tc of
    | INL tyid => OPTION_MAP (MAP (I ## LENGTH) o SND) $ oEL tyid tdefs
    | INR (PrimT Bool) => SOME ([«True»,0;«False»,0])
    | INR (CompPrimT (Tuple n)) => SOME ([«»,n])
    | _ => NONE
  od
End

Definition 

Definition get_PrimTys_def:
  get_PrimTys [] = SOME [] ∧
  get_PrimTys ((Atom $ PrimTy pty) :: rest) = OPTION_MAP (CONS pty) (get_PrimTys rest) ∧
  get_PrimTys _ = NONE
End

(* shows how the class constraint can be satisfied.
* e.g. Num a => Ord a, since Ord is a superclass of Num,
* (Monoid a, Monoid b) => Monoid (a, b), deal to instance declaration *)
Datatype:
  entailment = Entail ((mlstring # type) list) (mlstring # type)
End

Definition specialises_inst_def:
  specialises_inst (Entail ps p) (Entail qs q) ⇔
    ∃subs.
      LIST_REL (λ(c,t) (c',t'). c = c' ∧
      tsubst subs t = t') (p::ps) (q::qs)
End

(* if s is a super class of c then `Entail [(s,TypeVar 0)] (c,TypeVar 0)`
* will be in the set ie *)
(* This should be equivalent to `entail` after turning all the super classes
* and instance declarations to ie *)
Inductive has_dict:
[~lie:]
  p ∈ lie ⇒ has_dict ie lie p
[~ie:]
  it ∈ ie ∧ specialises_inst it (Entail cstrs p) ∧
  has_dicts ie lie cstrs ⇒
    has_dict ie lie p
[~dicts:]
  (∀p. MEM p ps ⇒ has_dict ie lie p) ⇒
    has_dicts ie lie ps
End

Inductive construct_dict:
[~lie:]
  FLOOKUP lie d = SOME p ⇒
    construct_dict ie lie p (pure_cexp$Var _ d)
[~ie:]
  FLOOKUP ie d = SOME it ∧
  specialises_inst it (Entail cstrs p) ∧
  construct_dicts ie lie cstrs ds ⇒
    construct_dict ie lie p (pure_cexp$App _ (pure_cexp$Var _ d) ds)
[~dicts:]
  (LIST_REL (construct_dict ie lie) ps ds) ⇒
    construct_dicts ie lie ps ds
End

Theorem has_dict_EXISTS_construct_dict:
  (∀p. has_dict (FRANGE ie) (FRANGE lie) p ⇒
    ∃(d: 'a cexp) . construct_dict ie lie p d) ∧
  ∀ps. has_dicts (FRANGE ie) (FRANGE lie) ps ⇒
    ∃(ds: 'a cexp list). construct_dicts ie lie ps ds
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
  (∀p (d:'a cexp). construct_dict ie lie p d ⇒
    has_dict (FRANGE ie) (FRANGE lie) p) ∧
  (∀ps (ds:'a cexp list). construct_dicts ie lie ps ds ⇒
    has_dicts (FRANGE ie) (FRANGE lie) ps)
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
   -> (env: (string # (num # Predtype)) list)
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
   has_dicts ie lie ps ⇒
      type_elaborate_texp ns clk ie lie db st env (Var _ x) (Var ps x) t)

[~Pred:]
  type_elaborate_texp ns clk ie (lie ∪ set ps) db st env e e' t ∧
  pred_type_kind_ok clk (SND ns) db (Pred ps t) ⇒
    pred_type_elaborate_texp ns clk ie lie db st env e e' (Pred ps t)

[~App:]
  type_elaborate_texp ns clk ie lie db st env e e' (Functions arg_tys ret_ty) ∧
  es ≠ [] ∧
  LIST_REL3 (type_elaborate_texp ns clk ie lie db st env) es es' arg_tys ⇒
    type_elaborate_texp ns clk ie lie db st env (App e es) (App e' es') ret_ty

[~Let:]
  LENGTH new = n ∧
  pred_type_elaborate_texp ns clk ie lie (new ++ db) (MAP (tshift n) st)
    (tshift_env_pred n env) e1 e1' pt1 ∧
  (* enforces all variables in the predicates to be well scoped:
   * rejects `Read a, Show a => String -> String` *)
  pred_type_well_scoped pt1 ∧
  type_elaborate_texp ns clk ie lie db st ((x,new,pt1)::env) e2 e2' t2 ⇒
     type_elaborate_texp ns clk ie lie db st env (Let (x,NONE) e1 e2)
        (Let (x,SOME (n,pt1)) e1' e2') t2

(* The poly type of the let binding is annotated by the user *)
[~LetSOME:]
  type_elaborate_texp ns clk ie lie db st env (Let (x,NONE) e1 e2)
    (Let (x,SOME (n,pt)) e1' e2') t2 ⇒
      type_elaborate_texp ns clk ie lie db st env (Let (x,SONE (n,pt)) e1 e2)
        (Let (x,SOME (n,pt)) e1' e2') t2

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
      ot' = SOME (LENGTH varks,scheme) ∧
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

(*
* Dictionary construction given that we have the elaborated expression.
* texp_construct_dict:
*     ns: mlstring set                    all constructors
* ->  ie: (mlstring |-> (class # type))   instance environment
* -> lie: (mlstring |-> entailment)       local instance environment
* -> env: mlstring set                    term variables in scope
* ->  ps: texp                           elaborated expression
* ->  ds:'a cexp                          translated cexp expression
*)

(* we need to record the variables/constructors to avoid name collision *)
Inductive texp_construct_dict:
[~Var:]
  construct_dicts ie lie ps ds ⇒
    texp_construct_dict ns ie lie env (Var ps x)
      (pure_cexp$App _ (pure_cexp$Var _ x) ds)

[~Pred:]
  (* enforce all variables in vs are fresh *)
  set (MAP FST vs) ∩ (FDOM lie ∪ FDOM ie ∪ env ∪ ns) = ∅ ∧
  texp_construct_dict ns ie (lie |++ vs) env e de ∧
  ps = MAP SND vs ⇒
    pred_texp_construct_dict ns ie lie env (Pred ps t) e (pure_cexp$Lam _ (MAP FST vs) de)

[~Let:]
  pred_texp_construct_dict ns ie lie env pt e1 de1 ∧
  texp_construct_dict ns ie lie (x INSERT env) e2 de2 ⇒
    texp_construct_dict ns ie lie env
      (typeclass_texp$Let (x,SOME (new,pt)) e1 e2)
      (pure_cexp$Let _ x de1 de2)

[~Letrec:]
  LIST_REL
    (λ((x,ot),e) (y,de).
      x = y ∧ ∃new pt. ot = SOME (new,pt) ∧
      pred_texp_construct_dict ns ie lie
        (env ∪ set (MAP (FST o FST) fns)) pt e de)
    fns dfns ∧
  texp_construct_dict ns ie lie (env ∪ set (MAP (FST o FST) fns)) e2 de2 ∧
  fns ≠ [] ⇒
    texp_construct_dict ns ie lie env
      (typeclass_texp$Letrec fns e) (pure_cexp$Letrec _ dfns de)

[~Prim:]
  LIST_REL (texp_construct_dict ns ie lie env) es des ⇒
    texp_construct_dict ns ie lie env (Prim c es) (Prim _ c des)

[~Lam:]
  texp_construct_dict ns ie lie
    (set (MAP FST xs) ∪ env) e de ⇒
      texp_construct_dict ns ie lie env (Lam xs e) (Lam _ (MAP FST xs) de)

[~App:]
  texp_construct_dict ns ie lie env e1 de1 ∧
  LIST_REL (texp_construct_dict ns ie lie env) es des ⇒
    texp_construct_dict ns ie lie env (App e1 es) (App _ de1 des)

[~NestedCase:]
  texp_construct_dict ns ie lie env e e' ∧
  LIST_REL (λ(p,e) (p',e'). p = p' ∧
      texp_construct_dict ns ie lie (v INSERT env ∪ pure_cexp$cepat_vars p) e e')
    ((p,e1)::pes) ((p,e1')::pes') ⇒
  texp_construct_dict ns ie lie env (NestedCase e v p e1 pes)
    (NestedCase _ e' v p e1' pes')
End

Definition acyclic_rec_def:
  acyclic_rec r f err x =
    if acyclic r ∧ ∃s. FINITE s ∧ domain r ⊆ s ∧ range r ⊆ s
    then
      let children = SET_TO_LIST {y | r (y,x)} in
        f x children (MAP (acyclic_rec r f err) children)
    else err
Termination
  WF_REL_TAC `λx y.
    FST x = FST y ∧
    acyclic (FST y) ∧ ∃s. FINITE s ∧ domain (FST y) ⊆ s ∧ range (FST y) ⊆ s ∧
    (FST y) (SND $ SND $ SND x, SND $ SND $ SND y)`
  >- (
    qspecl_then [
      `\r. acyclic r ∧ ∃s. FINITE s ∧ domain r ⊆ s ∧ range r ⊆ s`,
      `FST`,
      `λr x y. r(x,y)`,
      `SND o SND o SND`
    ] irule WF_PULL >>
    reverse $ rw[]
    >- (
      drule_all acyclic_WF >>
      simp[reln_to_rel_def,IN_DEF]
    ) >>
    metis_tac[]
  ) >>
  rw[] >>
  pop_assum mp_tac >>
  DEP_REWRITE_TAC[MEM_SET_TO_LIST] >>
  reverse $ rw[]
  >- metis_tac[] >>
  drule_then irule SUBSET_FINITE >>
  gvs[domain_def] >>
  rev_drule_at_then Any irule SUBSET_TRANS >>
  rw[SUBSET_DEF,IN_DEF] >>
  metis_tac[]
End

Definition acyclic_depth_def:
  acyclic_depth r x = acyclic_rec r (λx xs ys. list_max ys + 1n) 0 x
End

Theorem list_max_MAX_SET_set:
  list_max l = MAX_SET (set l)
Proof
  Induct_on `l` >>
  rw[miscTheory.list_max_def,MAX_SET_THM,MAX_DEF]
QED

Theorem acyclic_depth_alt:
  ∀r x.
    acyclic_depth r x =
      if acyclic r ∧ ∃s. FINITE s ∧ domain r ⊆ s ∧ range r ⊆ s
      then
        MAX_SET (IMAGE (acyclic_depth r) {y | r (y,x)}) + 1
      else 0
Proof
  simp[lambdify acyclic_depth_def] >>
  `∀r f e x.
     f = (λx xs ys. list_max ys + 1) ∧ e = 0 ⇒
     acyclic_rec r f e x =
     if acyclic r ∧ ∃s. FINITE s ∧ domain r ⊆ s ∧ range r ⊆ s then
       MAX_SET (IMAGE (λx. acyclic_rec r f e x) {y | r (y,x)}) + 1
     else 0` suffices_by rw[] >>
  ho_match_mp_tac acyclic_rec_ind >>
  reverse $ rw[]
  >- simp[acyclic_rec_def] >>
  simp[Once acyclic_rec_def] >>
  reverse $ IF_CASES_TAC
  >- metis_tac[] >>
  simp[list_max_MAX_SET_set,LIST_TO_SET_MAP] >>
  DEP_REWRITE_TAC[SET_TO_LIST_INV] >>
  gvs[domain_def,IN_DEF] >>
  drule_then irule SUBSET_FINITE >>
  rev_drule_at_then Any irule SUBSET_TRANS >>
  rw[SUBSET_DEF,IN_DEF] >>
  metis_tac[]
QED

Theorem acyclic_super_FINITE:
  acyclic (λp. ∃s x. FLOOKUP ce (SND p) = SOME (s,x) ∧ MEM (FST p) s) ⇒
  ∃s.
    FINITE s ∧
    domain
      (λp. ∃s ts. FLOOKUP ce (SND p) = SOME (s,ts) ∧ MEM (FST p) s) ⊆ s ∧
    range
      (λp. ∃s ts. FLOOKUP ce (SND p) = SOME (s,ts) ∧ MEM (FST p) s) ⊆ s
Proof
  strip_tac >>
  qexists `FDOM ce ∪
    BIGUNION (IMAGE (set o FST) $ FRANGE ce)` >>
  rw[]
  >- simp[FINITE_LIST_TO_SET]
  >- (
    irule pred_setTheory.SUBSET_TRANS >>
    irule_at (Pos last) $ cj 2 pred_setTheory.SUBSET_UNION >>
    rw[pred_setTheory.SUBSET_DEF,IN_DEF,set_relationTheory.domain_def,
         SRULE[IN_DEF] finite_mapTheory.FRANGE_FLOOKUP] >>
    first_x_assum $ irule_at (Pos last) >>
    simp[]
  ) >>
  irule pred_setTheory.SUBSET_TRANS >>
  irule_at (Pos last) $ cj 1 pred_setTheory.SUBSET_UNION >>
  rw[pred_setTheory.SUBSET_DEF,set_relationTheory.range_def,
    finite_mapTheory.flookup_thm]
QED

Definition split_translate_predicate_tuple_def:
  split_translate_predicate_tuple x =
  case x of
  | INL y => (FST y,INL $ SND $ SND y)
  | INR y => (FST y,INR $ SND $ SND y)
End

Definition translate_predicate_def:
  translate_predicate (ce: 'a |-> ('a list # (type list))) t (c:'a) =
  (if acyclic (λp. ∃s x. FLOOKUP ce (SND p) = SOME (s,x) ∧ MEM (FST p) s)
  then
  do
    (sups, ts) <- FLOOKUP ce c;
    sups' <- translate_predicatel ce t sups;
    return $ tcons_to_type (INR $ CompPrimT $ Tuple $ LENGTH sups' + LENGTH ts)
      (sups' ++ MAP (tsubst [t]) ts)
  od
  else NONE) ∧
  translate_predicatel ce ty [] = SOME [] ∧
  translate_predicatel ce ty (c::cs) =
  do
    h <- if acyclic (λp. ∃s x. FLOOKUP ce (SND p) = SOME (s,x) ∧ MEM (FST p) s)
      then translate_predicate ce ty c
      else NONE;
    t <- translate_predicatel ce ty cs;
    return $ h::t
  od
Termination
  simp[] >>
  WF_REL_TAC `λa b.
    let (ce,x) = split_translate_predicate_tuple a in
    let (ce',y) = split_translate_predicate_tuple b in
    ce = ce' ∧
    acyclic (λp. ∃s ts. FLOOKUP ce (SND p) = SOME (s,ts) ∧ MEM (FST p) s) ∧
    inv_image ($< LEX $<) (λc.
      (case c of
       | INL c =>
           acyclic_depth
            (λp. ∃s ts. FLOOKUP ce (SND p) = SOME (s,ts) ∧
              MEM (FST p) s) c
       | INR cs =>
          list_max $ MAP (acyclic_depth
            (λp. ∃s ts. FLOOKUP ce (SND p) = SOME (s,ts) ∧
              MEM (FST p) s)) cs),
      (case c of
       | INL c => 0
       | INR cs => LENGTH cs)) x y`
  >- (
    qspecl_then [
      `\(ce: 'a |-> ('a list # (type list))).
        acyclic (λp. ∃s ts. FLOOKUP ce (SND p) = SOME (s,ts) ∧
          MEM (FST p) s)`,
       `(FST o split_translate_predicate_tuple):
       (α |-> α list # type list) # δ # α +
       (α |-> α list # type list) # δ # (α list) ->
         (α |-> α list # type list)`,
       `λce. inv_image ($< LEX $<) (λc.
        (case c of
         | INL c =>
             acyclic_depth
              (λp. ∃s ts. FLOOKUP ce (SND p) = SOME (s,ts) ∧
                MEM (FST p) s) c
         | INR cs =>
            list_max $ MAP (acyclic_depth
              (λp. ∃s ts. FLOOKUP ce (SND p) = SOME (s,ts) ∧
                MEM (FST p) s)) cs),
        (case c of
         | INL c => 0
         | INR cs => LENGTH cs))`,
       `SND o split_translate_predicate_tuple`
      ] irule WF_PULL >>
    reverse $ rw[]
    >- DEP_REWRITE_TAC[WF_inv_image,WF_LEX,prim_recTheory.WF_LESS] >>
    Cases_on `x` >>
    Cases_on `y` >>
    gvs[split_translate_predicate_tuple_def]) >>
  rw[split_translate_predicate_tuple_def] >>
  simp[miscTheory.list_max_def] >>
  CONV_TAC $ RAND_CONV $ SCONV[Once acyclic_depth_alt] >>
  rw[list_max_MAX_SET_set,LIST_TO_SET_MAP] >>
  spose_not_then kall_tac >>
  pop_assum mp_tac >> simp[] >>
  metis_tac[acyclic_super_FINITE]
End

Theorem translate_predicatel_def:
  translate_predicatel ce ty [] = SOME [] ∧
  translate_predicatel ce ty (c::cs) =
  do
    h <- translate_predicate ce ty c;
    t <- translate_predicatel ce ty cs;
    return $ h::t
  od
Proof
  simp[translate_predicate_def]
QED

Theorem translate_predicate_alt = cj 1 translate_predicate_def;

Theorem translate_predicatel_OPT_MMAP:
  translate_predicatel ce ty l = OPT_MMAP (translate_predicate ce ty) l
Proof
  Induct_on `l` >>
  rw[translate_predicatel_def,listTheory.OPT_MMAP_def]
QED

Overload translate_pred = ``λce p. translate_predicate ce (SND p) (FST p)``;

Definition translate_pred_type_def:
  translate_pred_type ce (Pred ps t) =
  do
    pts <- OPT_MMAP (translate_pred ce) ps;
    return $ Functions pts t
  od
End

Definition translate_entailment_def:
  translate_entailment ce (Entail ps q) =
  do
    pts <- OPT_MMAP (translate_pred ce) ps;
    qt <- translate_pred ce q;
    return $ Functions pts qt
  od
End

(********************)

Definition get_names_namespace_def:
  get_names_namespace (ns: exndef # typedefs) =
    (MAP FST $ FST ns) ++ FLAT (MAP (MAP FST o SND) $ SND ns)
End

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
      ∃(d:'a cexp). pred_texp_construct_dict (set $ get_names_namespace ns)
        ie_map lie_map (set $ MAP FST env) pt e' d) ∧

  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    ∀lie_map.
      ie = FRANGE ie_map ∧
      lie = FRANGE lie_map ⇒
      ∃(d:'a cexp). texp_construct_dict (set $ get_names_namespace ns)
        ie_map lie_map (set $ MAP FST env) e' d)
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
    qexists `ZIP (vs,ps)` >>
    simp[MAP_ZIP] >>
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

Inductive type_tcexp:
[~Var:]
  (ALOOKUP env x = SOME s ∧ specialises (SND ns) db s t ⇒
      type_tcexp ns db st env (pure_tcexp$Var x) t)

[~Tuple:]
  (LIST_REL (type_tcexp ns db st env) es ts ⇒
      type_tcexp ns db st env (Prim (Cons «») es)
        (cons_types (Atom $ CompPrimTy $ Tuple $ LENGTH ts) ts))

[~Ret:]
  (type_tcexp ns db st env e t ⇒
      type_tcexp ns db st env (Prim (Cons «Ret») [e]) (Monad t))

[~Bind:]
  (type_tcexp ns db st env e1 (Monad t1) ∧
   type_tcexp ns db st env e2 (Functions [t1] (Monad t2)) ⇒
      type_tcexp ns db st env (Prim (Cons «Bind») [e1;e2]) (Monad t2))

[~Raise:]
  (type_tcexp ns db st env e (Atom Exception) ∧
   type_ok (SND ns) db t ⇒
      type_tcexp ns db st env (Prim (Cons «Raise») [e]) (Monad t))

[~Handle:]
  (type_tcexp ns db st env e1 (Monad t) ∧
   type_tcexp ns db st env e2 (Functions [Atom Exception] (Monad t)) ⇒
      type_tcexp ns db st env (Prim (Cons «Handle») [e1;e2]) (Monad t))

[~Act:]
  (type_tcexp ns db st env e (Atom $ PrimTy Message) ⇒
      type_tcexp ns db st env (Prim (Cons «Act») [e]) (Monad $ Atom $ PrimTy String))

[~Alloc:]
   type_tcexp ns db st env e1 (Atom $ PrimTy Integer) ∧
   type_tcexp ns db st env e2 t ⇒
      type_tcexp ns db st env (Prim (Cons «Alloc») [e1;e2])
        (Monad $ Cons (Atom $ CompPrimTy $ Array) t)

[~Length:]
   type_tcexp ns db st env e (Cons (Atom $ CompPrimTy $ Array) t) ⇒
      type_tcexp ns db st env (Prim (Cons «Length») [e]) (Monad $ Atom $ PrimTy Integer)

[~Deref:]
   type_tcexp ns db st env e1 (Cons (Atom $ CompPrimTy $ Array) t) ∧
   type_tcexp ns db st env e2 (Atom $ PrimTy Integer) ⇒
      type_tcexp ns db st env (Prim (Cons «Deref») [e1;e2]) (Monad t)

[~Update:]
   type_tcexp ns db st env e1 (Cons (Atom $ CompPrimTy $ Array) t) ∧
   type_tcexp ns db st env e2 (Atom $ PrimTy Integer) ∧
   type_tcexp ns db st env e3 t ⇒
      type_tcexp ns db st env (Prim (Cons «Update») [e1;e2;e3]) (Monad Unit)

[~Exception:]
   LIST_REL (type_tcexp (exndef,typedefs) db st env) es carg_ts ∧
   type_exception exndef (cname,carg_ts) ⇒
      type_tcexp ns db st env (Prim (Cons cname) es) (Atom Exception)

[~True:]
   type_tcexp ns db st env (Prim (Cons «True») []) (Atom $ PrimTy Bool)

[~False:]
   type_tcexp ns db st env (Prim (Cons «False») []) (Atom $ PrimTy Bool)

[~Cons:]
   LIST_REL (type_tcexp ns db st env) es carg_ts ∧
   EVERY (type_ok (SND ns) db) tyargs ∧
   type_cons (SND ns) db (cname,carg_ts) (tyid,tyargs) ⇒
      type_tcexp ns db st env
        (Prim (Cons cname) es) (tcons_to_type (INL tyid) tyargs)

[~Loc:]
   oEL n st = SOME t ⇒
      type_tcexp ns db st env (Prim (AtomOp $ Lit (Loc n)) [])
        (Cons (Atom $ CompPrimTy $ Array) t)

[~AtomOp:]
   LIST_REL (type_tcexp ns db st env) es ts ∧
   get_PrimTys ts = SOME pts ∧
   type_atom_op aop pts pt ⇒
      type_tcexp ns db st env (Prim (AtomOp aop) es) (Atom $ PrimTy pt)

[~Seq:]
  (type_tcexp ns db st env e1 t1 ∧ type_tcexp ns db st env e2 t2 ⇒
      type_tcexp ns db st env (Prim Seq [e1; e2]) t2)

[~App:]
  (type_tcexp ns db st env e (Functions arg_tys ret_ty) ∧
   LIST_REL (type_tcexp ns db st env) es arg_tys ∧ arg_tys ≠ [] ⇒
      type_tcexp ns db st env (App e es) ret_ty)

[~Lam:]
  (EVERY (type_ok (SND ns) db) arg_tys ∧
   LENGTH arg_tys = LENGTH xs ∧ arg_tys ≠ [] ∧
   type_tcexp ns db st (REVERSE (ZIP (xs, MAP ($, []) arg_tys)) ++ env) e ret_ty
      ⇒ type_tcexp ns db st env (Lam xs e) (Functions arg_tys ret_ty))

[~Let:]
   LENGTH new = n ∧
   type_tcexp ns (new ++ db) (MAP (tshift n) st) (tshift_env n env) e1 t1 ∧
   type_tcexp ns db st ((x,new,t1)::env) e2 t2 ⇒
      type_tcexp ns db st env (Let x e1 e2) t2

[~Letrec:]
   LIST_REL
    (λ(fn,body) (vars,scheme).
      type_tcexp ns (vars ++ db) (MAP (tshift $ LENGTH vars) st)
        (tshift_env (LENGTH vars) $
          REVERSE (ZIP (MAP FST fns,schemes)) ++ env)
        body scheme)
    fns schemes ∧
   EVERY (type_kind_scheme_ok (SND ns) db) schemes ∧ fns ≠ [] ∧
   type_tcexp ns db st (REVERSE (ZIP (MAP FST fns, schemes)) ++ env) e t ⇒
      type_tcexp ns db st env (Letrec fns e) t

[~NestedCase:]
  type_tcexp ns db st env e vt ∧
  EVERY (λ(p,e).
    ∃vts. type_cepat ns db p vt vts ∧
    type_tcexp ns db st
      (REVERSE (MAP (λ(v,t). (v,[],t)) vts) ++
          ((v,[],vt)::env))
      e t) ((p,e1)::pes) ∧
  exhaustive_cepat ns db vt (p INSERT (IMAGE FST $ set pes)) ∧
  ¬MEM v (FLAT (MAP (cepat_vars_l ∘ FST) ((p,e1)::pes))) ⇒
    type_tcexp ns db st env (NestedCase e v p e1 pes) t

[~Case:]
   type_tcexp ns db st env e vt ∧

   (* get the list of constructors and their arities *)
   get_constructors ns vt = SOME constructors ∧

   (* no catch-all case *)
   (usopt = NONE ⇒
      (* exhaustive pattern-match *)
        set (MAP FST css) = set (MAP FST constructors) ∧
      (* no duplicated patterns *)
        ALL_DISTINCT (MAP FST css)) ∧

   (* catch-all case *)
   (∀us_cn_ars us_e. usopt = SOME (us_cn_ars, us_e) ⇒
      (* exhaustive pattern-match *)
        set (MAP FST css) ∪ set (MAP FST us_cn_ars) = set (MAP FST constructors) ∧
      (* no duplicated patterns *)
        ALL_DISTINCT (MAP FST css ++ MAP FST us_cn_ars) ∧
      (* non-empty cases/underscore patterns *)
        css ≠ [] ∧ us_cn_ars ≠ [] ∧
      (* all underscore patterns are valid *)
        EVERY (λ(cn,ar).
          ALOOKUP constructors cn = SOME ar) us_cn_ars ∧
      (* continuation is well-typed *)
        type_tcexp ns db st ((v,[],vt)::env) us_e t) ∧

   (* For each case: *)
   EVERY (λ(cname,pvars,cexp).
      ∃ptys.
        destruct_type_cons ns db vt cname ptys ∧
        (* Pattern variables do not shadow case split and are distinct: *)
          ¬ MEM v pvars ∧ ALL_DISTINCT pvars ∧
        (* Continuation is well-typed: *)
          type_tcexp ns db st
            (REVERSE (ZIP (pvars, MAP ($, []) ptys)) ++
             (v,[],vt)::env)
            cexp t
      ) css ⇒
      type_tcexp ns db st env (Case e v css usopt) t

[~SafeProj:]
   type_tcexp ns db st env e t ∧
   destruct_type_cons ns db t cname tys ∧
   LENGTH tys = arity ∧ i < arity ∧ EL i tys = t ⇒
     type_tcexp ns db st env (SafeProj cname arity i e) t
End

Theorem texp_construct_dict_IMP_type_tcexp:
  acyclic_rec
    (λp. ∃s x. FLOOKUP ce (SND p) = SOME (s,x) ∧ MEM (FST p) s) ∧
  (* for all class environment, *)
  relate_ce_ie ce ie ∧
  relate_ce_clk ce clk ∧
  FRANGE ie_map = ie ⇒
  (∀lie db st env e e' pt.
    pred_type_elaborate_texp ns clk ie lie db st env e e' pt ⇒
    ∀lie_map d. 
      FRANGE lie_map = lie ∧
      pred_texp_construct_dict (set $ get_names_namespace ns)
        ie_map lie_map (IMAGE FST $ set env) pt e' (d:'a cexp) ⇒
    type_tcexp ns db st (translate_env env ++ lie_to_env ce lie ++ ie_to_env ce ie) d (translate_pred_type ce pt)) ∧
  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    ∀lie_map d.
      lie = FRANGE lie_map ∧
      texp_construct_dict (set $ get_names_namespace ns)
        ie_map lie_map (IMAGE FST $ set env) e' (d:'a cexp) ⇒
     type_tcexp ns db st (translate_env env ++ lie_to_env ce lie ++ ie_to_env ce ie) d t)
Proof
  strip_tac >>
  ho_match_mp_tac type_elaborate_texp_ind >>
QED

val _ = export_theory();
