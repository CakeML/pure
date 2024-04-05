open HolKernel Parse boolLib bossLib BasicProvers;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory;
open typeclass_typesTheory typeclass_tcexpTheory
typeclass_kindCheckTheory pure_configTheory;
open typeclass_env_mapTheory;
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
(* TODO: should we change this to kind instead of just arities *)
(* somthing like f [] and f Int ??*)
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
  pred_type_kind_ok (cl_map:class_map) (typedefs: typedefs) ks pt ⇔
    let cldb s = do
      clinfo <- FLOOKUP cl_map s;
      clinfo.kind
    od in
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

Overload type_scheme_ok =
  ``λtdefs ks (varks,scheme). type_ok tdefs (ks ++ varks) scheme``

Overload pred_type_scheme_kind_ok =
  ``λclm tdefs ks (varks,scheme). pred_type_kind_ok clm tdefs (ks ++ varks) scheme``

(* Does a type specialise a type scheme in a given variable context/namespace? *)
Definition specialises_def:
  specialises tdefs db (vars, scheme) t =
    ∃subs.
      LENGTH subs = LENGTH vars ∧
      (∀n. n < LENGTH subs ⇒
        kind_ok tdefs db (EL n vars) (EL n subs)) ∧
      tsubst subs scheme = t
End

Theorem specialises_alt:
  specialises tdefs db (vars, scheme) t =
  ∃subs.
    LIST_REL (λk sub. kind_ok tdefs db k sub) vars subs ∧
    tsubst subs scheme = t
Proof
  rw[specialises_def,EQ_IMP_THM] >>
  irule_at (Pos last) EQ_REFL >>
  gvs[LIST_REL_EVERY_ZIP,EVERY_EL,EL_ZIP]
QED

Definition specialises_pred_def:
  specialises_pred tdefs db (vars, scheme) pt =
    ∃subs.
      LENGTH subs = LENGTH vars ∧
      (∀n. n < LENGTH subs ⇒
        kind_ok tdefs db (EL n vars) (EL n subs)) ∧
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

(* TODO: notes: probably don't need it as we have kind checking
(* Typing judgments for type constructors *)
Definition type_cons_def:
  type_cons (typedefs : typedefs) (cname,carg_tys) (tyid,tyargs) ⇔
    ∃argks constructors schemes.
      (* There is some type definition: *)
        oEL tyid typedefs = SOME (argks, constructors) ∧
      (* Which declares the constructor: *)
        ALOOKUP constructors cname = SOME schemes ∧
      (* And we can specialise it appropriately: *)
        LIST_REL (λk tyarg. kind_ok typedefs ) argks tyargs ∧
        MAP (tsubst tyargs) schemes = carg_tys
End
*)

(* Typing judgments for exceptions *)
Definition type_exception_def:
  type_exception (exndef : exndef) (cname, carg_tys) ⇔
      ALOOKUP exndef cname = SOME carg_tys
End

Definition get_PrimTys_def:
  get_PrimTys [] = SOME [] ∧
  get_PrimTys (PrimTy pty :: rest) = OPTION_MAP (CONS pty) (get_PrimTys rest) ∧
  get_PrimTys _ = NONE
End

(*
  The main typing relation.
  type_tcexp :
      exndef # typedefs           -- type definitions for exceptions and datatypes
   -> num                         -- number of deBruijn indices in scope
   -> type list                   -- store typing
   -> (string # type_scheme) list -- term variables associated to type schemes
   -> tcexp -> type                -- expression and its type
*)

Definition user_annot_ok_def:
  (user_annot_ok NONE pt ⇔ T) ∧
  (user_annot_ok (SOME ut) pt ⇔ ut = pt)
End

Datatype:
  inst_type = Instance [(mlstring # type)] (mlstring # type)
End

Inductive has_dict:
[~lie:]
  p ∈ lie ⇒ has_dict ie lie p
[~ie:]
  it ∈ ie ∧ specialises_inst it (Instance cstrs p) ∧
  (∀cstr. MEM cstr cstrs ⇒ has_dict ie lie cstr) ⇒ 
    entail_type ie lie p
End

Definition has_dicts_def:
  has_dicts ps = (∀p. MEM p ps ⇒ has_dict ie lie p)
End

Inductive type_tcexp:
[~Var:]
  (ALOOKUP env x = SOME s ∧
   specialises_pred (SND ns) db s pt ⇒
      pred_type_tcexp ns ce ie lie db st env (Var NONE x) pt)

[~VarSOME:]
  (ALOOKUP env x = SOME s ∧
   specialises_pred (SND ns) db s pt ∧
   pt = Pred ps ut ∧ has_dicts ie lie ps ⇒
      type_tcexp ns ce ie lie db st env (Var (SOME ut) x) pt)

(* instantiate pred_type_tcexp to type_tcexp *)
[~Rel:]
  pred_type_tcexp ns ce ie lie db st env e (Pred ps t) ∧
  has_dicts ie lie ps ⇒
    type_tcexp ns ce ie lie db st env e t

(* adding context to type_tcexp for pred_type_tcexp *)
[~Pred:]
  type_tcexp ns ce ie (lie ∪ set ps) db st env e t ∧
  pred_type_well_scoped (Pred ps t) ⇒
  pred_type_tcexp ns ce ie lie db st env e (Pred ps t)

[~Tuple:]
  (LIST_REL (type_tcexp ns ce ie lie db st env) es ts ∧
  (pt = cons_types (Atom $ CompPrimTy $ Tuple (LENGTH es)) ts) ∧
  user_annot_ok ut pt ⇒
     type_tcexp ns ce ie lie db st env ((Prim ut (Cons «») es):tcexp) pt)

[~App:]
  (type_tcexp ns ce ie lie db st env e (Functions arg_tys ret_ty) ∧
   LIST_REL (type_tcexp ns ce ie lie db st env) es arg_tys ∧ arg_tys ≠ [] ∧
   user_annot_ok ut ret_ty ⇒
      type_tcexp ns ce ie lie db st env (App ut e es) ret_ty)

[~Let:]
  (type_tcexp ns (db + new) (MAP (tshift new) st) (tshift_env new env) e1 t1 ∧
   type_tcexp ns db st ((x,new,t1)::env) e2 t2 ⇒
      type_tcexp ns ce ie lie db st env (Let ut (x,pt) e1 e2) t2)
End


[~Lam:]
  (EVERY (type_ok (SND ns) db) arg_tys ∧
   LENGTH arg_tys = LENGTH xs ∧ arg_tys ≠ [] ∧

   type_tcexp ns ce ie lie db st (REVERSE (ZIP (xs, MAP ($, []) arg_tys)) ++ env) e ret_ty
      ⇒ type_tcexp ns ce ie lie db st env (Lam ut xs e) (Functions arg_tys ret_ty))
End

[~Ret:]
  (type_tcexp ns db st env e t ∧ user_annot_ok ut pt ⇒
      type_tcexp ns db st env (Prim ut (Cons «Ret») [e]) (M t))
End

[~Bind:]
  (type_tcexp ns db st env e1 (M t1) ∧
   type_tcexp ns db st env e2 (Function t1 (M t2)) ⇒
      type_tcexp ns db st env (Prim (Cons «Bind») [e1;e2]) (M t2)) ∧

[~Raise:]
  (type_tcexp ns db st env e Exception ∧
   type_ok (SND ns) db t ⇒
      type_tcexp ns db st env (Prim (Cons «Raise») [e]) (M t)) ∧

[~Handle:]
  (type_tcexp ns db st env e1 (M t) ∧
   type_tcexp ns db st env e2 (Function Exception (M t)) ⇒
      type_tcexp ns db st env (Prim (Cons «Handle») [e1;e2]) (M t)) ∧

[~Act:]
  (type_tcexp ns db st env e (PrimTy Message) ⇒
      type_tcexp ns db st env (Prim (Cons «Act») [e]) (M $ PrimTy String)) ∧

[~Alloc:]
  (type_tcexp ns db st env e1 (PrimTy Integer) ∧
   type_tcexp ns db st env e2 t ⇒
      type_tcexp ns db st env (Prim (Cons «Alloc») [e1;e2]) (M $ Array t)) ∧

[~Length:]
  (type_tcexp ns db st env e (Array t) ⇒
      type_tcexp ns db st env (Prim (Cons «Length») [e]) (M $ PrimTy Integer)) ∧

[~Deref:]
  (type_tcexp ns db st env e1 (Array t) ∧
   type_tcexp ns db st env e2 (PrimTy Integer) ⇒
      type_tcexp ns db st env (Prim (Cons «Deref») [e1;e2]) (M t)) ∧

[~Update:]
  (type_tcexp ns db st env e1 (Array t) ∧
   type_tcexp ns db st env e2 (PrimTy Integer) ∧
   type_tcexp ns db st env e3 t ⇒
      type_tcexp ns db st env (Prim (Cons «Update») [e1;e2;e3]) (M Unit)) ∧

[~Exception:]
  (LIST_REL (type_tcexp (exndef,typedefs) db st env) es carg_ts ∧
   type_exception exndef (cname,carg_ts) ⇒
      type_tcexp (exndef,typedefs) db st env (Prim (Cons cname) es) Exception) ∧

[~True:]
  (type_tcexp ns db st env (Prim (Cons «True») []) (PrimTy Bool)) ∧

[~False:]
  (type_tcexp ns db st env (Prim (Cons «False») []) (PrimTy Bool)) ∧

[~Cons:]
  (LIST_REL (type_tcexp (exndef,typedefs) db st env) es carg_ts ∧
   EVERY (type_ok typedefs db) tyargs ∧
   type_cons typedefs (cname,carg_ts) (tyid,tyargs) ⇒
      type_tcexp (exndef,typedefs) db st env
        (Prim (Cons cname) es) (TypeCons tyid tyargs)) ∧

[~Loc:]
  (oEL n st = SOME t ⇒
      type_tcexp ns db st env (Prim (AtomOp $ Lit (Loc n)) []) (Array t)) ∧

[~AtomOp:]
  (LIST_REL (type_tcexp ns db st env) es ts ∧
   get_PrimTys ts = SOME pts ∧
   type_atom_op aop pts pt ⇒
      type_tcexp ns db st env (Prim (AtomOp aop) es) (PrimTy pt)) ∧

[~Seq:]
  (type_tcexp ns db st env e1 t1 ∧ type_tcexp ns db st env e2 t2 ⇒
      type_tcexp ns db st env (Prim Seq [e1; e2]) t2) ∧

[~App:]
  (type_tcexp ns db st env e (Functions arg_tys ret_ty) ∧
   LIST_REL (type_tcexp ns db st env) es arg_tys ∧ arg_tys ≠ [] ⇒
      type_tcexp ns db st env (App e es) ret_ty) ∧

[~Lam:]
  (EVERY (type_ok (SND ns) db) arg_tys ∧
   LENGTH arg_tys = LENGTH xs ∧ arg_tys ≠ [] ∧
   type_tcexp ns db st (REVERSE (ZIP (xs, MAP ($, 0) arg_tys)) ++ env) e ret_ty
      ⇒ type_tcexp ns db st env (Lam xs e) (Functions arg_tys ret_ty)) ∧

[~Let:]
  (type_tcexp ns (db + new) (MAP (tshift new) st) (tshift_env new env) e1 t1 ∧
   type_tcexp ns db st ((x,new,t1)::env) e2 t2 ⇒
      type_tcexp ns db st env (Let x e1 e2) t2) ∧

[~Letrec:]
  (LIST_REL
    (λ(fn,body) (vars,scheme).
      type_tcexp ns (db + vars) (MAP (tshift vars) st)
        (tshift_env vars $ REVERSE (ZIP (MAP FST fns,schemes)) ++ env)
        body scheme)
    fns schemes ∧
   EVERY (type_scheme_ok (SND ns) db) schemes ∧ fns ≠ [] ∧
   type_tcexp ns db st (REVERSE (ZIP (MAP FST fns, schemes)) ++ env) e t ⇒
      type_tcexp ns db st env (Letrec fns e) t) ∧

[~BoolCase:]
  (type_tcexp ns db st env e (PrimTy Bool) ∧
   LENGTH css = 2 ∧ set (MAP FST css) = {«True»;«False»} ∧ eopt = NONE ∧
   EVERY (λ(cn,pvars,cexp). pvars = [] ∧
    type_tcexp ns db st ((v,0,PrimTy Bool)::env) cexp t) css ⇒
      type_tcexp ns db st env (Case e v css eopt) t) ∧

[~TupleCase:]
  (type_tcexp ns db st env e (Tuple tyargs) ∧
   css = [(«»,pvars,cexp)] ∧ ¬ MEM v pvars ∧ ALL_DISTINCT pvars ∧
   LENGTH pvars = LENGTH tyargs ∧ eopt = NONE ∧
   type_tcexp ns db st
      (REVERSE (ZIP (pvars, MAP ($, 0) tyargs)) ++ (v,0,Tuple tyargs)::env)
        cexp t ⇒
      type_tcexp ns db st env (Case e v css eopt) t) ∧

[~ExceptionCase:]
  (type_tcexp (exndef,typedefs) db st env e Exception ∧

   (* Pattern match is exhaustive: *)
   set (MAP FST exndef) = set (MAP FST css) ∧ eopt = NONE ∧

   (* forbid duplicated patterns *)
   LENGTH exndef = LENGTH css ∧

   EVERY (λ(cname,pvars,cexp). (* For each case: *)
      ∃tys.
        ALOOKUP exndef cname = SOME tys ∧
        (* Pattern variables do not shadow case split and are distinct: *)
          ¬ MEM v pvars ∧ ALL_DISTINCT pvars ∧
        (* Constructor arities match *)
          LENGTH tys = LENGTH pvars ∧
        (* Continuation is well-typed: *)
          type_tcexp (exndef,typedefs) db st
            (REVERSE (ZIP (pvars, MAP ($, 0) tys)) ++ (v,0,Exception)::env) cexp t
      ) css ⇒
      type_tcexp (exndef,typedefs) db st env (Case e v css eopt) t) ∧

[~Case:]
  (type_tcexp (exndef,typedefs) db st env e (TypeCons tyid tyargs) ∧

   (* The type exists with correct arity: *)
   oEL tyid typedefs = SOME (arity, constructors) ∧ LENGTH tyargs = arity ∧

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
        EVERY (λ(cn,ar). ∃schemes.
          ALOOKUP constructors cn = SOME schemes ∧ ar = LENGTH schemes) us_cn_ars ∧
      (* continuation is well-typed *)
        type_tcexp (exndef, typedefs) db st ((v,0,TypeCons tyid tyargs)::env) us_e t) ∧

   (* For each case: *)
   EVERY (λ(cname,pvars,cexp).
      ∃schemes ptys.
        ALOOKUP constructors cname = SOME schemes ∧
        (* Constructor arities match: *)
          LENGTH pvars = LENGTH schemes ∧
        (* Pattern variables do not shadow case split and are distinct: *)
          ¬ MEM v pvars ∧ ALL_DISTINCT pvars ∧
        (* Constructor argument types match: *)
          MAP (tsubst tyargs) schemes = ptys ∧
        (* Continuation is well-typed: *)
          type_tcexp (exndef,typedefs) db st
            (REVERSE (ZIP (pvars, MAP ($, 0) ptys)) ++
             (v,0,TypeCons tyid tyargs)::env)
            cexp t
      ) css ⇒
      type_tcexp (exndef,typedefs) db st env (Case e v css usopt) t) ∧

[~TupleSafeProj:]
  (type_tcexp ns db st env e (Tuple tyargs) ∧
   LENGTH tyargs = arity ∧ oEL i tyargs = SOME t ⇒
    type_tcexp ns db st env (SafeProj «» arity i e) t) ∧

[~ExceptionSafeProj:]
  (type_tcexp (exndef,typedefs) db st env e Exception ∧
   ALOOKUP exndef cname = SOME tys ∧
   LENGTH tys = arity ∧ oEL i tys = SOME t ⇒
    type_tcexp (exndef,typedefs) db st env (SafeProj cname arity i e) t) ∧

[~SafeProj:]
  (type_tcexp (exndef,typedefs) db st env e (TypeCons tyid tyargs) ∧
   (* The type exists with correct arity: *)
      oEL tyid typedefs = SOME (tyarity, constructors) ∧ LENGTH tyargs = tyarity ∧
   (* The constructor exists with correct arity: *)
      ALOOKUP constructors cname = SOME tys ∧ LENGTH tys = arity ∧
   (* We can project the constructor argument at the right type: *)
      oEL i tys = SOME scheme ∧ tsubst tyargs scheme = t ⇒
    type_tcexp (exndef,typedefs) db st env (SafeProj cname arity i e) t)
End
*)
(********************)

val _ = export_theory();
