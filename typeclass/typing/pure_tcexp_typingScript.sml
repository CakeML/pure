open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory relationTheory set_relationTheory pred_setTheory;
open typeclass_typesTheory pure_tcexpTheory typeclass_texpTheory
typeclass_kindCheckTheory pure_configTheory;
open monadsyntax;
open typeclass

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "option";

val _ = new_theory "pure_tcexp_typing";

Type tcexp_typedef[pp] = ``:Kind list # ((mlstring # type_kind_scheme list) list)``;
Type tcexp_typedefs[pp] = ``:tcexp_typedef list``;
Type tcexp_namespace[pp] = ``:exndef # tcexp_typedefs``;

Definition namespace_to_tcexp_namespace_def:
  namespace_to_tcexp_namespace (ns:exndef # typedefs) =
    ((FST ns,MAP (I ## MAP (I ## MAP ($, []))) (SND ns))):tcexp_namespace
End

Definition type_scheme_ok_def:
  type_scheme_ok (typedefs: tcexp_typedefs) ks
    ((varks,t):type_kind_scheme) =
  kind_ok typedefs (varks ++ ks) kindType t
End

Definition tcexp_namespace_ok_def:
  tcexp_namespace_ok (exndef : exndef, typedefs : tcexp_typedefs) ⇔
    (* No empty type definitions: *)
      EVERY (λ(ak,td). td ≠ []) typedefs ∧
    (* Unique, unreserved constructor names: *)
      ALL_DISTINCT
        (MAP implode (SET_TO_LIST (reserved_cns DELETE "Subscript")) ++
         MAP FST exndef ++ MAP FST (FLAT $ MAP SND typedefs)) ∧
    (* Every constructor type is closed wrt kinds and uses only defined
       types: *)
      EVERY (λ(ak,td).
        EVERY (λ(cn,argtys). EVERY (type_scheme_ok typedefs ak) argtys) td) typedefs ∧
    (* Every exception constructor type is closed and uses only defined types: *)
      EVERY (λ(cn,tys). EVERY (type_ok typedefs []) tys) exndef ∧
    (* Subscript is a valid exception *)
      MEM («Subscript»,[]) exndef
End

Definition tcexp_type_cons_def:
  tcexp_type_cons (typedefs:tcexp_typedefs) db (cname,carg_tys:type_kind_scheme list) (tyid,tyargs) ⇔
    ∃argks constructors schemes.
      (* There is some type definition: *)
        oEL tyid typedefs = SOME (argks, constructors) ∧
      (* Which declares the constructor: *)
        ALOOKUP constructors cname = SOME schemes ∧
      (* And we can specialise it appropriately: *)
        LIST_REL (kind_ok typedefs db) argks tyargs ∧
        LIST_REL (λ(ks,scheme) (ks',carg_t).
          ks = ks' ∧
          subst_db (LENGTH ks) tyargs scheme = carg_t
          ) schemes carg_tys
End

Definition tcexp_destruct_type_cons_def:
  tcexp_destruct_type_cons (edef:exndef,tdefs: tcexp_typedefs) db t cname carg_tys ⇔
  if t = Atom Exception
  then
    EVERY (\x. FST x = []) carg_tys ∧
    type_exception edef (cname,MAP SND carg_tys)
  else
  ∃tc targs.
    split_ty_head t = SOME (tc,targs) ∧
    case tc of
    | INL tyid => tcexp_type_cons tdefs db (cname,carg_tys) (tyid,targs)
    | INR (PrimT Bool) => MEM cname [«True»;«False»] ∧ carg_tys = []
    | INR (CompPrimT (Tuple n)) => cname = «» ∧ MAP ($, []) targs = carg_tys
    | _ => F
End

Definition get_constructors_def:
  get_constructors (edef:exndef,tdefs) t ⇔
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

Inductive tcexp_type_cepat:
[~Var:]
  tcexp_type_cepat ns db (cepatVar v) (tk:type_kind_scheme) [(v,tk)]

[~UScore:]
  tcexp_type_cepat ns db cepatUScore (tk:type_kind_scheme) []

[~Cons:]
  tcexp_destruct_type_cons ns db t c ts ∧
  LIST_REL3 (tcexp_type_cepat ns db) pats ts vtss ⇒
    tcexp_type_cepat ns db (cepatCos c pats) ([],t) (FLAT vtss)
End

Inductive tcexp_exhaustive_cepat:
[~Var:]
  cepatVar v ∈ pats ⇒
    tcexp_exhaustive_cepat ns db (tk:type_kind_scheme) pats

[~UScore:]
  cepatUScore ∈ pats ⇒
    tcexp_exhaustive_cepat ns db tk pats

[~Cons:]
  (∀c ts. tcexp_destruct_type_cons ns db t c ts ⇒
    ∃(pss:cepat list set).
      tcexp_exhaustive_cepatl ns db ts pss ∧ IMAGE (cepat c) pss ⊆ pats) ⇒
  tcexp_exhaustive_cepat ns db ([],t) pats

[~Nil:]
  [] ∈ pss ⇒
    tcexp_exhaustive_cepatl ns db [] pss

[~List:]
  tcexp_exhaustive_cepat ns db tk hs ∧ 
  tcexp_exhaustive_cepatl ns db ts tls ∧
  IMAGE (UNCURRY CONS) (hs × tls) ⊆ pss ⇒
    tcexp_exhaustive_cepatl ns db (tk::ts) pss
End

(* typing rules for tcexp (expressions after dictionary construction) *)
Inductive type_tcexp:
[~Var:]
  (ALOOKUP env x = SOME s ∧ specialises (SND ns) db s t ⇒
      type_tcexp (ns:tcexp_namespace) db st env (pure_tcexp$Var x) t)

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
   LIST_REL (type_tcexp (exndef,typedefs) db st env) es earg_ts ∧
   type_exception exndef (cname,earg_ts) ⇒
      type_tcexp ns db st env (Prim (Cons cname) es) (Atom Exception)

[~True:]
   type_tcexp ns db st env (Prim (Cons «True») []) (Atom $ PrimTy Bool)

[~False:]
   type_tcexp ns db st env (Prim (Cons «False») []) (Atom $ PrimTy Bool)

[~Cons:]
   LIST_REL (λe (ks,t).
      type_tcexp ns (ks ++ db)
        (MAP (tshift (LENGTH ks)) st)
        (tshift_env (LENGTH ks) env) e t)
      es (carg_ts: type_kind_scheme list) ∧
   EVERY (type_ok (SND ns) db) tyargs ∧
   tcexp_type_cons (SND ns) db (cname,carg_ts) (tyid,tyargs) ⇒
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
    ∃vts. tcexp_type_cepat ns db p ([],vt) vts ∧
    type_tcexp ns db st
      (REVERSE vts ++ ((v,[],vt)::env))
      e t) ((p,e1)::pes) ∧
  tcexp_exhaustive_cepat ns db ([],vt) (p INSERT (IMAGE FST $ set pes)) ∧
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
        tcexp_destruct_type_cons ns db vt cname ptys ∧
        (* Pattern variables do not shadow case split and are distinct: *)
          ¬ MEM v pvars ∧ ALL_DISTINCT pvars ∧
        (* Continuation is well-typed: *)
          type_tcexp ns db st
            (REVERSE (ZIP (pvars, ptys)) ++
             (v,[],vt)::env)
            cexp t
      ) css ⇒
      type_tcexp ns db st env (Case e v css usopt) t

[~SafeProj:]
   type_tcexp ns (ks ++ db) (MAP (tshift $ LENGTH ks) st)
    (tshift_env (LENGTH ks) env) e t' ∧
   tcexp_destruct_type_cons ns db t cname tys ∧
   LENGTH tys = arity ∧ i < arity ∧ EL i tys = (ks,t') ⇒
     type_tcexp ns db st env (SafeProj cname arity i e) t
End

