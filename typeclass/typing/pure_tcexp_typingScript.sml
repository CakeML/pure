open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory miscTheory;
open listTheory alistTheory relationTheory set_relationTheory pred_setTheory;
open typeclass_typesTheory typeclass_kindCheckTheory;
open pure_cexpTheory pure_configTheory;
open pure_tcexpTheory pure_tcexp_lemmasTheory;
open typeclass_texpTheory typeclass_typingTheory;
open monadsyntax;

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "option";

val _ = new_theory "pure_tcexp_typing";

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
        MAP
          (λ(ks,scheme).
            (ks, subst_db (LENGTH ks)
                 (MAP (tshift $ LENGTH ks) tyargs) scheme))
          schemes
        = carg_tys
End

Theorem tcexp_type_cons_carg_tys_unique:
  tcexp_type_cons tdefs db (cname,carg_tys) (tyid,tyargs) ∧
  tcexp_type_cons tdefs db (cname,carg_tys') (tyid,tyargs) ⇒
  carg_tys = carg_tys'
Proof
  rw[tcexp_type_cons_def] >>
  gvs[]
QED

Definition tcexp_destruct_type_cons_def:
  tcexp_destruct_type_cons (edef:exndef,tdefs: tcexp_typedefs) db t cname carg_tys ⇔
  if t = Atom Exception
  then
    ∃ts. type_exception edef (cname,ts) ∧
      carg_tys = MAP ($, []) ts
  else
  ∃tc targs.
    split_ty_cons t = SOME (tc,targs) ∧
    case tc of
    | INL tyid => tcexp_type_cons tdefs db (cname,carg_tys) (tyid,targs)
    | INR (PrimT Bool) =>
        MEM cname [«True»;«False»] ∧
          carg_tys = [] ∧ targs = []
    | INR (CompPrimT (Tuple n)) => cname = «» ∧
        carg_tys = MAP ($, []) targs ∧ LENGTH carg_tys = n
    | _ => F
End

Theorem tcexp_destruct_type_cons_unique:
  tcexp_destruct_type_cons ns db t cname carg_tys ∧
  tcexp_destruct_type_cons ns db t cname carg_tys' ⇒
  carg_tys = carg_tys'
Proof
  Cases_on `ns` >>
  rw[tcexp_destruct_type_cons_def] >>
  gvs[type_exception_def] >>
  every_case_tac >> gvs[] >>
  metis_tac[tcexp_type_cons_carg_tys_unique]
QED

Definition tcexp_get_cases_def:
  tcexp_get_cases (ns:exndef # tcexp_typedefs) t ⇔
  if t = Atom Exception
  then SOME $ MAP (I ## MAP ($, [])) (FST ns)
  else do
    (tc,targs) <- split_ty_cons t;
    case tc of
    | INL tyid => do
        (argks,constructors) <- LLOOKUP (SND ns) tyid;
        assert (LENGTH targs = LENGTH argks);
        SOME $
          MAP
            (I ##
            MAP
              (λ(ks,scheme).
                (ks,
                subst_db (LENGTH ks)
                  (MAP (tshift $ LENGTH ks) targs) scheme)))
            constructors
      od
    | INR (PrimT Bool) => do
        assert (LENGTH targs = 0);
        SOME ([«True»,[]; «False»,[]])
      od
    | INR (CompPrimT (Tuple n)) => do
        assert (LENGTH targs = n);
        SOME [«»,MAP ($, []) targs]
      od
    | _ => NONE
  od
End

Theorem tcexp_get_cases_ALL_DISTINCT:
  tcexp_namespace_ok ns ∧
  tcexp_get_cases ns t = SOME cons ⇒
  ALL_DISTINCT (MAP FST cons)
Proof
  Cases_on `ns` >>
  rw[tcexp_get_cases_def,EXISTS_PROD,tcexp_namespace_ok_def,
    ALL_DISTINCT_APPEND] >>
  every_case_tac >>
  gvs[MAP_MAP_o,ALL_DISTINCT_FLAT,MAP_FLAT,EXISTS_PROD] >>
  gvs[LLOOKUP_THM,MEM_MAP,PULL_EXISTS] >>
  drule_then assume_tac $ SRULE[PULL_EXISTS] $ iffRL MEM_EL >>
  qpat_x_assum `∀y. MEM y _ ⇒ ALL_DISTINCT _` drule >>
  simp[]
QED

Theorem tcexp_destruct_type_cons_tcexp_get_cases_SOME:
  tcexp_destruct_type_cons ns db t cname carg_tys ⇒
  ∃cts. tcexp_get_cases ns t = SOME cts
Proof
  Cases_on `ns` >>
  rw[tcexp_destruct_type_cons_def,
    tcexp_get_cases_def] >>
  simp[] >>
  every_case_tac >>
  gvs[tcexp_type_cons_def,LIST_REL_EL_EQN]
QED

Theorem tcexp_destruct_type_cons_MEM_tcexp_get_cases:
  tcexp_destruct_type_cons ns db t cname carg_tys ∧
  tcexp_get_cases ns t = SOME cts ⇒
  MEM (cname,carg_tys) cts
Proof
  Cases_on `ns` >>
  rw[tcexp_destruct_type_cons_def,
    tcexp_get_cases_def] >>
  gvs[type_exception_def,MEM_MAP,EXISTS_PROD,ALOOKUP_MEM] >>
  every_case_tac >>
  gvs[tcexp_type_cons_def,MEM_MAP,EXISTS_PROD,ALOOKUP_MEM] >>
  metis_tac[ALOOKUP_MEM]
QED

Inductive tcexp_type_cepat:
[~Var:]
  specialises (SND ns) db tk t ⇒
  tcexp_type_cepat ns db (cepatVar v) (tk:type_kind_scheme) [(v,t)]

[~UScore:]
  tcexp_type_cepat ns db cepatUScore (tk:type_kind_scheme) []

[~Cons:]
  tcexp_destruct_type_cons ns db t c ts ∧
  LIST_REL3 (tcexp_type_cepat ns db) pats ts vtss ⇒
    tcexp_type_cepat ns db (cepatCons c pats) ([],t) (FLAT vtss)
End

Inductive tcexp_exhaustive_cepat:
[~Var:]
  cepatVar v ∈ pats ⇒
    tcexp_exhaustive_cepat ns (tk:type_kind_scheme) pats

[~UScore:]
  cepatUScore ∈ pats ⇒
    tcexp_exhaustive_cepat ns tk pats

[~Cons:]
  tcexp_get_cases ns t = SOME cts ∧
  (∀c ts. MEM (c,ts) cts ⇒
    ∃(pss:cepat list set).
      tcexp_exhaustive_cepatl ns ts pss ∧ IMAGE (cepatCons c) pss ⊆ pats) ⇒
  tcexp_exhaustive_cepat ns ([],t) pats

[~Nil:]
  [] ∈ pss ⇒
    tcexp_exhaustive_cepatl ns [] pss

[~List:]
  tcexp_exhaustive_cepat ns tk hs ∧
  tcexp_exhaustive_cepatl ns ts tls ∧
  IMAGE (UNCURRY CONS) (hs × tls) ⊆ pss ⇒
    tcexp_exhaustive_cepatl ns (tk::ts) pss
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
   LIST_REL (type_tcexp ns db st env) es earg_ts ∧
   type_exception (FST ns) (cname,earg_ts) ⇒
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
  type_tcexp ns (new ++ db) (MAP (tshift (LENGTH new)) st)
    (tshift_env (LENGTH new) env) e1 t1 ∧
  type_tcexp ns db st env e2 t2 ⇒
      type_tcexp ns db st env (Prim Seq [e1; e2]) t2

[~App:]
  type_tcexp ns db st env e (Functions arg_tys ret_ty) ∧
  LIST_REL (type_tcexp ns db st env) es arg_tys ∧ arg_tys ≠ [] ⇒
      type_tcexp ns db st env (App e es) ret_ty

[~Lam:]
  EVERY (type_ok (SND ns) db) arg_tys ∧
  LENGTH arg_tys = LENGTH xs ∧ arg_tys ≠ [] ∧
  type_tcexp ns db st (REVERSE (ZIP (xs, MAP ($, []) arg_tys)) ++ env) e ret_ty
      ⇒ type_tcexp ns db st env (Lam xs e) (Functions arg_tys ret_ty)

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
    ∃vts.
    tcexp_type_cepat ns db p ([],vt) vts ∧
    type_tcexp ns db st
      (REVERSE (MAP (λ(v,t). (v,[],t)) vts) ++ ((v,[],vt)::env))
      e t) ((p,e1)::pes) ∧
  tcexp_exhaustive_cepat ns ([],vt) (p INSERT (IMAGE FST $ set pes)) ∧
  ¬MEM v (FLAT (MAP (cepat_vars_l ∘ FST) ((p,e1)::pes))) ⇒
    type_tcexp ns db st env (NestedCase e v p e1 pes) t

[~Case:]
   (* Since we have at least one case for exception,
   * and at least one case for every datatype,
   * t must be type_ok,
   * we don't need to add the type_ok constraint to the premise *)
   type_tcexp ns db st env e vt ∧

   (* get the list of constructors and their arities *)
   tcexp_get_cases ns vt = SOME constructors ∧

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
          ∃ks. ALOOKUP constructors cn = SOME ks ∧
            ar = LENGTH ks) us_cn_ars ∧
      (* continuation is well-typed *)
        type_tcexp ns db st ((v,[],vt)::env) us_e t) ∧

   (* For each case: *)
   EVERY (λ(cname,pvars,cexp).
      ∃ptys ptys'.
        tcexp_destruct_type_cons ns db vt cname ptys ∧
        LIST_REL (specialises (SND ns) db) ptys ptys' ∧
        (* Constructor arities match: *)
        LENGTH pvars = LENGTH ptys' ∧
        (* Pattern variables do not shadow case split and are distinct: *)
          ¬ MEM v pvars ∧ ALL_DISTINCT pvars ∧
        (* Continuation is well-typed: *)
          type_tcexp ns db st
            (REVERSE (ZIP (pvars, MAP (λt. ([],t)) ptys')) ++
             (v,[],vt)::env)
            cexp t
      ) css ⇒
      type_tcexp ns db st env (Case e v css usopt) t

[~SafeProj:]
   type_tcexp ns db st env e t' ∧
   tcexp_destruct_type_cons ns db t' cname tys ∧
   LENGTH tys = arity ∧ i < arity ∧ EL i tys = tk ∧
   specialises (SND ns) db tk t ⇒
     type_tcexp ns db st env (SafeProj cname arity i e) t
End

val _ = export_theory();
