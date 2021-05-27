open HolKernel Parse boolLib bossLib BasicProvers;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory;
open pure_cexpTheory pure_configTheory;

val _ = new_theory "pure_typing";


(******************** Types ********************)

Datatype:
  prim_ty = Integer | String | Message | Bool
End

Datatype:
  type = TypeVar num
       | PrimTy prim_ty
       | Exception
       | TypeCons num (type list)
       | Tuple (type list)
       | Function (type list) type
       | Array type
       | M type
End

Overload Unit = ``Tuple []``;

Type type_scheme[pp] = ``:num # type``;

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
(* TODO make finite maps *)
Type typedef[pp] = ``:num # ((string # type list) list)``;
Type typedefs[pp] = ``:typedef list``;
Type exndef[pp] = ``:(string # type list) list``;


(********** Substitutions and shifts **********)

Definition subst_db_def:
  subst_db skip ts (TypeVar v) = (
    if skip ≤ v ∧ v < skip + LENGTH ts then
      EL (v - skip) ts
    else if skip ≤ v then
      TypeVar (v - LENGTH ts)
    else TypeVar v) ∧
  subst_db skip ts (PrimTy p) = PrimTy p ∧
  subst_db skip ts  Exception = Exception ∧
  subst_db skip ts (TypeCons n tcs) = TypeCons n (MAP (subst_db skip ts) tcs) ∧
  subst_db skip ts (Tuple tcs) = Tuple  (MAP (subst_db skip ts) tcs) ∧
  subst_db skip ts (Function tfs t) =
    Function (MAP (subst_db skip ts) tfs) (subst_db skip ts t) ∧
  subst_db skip ts (Array t) = Array (subst_db skip ts t) ∧
  subst_db skip ts (M t) = M (subst_db skip ts t)
Termination
  WF_REL_TAC `measure (type_size o SND o SND)` >> rw[fetch "-" "type_size_def"] >>
  rename1 `MEM _ ts` >> Induct_on `ts` >> rw[fetch "-" "type_size_def"] >> gvs[]
End

Definition shift_db_def:
  shift_db skip n (TypeVar v) = (
    if skip ≤ v then TypeVar (v + n) else TypeVar v) ∧
  shift_db skip n (PrimTy p) = PrimTy p ∧
  shift_db skip n  Exception = Exception ∧
  shift_db skip n (TypeCons tn tcs) = TypeCons tn (MAP (shift_db skip n) tcs) ∧
  shift_db skip n (Tuple tcs) = Tuple  (MAP (shift_db skip n) tcs) ∧
  shift_db skip n (Function tfs t) =
    Function (MAP (shift_db skip n) tfs) (shift_db skip n t) ∧
  shift_db skip n (Array t) = Array (shift_db skip n t) ∧
  shift_db skip n (M t) = M (shift_db skip n t)
Termination
  WF_REL_TAC `measure (type_size o SND o SND)` >> rw[fetch "-" "type_size_def"] >>
  rename1 `MEM _ ts` >> Induct_on `ts` >> rw[fetch "-" "type_size_def"] >> gvs[]
End

Overload subst_db_scheme =
  ``λn ts (vars,scheme).
      (vars, subst_db (n + vars) (MAP (shift_db 0 vars) ts) scheme)``;
Overload shift_db_scheme =
  ``λskip shift (vars,scheme).
      (vars, shift_db (skip + vars) shift scheme)``;
Overload tsubst = ``subst_db 0``;
Overload tshift = ``shift_db 0``;
Overload tshift_scheme = ``λn (vars,scheme). (vars, shift_db vars n scheme)``;
Overload tshift_env = ``λn. MAP (λ(x,scheme). (x, tshift_scheme n scheme))``;


(******************** Properties of types ********************)

Definition freetyvars_ok_def:
  freetyvars_ok n (TypeVar v) = (v < n) ∧
  freetyvars_ok n (PrimTy p) = T ∧
  freetyvars_ok n  Exception = T ∧
  freetyvars_ok n (TypeCons c ts) = EVERY (freetyvars_ok n) ts ∧
  freetyvars_ok n (Tuple ts) = EVERY (freetyvars_ok n) ts ∧
  freetyvars_ok n (Function ts t) =
    (EVERY (freetyvars_ok n) ts ∧ freetyvars_ok n t) ∧
  freetyvars_ok n (Array t) = freetyvars_ok n t ∧
  freetyvars_ok n (M t) = freetyvars_ok n t
Termination
  WF_REL_TAC `measure (type_size o SND)` >> rw[fetch "-" "type_size_def"] >>
  rename1 `MEM _ ts` >> Induct_on `ts` >> rw[fetch "-" "type_size_def"] >> gvs[]
End

Overload freetyvars_ok_scheme =
  ``λn (vars,scheme). freetyvars_ok (n + vars) scheme``;

(* Does a type only contain defined constructors, and non-nullary functions? *)
Definition type_wf_def:
  type_wf (typedefs : typedefs) (TypeVar n) = T ∧
  type_wf typedefs (PrimTy pty) = T ∧
  type_wf typedefs  Exception = T ∧
  type_wf typedefs (TypeCons id tyargs) = (
    EVERY (type_wf typedefs) tyargs ∧
    ∃arity constructors.
      (* Type definition exists: *)
        oEL id typedefs = SOME (arity, constructors) ∧
      (* And has correct arity: *)
        LENGTH tyargs = arity) ∧
  type_wf typedefs (Tuple ts) =
    EVERY (type_wf typedefs) ts ∧
  type_wf typedefs (Function ts t) = (
    type_wf typedefs t ∧
    ts ≠ [] ∧ EVERY (type_wf typedefs) ts) ∧
  type_wf typedefs (Array t) = type_wf typedefs t ∧
  type_wf typedefs (M t) = type_wf typedefs t
Termination
  WF_REL_TAC `measure (type_size o SND)` >> rw[fetch "-" "type_size_def"] >>
  rename1 `MEM _ ts` >> Induct_on `ts` >> rw[fetch "-" "type_size_def"] >> gvs[]
End

Definition type_ok_def:
  type_ok typedefs db t ⇔
    freetyvars_ok db t ∧
    type_wf typedefs t
End

Overload type_scheme_ok =
  ``λtdefs db (vars,scheme). type_ok tdefs (db + vars) scheme``

(* Does a type specialise a type scheme in a given variable context/namespace? *)
Definition specialises_def:
  specialises tdefs db (vars, scheme) t =
    ∃subs.
      EVERY (type_ok tdefs db) subs ∧
      LENGTH subs = vars ∧
      tsubst subs scheme = t
End

(* Our namespace is an exception definition and some datatype definitions *)
Definition namespace_ok_def:
  namespace_ok (exndef : exndef, typedefs : typedefs) ⇔
    (* No empty type definitions: *)
      EVERY (λ(ar,td). td ≠ []) typedefs ∧
    (* Unique, unreserved constructor names: *)
      ALL_DISTINCT (SET_TO_LIST reserved_cns ++
        MAP FST exndef ++ MAP FST (FLAT $ MAP SND typedefs)) ∧
    (* Every constructor type is closed wrt type arity and uses only defined types: *)
      EVERY (λ(ar,td).
        EVERY (λ(cn,argtys). EVERY (type_ok typedefs ar) argtys) td) typedefs ∧
    (* Every exception constructor type is closed and uses only defined types: *)
      EVERY (λ(cn,tys). EVERY (type_ok typedefs 0) tys) exndef
End


(******************** Typing judgements ********************)

(* Handle Locs separately *)
Inductive type_lit:
  type_lit (Int i) Integer ∧
  type_lit (Str s) String ∧
  type_lit (Msg s1 s2) Message
End

Inductive type_atom_op:
[~Lit:]
  (type_lit l t ⇒ type_atom_op (Lit l) [] t) ∧

[~Eq:]
  (t ≠ Bool ⇒ type_atom_op Eq [t;t] Bool) ∧

[~IntOps_Int:]
  (MEM op [Add; Sub; Mul; Div; Mod] ⇒
    type_atom_op op [Integer;Integer] Integer) ∧

[~IntOps_Bool:]
  (MEM op [Lt; Leq; Gt; Geq] ⇒
    type_atom_op op [Integer;Integer] Bool) ∧

[~Len:]
  (type_atom_op Len [String] Integer) ∧

[~Elem:]
  (type_atom_op Elem [String;Integer] Integer) ∧

[~Concat:]
  (EVERY (λt. t = String) ts ⇒
    type_atom_op Concat ts String) ∧

[~Implode:]
  (EVERY (λt. t = Integer) ts ⇒
    type_atom_op Implode ts String) ∧

[~Substring1:]
  (type_atom_op Substring [String;Integer] String) ∧

[~Substring2:]
  (type_atom_op Substring [String;Integer;Integer] String) ∧

[~StrOps_Bool:]
  (MEM op [StrLt; StrLeq; StrGt; StrGeq] ⇒
    type_atom_op op [String;String] Bool) ∧

[~Message:]
  (type_atom_op (Message s) [String] Message)
End

(* Typing judgments for type constructors *)
Definition type_cons_def:
  type_cons (typedefs : typedefs) (cname,carg_tys) (tyid,tyargs) ⇔
    ∃arity constructors schemes.
      (* There is some type definition: *)
        oEL tyid typedefs = SOME (arity, constructors) ∧
      (* Which declares the constructor: *)
        ALOOKUP constructors cname = SOME schemes ∧
      (* And we can specialise it appropriately: *)
        LENGTH tyargs = arity ∧
        MAP (tsubst tyargs) schemes = carg_tys
End

(* Typing judgments for exceptions *)
Definition type_exception_def:
  type_exception (exndef : exndef) (cname, carg_tys) ⇔
      ALOOKUP exndef cname = SOME carg_tys
End

Definition type_application_def:
  type_application [] rt [] = SOME rt ∧
  type_application (ft::fts) rt [] = SOME $ Function (ft::fts) rt ∧
  type_application [] (Function fts rt) (at::ats) =
    type_application fts rt (at::ats) ∧
  type_application (ft::fts) rt (at::ats) =
    (if ft ≠ at then NONE else type_application fts rt ats) ∧
  type_application _ _ _ = NONE
Termination
  WF_REL_TAC
    `inv_image ($< LEX $<) (λ(fts,rt,ats). (type_size rt, LENGTH fts))` >> rw[]
End

Definition get_PrimTys_def:
  get_PrimTys [] = SOME [] ∧
  get_PrimTys (PrimTy pty :: rest) = OPTION_MAP (CONS pty) (get_PrimTys rest) ∧
  get_PrimTys _ = NONE
End

(*
  The main typing relation.
  type_cexp :
      exndef # typedefs           -- type definitions for exceptions and datatypes
   -> num                         -- number of deBruijn indices in scope
   -> type list                   -- store typing TODO think about this more
   -> (string # type_scheme) list -- term variables associated to type schemes
   -> α cexp -> type                -- expression and its type
*)
Inductive type_cexp:
[~Var:]
  (ALOOKUP env x = SOME s ∧ specialises (SND ns) db s t ⇒
      type_cexp ns db st env (Var c x) t) ∧

[~Tuple:]
  (LIST_REL (type_cexp ns db st env) es ts ⇒
      type_cexp ns db st env (Prim c (Cons "") es) (Tuple ts)) ∧

[~Ret:]
  (type_cexp ns db st env e t ⇒
      type_cexp ns db st env (Prim c (Cons "Ret") [e]) (M t)) ∧

[~Bind:]
  (type_cexp ns db st env e1 (M t1) ∧
   type_cexp ns db st env e2 (Function [t1] (M t2)) ⇒
      type_cexp ns db st env (Prim c (Cons "Bind") [e1;e2]) (M t2)) ∧

[~Raise:]
  (type_cexp ns db st env e Exception ∧
   type_ok (SND ns) db t ⇒
      type_cexp ns db st env (Prim c (Cons "Raise") [e]) (M t)) ∧

[~Handle:]
  (type_cexp ns db st env e1 (M t) ∧
   type_cexp ns db st env e2 (Function [Exception] (M t)) ⇒
      type_cexp ns db st env (Prim c (Cons "Handle") [e1;e2]) (M t)) ∧

[~Act:]
  (type_cexp ns db st env e (PrimTy Message) ⇒
      type_cexp ns db st env (Prim c (Cons "Act") [e]) (M Unit)) ∧

[~Alloc:]
  (type_cexp ns db st env e1 (PrimTy Integer) ∧
   type_cexp ns db st env e2 t ⇒
      type_cexp ns db st env (Prim c (Cons "Alloc") [e1;e2]) (M $ Array t)) ∧

[~Length:]
  (type_cexp ns db st env e (Array t) ⇒
      type_cexp ns db st env (Prim c (Cons "Length") [e]) (M $ PrimTy Integer)) ∧

[~Deref:]
  (type_cexp ns db st env e1 (Array t) ∧
   type_cexp ns db st env e2 (PrimTy Integer) ⇒
      type_cexp ns db st env (Prim c (Cons "Deref") [e1;e2]) (M t)) ∧

[~Update:]
  (type_cexp ns db st env e1 (Array t) ∧
   type_cexp ns db st env e2 (PrimTy Integer) ∧
   type_cexp ns db st env e3 t ⇒
      type_cexp ns db st env (Prim c (Cons "Update") [e1;e2;e3]) (M Unit)) ∧

[~Exception:]
  (LIST_REL (type_cexp (exndef,typedefs) db st env) es carg_ts ∧
   type_exception exndef (cname,carg_ts) ⇒
      type_cexp (exndef,typedefs) db st env (Prim c (Cons cname) es) Exception) ∧

[~True:]
  (type_cexp ns db st env (Prim c (Cons "True") []) (PrimTy Bool)) ∧

[~False:]
  (type_cexp ns db st env (Prim c (Cons "False") []) (PrimTy Bool)) ∧

[~Subscript:]
  (type_cexp ns db st env (Prim c (Cons "Subscript") []) Exception) ∧

[~Cons:]
  (LIST_REL (type_cexp (exndef,typedefs) db st env) es carg_ts ∧
   EVERY (type_ok typedefs db) tyargs ∧
   type_cons typedefs (cname,carg_ts) (tyid,tyargs) ⇒
      type_cexp (exndef,typedefs) db st env
        (Prim c (Cons cname) es) (TypeCons tyid tyargs)) ∧

[~Loc:]
  (oEL n st = SOME t ⇒
      type_cexp ns db st env (Prim c (AtomOp $ Lit (Loc n)) []) (Array t)) ∧

[~AtomOp:]
  (LIST_REL (type_cexp ns db st env) es ts ∧
   get_PrimTys ts = SOME pts ∧
   type_atom_op aop pts pt ⇒
      type_cexp ns db st env (Prim c (AtomOp aop) es) (PrimTy pt)) ∧

[~Seq:]
  (type_cexp ns db st env e1 t1 ∧ type_cexp ns db st env e2 t2 ⇒
      type_cexp ns db st env (Prim c Seq [e1; e2]) t2) ∧

[~App:]
  (type_cexp ns db st env e (Function ts t) ∧
   LIST_REL (type_cexp ns db st env) es arg_tys ∧ arg_tys ≠ [] ∧
   type_application ts t arg_tys = SOME res_ty ⇒
      type_cexp ns db st env (App c e es) res_ty) ∧

[~Lam:]
  (EVERY (type_ok (SND ns) db) arg_tys ∧
   LENGTH arg_tys = LENGTH xs ∧ arg_tys ≠ [] ∧
   type_cexp ns db st (REVERSE (ZIP (xs, MAP ($, 0) arg_tys)) ++ env) e ret_ty
      ⇒ type_cexp ns db st env (Lam c xs e) (Function arg_tys ret_ty)) ∧

[~Let:]
  (* TODO CHECK - should not need value restriction for call-by-name semantics *)
  (* However this just desugars to normal application *)
  (type_cexp ns (db + new) (MAP (tshift new) st) (tshift_env new env) e1 t1 ∧
   type_cexp ns db st ((x,new,t1)::env) e2 t2 ⇒
      type_cexp ns db st env (Let c x e1 e2) t2) ∧

[~Letrec:]
  (LIST_REL
    (λ(fn,body) (vars,scheme).
      type_cexp ns (db + vars) (MAP (tshift vars) st)
        (tshift_env vars $ REVERSE (ZIP (MAP FST fns,schemes)) ++ env)
        body scheme)
    fns schemes ∧
   EVERY (type_scheme_ok (SND ns) db) schemes ∧ fns ≠ [] ∧
   type_cexp ns db st (REVERSE (ZIP (MAP FST fns, schemes)) ++ env) e t ⇒
      type_cexp ns db st env (Letrec c fns e) t) ∧

[~Case:]
  (type_cexp (exndef,typedefs) db st env e (TypeCons tyid tyargs) ∧
   (* The type exists with correct arity: *)
     oEL tyid typedefs = SOME (arity, constructors) ∧ LENGTH tyargs = arity ∧
   (* Pattern match is exhaustive: *)
      set (MAP FST constructors) = set (MAP FST css) ∧
      LENGTH constructors = LENGTH css ∧
      (* TODO this forbids duplicated patterns - perhaps overkill? *)
   EVERY (λ(cname,pvars,cexp). (* For each case: *)
      ∃schemes ptys.
        ALOOKUP constructors cname = SOME schemes ∧
        (* Type arities match (should hopefully be the case from typing e): *)
          LENGTH tyargs = arity ∧
        (* Constructor arities match: *)
          LENGTH pvars = LENGTH schemes ∧
        (* Constructor argument types match: *)
          MAP (tsubst tyargs) schemes = ptys ∧
        (* Continuation is well-typed: *)
          type_cexp (exndef,typedefs) db st
            (REVERSE (ZIP (pvars, MAP ($, 0) ptys)) ++ (v,0,TypeCons tyid tyargs)::env)
            cexp t
      ) css ⇒
      type_cexp (exndef,typedefs) db st env (Case c e v css) t)
End


(********************)

val _ = export_theory();
