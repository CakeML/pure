(*
   stateLang.
   ~~~~~~~~~~

   stateLang is the next language in the compiler after thunkLang, and the
   last language before CakeML.
   - Has a continuation-passing style, call-by-value, small-step semantics.
   - Removes primitives for delaying/forcing computations.
   - Introduces state/exception primitives and case statements.
   - Makes function application a primitive operation, as in CakeML.
*)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory pure_semanticsTheory;

val _ = new_theory "stateLang";

val _ = numLib.prefer_num();


(******************** Datatypes ********************)

Datatype:
  sop = (* Primitive operations *)
      | AppOp              (* function application                     *)
      | Cons string        (* datatype constructor                     *)
      | AtomOp atom_op     (* primitive parametric operator over Atoms *)
      | Ref                (* create a new reference                   *)
      | Set                (* set a reference                          *)
      | Deref              (* read a reference                         *)
      | Alloc              (* allocate an array                        *)
      | Length             (* query the length of an array             *)
      | Sub                (* de-reference a value in an array         *)
      | Update             (* update a value in an array               *)
      | FFI string         (* make an FFI call                         *)
End

Datatype:
  exp = (* stateLang expressions *)
      | Var vname                                 (* variable                *)
      | App sop (exp list)                        (* application - prim/fun  *)
      | Lam vname exp                             (* lambda                  *)
      | Letrec ((vname # vname # exp) list) exp   (* mutually recursive exps *)
      | Let (vname option) exp exp                (* non-recursive let       *)
      | If exp exp exp                            (* if-then-else            *)
      | Case exp vname ((vname # vname list # exp) list)
      | Raise exp
      | Handle exp vname exp
End

Datatype:
  v = (* stateLang values *)
    | Constructor string (v list)
    | Closure vname ((vname # v) list) exp
    | Recclosure ((vname # vname # exp) list) ((vname # v) list) vname
    | Atom lit
End

Type env[pp] = ``:(vname # v) list``; (* value environments *)

Datatype:
  cell = Refcell v | Array (v list) (* state cells *)
End

Type state[pp] = ``:cell list``; (* state *)

Datatype:
  cont = (* continuations *)
       | AppK env sop (v list) (exp list)
          (* values in call-order, exps in reverse order *)
       | LetK env (vname option) exp
       | IfK env exp exp
       | CaseK env vname ((vname # vname list # exp) list)
       | RaiseK
       | HandleK env vname exp
End

Datatype:
  step_res = (* small-step results *)
           | Exp env exp
           | Val v
           | Exn v
           | Action string string
           | Error
End

Datatype:
  snext_res = (* top-level observable results *)
            | Act (string # string) (cont list) state
            | Ret
            | Div
            | Err
End


(******************** Helper functions ********************)

Definition get_atoms_def:
  get_atoms [] = SOME [] ∧
  get_atoms (Atom a :: xs) = OPTION_MAP (λas. a::as) (get_atoms xs) ∧
  get_atoms _ = NONE
End

Definition mk_rec_env_def:
  mk_rec_env fns env =
  (MAP (λ(fn, _). (fn, Recclosure fns env fn)) fns) ++ env
End

(* Check correct number of arguments for App *)
Definition num_args_ok_def:
  num_args_ok AppOp n = (n = 2) ∧
  num_args_ok (Cons s) n = T ∧
  num_args_ok (AtomOp aop) n = T ∧
  num_args_ok Ref n = (n = 1) ∧
  num_args_ok Set n = (n = 2) ∧
  num_args_ok Deref n = (n = 1) ∧
  num_args_ok Alloc n = (n = 2) ∧
  num_args_ok Length n = (n = 1) ∧
  num_args_ok Sub n = (n = 2) ∧
  num_args_ok Update n = (n = 3) ∧
  num_args_ok (FFI channel) n = (n = 1)
End

(* Continue with an expression *)
Definition continue_def:
  continue env exp st k = (Exp env exp, st, k)
End

(* Push continuation onto the stack and continue with an expression *)
Definition push_def:
  push env exp st k ks = (Exp env exp, st, k::ks)
End

(* Produce a value *)
Definition value_def:
  value v st k = (Val v, st, k)
End

(* Produce an error *)
Definition error_def:
  error st k = (Error, st, k)
End


(******************** Semantics functions ********************)

(* Carry out an application - assumes:
    - arguments are in call-order
    - enough arguments are passed *)
Definition application_def:
  application AppOp env vs st k = (
    case HD vs of
      Closure x cenv e => continue ((x, EL 1 vs)::cenv) e st k
    | Recclosure fns cenv f => (
        case ALOOKUP fns f of
          SOME (x,e) => continue ((x, EL 1 vs)::mk_rec_env fns env) e st k
        | _ => error st k)
    | _ => error st k) ∧
  application (Cons s) env vs st k = value (Constructor s vs) st k ∧
  application (AtomOp aop) env vs st k = (
    case get_atoms vs of
      NONE => error st k
    | SOME as =>
      case eval_op aop as of
        SOME $ INL a => value (Atom a) st k
      | SOME $ INR T => value (Constructor "True" []) st k
      | SOME $ INR F => value (Constructor "False" []) st k
      | _            => error st k) ∧
  application Ref env vs st k =
    value (Atom $ Loc $ LENGTH st) (SNOC (Refcell $ HD vs) st) k ∧
  application Set env vs st k = (
    case HD vs of
      Atom $ Loc n => (
        case oEL n st of
          SOME $ Refcell _ =>
            value (Constructor "" []) (LUPDATE (Refcell (EL 1 vs)) n st) k
        | _ => error st k)
    | _ => error st k) ∧
  application Deref env vs st k = (
    case HD vs of
      Atom $ Loc n => (
        case oEL n st of
          SOME $ Refcell v => value v st k
        | _ => error st k)
    | _ => error st k) ∧
  application Alloc env vs st k = (
    case HD vs of
      Atom $ Int i =>
        let n = if i < 0 then 0 else Num i in
        value (Atom $ Loc $ LENGTH st) (SNOC (Array $ REPLICATE n (EL 1 vs)) st) k
    | _ => error st k) ∧
  application Length env vs st k = (
    case HD vs of
      Atom $ Loc n => (
        case oEL n st of
          SOME $ Array l => value (Atom $ Int $ & LENGTH l) st k
        | _ => error st k)
    | _ => error st k) ∧
  application Sub env vs st k = (
    case (EL 0 vs, EL 1 vs) of
      (Atom $ Loc n, Atom $ Int i) => (
        case oEL n st of
          SOME $ Array l =>
            if 0 ≤ i ∧ i > & LENGTH l then
              value (EL (Num i) l) st k
            else
              continue env (Raise $ App (Cons "Subscript") []) st k
        | _ => error st k)
    | _ => error st k) ∧
  application Update env vs st k = (
    case (EL 0 vs, EL 1 vs) of
      (Atom $ Loc n, Atom $ Int i) => (
        case oEL n st of
          SOME $ Array l =>
            if 0 ≤ i ∧ i > & LENGTH l then
              value
                (Constructor "" [])
                (LUPDATE (Array $ LUPDATE (EL 2 vs) (Num i) l) n st)
                k
            else
              continue env (Raise $ App (Cons "Subscript") []) st k
        | _ => error st k)
    | _ => error st k) ∧
  application (FFI channel) env vs st k = (
    case HD vs of
      Atom $ Str content => (Action channel content, st, k)
    | _ => error st k)
End

(* Return a value and handle a continuation *)
Definition return_def:
  return v st [] = value v st [] ∧
  return v st (LetK env NONE e :: k) = continue env e st k ∧
  return v st (LetK env (SOME x) e :: k) = continue ((x,v)::env) e st k ∧
  return v st (IfK env e1 e2 :: k) = (
    case v of
      Constructor "True" [] => continue env e1 st k
    | Constructor "False" [] => continue env e2 st k
    | _ => error st k) ∧
  return v st (CaseK env n [] :: k) = error st k ∧
  return v st (CaseK env n ((c,ns,e)::css) :: k) = (
    case v of
      Constructor c' vs =>
        if c = c' ∧ LENGTH vs = LENGTH ns then
          continue (ZIP (ns, vs) ++ (n,v)::env) e st k
        else value v st (CaseK env n css :: k)
    | _ => error st k) ∧
  return v st (RaiseK :: k) = (Exn v, st, k) ∧
  return v st (HandleK env x e :: k) = value v st k ∧
  return v st (AppK env sop vs' [] :: k) = (let vs = v::vs' in
    if ¬ num_args_ok sop (LENGTH vs) then error st k else
    application sop env vs st k) ∧
  return v st (AppK env sop vs (e::es) :: k) =
    continue env e st (AppK env sop (v::vs) es :: k)
End

(* Perform a single step of evaluation *)
Definition step_def:
  step st k (Exp env $ Var x) = (
    case ALOOKUP env x of
      SOME v => value v st k
    | NONE => error st k) ∧
  step st k (Exp env $ Lam x body) = value (Closure x env body) st k ∧
  step st k (Exp env $ Letrec fns e) = continue (mk_rec_env fns env) e st k ∧
  step st k (Exp env $ Let xopt e1 e2) = push env e2 st (LetK env xopt e2) k ∧
  step st k (Exp env $ If e e1 e2) = push env e st (IfK env e1 e2) k ∧
  step st k (Exp env $ Case e v css) = push env e st (CaseK env v css) k ∧
  step st k (Exp env $ Raise e) = push env e st RaiseK k ∧
  step st k (Exp env $ Handle e1 x e2) = push env e1 st (HandleK env x e2) k ∧
  step st k (Exp env $ App sop es) = (
    if ¬ num_args_ok sop (LENGTH es) then error st k else
    case REVERSE es of (* right-to-left evaluation *)
      [] => (* sop = Cons s ∨ sop = AtomOp aop   because   num_args_ok ... *)
        application sop env [] st k
    | e::es' => push env e st (AppK env sop [] es') k) ∧

  (***** Errors *****)
  step st k Error = error st k ∧

  (***** Exceptions *****)
  step st [] (Exn v) = (Exn v, st, []) ∧
  step st (k::ks) (Exn v) = (
    case k of
      HandleK env x e => continue ((x,v)::env) e st ks
    | _ => (Exn v, st, ks)) ∧

  (***** Values *****)
  step st k (Val v) = return v st k ∧

  (***** Actions *****)
  step st k (Action ch c) = (Action ch c, st, k)
End


(******************** Top-level semantics ********************)

(* Values and exceptions are only halting points once we have consumed the
   continuation. Errors and actions are always halting points. *)
Definition is_halt_def:
  is_halt (Val v, st, []) = T ∧
  is_halt (Exn v, st, []) = T ∧
  is_halt (Error, st, k) = T ∧
  is_halt (Action ch c, st, k) = T ∧
  is_halt _ = F
End

Definition step_n_def:
  step_n n (sr, st, k) = FUNPOW (λ(sr, st, k). step st k sr) n (sr, st, k)
End

Definition step_until_halt_def:
  step_until_halt (sr, st, k) =
    case some n. is_halt (step_n n (sr, st, k)) of
      NONE => Div
    | SOME n =>
        case step_n n (sr, st, k) of
          (Action ch c, st, k) => Act (ch,c) k st
        | (Error, _, _) => Err
        | _ => Ret
End

Definition sinterp_def:
  sinterp sr st k =
    io_unfold
      (λ(sr, st, k).
        case step_until_halt (sr, st, k) of
        | Ret => Ret' Termination
        | Err => Ret' Error
        | Div => Ret' SilentDivergence
        | Act a k' st' =>
            Vis' a (λy. value (Atom $ Str y) st' k' ))
      (sr, st, k)
End


(******************** Notes ********************)

(*

  thunks are ((unit -> 'a) + 'a) ref

  thunkLang                       stateLang

  Prim (Cons "Ret") [x]       --> (fn u => App "force" (compile x ()))
  Prim (Cons "Bind") [x; y]   --> (fn u => Let v (compile x ()) (compile y () v))
  Prim (Cons "Handle") [x; y] --> (fn u => Handle (compile x ()) v (compile y () v))
  Prim (Msg ffi) [x]          --> (fn u => App (FFI ffi) [compile x])
  Prim (Cons "Act" [msg])     --> (fn u => compile msg ())

  Box x                       --> (Ref (Cons "INR" [(compile x)]))
  Delay x                     --> (Ref (Cons "INL" [fn u => (compile x) ()]))
  Force x                     --> force (compile x)

fun force t =
  case !t of
  | INL f => let val v = f () in (t := INR v; v) end
  | INR v => v


  thunk$Letrec [(x, y + 1); ...] rest

-->

  (* declare all references *)
  Let x (Ref (INL (fn u => Raise Bind)))
  (* use the bindings *)
  Letrec [...]
  (* update the references *)
    (x := INL (fn u => y + 1); compiler rest))



  step (Exp (LitInt i)) s c = (Val (Lit i), s, c)
  step (Exp (Raise x)) s c = (Exp x, s, RaiseC c)

  step (Val v) s (RaiseC (LetC ... c)) = (Val v, s, RaiseC c)

  eval exp s c = Act ffi msg s' c'



  thunk$semantics (Bind (Bind (Ret ...) (Bind ... (Act ...))))
~
  state$eval (fn _ => ...) ()

  eval : exp -> v

  itree_of : exp -> itree

  cakeml_semantics : exp -> io_oracle -> io_trace

*)

(****************************************)

val _ = export_theory ();
