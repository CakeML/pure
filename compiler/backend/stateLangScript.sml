(*
   stateLang.
   ~~~~~~~~~~

   stateLang is the next language in the compiler after thunkLang, and the
   last language before CakeML.
   - Has a continuation-passing style, call-by-value semantics.
   - Removes explicit syntax for delaying/forcing computations
   - Introduces explicit state and case statements
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory pure_semanticsTheory;

val _ = new_theory "stateLang";

val _ = numLib.prefer_num();

Datatype:
  sop = (* Primitive operations *)
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
  exp = Var vname                                 (* variable                *)
      | Prim sop (exp list)                       (* primitive operations    *)
      | App exp exp                               (* function application    *)
      | Lam vname exp                             (* lambda                  *)
      | Letrec ((vname # vname # exp) list) exp   (* mutually recursive exps *)
      | Let (vname option) exp exp                (* non-recursive let       *)
      | If exp exp exp                            (* if-then-else            *)
      | Case exp vname ((vname # vname list # exp) list)
      | Raise exp
      | Handle exp vname exp
End

Overload "Cons" = ``λs es. Prim (Cons s) es``

Datatype:
  v = Constructor string (v list)
    | Closure vname ((vname # v) list) exp
    | Recclosure ((vname # vname # exp) list) ((vname # v) list) vname
    | Atom lit
End

Type env[pp] = ``:(vname # v) list``;

Datatype:
  cell = Refcell v | Array (v list)
End

Type state[pp] = ``:cell list``;

Datatype:
  cont = AppK env exp
       | SeqK env exp
       | ClosureK env vname exp
       | IfK env exp exp
       | CaseK env vname ((vname # vname list # exp) list)
       | HandleK env vname exp
       | PrimK env sop (v list) (exp list)
End

Datatype:
  step_res = Exp (env # exp) | Val v | Error
End

Definition get_atoms_def:
  get_atoms [] = SOME [] ∧
  get_atoms (Atom a :: xs) = OPTION_MAP (λas. a::as) (get_atoms xs) ∧
  get_atoms _ = NONE
End

Definition mk_recclosure_def:
  mk_recclosure fns env =
  (MAP (λ(fn, _). (fn, Recclosure fns env fn)) fns) ++ env
End

Definition step_def:
  step st k (Exp (env, Var x)) = (
    case ALOOKUP env x of
      SOME v => (Val v, st, k)
    | NONE => (Error, st, k)) ∧
  step st k (Exp (env, App e1 e2)) = (Exp (env, e1), st, AppK env e2 :: k) ∧
  step st k (Exp (env, Lam x body)) = (Val $ Closure x env body, st, k) ∧
  step st k (Exp (env, Letrec fns e)) = (Exp (mk_recclosure fns env, e), st, k) ∧
  step st k (Exp (env, Let NONE e1 e2)) = (Exp (env, e2), st, SeqK env e2 :: k) ∧
  step st k (Exp (env, Let (SOME x) e1 e2)) =
    (Exp (env, e1), st, ClosureK env x e2 :: k) ∧
  step st k (Exp (env, If e e1 e2)) = (Exp (env, e), st, IfK env e1 e2 :: k) ∧
  step st k (Exp (env, Case e v css)) = (Exp (env, e), st, CaseK env v css :: k) ∧
  step st k (Exp (env, Raise e)) = (
    case k of
      [] => ARB (* TODO *)
    | HandleK henv x e2 :: k => (Exp (env, e), st, ClosureK henv x e2 :: k)
    | _ :: k => (Exp (env, Raise e), st, k)) ∧
  step st k (Exp (env, Handle e1 x e2)) = (Exp (env, e1), st, (HandleK env x e2 :: k)) ∧
  step st k (Exp (env, Prim sop es)) = (case sop of
    | Cons s => (
        case es of
          [] => (Val (Constructor s []), st, k)
        | e::es => (Exp (env, e), st, PrimK env (Cons s) [] es :: k))
    | AtomOp aop => (
        case es of
          [] => (
            case eval_op aop [] of
              SOME (INL v) => (Val (Atom v), st, k)
            | SOME (INR b) =>
                (Val (Constructor (if b then "True" else "False") []), st, k)
            | _ => (Error, st, k))
        | _ => (Exp (env, HD es), st, PrimK env sop [] (TL es) :: k))
    | Ref =>
        if LENGTH es ≠ 1 then (Error, st, k) else
        (Exp (env, HD es), st, PrimK env sop [] (TL es) :: k)
    | Set =>
        if LENGTH es ≠ 2 then (Error, st, k) else
        (Exp (env, HD es), st, PrimK env sop [] (TL es) :: k)
    | Deref =>
        if LENGTH es ≠ 1 then (Error, st, k) else
        (Exp (env, HD es), st, PrimK env sop [] (TL es) :: k)
    | Alloc =>
        if LENGTH es ≠ 2 then (Error, st, k) else
        (Exp (env, HD es), st, PrimK env sop [] (TL es) :: k)
    | Length =>
        if LENGTH es ≠ 1 then (Error, st, k) else
        (Exp (env, HD es), st, PrimK env sop [] (TL es) :: k)
    | Sub =>
        if LENGTH es ≠ 2 then (Error, st, k) else
        (Exp (env, HD es), st, PrimK env sop [] (TL es) :: k)
    | Update =>
        if LENGTH es ≠ 3 then (Error, st, k) else
        (Exp (env, HD es), st, PrimK env sop [] (TL es) :: k)
    | FFI msg =>
        if LENGTH es ≠ 1 then (Error, st, k) else
        (Exp (env, HD es), st, PrimK env sop [] (TL es) :: k)
    ) ∧

  step st k Error = (Error, st, k) ∧

  step st [] (Val v) = (Val v, st, []) ∧
  step st (AppK env e :: k) (Val v) = (
    case v of
      Closure x cenv body => (Exp (env, e), st, ClosureK cenv x body :: k)
    | _ => (Error, st, k)) ∧
  step st (SeqK env e :: k) (Val v) = (Exp (env, e), st, k) ∧
  step st (ClosureK cenv x body :: k) (Val v) = (Exp ((x,v)::cenv, body), st, k) ∧
  step st (IfK env e1 e2 :: k) (Val v) = (
    case v of
      Constructor "True" [] => (Exp (env, e1), st, k)
    | Constructor "False" [] => (Exp (env, e2), st, k)
    | _ => (Error, st, k)) ∧
  step st (CaseK env n [] :: k) (Val v) = (Error, st, k) ∧
  step st (CaseK env n ((c,ns,e)::css) :: k) (Val v) = (
    case v of
      Constructor c' vs =>
        if c = c' ∧ LENGTH vs = LENGTH ns then
          (Exp (ZIP (ns, vs) ++ (n,v)::env, e), st, k)
        else (Val v, st, (CaseK env n ((c,ns,e)::css) :: k))
    | _ => (Error, st, k)) ∧
  step st (HandleK env x e :: k) (Val v) = (Val v, st, k) ∧
  step st (PrimK env sop vs' [] :: k) (Val v) = (let vs = SNOC v vs' in
    case sop of
    | Cons s => (Val (Constructor s vs), st, k)
    | AtomOp aop => (
        case get_atoms vs of
          NONE => (Error, st, k)
        | SOME as => (
          case eval_op aop as of
            SOME (INL v) => (Val (Atom v), st, k)
          | SOME (INR b) =>
              (Val (Constructor (if b then "True" else "False") []), st, k)
          | _ => (Error, st, k)))
    | Ref =>
        if LENGTH vs ≠ 1 then (Error, st, k) else
        (Val (Atom $ Loc $ LENGTH st), st ++ [Refcell $ HD vs], k)
    | Set =>
        if LENGTH vs ≠ 2 then (Error, st, k) else (
        case HD vs of
          Atom (Loc n) => (
            case oEL n st of
              SOME (Refcell _) =>
                (Val (Constructor "" []), LUPDATE (Refcell (EL 1 vs)) n st, k)
            | _ => (Error, st, k))
        | _ => (Error, st, k))
    | Deref =>
        if LENGTH vs ≠ 1 then (Error, st, k) else (
        case HD vs of
          Atom (Loc n) => (
            case oEL n st of
              SOME (Refcell v) => (Val v, st, k)
            | _ => (Error, st, k))
        | _ => (Error, st, k))
    | Alloc =>
        if LENGTH vs ≠ 2 then (Error, st, k) else (
        case HD vs of
          Atom (Int i) =>
            let n = if i < 0 then 0 else Num i in
            (Val (Atom $ Loc $ LENGTH st), st ++ [Array $ REPLICATE n (EL 1 vs)], k))
    | Length =>
        if LENGTH vs ≠ 1 then (Error, st, k) else (
        case HD vs of
          Atom (Loc n) => (
            case oEL n st of
              SOME (Array l) => (Val (Atom $ Int $ & LENGTH l), st, k)
            | _ => (Error, st, k))
        | _ => (Error, st, k))
    | Sub =>
        if LENGTH vs ≠ 2 then (Error, st, k) else (
        case (EL 0 vs, EL 1 vs) of
          (Atom (Loc n), Atom (Int i)) => (
            case oEL n st of
              SOME (Array l) =>
                if 0 ≤ i ∧ i > & LENGTH l then
                  (Val $ EL (Num i) l, st, k)
                else
                  (Exp (env, Raise (Prim (Cons "Subscript") [])), st, k)
            | _ => (Error, st, k))
        | _ => (Error, st, k))
    | Update =>
        if LENGTH vs ≠ 3 then (Error, st, k) else (
        case (EL 0 vs, EL 1 vs) of
          (Atom (Loc n), Atom (Int i)) => (
            case oEL n st of
              SOME (Array l) =>
                if 0 ≤ i ∧ i > & LENGTH l then
                  (Val $ Constructor "" [],
                   LUPDATE (Array $ LUPDATE (EL 2 vs) (Num i) l) n st, k)
                else
                  (Exp (env, Raise (Prim (Cons "Subscript") [])), st, k)
            | _ => (Error, st, k))
        | _ => (Error, st, k))
    | FFI msg =>
        if LENGTH vs ≠ 1 then (Error, st, k) else (
          ARB (* TODO *)
        )
      ) ∧
  step st (PrimK env sop vs (e::es) :: k) (Val v) =
    (Exp (env, e), st, (PrimK env sop (SNOC v vs) es :: k))
End

(********** Notes **********)

(*

  thunks are ((unit -> 'a) + 'a) ref

  thunkLang                       stateLang

  Prim (Cons "Ret") [x]       --> (fn u => App "force" (compile x ()))
  Prim (Cons "Bind") [x; y]   --> (fn u => Let v (compile x ()) (compile y () v))
  Prim (Cons "Handle") [x; y] --> (fn u => Handle (compile x ()) v (compile y () v))
  Prim (Msg ffi) [x]          --> (fn u => Prim (FFI ffi) [compile x])
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

val _ = export_theory ();
