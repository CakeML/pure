(*
   stateLang.
   ~~~~~~~~~~

   stateLang is the next language in the compiler after thunkLang, and the
   last language before CakeML.
   - Has a continuation-passing style, call-by-value, small-step semantics.
   - Removes primitives for delaying/forcing computations.
   - Introduces state/exception primitives.
   - Makes function application a primitive operation, as in CakeML.
*)
Theory stateLang
Ancestors
  string option sum pair list alist
  pure_exp arithmetic mlstring
  pure_semantics state_cexp
Libs
  BasicProvers dep_rewrite


val _ = numLib.prefer_num();


(******************** Datatypes ********************)

Datatype:
  thunk_mode = Evaluated | NotEvaluated
End

Datatype:
  sop = (* Primitive operations *)
      | AppOp              (* function application                     *)
      | Cons string        (* datatype constructor                     *)
      | AtomOp atom_op     (* primitive parametric operator over Atoms *)
      | Proj string num    (* projection                               *)
      | IsEq string num    (* check whether same data constructor      *)
      | Alloc              (* allocate an array                        *)
      | Length             (* query the length of an array             *)
      | Sub                (* de-reference a value in an array         *)
      | Update             (* update a value in an array               *)
      | AllocMutThunk thunk_mode (* allocate a mutable thunk           *)
      | UpdateMutThunk thunk_mode (* update an unevaluated thunk       *)
      | ForceMutThunk      (* force a mutable thunk                    *)
      | FFI string         (* make an FFI call                         *)
End

Type vname = “:string”

Datatype:
  exp = (* stateLang expressions *)
      | Var vname                           (* variable                *)
      | App sop (exp list)                  (* application - prim/fun  *)
      | Lam (vname option) exp              (* lambda                  *)
      | Letrec ((vname # exp) list) exp     (* mutually recursive exps *)
      | Let (vname option) exp exp          (* non-recursive let       *)
      | If exp exp exp                      (* if-then-else            *)
      | Case vname ((vname # vname list # exp) list)  (* pattern match *)
          ((((vname # num) list) # exp) option)    (* fallthrough case *)
      | Delay exp                           (* suspend in a Thunk      *)
      | Box exp                             (* wrap result in a Thunk  *)
      | Force exp                           (* evaluates a Thunk       *)
      | Raise exp                           (* raise an exception      *)
      | Handle exp vname exp                (* handle an exception     *)
      | HandleApp exp exp                   (* handle that takes fun   *)
End

Overload Lit = “λl. App (AtomOp (Lit l)) []”
Overload Unit = “App (Cons "") []”

Datatype:
  v = (* stateLang values *)
    | Constructor string (v list)
    | Closure (vname option) ((vname # v) list) exp
    | Recclosure ((vname # exp) list) ((vname # v) list) vname
    | Thunk (v + (vname # v) list # exp)
    | Atom lit
End

Type env[pp] = ``:(vname # v) list``; (* value environments *)

Datatype:
  store_v =
    Array (v list)
  | ThunkMem thunk_mode v
End

Definition store_same_type_def:
  store_same_type v1 v2 =
    case (v1, v2) of
      (Array _, Array _                     ) => T
    | (ThunkMem NotEvaluated _, ThunkMem _ _) => T
    | _ => F
End

Type state[pp] = ``:store_v list``; (* state *)

Datatype:
  cont = (* continuations *)
       | AppK env sop (v list) (exp list)
         (* values in call-order, exps in reverse order *)
       | LetK env (vname option) exp
       | IfK env exp exp
       | BoxK
       | ForceK1
       | ForceK2 (state option)
       | RaiseK
       | HandleK env vname exp
       | HandleAppK env exp
       | ForceMutK num
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
            | Act (string # string) (cont list) (state option)
            | Ret
            | Div
            | Err
End

(******************** Helper functions ********************)

Definition freevars_def[simp]:
  freevars (Var v) = {v} ∧
  freevars (App sop es) = BIGUNION (set (MAP freevars es)) ∧
  freevars (Lam NONE e) = freevars e ∧
  freevars (Lam (SOME x) e) = freevars e DELETE x ∧
  freevars (Letrec fns e) =
    (freevars e ∪ (BIGUNION $ set $ MAP (λ(f,e). freevars e) fns)) DIFF
    set (MAP FST fns) ∧
  freevars (Let NONE e1 e2) = freevars e1 ∪ freevars e2 ∧
  freevars (Let (SOME x) e1 e2) = freevars e1 ∪ (freevars e2 DELETE x) ∧
  freevars (If e e1 e2) = freevars e ∪ freevars e1 ∪ freevars e2 ∧
  freevars (Delay e) = freevars e ∧
  freevars (Box e) = freevars e ∧
  freevars (Force e) = freevars e ∧
  freevars (Case v css d) =
    ((case d of SOME (_,e) => freevars e | _ => {}) ∪ {v} ∪
     (BIGUNION (set (MAP (λ(s,vs,e). freevars e DIFF set vs) css)) DELETE v)) ∧
  freevars (Raise e) = freevars e ∧
  freevars (Handle e1 x e2) = freevars e1 ∪ (freevars e2 DELETE x) ∧
  freevars (HandleApp e1 e2) = freevars e1 ∪ freevars e2
Termination
  WF_REL_TAC `measure exp_size` >> rw[fetch "-" "exp_size_def"]
End

Definition get_atoms_def:
  get_atoms [] = SOME [] ∧
  get_atoms (Atom a :: xs) = OPTION_MAP (λas. a::as) (get_atoms xs) ∧
  get_atoms _ = NONE
End

Definition mk_rec_env_def[simp]:
  mk_rec_env funs env =
    MAP (λ(fn, _). (fn, Recclosure funs env fn)) funs ++ env
End

(* Check correct number of arguments for App *)
Definition num_args_ok_def[simp]:
  num_args_ok AppOp n = (n = 2) ∧
  num_args_ok (Cons s) n = T ∧
  num_args_ok (AtomOp aop) n = T ∧
  num_args_ok (Proj _ _) n = (n = 1) ∧
  num_args_ok (IsEq _ _) n = (n = 1) ∧
  num_args_ok Sub n = (n = 2) ∧
  num_args_ok Alloc n = (n = 2) ∧
  num_args_ok Length n = (n = 1) ∧
  num_args_ok Update n = (n = 3) ∧
  num_args_ok (AllocMutThunk _) n = (n = 1) ∧
  num_args_ok (UpdateMutThunk _) n = (n = 2) ∧
  num_args_ok ForceMutThunk n = (n = 1) ∧
  num_args_ok (FFI channel) n = (n = 1)
End

(* Continue with an expression *)
Definition continue_def:
  continue env exp (st:state option) k = (Exp env exp, st, k)
End

(* Push continuation onto the stack and continue with an expression *)
Definition push_def:
  push env exp (st:state option) k ks = (Exp env exp, st, k::ks)
End

(* Produce a value *)
Definition value_def:
  value v (st:state option) k = (Val v, st, k)
End

(* Produce an error *)
Definition error_def:
  error (st:state option) k = (Error, st, k)
End

Definition dest_Closure_def[simp]:
  dest_Closure (Closure s env x) = SOME (s, env, x) ∧
  dest_Closure _ = NONE
End

Definition dest_Recclosure_def[simp]:
  dest_Recclosure (Recclosure funs env fn) = SOME (funs, env, fn) ∧
  dest_Recclosure _ = NONE
End

Definition dest_anyClosure_def:
  dest_anyClosure v =
    case dest_Closure v of
    | SOME x => SOME x
    | NONE =>
      case dest_Recclosure v of
      | NONE => NONE
      | SOME (f, env, n) =>
          case ALOOKUP f n of
          | SOME (Lam s x) => SOME (s, mk_rec_env f env, x)
          | _ => NONE
End

Definition opt_bind_def:
  opt_bind NONE v env = env ∧
  opt_bind (SOME n) v env = (n,v)::env
End

Definition dest_Thunk_def[simp]:
  dest_Thunk (Thunk x) = SOME x ∧
  dest_Thunk _ = NONE
End

Definition dest_anyThunk_def:
  dest_anyThunk v =
    case dest_Thunk v of
    | SOME w => SOME (w, [])
    | NONE =>
      case dest_Recclosure v of
      | NONE => NONE
      | SOME (f, env, n) =>
        case ALOOKUP f n of
          SOME (Delay x) => SOME (INR (env, x), f)
        | _ => NONE
End

(******************** Semantics functions ********************)

(* Carry out an application - assumes:
    - arguments are in call-order
    - enough arguments are passed *)
Definition application_def:
  application AppOp vs (st:state option) k = (
    case dest_anyClosure (HD vs) of
    | NONE => error st k
    | SOME (arg, env', e) =>
        continue (opt_bind arg (EL 1 vs) env') e st k) ∧
  application (Cons s) vs st k = value (Constructor s vs) st k ∧
  application (AtomOp aop) vs st k = (
    case get_atoms vs of
      NONE => error st k
    | SOME as =>
      case eval_op aop as of
        SOME $ INL a => value (Atom a) st k
      | SOME $ INR T => value (Constructor "True" []) st k
      | SOME $ INR F => value (Constructor "False" []) st k
      | _            => error st k) ∧
  application Alloc vs st k = (
    case HD vs, st of
      Atom (Int i), SOME stores =>
        let n = if i < 0 then 0 else Num i in
        value (Atom $ Loc $ LENGTH stores)
              (SOME (SNOC (Array $ REPLICATE n (EL 1 vs)) stores))
              k
    | _ => error st k) ∧
  application Length vs st k = (
    case HD vs, st of
      Atom (Loc n), SOME stores => (
        case oEL n stores of
          SOME (Array l) => value (Atom $ Int $ & LENGTH l) st k
        | _ => error st k)
    | _ => error st k) ∧
  application (Proj s i) vs st k = (
    case HD vs of
      Constructor t ys => (
        if t = s ∧ i < LENGTH ys then
          value (EL i ys) st k
        else error st k)
    | _ => error st k) ∧
  application (IsEq s i) vs st k = (
    case HD vs of
      Constructor t ys => (
        if t = s ⇒ i = LENGTH ys then
          value (Constructor (if t = s then "True" else "False") []) st k
        else error st k)
    | _ => error st k) ∧
  application Sub vs st k = (
    case (EL 0 vs, EL 1 vs, st) of
      (Atom $ Loc n, Atom $ Int i, SOME stores) => (
        case oEL n stores of
          SOME (Array l) =>
            if 0 ≤ i ∧ i < & LENGTH l then
              value (EL (Num i) l) st k
            else
              (Exn (Constructor "Subscript" []), st, k)
        | _ => error st k)
    | _ => error st k) ∧
  application Update vs st k = (
    case (EL 0 vs, EL 1 vs, st) of
      (Atom $ Loc n, Atom $ Int i, SOME stores) => (
        case oEL n stores of
          SOME (Array l) =>
            if 0 ≤ i ∧ i < & LENGTH l then
              value
                (Constructor "" [])
                (SOME (LUPDATE (Array $ LUPDATE (EL 2 vs) (Num i) l) n stores))
                k
            else
              (Exn (Constructor "Subscript" []), st, k)
        | _ => error st k)
    | _ => error st k) ∧
  application (AllocMutThunk mode) vs st k = (
    case HD vs, st of
      v, SOME stores =>
        value (Atom $ Loc $ LENGTH stores)
              (SOME (SNOC (ThunkMem mode v) stores))
              k
    | _ => error st k) ∧
  application (UpdateMutThunk mode) vs st k = (
    case HD vs, st of
      (Atom $ Loc n, SOME stores) => (
        case oEL n stores of
          SOME (ThunkMem NotEvaluated _) =>
          value
            (Constructor "" [])
            (SOME (LUPDATE (ThunkMem mode (EL 1 vs)) n stores))
            k
        | _ => error st k)
    | _ => error st k) ∧
  application ForceMutThunk vs st k = (
    case HD vs, st of
      (Atom $ Loc n, SOME stores) => (
        case oEL n stores of
          SOME (ThunkMem Evaluated v) => value v st k
        | SOME (ThunkMem NotEvaluated f) =>
            value
              f
              st
              (AppK [] AppOp [Constructor "" []] [] :: ForceMutK n :: k)
        | _ => error st k)
    | _ => error st k) ∧
  application (FFI channel) vs st k = (
    case HD vs, st of
      (Atom $ Str content, SOME _) => (Action channel content, st, k)
    | _ => error st k)
End

(* Return a value and handle a continuation *)
Definition return_def:
  return v st [] = value v st [] ∧
  return v st (LetK env NONE e :: k) = continue env e st k ∧
  return v st (LetK env (SOME x) e :: k) = continue ((x,v)::env) e st k ∧
  return v st (IfK env e1 e2 :: k) = (
    if v = Constructor "True"  [] then continue env e1 st k else
    if v = Constructor "False" [] then continue env e2 st k else
      error st k) ∧
  return v st (RaiseK :: k) =
    (if st = NONE then error st k else (Exn v, st, k)) ∧
  return v st (HandleK env x e :: k) = value v st k ∧
  return v st (HandleAppK env e :: k) = value v st k ∧
  return v st (AppK env sop vs' [] :: k) = (let vs = v::vs' in
    if ¬ num_args_ok sop (LENGTH vs) then error st k else
    application sop vs st k) ∧
  return v st (AppK env sop vs (e::es) :: k) =
    continue env e st (AppK env sop (v::vs) es :: k) ∧
  return v st (ForceK1 :: k) =
    (case dest_anyThunk v of
     | NONE => error st k
     | SOME (INL v, _) => value v st k
     | SOME (INR (env, x), fns) => continue (mk_rec_env fns env) x NONE (ForceK2 st :: k)) ∧
  return v temp_st (ForceK2 st :: k) =
    (case dest_anyThunk v of
     | NONE => value v st k
     | SOME _ => error st k) ∧
  return v st (BoxK :: k) =
    (case dest_anyThunk v of
     | NONE => value (Thunk $ INL v) st k
     | SOME _ => error st k) ∧
  return v st (ForceMutK n :: k) =
    (case st of
       SOME stores =>
         if n < LENGTH stores ∧
            store_same_type (EL n stores) (ThunkMem Evaluated v) then
           value v (SOME (LUPDATE (ThunkMem Evaluated v) n stores)) k
         else
           error st k
     | NONE => error st k)
End

Definition find_match_list_def:
  find_match_list c ws env [] d =
    (case d of
     | NONE => NONE
     | SOME (alts:((vname # num) list),e:exp) =>
         if ALOOKUP alts c = SOME (LENGTH ws) then SOME (env,e) else NONE) ∧
  find_match_list c ws env ((c',ns,e)::rows) d =
    if c = c' then
      if LENGTH ns = LENGTH ws then
        SOME (REVERSE (ZIP (ns, ws)) ++ env, e)
      else NONE
    else find_match_list c ws env rows d
End

Definition find_match_def:
  find_match w env n css d =
    if MEM n (FLAT (MAP (FST o SND) css)) ∨ css = [] then NONE else
      case w of
      | Constructor c ws => find_match_list c ws env css d
      | _ => NONE
End

Overload IntLit = “λi. App (AtomOp (Lit (Int i))) []”
Overload Eq = “λx y. App (AtomOp Eq) [x; y]”

(* Perform a single step of evaluation *)
Definition step_def:
  step st k (Exp env $ Var x) = (
    case ALOOKUP env x of
      SOME v => value v st k
    | NONE => error st k) ∧
  step st k (Exp env $ Lam x body) = value (Closure x env body) st k ∧
  step st k (Exp env $ Delay body) = value (Thunk $ INR (env, body)) st k ∧
  step st k (Exp env $ Letrec fns e) = continue (mk_rec_env fns env) e st k ∧
  step st k (Exp env $ Let xopt e1 e2) = push env e1 st (LetK env xopt e2) k ∧
  step st k (Exp env $ If e e1 e2) = push env e st (IfK env e1 e2) k ∧
  step st k (Exp env $ Case v css d) = (
    case ALOOKUP env v of
      NONE => error st k
    | SOME w =>
      case find_match w env v css d of
      | NONE => error st k
      | SOME (env1,e1) => continue env1 e1 st k) ∧
  step st k (Exp env $ Raise e) = push env e st RaiseK k ∧
  step st k (Exp env $ Handle e1 x e2) = push env e1 st (HandleK env x e2) k ∧
  step st k (Exp env $ HandleApp e1 e2) = push env e2 st (HandleAppK env e1) k ∧
  step st k (Exp env $ App sop es) = (
    if ¬ num_args_ok sop (LENGTH es) then error st k else
    case REVERSE es of (* right-to-left evaluation *)
      [] => (* sop = Cons s ∨ sop = AtomOp aop   because   num_args_ok ... *)
        application sop [] st k
    | e::es' => push env e st (AppK env sop [] es') k) ∧
  step st k (Exp env $ Box e) = push env e st BoxK k ∧
  step st k (Exp env $ Force e) = push env e st ForceK1 k ∧

  (***** Errors *****)
  step st k Error = error st k ∧

  (***** Exceptions *****)
  step st [] (Exn v) = (Exn v, st, []) ∧
  step st (k::ks) (Exn v) = (
    case k of
      HandleK env x e => continue ((x,v)::env) e st ks
    | HandleAppK env e => push env e st (AppK env AppOp [v] []) ks
    | _ => (Exn v, st, ks)) ∧

  (***** Values *****)
  step st k (Val v) = return v st k ∧

  (***** Actions *****)
  step st k (Action ch c) = (Action ch c, st, k)
End


(******************** Top-level semantics ********************)

(* Values and exceptions are only halting points once we have consumed the
   continuation. Errors and actions are always halting points. *)
Definition is_halt_def[simp]:
  is_halt (Val v, st:state option, []) = T ∧
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
    itree_unfold_err
      (λ(sr, st, k).
        case step_until_halt (sr, st, k) of
        | Ret => Ret' Termination
        | Err => Ret' Error
        | Div => Div'
        | Act a k' st' => Vis' a (λy. value (Atom (Str y)) st' k' ))
      ((λ_ ret. STRLEN ret ≤ max_FFI_return_size),
       pure_semantics$FinalFFI,
       λs. pure_semantics$FinalFFI s pure_semantics$FFI_failure)
      (sr, st, k)
End

Definition semantics_def:
  semantics e env state k = sinterp (Exp env e) state k
End

Definition itree_of_def:
  itree_of e = semantics e [] (SOME []) []
End

(******************** Lemmas ********************)

Theorem sinterp:
  sinterp sr st k =
    case step_until_halt (sr,st,k) of
    | Ret => Ret Termination
    | Err => Ret Error
    | Div => Div
    | Act e k' st' =>
        Vis e (λa. case a of
                   | INL x => Ret $ FinalFFI e x
                   | INR y =>
                      if LENGTH y ≤ max_FFI_return_size then
                        sinterp (Val $ Atom $ Str y) st' k'
                      else Ret $ FinalFFI e FFI_failure)
Proof
  rw[sinterp_def] >> rw[Once itreeTheory.itree_unfold_err] >> simp[] >>
  CASE_TAC >> gvs[] >> rw[FUN_EQ_THM, value_def]
QED

Theorem step_n_add:
  step_n (m+n) x = step_n m (step_n n x)
Proof
  PairCases_on ‘x’ \\ fs [step_n_def,FUNPOW_ADD]
  \\ AP_THM_TAC \\ fs [FUN_EQ_THM,FORALL_PROD,step_n_def]
QED

Theorem step_n_SUC:
  step_n (SUC n) x = step_n n (step_n 1 x)
Proof
  fs [ADD1,step_n_add]
QED

Theorem step_n_alt:
  step_n 0 res = res ∧
  step_n (SUC n) res = (λ(sr,st,k). step st k sr) (step_n n res)
Proof
  PairCases_on `res` >>
  rw[step_n_def, arithmeticTheory.FUNPOW_0, arithmeticTheory.FUNPOW_SUC]
QED

Theorem is_halt_step_same:
  ∀sr st k. is_halt (sr, st, k) ⇒ step st k sr = (sr, st, k)
Proof
  Cases_on ‘st’ >> Cases_on ‘k’
  >> Cases_on ‘sr’ >> gvs[is_halt_def] >> rw[]
  >> fs [step_def,return_def,value_def,error_def,is_halt_def]
QED

Theorem step_n_mono:
  ∀n res. is_halt (step_n n res) ⇒ ∀m. n < m ⇒ step_n n res = step_n m res
Proof
  rw[] >> Induct_on `m` >> gvs[] >>
  PairCases_on `res` >> rw[step_n_alt] >>
  Cases_on `n = m` >> gvs[] >>
  pairarg_tac >> gvs[is_halt_step_same]
QED

Theorem is_halt_imp_eq:
  is_halt (step_n n res) ∧ is_halt (step_n m res) ⇒
  step_n n res = step_n m res
Proof
  ‘n < m ∨ m = n ∨ m < n’ by decide_tac
  \\ metis_tac [step_n_mono]
QED

Theorem step_n_0[simp]:
  step_n 0 x = x
Proof
  PairCases_on ‘x’ \\ fs [step_n_def]
QED

Theorem step_n_1[simp]:
  step_n 1 x = step (FST (SND x)) (SND (SND x)) (FST x)
Proof
  PairCases_on ‘x’ \\ fs [step_n_def]
QED

Theorem is_halt_step_n_same:
  ∀n x. is_halt x ⇒ step_n n x = x
Proof
  Induct \\ fs [FORALL_PROD,step_n_SUC,is_halt_step_same]
QED

Theorem step_unitl_halt_unwind:
  step ss1 sk1 r1 = (r1',ss1',sk1') ⇒
  step_until_halt (r1,ss1,sk1) =
  step_until_halt (r1',ss1',sk1')
Proof
  fs [step_until_halt_def]
  \\ reverse (DEEP_INTRO_TAC some_intro \\ fs [] \\ rw [])
  >-
   (qsuff_tac ‘∀x. ¬is_halt (step_n x (r1',ss1',sk1'))’ >- fs []
    \\ rw [] \\ first_x_assum (qspec_then ‘x+1’ mp_tac)
    \\ rewrite_tac [step_n_add] \\ fs [])
  \\ Cases_on ‘x’ \\ fs []
  >-
   (imp_res_tac is_halt_step_same \\ gvs []
    \\ ‘∀n. step_n n (r1,ss1,sk1) = (r1,ss1,sk1)’ by
      (Induct \\ fs [ADD1,step_n_add])
    \\ fs [] \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw [])
  \\ fs [ADD1,step_n_add]
  \\ fs [] \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
  \\ ‘n < x ∨ x < n ∨ x = n’ by decide_tac \\ gvs[]
  \\ imp_res_tac step_n_mono \\ fs []
QED

Theorem step =
  LIST_CONJ [step_def,push_def,return_def,value_def,opt_bind_def,continue_def,
             application_def,dest_anyClosure_def,dest_Closure_def,error_def];

(****************************************)

Theorem is_halt_step:
  ∀n x. is_halt x ⇒ step_n n x = x
Proof
  Induct \\ simp [ADD1,step_n_add,FORALL_PROD] \\ Cases \\ fs []
  >- (rw [] \\ rename [‘(Val _,x,y)’] \\ Cases_on ‘y’ \\ fs [step])
  >- (rw [] \\ rename [‘(Exn _,x,y)’] \\ Cases_on ‘y’ \\ fs [step])
  \\ rw [] \\ fs [step]
QED

Theorem is_halt_simp[simp]:
  (is_halt (Exn v,s,k) ⇔ k = []) ∧
  (is_halt (Val v,s,k) ⇔ k = [])
Proof
  Cases_on ‘k’ \\ fs []
QED

Theorem step_Error[simp]:
  ∀n ts tk tr1 ts1 tk1.
    tr1 ≠ Error ⇒ step_n n (Error,ts,tk) ≠ (tr1,ts1,tk1)
Proof
  Induct \\ fs [ADD1,step_n_add,step,error_def]
QED

Theorem step_n_Exn_NIL:
  step_n n (Exn v,s,[]) = (Exn v,s,[])
Proof
  Induct_on ‘n’ >> rw[step,ADD1,step_n_add]
QED

Triviality application_Action:
  application p vs st k = (Action channel content,st1,k1) ⇒
  p = FFI channel ∧ ∃st1. st = SOME st1
Proof
  fs [application_def |> DefnBase.one_line_ify NONE, AllCaseEqs(), error_def, value_def]
  \\ rw [] \\ fs []
  \\ fs [continue_def,push_def]
QED

Theorem step_n_is_halt_SOME:
  step_n x (tr,SOME ts,tk) = (Action a b,a1,a2) ⇒
  ∃ts2. a1 = SOME ts2
Proof
  qsuff_tac
    ‘∀x input a b a1 a2.
       step_n x input = (Action a b,a1,a2) ⇒
       ∀ts1. FST (SND input) = SOME ts1 ⇒ ∃ts2. a1 = SOME ts2’
  >- (rw [] \\ first_x_assum drule \\ fs [])
  \\ Induct
  \\ fs [FUNPOW_SUC,step_n_def,FORALL_PROD] \\ rw []
  \\ pairarg_tac \\ fs []
  \\ qpat_x_assum ‘_ = (Action a b,a1,a2)’ mp_tac
  \\ simp [step_def |> DefnBase.one_line_ify NONE,AllCaseEqs(),error_def,push_def]
  \\ fs [value_def,continue_def]
  \\ rw []
  \\ imp_res_tac application_Action \\ gvs []
  \\ fs [return_def,value_def]
  \\ res_tac \\ fs []
  \\ gvs [return_def |> DefnBase.one_line_ify NONE,AllCaseEqs(),error_def]
  \\ imp_res_tac application_Action \\ gvs []
  \\ fs [application_def,AllCaseEqs(),error_def]
  \\ gvs [value_def,continue_def]
QED

Theorem application_cut_cont[local]:
  ∀sop vs st k x y z k'.
  application sop vs st k = (x,y,z) ∧ num_args_ok sop (LENGTH vs) ∧ k' ≼ k ⇒
  ∃x' y' z'. application sop vs st k' = (x',y',z') ∧
       ((x,y,z) = (x',y',z' ++ DROP (LENGTH k') k) ∨ is_halt (x',y',z'))
Proof
  Cases >> rw[step] >>
  gvs[AllCaseEqs(),dest_Closure_def,quantHeuristicsTheory.LIST_LENGTH_1,
        rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.DROP_APPEND2,
        APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >>
  metis_tac[]
QED

Theorem return_cut_cont[local]:
  ∀v st k x y z k'.
  return v st k = (x,y,z) ∧ k' ≼ k ⇒
  ∃x' y' z'. return v st k' = (x',y',z') ∧
       ((x,y,z) = (x',y',z' ++ DROP (LENGTH k') k) ∨ is_halt (x',y',z'))
Proof
  ho_match_mp_tac return_ind >>
  rw[] >>
  gvs[AllCaseEqs(),dest_Closure_def,quantHeuristicsTheory.LIST_LENGTH_1,
        rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.DROP_APPEND2,
        APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV),step] >>
  rename [‘k' ++ _’] >>
  drule_then (qspec_then ‘k'’ mp_tac) application_cut_cont >>
  gvs[rich_listTheory.DROP_APPEND2]
QED

Theorem step_cut_cont[local]:
  ∀st k sr k' x y z.
  step st k sr = (x,y,z) ∧ k' ≼ k ⇒
  ∃x' y' z'. step st k' sr = (x',y',z') ∧
       ((x,y,z) = (x',y',z' ++ DROP (LENGTH k') k) ∨ is_halt (x',y',z'))
Proof
  ho_match_mp_tac step_ind >>
  rw[step,AllCaseEqs()] >> rw[] >>
  gvs[rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.DROP_APPEND2,
      APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV),step,AllCaseEqs()]
  >- (drule_then (qspec_then ‘k'’ mp_tac) application_cut_cont >>
      gvs[rich_listTheory.DROP_APPEND2])
  >- metis_tac[]
  >- (drule_then (qspec_then ‘k'’ mp_tac) return_cut_cont >>
      gvs[rich_listTheory.DROP_APPEND2])
QED

Theorem step_n_cut_cont_gen:
  ∀n x s k y k'.
  step_n n (x,s,k) = y ∧ is_halt y ∧ k' ≼ k ⇒
  ∃m z. m ≤ n ∧ step_n m (x,s,k') = z ∧ is_halt z
Proof
  Induct >> rw [ADD1,step_n_add,step,error_def]
  >- (Cases_on ‘x’ >> gvs[]) >>
  ‘∃xx y z. step s k x = (xx,y,z)’ by metis_tac[PAIR] >>
  drule_then (drule_then strip_assume_tac) step_cut_cont >> gvs[]
  >- (Q.REFINE_EXISTS_TAC ‘SUC m’ >> gvs[ADD1,step_n_add] >>
      first_x_assum match_mp_tac >>
      first_x_assum(irule_at (Pos hd)) >>
      simp[]) >>
  qexists_tac ‘1’ >> simp[]
QED

Theorem step_n_cut_cont:
  step_n n (x,s,k) = y ∧ is_halt y ⇒
  ∃m z. m ≤ n ∧ step_n m (x,s,[]) = z ∧ is_halt z
Proof
  metis_tac[rich_listTheory.IS_PREFIX_NIL,step_n_cut_cont_gen]
QED

Theorem step_n_Error:
  step_n n (Error,ts,tk) = (Error,ts,tk)
Proof
  Induct_on ‘n’ \\ fs [step_n_def,FUNPOW,step_def,error_def]
QED

Theorem step_n_Val:
  step_n n (Val v,ts,[]) = (Val v,ts,[])
Proof
  Induct_on ‘n’ \\ fs [step_n_def,FUNPOW,step_def,return_def,value_def]
QED

Theorem step_n_Action:
  step_n n (Action a b, s, k) = (Action a b, s, k)
Proof
  Induct_on `n` >> rw[step_n_SUC, step_def]
QED

Definition forceK2_none_def[simp]:
  forceK2_none (ForceK2 _) = ForceK2 NONE ∧
  forceK2_none y = y
End

Theorem application_NONE:
  application Alloc [v1;v2] NONE s = (Error,NONE,s) ∧
  application Length [v1] NONE s = (Error,NONE,s) ∧
  application Sub [v1;v2] NONE s = (Error,NONE,s) ∧
  application Update [v1;v2;v3] NONE s = (Error,NONE,s) ∧
  application (AllocMutThunk m) [v1] NONE s = (Error,NONE,s) ∧
  application (UpdateMutThunk m) [v1;v2] NONE s = (Error,NONE,s) ∧
  application ForceMutThunk [v1] NONE s = (Error,NONE,s) ∧
  application (FFI f) [v1] NONE s = (Error,NONE,s)
Proof
  fs [application_def,error_def]
  \\ EVERY_CASE_TAC \\ fs []
QED

Theorem step_n_NONE:
  step_n n (Exp tenv1 te,ts,[]) = (tr1,ts1,tk1) ∧ is_halt (tr1,ts1,tk1) ⇒
  step_n n (Exp tenv1 te,NONE,[]) = (tr1,NONE,tk1) ∧ (∃res. tr1 = Val res) ∨
  ∀k. ∃ts2 tk2. step_n n (Exp tenv1 te,NONE,k) = (Error,ts2,tk2)
Proof
  qsuff_tac ‘
   ∀n e ts rest tr1 ts1 tk1.
     step_n n (e,ts,rest) = (tr1,ts1,tk1) ∧ ~is_halt (e,ts,rest) ∧
     (∀x. e ≠ Exn x) ∧ is_halt (tr1,ts1,tk1) ⇒
     step_n n (e,NONE,MAP forceK2_none rest) = (tr1,NONE,tk1) ∧ (∃res. tr1 = Val res) ∨
     ∀k. ∃ts2 tk2. step_n n (e,NONE,MAP forceK2_none rest ++ k) = (Error,ts2,tk2)’
  >- (rw [] \\ last_x_assum drule \\ fs [])
  \\ completeInduct_on ‘n’
  \\ Cases_on ‘n’
  >- (fs [] \\ rw [] \\ fs [])
  \\ fs [step_n_def,FUNPOW] \\ rw []
  \\ qpat_x_assum ‘_ = _’ mp_tac
  \\ reverse (Cases_on ‘e’) \\ fs []
  >~ [‘Exp l1 e1’] >-
   (Cases_on ‘e1’
    >~ [‘Var’] >-
     (fs [step_def]
      \\ CASE_TAC \\ fs [error_def,step_n_Error,GSYM step_n_def,value_def]
      \\ Cases_on ‘rest’ \\ fs [step_n_Val]
      \\ rw [] \\ fs [step_n_Val]
      \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
      \\ strip_tac \\ fs [])
    >~ [‘Lam’] >-
     (fs [step_def,value_def]
      \\ fs [error_def,step_n_Error,GSYM step_n_def,value_def]
      \\ Cases_on ‘rest’ \\ fs [step_n_Val]
      \\ rw [] \\ fs [step_n_Val]
      \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
      \\ strip_tac \\ fs [])
    >~ [‘Letrec’] >-
     (fs [step_def,value_def,continue_def]
      \\ rw [] \\ fs [step_n_Val]
      \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
      \\ strip_tac \\ fs [])
    >~ [‘Let’] >-
     (fs [step_def,value_def,continue_def,push_def]
      \\ rw [] \\ fs [step_n_Val]
      \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
      \\ strip_tac \\ fs [])
    >~ [‘If’] >-
     (fs [step_def,value_def,continue_def,push_def]
      \\ rw [] \\ fs [step_n_Val]
      \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
      \\ strip_tac \\ fs [])
    >~ [‘Case’] >-
     (fs [step_def,value_def,continue_def,push_def]
      \\ rw [] \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
      \\ CASE_TAC \\ fs []
      \\ fs [GSYM step_n_def,step_n_Error]
      \\ CASE_TAC \\ fs []
      \\ fs [GSYM step_n_def,step_n_Error]
      \\ CASE_TAC \\ fs []
      \\ fs [GSYM step_n_def,step_n_Error]
      \\ first_x_assum irule \\ fs []
      \\ first_x_assum $ irule_at $ Pos last \\ fs [])
    >~ [‘Delay’] >-
     (fs [step_def,value_def,continue_def,push_def]
      \\ rw [] \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
      \\ Cases_on ‘rest’ \\ fs [step_n_Val]
      \\ rw [] \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
      \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
      \\ strip_tac \\ fs [])
    >~ [‘Box’] >-
     (fs [step_def,value_def,continue_def,push_def]
      \\ rw [] \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
      \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
      \\ strip_tac \\ fs [])
    >~ [‘Force’] >-
     (fs [step_def,value_def,continue_def,push_def]
      \\ rw [] \\ fs [step_n_Val]
      \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
      \\ strip_tac \\ fs [])
    >~ [‘Raise’] >-
     (fs [step_def,value_def,continue_def,push_def]
      \\ rw [] \\ fs [step_n_Val]
      \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
      \\ strip_tac \\ fs [])
    >~ [‘Handle’] >-
     (fs [step_def,value_def,continue_def,push_def]
      \\ rw [] \\ fs [step_n_Val]
      \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
      \\ strip_tac \\ fs [])
    >~ [‘HandleApp’] >-
     (fs [step_def,value_def,continue_def,push_def]
      \\ rw [] \\ fs [step_n_Val]
      \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
      \\ strip_tac \\ fs [])
    >~ [‘App’] >-
     (fs [step_def,value_def,continue_def,push_def]
      \\ rw [] \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
      \\ reverse CASE_TAC \\ gvs []
      >-
       (rw [] \\ gvs [GSYM step_n_def]
        \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
        \\ strip_tac \\ fs [])
      \\ Cases_on ‘s’ \\ fs [num_args_ok_def]
      \\ fs [application_def,value_def]
      >- (rw [] \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
          \\ rw [] \\ gvs [GSYM step_n_def]
          \\ Cases_on ‘rest’ \\ fs [step_n_Val]
          \\ rw [] \\ gvs [GSYM step_n_def,step_n_Val]
          \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
          \\ strip_tac \\ fs [])
      >- (fs [get_atoms_def] \\ Cases_on ‘eval_op a []’ \\ fs []
          \\ rw [] \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
          \\ Cases_on ‘x’ \\ fs [] \\ rw []
          \\ Cases_on ‘rest’ \\ fs [step_n_Val]
          \\ rw [] \\ gvs [GSYM step_n_def,step_n_Val]
          \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
          \\ strip_tac \\ fs [])
      \\ rw [] \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]))
  \\ Cases_on ‘rest’ \\ fs [] \\ fs [step_def]
  \\ Cases_on ‘h’
  >~ [‘LetK _ opt’] >-
   (Cases_on ‘opt’ \\ fs [return_def,continue_def]
    \\ rw [] \\ gvs [GSYM step_n_def,step_n_Val]
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
    \\ strip_tac \\ fs [])
  >~ [‘IfK’] >-
   (fs [return_def,continue_def]
    \\ rw [] \\ gvs [GSYM step_n_def,step_n_Val]
    \\ rw [] \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
    \\ strip_tac \\ fs [])
  >~ [‘BoxK’] >-
   (fs [return_def,continue_def,value_def]
    \\ rw [] \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
    \\ Cases_on ‘t’ \\ fs [step_n_Val] \\ gvs [step_n_Val]
    \\ Cases_on `dest_anyThunk v` \\ gvs []
    \\ last_x_assum $ drule_at Any \\ rw []
    \\ last_x_assum $ qspec_then `n'` assume_tac \\ gvs [step_n_def]
    \\ last_x_assum $ drule_at Any \\ rw [] \\ gvs [GSYM step_n_def]
    \\ gvs [step_n_Val,step_n_Error])
  >~ [‘ForceK1’] >-
   (fs [return_def,continue_def,value_def]
    \\ CASE_TAC
    \\ rw [] \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
    \\ Cases_on ‘x’ \\ fs [step_n_Val] \\ gvs [step_n_Val]
    \\ Cases_on ‘q’ \\ fs [step_n_Val] \\ gvs [step_n_Val]
    >-
     (Cases_on ‘t’ \\ fs [step_n_Val] \\ gvs [step_n_Val]
      \\ rw [] \\ gvs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
      \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
      \\ strip_tac \\ fs [])
    \\ CASE_TAC \\ fs []
    \\ rw [] \\ gvs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
    \\ strip_tac \\ fs [])
  >~ [‘ForceK2’] >-
   (fs [return_def,continue_def,value_def]
    \\ Cases_on ‘t’ \\ fs [step_n_Val] \\ gvs [step_n_Val]
    \\ rw [] \\ gvs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
    \\ Cases_on `dest_anyThunk v` \\ gvs []
    \\ last_x_assum $ drule_at Any \\ rw []
    \\ last_x_assum $ qspec_then `n'` assume_tac \\ gvs [step_n_def]
    \\ last_x_assum $ drule_at Any \\ rw [] \\ gvs [GSYM step_n_def]
    \\ gvs [step_n_Val,step_n_Error])
  >~ [‘RaiseK’] >-
   (fs [return_def,error_def] \\ fs [error_def]
    \\ rw [] \\ gvs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  >~ [‘HandleK’] >-
   (fs [return_def,error_def] \\ fs [error_def]
    \\ fs [return_def,continue_def,value_def]
    \\ Cases_on ‘t’ \\ fs [step_n_Val] \\ gvs [step_n_Val]
    \\ rw [] \\ gvs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
    \\ strip_tac \\ fs [])
  >~ [‘HandleAppK’] >-
   (fs [return_def,error_def,value_def]
    \\ Cases_on ‘t’ \\ fs [step_n_Val] \\ gvs [step_n_Val]
    \\ rw [] \\ gvs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
    \\ strip_tac \\ fs [])
  >~ [‘ForceMutK’] >-
   (fs [return_def,error_def,value_def]
    \\ Cases_on ‘t’ \\ fs [step_n_Val] \\ gvs [step_n_Val]
    \\ rw [] \\ gvs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  \\ rename [‘AppK env sop vs es’] \\ gvs []
  \\ reverse (Cases_on ‘es’)
  \\ fs [return_def,continue_def]
  >- (rw [] \\ gvs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
      \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
      \\ strip_tac \\ fs [])
  \\  IF_CASES_TAC \\ fs []
  >- (rw [] \\ gvs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  \\ Cases_on ‘sop’
  >~ [‘AppOp’] >-
   (gvs [application_def,num_args_ok_def,LENGTH_EQ_NUM_compute]
    \\ CASE_TAC \\ gvs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
    \\ PairCases_on ‘x’ \\ fs [continue_def] \\ rw []
    \\ gvs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
    \\ strip_tac \\ fs [])
  >~ [‘Cons’] >-
   (gvs [application_def,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ Cases_on ‘t’ \\ fs [step_n_Val] \\ gvs [step_n_Val]
    \\ rw [] \\ gvs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
    \\ strip_tac \\ fs [])
  >~ [‘AtomOp’] >-
   (gvs [application_def,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ CASE_TAC \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
    \\ CASE_TAC \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
    \\ Cases_on ‘x'’ \\ fs [] \\ rw []
    \\ Cases_on ‘t’ \\ fs [step_n_Val]
    \\ rw [] \\ gvs [GSYM step_n_def,step_n_Val]
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
    \\ strip_tac \\ fs [])
  >~ [‘Proj’] >-
   (gvs [application_def,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ CASE_TAC \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
    \\ CASE_TAC \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def]
    \\ Cases_on ‘t’ \\ fs [step_n_Val]
    \\ rw [] \\ gvs [GSYM step_n_def,step_n_Val]
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
    \\ strip_tac \\ fs [])
  >~ [‘IsEq’] >-
   (gvs [application_def,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ rpt (CASE_TAC \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
    \\ Cases_on ‘t’ \\ fs [step_n_Val]
    \\ rw [] \\ gvs [GSYM step_n_def,step_n_Val]
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
    \\ strip_tac \\ fs [])
  >~ [‘Alloc’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  >~ [‘Length’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  >~ [‘Sub’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  >~ [‘Update’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ Cases_on ‘vs’ \\ fs [] \\ Cases_on ‘t'’ \\ fs [] \\ Cases_on ‘t''’ \\ fs []
    \\ gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  >~ [‘AllocMutThunk’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  >~ [‘UpdateMutThunk’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ Cases_on ‘t’ \\ fs [] \\ Cases_on ‘t'’ \\ fs []
    \\ gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  >~ [‘ForceMutThunk’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ Cases_on ‘t’ \\ fs []
    \\ gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  >~ [‘FFI’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
QED

Theorem application_set_cont[local]:
  ∀sop vs st k' sr k x y z.
  application sop vs st k' = (x,y,z) ∧ x ≠ Error ∧ (∀v. x = Exn v ⇒ z ≠ []) ⇒ k' ≼ k ⇒
  application sop vs st k = (x,y,z ++ DROP (LENGTH k') k)
Proof
  Cases >> rw[step] >>
  gvs[AllCaseEqs(),dest_Closure_def,quantHeuristicsTheory.LIST_LENGTH_1,
        rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.DROP_APPEND2,
        APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)]
QED

Theorem step_weaken:
  step st k sr = (sr', st', k') ∧
  ¬is_halt (sr', st', k')
  ⇒ step st (k ++ extra) sr = (sr', st', k' ++ extra)
Proof
  rw[] >>
  Cases_on ‘sr’ >> gvs[step_def, error_def]
  >- (
    Cases_on ‘e’ >> gvs[step_def, AllCaseEqs()] >>
    gvs[error_def, value_def, push_def, continue_def] >>
    Cases_on ‘s’ >> gvs[num_args_ok_def, application_def, value_def] >>
    gvs[get_atoms_def, oneline pure_configTheory.eval_op_def] >>
    gvs[pure_configTheory.concat_def, pure_configTheory.implode_def] >>
    gvs[AllCaseEqs(), error_def]
    )
  >- (
    Cases_on ‘k’ >> gvs[return_def, value_def] >>
    gvs[oneline return_def, AllCaseEqs(), error_def, continue_def, value_def] >>
    Cases_on ‘sop’ >> gvs[num_args_ok_def, LENGTH_EQ_NUM_compute] >>
    gvs[application_def, AllCaseEqs(), error_def, value_def, continue_def]
    )
  >- (
    Cases_on ‘k’ >> gvs[step_def] >>
    gvs[AllCaseEqs(), push_def, continue_def]
    )
QED

Theorem step_n_weaken:
  ∀n e ts k res ts1 k1.
    step_n n (e,ts,k) = (res,ts1,k1) ∧ ¬is_halt (res,ts1,k1)
  ⇒ ∀k2. step_n n (e,ts,k ++ k2) = (res,ts1,k1 ++ k2)
Proof
  Induct >> rw[step_n_SUC] >>
  qmatch_asmsub_abbrev_tac ‘step_n n x’ >>
  PairCases_on ‘x’ >> gvs[] >>
  ‘¬is_halt (x0,x1,x2)’ by (
    CCONTR_TAC >> gvs[] >>
    drule is_halt_step_n_same >>
    disch_then $ qspec_then ‘n’ assume_tac >> gvs[]) >>
  drule step_weaken >> simp[]
QED

Theorem step_weaken_alt:
  step st k sr = (sr', st', k') ∧
  ¬is_halt (sr, st, k)
  ⇒ step st (k ++ extra) sr = (sr', st', k' ++ extra)
Proof
  rw[] >>
  Cases_on ‘sr’ >> gvs[step_def, error_def]
  >- (
    Cases_on ‘e’ >> gvs[step_def, AllCaseEqs()] >>
    gvs[error_def, value_def, push_def, continue_def] >>
    Cases_on ‘s’ >> gvs[num_args_ok_def, application_def, value_def] >>
    gvs[get_atoms_def, oneline pure_configTheory.eval_op_def] >>
    gvs[pure_configTheory.concat_def, pure_configTheory.implode_def] >>
    gvs[AllCaseEqs(), error_def]
    )
  >- (
    Cases_on ‘k’ >> gvs[return_def, value_def] >>
    gvs[oneline return_def, AllCaseEqs(), error_def, continue_def, value_def] >>
    Cases_on ‘sop’ >> gvs[num_args_ok_def, LENGTH_EQ_NUM_compute] >>
    gvs[application_def, AllCaseEqs(), error_def, value_def, continue_def]
    )
  >- (
    Cases_on ‘k’ >> gvs[step_def] >>
    gvs[AllCaseEqs(), push_def, continue_def]
    )
QED

Theorem step_n_to_halt_min:
  ∀n conf conf'.
  step_n n conf = conf' ∧ ¬is_halt conf ∧ is_halt conf'
  ⇒ ∃m mid.
      m < n ∧ step_n m conf = mid ∧ ¬is_halt mid ∧ step_n 1 mid = conf'
Proof
  Induct >> rw[] >> gvs[step_n_SUC] >>
  PairCases_on ‘conf’ >> gvs[] >>
  Cases_on ‘is_halt (step conf1 conf2 conf0)’ >> gvs[]
  >- (
    drule is_halt_step_n_same >> rw[] >>
    qexists ‘0’ >> simp[]
    ) >>
  last_x_assum drule >> simp[] >> strip_tac >> qexists ‘SUC m’ >> simp[step_n_SUC]
QED

Theorem num_args_ok_0:
  num_args_ok op 0 ⇔ (∃s. op = Cons s) ∨ (∃aop. op = AtomOp aop)
Proof
  Cases_on ‘op’ >> gvs[]
QED

Theorem application_cont:
  application op vs st k = (sr, st', k') ⇒
  ∃k''. k' = k'' ++ k
Proof
  rw[] >> Cases_on ‘op’ >> gvs[application_def, AllCaseEqs()] >>
  gvs[error_def, continue_def, value_def]
QED

Theorem step_to_halting_value:
  step st k sr = (Val v, sr', [])
  ⇒ (k = [] ∧ ((∃env e. sr = Exp env e) ∨ (sr = Val v))) ∨
    (∃v' f. sr = Val v' ∧ k = [f])
Proof
  gvs[oneline step_def, return_def, value_def, error_def, push_def, continue_def,
      AllCaseEqs()] >>
  rw[] >> gvs[]
  >- (drule application_cont >> simp[]) >>
  gvs[oneline return_def, AllCaseEqs(), error_def, continue_def, value_def] >>
  drule application_cont >> simp[]
QED

Theorem step_n_set_cont:
  step_n n (Exp tenv1 te,ts,[]) = (Val res,ts1,[]) ⇒
  ∃n5. n5 ≤ n ∧ ∀k. step_n n5 (Exp tenv1 te,ts,k) = (Val res,ts1,k)
Proof
  rw[] >>
  drule step_n_to_halt_min >> rw[] >>
  qmatch_asmsub_abbrev_tac ‘¬is_halt mid’ >>
  PairCases_on ‘mid’ >> gvs[] >>
  drule_all step_n_weaken >> strip_tac >> gvs[] >>
  drule step_weaken_alt >> simp[] >> strip_tac >>
  qexists ‘SUC m’ >> simp[step_n_alt]
QED

Theorem step_append_cont:
  step ts k e = (res,ts1,k1) ∧ ¬is_halt (res,ts1,k1) ⇒
    step ts (k ++ k2) e = (res,ts1,k1 ++ k2)
Proof
  Cases_on ‘e’ \\ strip_tac \\ gvs [step]
  >~ [‘Exp’] >- (
    Cases_on ‘e'’ \\ gvs [step, AllCaseEqs()]
    \\ Cases_on ‘s’ \\ gvs [num_args_ok_def, LENGTH_EQ_NUM_compute]
    \\ gvs [step, AllCaseEqs(), get_atoms_def])
  >~ [‘Exn’] >- (Cases_on ‘k’ \\ gvs [step, AllCaseEqs()])
  \\ Cases_on ‘k’ \\ gvs [step]
  \\ Cases_on ‘ts’ \\ gvs [num_args_ok_def, LENGTH_EQ_NUM_compute, step]
  \\ Cases_on ‘h’ \\ gvs [step, AllCaseEqs()]
  >>~- ([‘AppK’],
    Cases_on ‘l1’ \\ gvs [step]
    \\ IF_CASES_TAC \\ gvs [step]
    \\ Cases_on ‘s’ \\ gvs [step, AllCaseEqs()])
  >>~- ([‘LetK’], Cases_on ‘o'’ \\ gvs [step])
QED

Theorem return_fast_forward_lemma[local]:
  ∀v st k' sr k x y z.
  return v st k' = (x,y,z) ∧ (is_halt (x,y,z) ⇒ ∃v. x = Val v) ∧ k' ≼ k ⇒
  return v st k = (x,y,z ++ DROP (LENGTH k') k) ∨
  ((st,k',Val v) = (y,z,x))
Proof
  ho_match_mp_tac return_ind >>
  rw[step,AllCaseEqs()] >> rw[] >>
  gvs[rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.DROP_APPEND2,
      APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV),step,AllCaseEqs()] >>
  TRY(rename1 ‘list_CASE k'’ >> Cases_on ‘k'’ >>
      gvs[step,rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.DROP_APPEND2]) >>
  drule application_set_cont >>
  simp[rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.DROP_APPEND2] >>
  disch_then (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
  gvs[rich_listTheory.DROP_APPEND2] >>
  Cases_on ‘x’ >> gvs[]
QED

Theorem step_fast_forward_lemma[local]:
  ∀s k' sr k x y z.
  step s k' sr = (x,y,z) ∧ (is_halt (x,y,z) ⇒ ∃v. x = Val v) ∧ k' ≼ k ⇒
  step s k sr = (x,y,z ++ DROP (LENGTH k') k) ∨
  ((s,k',sr) = (y,z,x))
Proof
  ho_match_mp_tac step_ind >>
  rw[step,AllCaseEqs()] >> rw[] >>
  gvs[rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.DROP_APPEND2,
      APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV),step,AllCaseEqs()] >>
  TRY(rename1 ‘list_CASE k'’ >> Cases_on ‘k'’ >>
      gvs[step,rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.DROP_APPEND2])
  >- (drule application_set_cont >>
      simp[rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.DROP_APPEND2] >>
      disch_then (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
      gvs[rich_listTheory.DROP_APPEND2] >>
      Cases_on ‘x’ >> gvs[]) >>
  drule return_fast_forward_lemma >>
  gvs[rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.DROP_APPEND2,PULL_EXISTS]
QED

Theorem is_halt_prefix:
  ∀sr k s k'. is_halt (sr,s,k) ∧ k' ≼ k ⇒ is_halt (sr,s,k')
Proof
  Cases >> Cases >> rw[] >> gvs[]
QED

Theorem step_n_fast_forward_gen:
  ∀m2 sr ss k' ss2 sk2 k sr1 ss1 sk1 n v2.
  step_n m2 (sr,ss,k') = (Val v2,ss2,sk2) ∧
  step_n n (sr,ss,k) = (sr1,ss1,sk1) ∧ is_halt (sr1,ss1,sk1) ∧
  k' ≼ k
  ⇒
  ∃m3. m3 ≤ n ∧ step_n m3 (Val v2,ss2,sk2 ++ DROP (LENGTH k') k) = (sr1,ss1,sk1)
Proof
  Induct >> rpt strip_tac
  >- (irule_at (Pos hd) LESS_EQ_REFL >>
      gvs[rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.DROP_APPEND2]) >>
  gvs[ADD1,step_n_add] >>
  rename [‘step s k' sr’] >>
  ‘∃x y z. step s k' sr = (x,y,z)’ by metis_tac[PAIR] >>
  drule step_fast_forward_lemma >>
  disch_then(drule_at (Pos last)) >>
  impl_tac >- (rw[] >> gvs[is_halt_step_n_same]) >>
  reverse strip_tac
  >- (gvs[] >> metis_tac[]) >>
  Cases_on ‘n’
  >- (drule_then assume_tac is_halt_step_same >>
      gvs[] >>
      drule_all_then assume_tac is_halt_prefix >>
      gvs[is_halt_step_n_same,is_halt_step_same]) >>
  gvs[ADD1,step_n_add] >>
  first_x_assum drule >>
  disch_then drule >>
  simp[] >>
  gvs[] >>
  gvs[rich_listTheory.DROP_APPEND2] >>
  strip_tac >>
  first_x_assum(irule_at (Pos last)) >>
  simp[]
QED

Theorem step_n_fast_forward:
  step_n n (sr,ss,k::ks) = (sr1,ss1,sk1) ∧ is_halt (sr1,ss1,sk1) ∧
  step_n m2 (sr,ss,[]) = (Val v2,ss2,[]) ⇒
  ∃m3. m3 ≤ n ∧ step_n m3 (Val v2,ss2,k::ks) = (sr1,ss1,sk1)
Proof
  rpt strip_tac >>
  drule_at (Pat ‘is_halt’) step_n_fast_forward_gen >>
  rpt $ disch_then dxrule >>
  rw[]
QED

Theorem find_match_list_SOME:
  find_match_list cn ws env css d = SOME (env', e) ⇔
  (∃vs.
    ALOOKUP css cn = SOME (vs, e) ∧ LENGTH ws = LENGTH vs ∧
    env' = REVERSE (ZIP (vs,ws)) ++ env) ∨
  (ALOOKUP css cn = NONE ∧
   ∃alts. d = SOME (alts, e) ∧ ALOOKUP alts cn = SOME (LENGTH ws) ∧ env' = env)
Proof
  Induct_on `css` >> rw[find_match_list_def]
  >- (gvs[AllCaseEqs(), PULL_EXISTS] >> eq_tac >> rw[]) >>
  PairCases_on `h` >> gvs[find_match_list_def] >>
  IF_CASES_TAC >> gvs[] >> eq_tac >> rw[]
QED

Theorem find_match_SOME:
  find_match v env x css usopt = SOME (env', e) ⇔
  ¬ MEM x (FLAT (MAP (FST o SND) css)) ∧ css ≠ [] ∧
  ∃cn vs. v = Constructor cn vs ∧
          find_match_list cn vs env css usopt = SOME (env', e)
Proof
  simp[find_match_def, AllCaseEqs()] >> eq_tac >> rw[]
QED

Theorem ForceMutK_sanity:
  oEL n st = SOME (ThunkMem NotEvaluated f) ⇒
  step_n 1 (application ForceMutThunk [Atom (Loc n)] (SOME st) k) =
    application AppOp [f; Constructor "" []] (SOME st) (ForceMutK n :: k)
Proof[exclude_simps = step_n_1]
  strip_tac >>
  simp[Once application_def, value_def] >>
  simp[step_n_def, step_def, return_def]
QED


(* step' *)

Definition return'_def:
  return' avoid v st (ForceK1 :: k) =
    (if v ∈ avoid then error st k else
     case dest_anyThunk v of
     | NONE => error st k
     | SOME (INL v, _) => value v st k
     | SOME (INR (env, x), fns) => continue (mk_rec_env fns env) x NONE (ForceK2 st :: k)) ∧
  return' avoid v st rest = return v st rest
End

Definition step'_def:
  step' avoid st k (Val v) = return' avoid v st k ∧
  step' avoid st k x = step st k x
End

Definition step'_n_def:
  step'_n n avoid (sr, st, k) = FUNPOW (λ(sr, st, k). step' avoid st k sr) n (sr, st, k)
End

Theorem step'_n_add:
  ∀m n x. step'_n (m + n) avoid x = step'_n m avoid (step'_n n avoid x)
Proof
  gvs [step'_n_def,FORALL_PROD,FUNPOW_ADD] \\ rw []
  \\ AP_THM_TAC \\ gvs [FUN_EQ_THM,FORALL_PROD,step'_n_def]
QED

Theorem step'_n_SUC:
  step'_n (SUC n) avoid x = step'_n n avoid (step'_n 1 avoid x)
Proof
  fs [ADD1,step'_n_add]
QED

Theorem step'_n_0[simp]:
  step'_n 0 avoid x = x
Proof
  PairCases_on ‘x’ \\ fs [step'_n_def]
QED

Theorem step'_n_1[simp]:
  step'_n 1 avoid x = step' avoid (FST (SND x)) (SND (SND x)) (FST x)
Proof
  PairCases_on ‘x’ \\ fs [step'_n_def]
QED

Theorem is_halt_step'_same:
  ∀sr st k avoid. is_halt (sr,st,k) ⇒ step' avoid st k sr = (sr,st,k)
Proof
  Cases
  \\ gvs [oneline is_halt_def,AllCaseEqs(),step'_def,return'_def,step]
QED

Theorem is_halt_step'_n_same:
  ∀n x. is_halt x ⇒ step'_n n avoid x = x
Proof
  Induct \\ fs [FORALL_PROD,is_halt_step'_same,step'_n_def,FUNPOW]
QED

Theorem step'_n_mono:
  ∀n avoid res.
    is_halt (step'_n n avoid res) ⇒
      ∀m. n < m ⇒ step'_n n avoid res = step'_n m avoid res
Proof
  rw [] \\ Induct_on ‘m’ \\ gvs []
  \\ PairCases_on ‘res’ \\ gvs [step'_n_def, FUNPOW_SUC]
  \\ Cases_on ‘n = m’ \\ gvs []
  \\ pairarg_tac \\ gvs [is_halt_step'_same]
  \\ strip_tac \\ gvs [is_halt_step'_same]
QED

Theorem step'_n_unfold:
  (∃n. k = n + 1 ∧ step'_n n avoid (step' avoid st c sr) = res) ⇒
  step'_n k avoid (sr,st,c) = res
Proof
  Cases_on ‘k’ >- fs []
  \\ rewrite_tac [step'_n_def,FUNPOW]
  \\ fs [ADD1]
  \\ Cases_on ‘step' avoid st c sr’ \\ Cases_on ‘r’
  \\ fs [step'_n_def]
QED

Theorem step_m'_Error[simp]:
  ∀n. step'_n n avoid (Error,ts,tk) = (Error,ts,tk)
Proof
  Induct \\ gvs [step'_n_def,FUNPOW,step'_def,step]
QED

Theorem step'_n_IMP_step_n:
  ∀n avoid x r y z.
    step'_n n avoid x = (r,y,z) ∧ r ≠ Error ⇒
    step_n n x = (r,y,z)
Proof
  Induct \\ gvs [step'_n_def,step_n_def,FORALL_PROD,FUNPOW] \\ rw []
  \\ ‘∃q. step' avoid p_1' p_2 p_1 = q’ by gvs []
  \\ PairCases_on ‘q’ \\ gvs []
  \\ ‘∃t. step p_1' p_2 p_1 = t’ by gvs []
  \\ PairCases_on ‘t’ \\ gvs []
  \\ gvs [GSYM step'_n_def,GSYM step_n_def]
  \\ Cases_on ‘q0 = Error’ \\ gvs []
  \\ qsuff_tac ‘(q0,q1,q2) = (t0,t1,t2)’
  >- (gvs [] \\ metis_tac [])
  \\ last_x_assum kall_tac
  \\ gvs [oneline step'_def,AllCaseEqs(),oneline return'_def,
          step_def,return_def,error_def]
QED

Theorem step'_append_cont:
  step' avoid ts k e = (res,ts1,k1) ∧ ¬is_halt (res,ts1,k1) ⇒
    step' avoid ts (k ++ k2) e = (res,ts1,k1 ++ k2)
Proof
  Cases_on ‘e’ \\ strip_tac \\ gvs [step'_def, step_append_cont]
  \\ Cases_on ‘k’ \\ gvs [return'_def, step]
  \\ Cases_on ‘h’ \\ gvs [return'_def, step, AllCaseEqs()]
  >~ [‘AppK’] >- (
    Cases_on ‘l1’ \\ gvs [step]
    \\ IF_CASES_TAC \\ gvs [step]
    \\ Cases_on ‘s’ \\ gvs [step, AllCaseEqs()])
  >~ [‘LetK’] >- (Cases_on ‘o'’ \\ gvs [step])
QED

Theorem step'_n_append_cont:
  ∀n avoid e ts k res ts1 k1.
    step'_n n avoid (e,ts,k) = (res,ts1,k1) ∧ ~is_halt (res,ts1,k1) ⇒
    ∀k2. step'_n n avoid (e,ts,k ++ k2) = (res,ts1,k1 ++ k2)
Proof
  completeInduct_on ‘n’ \\ rw []
  \\ Cases_on ‘n’ \\ gvs [step'_n_def, FUNPOW] \\ rw []
  \\ ‘∃x. step' avoid ts k e = x’ by gvs [] \\ PairCases_on ‘x’ \\ gvs []
  \\ ‘∃y. step' avoid ts (k ++ k2) e = y’ by gvs []
  \\ PairCases_on ‘y’ \\ gvs []
  \\ gvs [GSYM step'_n_def, PULL_FORALL]
  \\ Cases_on ‘is_halt (x0,x1,x2)’ \\ gvs [is_halt_step'_n_same]
  \\ drule_all step'_append_cont \\ rw [] \\ gvs []
QED

Triviality step'_not_ForceK1:
  v1 ∉ avoid ∧
  step' avoid s k x = (r0,r1,r2) ∧
  (∀ts. x = Val v1 ⇒ k ≠ ForceK1::ts) ⇒
    step' (v1 INSERT avoid) s k x = (r0,r1,r2)
Proof
  rw []
  \\ Cases_on ‘x’ \\ gvs [step'_def]
  \\ Cases_on ‘k’ \\ gvs [return'_def]
  \\ Cases_on ‘h’ \\ gvs [return'_def]
QED

Theorem add_to_avoid:
  ∀m avoid x s k v v1.
    v1 ∉ avoid ∧
    step'_n m avoid (x,s,k) = (Val v,NONE,[]) ∧
    (∀n s1 ts. step'_n n avoid (x,s,k) ≠ (Val v1,s1,ForceK1::ts)) ⇒
    step'_n m (v1 INSERT avoid) (x,s,k) = (Val v,NONE,[])
Proof
  completeInduct_on ‘m’ \\ rw [] \\ gvs []
  \\ Cases_on ‘m’ \\ gvs [step'_n_def, FUNPOW]
  \\ ‘∃r. step' avoid s k x = r’ by gvs [] \\ PairCases_on ‘r’ \\ gvs []
  \\ ‘∃r'. step' (v1 INSERT avoid) s k x = r'’ by gvs []
  \\ PairCases_on ‘r'’ \\ gvs []
  \\ gvs [GSYM step'_n_def]
  \\ first_assum $ qspec_then ‘0’ assume_tac \\ fs []
  \\ drule_all step'_not_ForceK1 \\ rw []
  \\ pop_assum kall_tac
  \\ last_x_assum $ qspec_then ‘n’ assume_tac \\ gvs []
  \\ pop_assum irule \\ rw [] \\ gvs []
  \\ first_x_assum $ qspec_then ‘n' + 1’ assume_tac \\ gvs []
  \\ pop_assum $ qspecl_then [‘s1’,‘ts’] assume_tac \\ gvs []
  \\ gvs [GSYM ADD1, step'_n_def, FUNPOW]
QED

Triviality step'_n_not_halt_mul:
  ∀m n avoid x s k.
    (∀k1. ¬is_halt (x,s,k1)) ∧
    (∀k. ∃k1. step'_n n avoid (x,s,k) = (x,s,k1)) ⇒
    ∃k1. step'_n (m * n) avoid (x,s,k) = (x,s,k1)
Proof
  Induct \\ rw [] \\ gvs []
  \\ simp [ADD1, LEFT_ADD_DISTRIB, step'_n_add]
  \\ last_x_assum drule_all \\ rw []
  \\ pop_assum $ qspec_then ‘k’ assume_tac \\ gvs []
QED

Theorem step'_n_INSERT:
  step'_n m avoid (Exp (mk_rec_env x1 y0) y1,NONE,[]) = (Val v,NONE,[]) ∧
  dest_anyThunk v1 = SOME (INR (y0,y1),x1) ⇒
    step'_n m (v1 INSERT avoid) (Exp (mk_rec_env x1 y0) y1,NONE,[]) =
      (Val v,NONE,[])
Proof
  Cases_on ‘v1 ∈ avoid’
  >- (
    ‘v1 INSERT avoid = avoid’ by (
      gvs [pred_setTheory.EXTENSION] \\ metis_tac [])
    \\ gvs [])
  \\ strip_tac
  \\ Cases_on ‘∃n s1 ts. step'_n n avoid (Exp (mk_rec_env x1 y0) y1,NONE,[]) =
                      (Val v1,s1,ForceK1::ts)’ \\ gvs []
  >- (
    dxrule step'_n_append_cont \\ gvs [] \\ strip_tac
    \\ ‘∀k2. ∃k3.
          step'_n (n+1) avoid (Exp (mk_rec_env x1 y0) y1,NONE,k2) =
            (Exp (mk_rec_env x1 y0) y1,NONE,k3)’ by (
      once_rewrite_tac [ADD_COMM]
      \\ asm_rewrite_tac [step'_n_add]
      \\ gvs [step'_n_1,step'_def,return'_def,continue_def,mk_rec_env_def])
    \\ pop_assum mp_tac \\ pop_assum kall_tac \\ strip_tac
    \\ qsuff_tac ‘F’ \\ gvs []
    \\ dxrule_at Any step'_n_not_halt_mul \\ rpt strip_tac \\ gvs []
    \\ pop_assum $ qspecl_then [‘m + 1’, ‘[]’] assume_tac \\ gvs []
    \\ ‘is_halt (step'_n m avoid (Exp (mk_rec_env x1 y0) y1,NONE,[]))’
      by gvs []
    \\ drule step'_n_mono \\ rw []
    \\ qexists ‘(m + 1) * (n + 1)’ \\ gvs [])
  \\ gvs [add_to_avoid]
QED

Theorem is_halt_imp_eq':
  is_halt (step'_n n avoid res) ∧ is_halt (step'_n m avoid res) ⇒
  step'_n n avoid res = step'_n m avoid res
Proof
  ‘n < m ∨ m = n ∨ m < n’ by decide_tac
  \\ metis_tac [step'_n_mono]
QED

Theorem step'_n_fast_forward_gen:
  ∀m2 sr ss k' ss2 sk2 k sr1 ss1 sk1 n v2.
  step_n m2 (sr,ss,k') = (Val v2,ss2,sk2) ∧
  step'_n n avoid (sr,ss,k) = (sr1,ss1,sk1) ∧ is_halt (sr1,ss1,sk1) ∧
  k' ≼ k ∧ sr1 ≠ Error
  ⇒
  ∃m3. m3 ≤ n ∧ step'_n m3 avoid (Val v2,ss2,sk2 ++ DROP (LENGTH k') k) = (sr1,ss1,sk1)
Proof
  Induct >> rpt strip_tac
  >- (irule_at (Pos hd) LESS_EQ_REFL >>
      gvs[rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.DROP_APPEND2]) >>
  gvs[ADD1,step'_n_add,step_n_add] >>
  rename [‘step s k' sr’] >>
  ‘∃x y z. step s k' sr = (x,y,z)’ by metis_tac[PAIR] >>
  drule step_fast_forward_lemma >>
  disch_then(drule_at (Pos last)) >>
  impl_tac >- (rw[] >> gvs[is_halt_step_n_same]) >>
  reverse strip_tac
  >- (gvs[] >> metis_tac[]) >>
  Cases_on ‘n’
  >- (drule_then assume_tac is_halt_step'_same >>
      gvs[] >>
      drule_all_then assume_tac is_halt_prefix >>
      gvs[is_halt_step_n_same,is_halt_step_same]) >>
  gvs[ADD1,step'_n_add] >>
  ‘step' avoid s k sr = step s k sr’ by
   (Cases_on ‘sr’ \\ gvs [step'_def]
    \\ Cases_on ‘k’ \\ gvs [return'_def,step]
    \\ Cases_on ‘h’ \\ gvs [return'_def,step]
    \\ rw [] \\ gvs []) >>
  gvs [] >>
  first_x_assum drule >>
  disch_then drule >>
  simp[] >>
  gvs[] >>
  gvs[rich_listTheory.DROP_APPEND2] >>
  strip_tac >>
  first_x_assum(irule_at (Pos last)) >>
  simp[]
QED

Theorem step'_n_fast_forward:
  step'_n n avoid (sr,ss,k::ks) = (sr1,ss1,sk1) ∧ is_halt (sr1,ss1,sk1) ∧
  step_n m2 (sr,ss,[]) = (Val v2,ss2,[]) ∧ sr1 ≠ Error ⇒
  ∃m3. m3 ≤ n ∧ step'_n m3 avoid (Val v2,ss2,k::ks) = (sr1,ss1,sk1)
Proof
  rpt strip_tac >>
  drule_at (Pat ‘is_halt’) step'_n_fast_forward_gen >>
  rpt $ disch_then dxrule >> rw[]
QED

Theorem step'_n_eq:
  ∀n x. step'_n n {} x = step_n n x
Proof
  Induct \\ gvs [step_n_def,step'_n_def,FORALL_PROD,FUNPOW_SUC]
  \\ rw [] \\ AP_THM_TAC \\ gvs [FUN_EQ_THM]
  \\ Cases \\ gvs [step'_def]
  \\ Cases_on ‘k’ \\ gvs [return'_def,return_def,step_def]
  \\ Cases_on ‘h’ \\ gvs [return'_def,return_def,step_def]
QED

Theorem step_n_IMP_step'_n:
  step_n n x = y ⇒ step'_n n {} x = y
Proof
  gvs [step'_n_eq]
QED

Theorem step'_NONE_Val:
  step' avoid NONE (forceK2_none h::xs) (Val v) = (x0,x1,x2) ∧ x0 ≠ Error ⇒
  ∃xs1. x2 = MAP forceK2_none xs1 ++ xs ∧ x1 = NONE ∧
        (∀e. x0 ≠ Exn e) ∧ (∀e a. x0 ≠ Action e a) ∧
        ∀ys. step' avoid NONE (forceK2_none h::ys) (Val v) =
               (x0,x1,MAP forceK2_none xs1 ++ ys)
Proof
  Cases_on ‘h’ \\ fs [] \\ fs [step_def,step'_def] \\ strip_tac
  \\ gvs [return'_def,return_def |> DefnBase.one_line_ify NONE,AllCaseEqs(),
          forceK2_none_def |> DefnBase.one_line_ify NONE,AllCaseEqs(),
          continue_def,error_def,value_def,push_def]
  \\ rename [‘num_args_ok s’]
  \\ Cases_on ‘s’ \\ gvs [num_args_ok_def,LENGTH_EQ_NUM_compute]
  \\ gvs [application_def,AllCaseEqs(),error_def,continue_def,value_def]
QED

Theorem step_NONE_Exp:
  step NONE xs (Exp l e) = (x0,x1,x2) ∧ x0 ≠ Error ⇒
  ∃xs1. x2 = MAP forceK2_none xs1 ++ xs ∧ x1 = NONE ∧
        (∀e. x0 ≠ Exn e) ∧ (∀e a. x0 ≠ Action e a) ∧
        ∀ys. step NONE ys (Exp l e) = (x0,x1,MAP forceK2_none xs1 ++ ys)
Proof
  Cases_on ‘e’
  >~ [‘Let opt’] >-
   (Cases_on ‘opt’
    \\ fs [step_def,AllCaseEqs()] \\ rw []
    \\ gvs [error_def,value_def,continue_def,push_def]
    \\ gvs [forceK2_none_def |> DefnBase.one_line_ify NONE,AllCaseEqs()])
  >~ [‘Case _ _ rows’] >-
   (Cases_on ‘rows’
    \\ fs [step_def,AllCaseEqs()] \\ rw []
    \\ gvs [error_def,value_def,continue_def,push_def]
    \\ gvs [forceK2_none_def |> DefnBase.one_line_ify NONE,AllCaseEqs()])
  >~ [‘App’] >-
   (fs [step_def,AllCaseEqs()] \\ rw [] \\ gvs [error_def,push_def]
    \\ gvs [forceK2_none_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
    \\ Cases_on ‘s’ \\ gvs [num_args_ok_def]
    \\ gvs [application_def,value_def,AllCaseEqs(),error_def,get_atoms_def])
  \\ fs [step_def,AllCaseEqs()] \\ rw []
  \\ gvs [error_def,value_def,continue_def,push_def]
  \\ gvs [forceK2_none_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
QED

Theorem step'_n_NONE_split:
  ∀avoid.
    step'_n n avoid (Exp env x,NONE,k::tk) = (r,z) ∧ is_halt (r,z) ∧ r ≠ Error ⇒
    ∃m1 m2 v.
      step'_n m1 avoid (Exp env x,NONE,[]) = (Val v,NONE,[]) ∧ m1 < n ∧
      step'_n m2 avoid (Val v,NONE,k::tk) = (r,z) ∧ m2 ≤ n
Proof
  gen_tac
  \\ qsuff_tac ‘
    ∀n xs te k tk r z.
      step'_n n avoid (te,NONE,MAP forceK2_none xs ++ k::tk) = (r,z) ∧ te ≠ Error ∧
      ~is_halt (te,NONE,MAP forceK2_none xs) ∧
      (∀e. te ≠ Exn e) ∧ (∀e a. te ≠ Action e a) ∧ is_halt (r,z) ∧ r ≠ Error ⇒
      ∃m1 m2 v.
        step'_n m1 avoid (te,NONE,MAP forceK2_none xs) = (Val v,NONE,[]) ∧ m1 < n ∧
        step'_n m2 avoid (Val v,NONE,k::tk) = (r,z) ∧ m2 ≤ n’
  >-
   (rw []
    \\ last_x_assum $ qspecl_then [‘n’,‘[]’] mp_tac \\ fs []
    \\ disch_then drule \\ fs []
    \\ strip_tac
    \\ first_x_assum $ irule_at $ Pos $ hd \\ fs []
    \\ first_x_assum $ irule_at $ Pos $ hd \\ fs [])
  \\ strip_tac
  \\ completeInduct_on ‘n’ \\ rw []
  \\ reverse (Cases_on ‘te’) \\ fs []
  >-
   (Cases_on ‘xs’
    \\ gvs [] \\ Cases_on ‘n’ \\ gvs [step'_n_SUC]
    \\ ‘∃x. step' avoid NONE (forceK2_none h::(MAP forceK2_none t ++ k::tk))
              (Val v) = x’ by fs []
    \\ PairCases_on ‘x’ \\ fs []
    \\ Cases_on ‘x0 = Error’
    >-
     (‘is_halt (Error,x1,x2)’ by fs []
      \\ qpat_x_assum ‘_ = (r,_)’ mp_tac
      \\ DEP_REWRITE_TAC [is_halt_step'_n_same] \\ fs [])
    \\ drule_all step'_NONE_Val \\ strip_tac \\ gvs []
    \\ Q.REFINE_EXISTS_TAC ‘SUC m3’ \\ fs [step'_n_SUC]
    \\ rename [‘step'_n n’]
    \\ full_simp_tac bool_ss [GSYM MAP_APPEND]
    \\ Cases_on ‘is_halt (x0,NONE,MAP forceK2_none xs1 ++ MAP forceK2_none t)’
    >-
     (Cases_on ‘x0’ \\ gvs []
      \\ qexists_tac ‘0’ \\ fs []
      \\ qexists_tac ‘n’ \\ fs []
      \\ Cases_on ‘n’ \\ gvs [])
    \\ first_x_assum $ drule_at $ Pos $ el 2
    \\ impl_tac >- fs []
    \\ rw []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
  \\ gvs []
  \\ Cases_on ‘n’ \\ gvs [step'_n_SUC]
  \\ rename [‘step'_n n’]
  \\ ‘∃x. step' avoid NONE (MAP forceK2_none xs ++ k::tk) (Exp l e) = x’ by fs []
  \\ PairCases_on ‘x’ \\ fs []
  \\ Cases_on ‘x0 = Error’
  >-
   (‘is_halt (Error,x1,x2)’ by fs []
    \\ qpat_x_assum ‘_ = (r,_)’ mp_tac
    \\ DEP_REWRITE_TAC [is_halt_step'_n_same] \\ fs [])
  \\ gvs [step'_def]
  \\ drule_all step_NONE_Exp \\ strip_tac \\ gvs []
  \\ Q.REFINE_EXISTS_TAC ‘SUC m3’ \\ fs [step'_n_SUC,step'_def]
  \\ full_simp_tac bool_ss [GSYM MAP_APPEND]
  \\ Cases_on ‘is_halt (x0,NONE,MAP forceK2_none xs1 ++ MAP forceK2_none xs)’
  >-
   (Cases_on ‘x0’ \\ gvs []
    \\ qexists_tac ‘0’ \\ fs []
    \\ qexists_tac ‘n’ \\ fs []
    \\ Cases_on ‘n’ \\ gvs [])
  \\ first_x_assum $ drule_at $ Pos $ el 2
  \\ impl_tac >- fs []
  \\ rw []
  \\ first_x_assum $ irule_at $ Pos hd \\ fs []
  \\ first_x_assum $ irule_at $ Pos $ hd \\ fs []
QED

Theorem step_n_NONE_split:
  step_n n (Exp env x,NONE,k::tk) = (r,z) ∧ is_halt (r,z) ∧ r ≠ Error ⇒
  ∃m1 m2 v.
    step_n m1 (Exp env x,NONE,[]) = (Val v,NONE,[]) ∧ m1 < n ∧
    step_n m2 (Val v,NONE,k::tk) = (r,z) ∧ m2 ≤ n
Proof
  qspec_then ‘{}’ assume_tac step'_n_NONE_split
  \\ gvs [step'_n_eq]
QED

(* meaning of cexp *)

Definition sop_of_def[simp]:
  sop_of (AppOp:csop) = (AppOp:sop) ∧
  sop_of (Cons n) = Cons (explode n) ∧
  sop_of (AtomOp m) = AtomOp m ∧
  sop_of Alloc = Alloc ∧
  sop_of Length = Length ∧
  sop_of Sub = Sub ∧
  sop_of Update = Update ∧
  sop_of (AllocMutThunk Evaluated) = (AllocMutThunk Evaluated) ∧
  sop_of (AllocMutThunk NotEvaluated) = (AllocMutThunk NotEvaluated) ∧
  sop_of (UpdateMutThunk Evaluated) = (UpdateMutThunk Evaluated) ∧
  sop_of (UpdateMutThunk NotEvaluated) = (UpdateMutThunk NotEvaluated) ∧
  sop_of ForceMutThunk = ForceMutThunk ∧
  sop_of (FFI s) = FFI (explode s)
End

Definition exp_of_def:
  exp_of ((Var n):cexp) = (Var (explode n)):exp ∧
  exp_of (App op xs) = App (sop_of op) (MAP exp_of xs) ∧
  exp_of (Lam vn x) = Lam (OPTION_MAP explode vn) (exp_of x) ∧
  exp_of (Letrec funs x) =
    Letrec (MAP (λ(f,v,y). (explode f,Lam (SOME (explode v)) (exp_of y))) funs) (exp_of x) ∧
  exp_of (Let vn x y) = Let (OPTION_MAP explode vn) (exp_of x) (exp_of y) ∧
  exp_of (If x y z) = If (exp_of x) (exp_of y) (exp_of z) ∧
  exp_of (Case v rows d) =
    Case (explode v)
         (MAP (λ(v,vs,y). (explode v,MAP explode vs,exp_of y)) rows)
         (OPTION_MAP (λ(alts,e). (MAP (explode ## I) alts, exp_of e)) d) ∧
  exp_of (Raise x) = Raise (exp_of x) ∧
  exp_of (Handle x v y) = Handle (exp_of x) (explode v) (exp_of y) ∧
  exp_of (HandleApp x y) = HandleApp (exp_of x) (exp_of y)
Termination
  WF_REL_TAC ‘measure cexp_size’
End

Theorem exp_of_def[simp,allow_rebind] = exp_of_def |> CONV_RULE (DEPTH_CONV ETA_CONV);
