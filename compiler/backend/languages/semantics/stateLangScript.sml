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

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory pure_semanticsTheory arithmeticTheory
     state_cexpTheory mlstringTheory;

val _ = new_theory "stateLang";

val _ = set_grammar_ancestry ["pure_semantics","state_cexp"];

val _ = numLib.prefer_num();


(******************** Datatypes ********************)

Datatype:
  sop = (* Primitive operations *)
      | AppOp              (* function application                     *)
      | Cons string        (* datatype constructor                     *)
      | AtomOp atom_op     (* primitive parametric operator over Atoms *)
      | Proj string num    (* projection                               *)
      | IsEq string num    (* check whether same data constructor      *)
      | Alloc              (* allocate an array                        *)
      | Ref                (* allocates an array in a different way    *)
      | Length             (* query the length of an array             *)
      | Sub                (* de-reference a value in an array         *)
      | UnsafeSub          (* de-reference but without a bounds check  *)
      | Update             (* update a value in an array               *)
      | UnsafeUpdate       (* update without a bounds check            *)
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

Type state[pp] = ``:(v list) list``; (* state *)

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
    ((case d of SOME (_,e) => freevars e | _ => {}) ∪
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
  num_args_ok UnsafeSub n = (n = 2) ∧
  num_args_ok Alloc n = (n = 2) ∧
  num_args_ok Ref n = T ∧
  num_args_ok Length n = (n = 1) ∧
  num_args_ok Update n = (n = 3) ∧
  num_args_ok UnsafeUpdate n = (n = 3) ∧
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
  application AppOp env vs (st:state option) k = (
    case dest_anyClosure (HD vs) of
    | NONE => error st k
    | SOME (arg, env', e) =>
        continue (opt_bind arg (EL 1 vs) env') e st k) ∧
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
  application Alloc env vs st k = (
    case HD vs, st of
      Atom (Int i), SOME arrays =>
        let n = if i < 0 then 0 else Num i in
        value (Atom $ Loc $ LENGTH arrays)
          (SOME (SNOC (REPLICATE n (EL 1 vs)) arrays)) k
    | _ => error st k) ∧
  application Ref env vs st k = (
    case st of
      SOME arrays =>
        value (Atom $ Loc $ LENGTH arrays)
          (SOME (SNOC vs arrays)) k
    | _ => error st k) ∧
  application Length env vs st k = (
    case HD vs, st of
      Atom (Loc n), SOME arrays => (
        case oEL n arrays of
          SOME l => value (Atom $ Int $ & LENGTH l) st k
        | _ => error st k)
    | _ => error st k) ∧
  application (Proj s i) env vs st k = (
    case HD vs of
      Constructor t ys => (
        if t = s ∧ i < LENGTH ys then
          value (EL i ys) st k
        else error st k)
    | _ => error st k) ∧
  application (IsEq s i) env vs st k = (
    case HD vs of
      Constructor t ys => (
        if t = s ⇒ i = LENGTH ys then
          value (Constructor (if t = s then "True" else "False") []) st k
        else error st k)
    | _ => error st k) ∧
  application Sub env vs st k = (
    case (EL 0 vs, EL 1 vs, st) of
      (Atom $ Loc n, Atom $ Int i, SOME arrays) => (
        case oEL n arrays of
          SOME l =>
            if 0 ≤ i ∧ i < & LENGTH l then
              value (EL (Num i) l) st k
            else
              (Exn (Constructor "Subscript" []), st, k)
        | _ => error st k)
    | _ => error st k) ∧
  application UnsafeSub env vs st k = (
    case (EL 0 vs, EL 1 vs, st) of
      (Atom $ Loc n, Atom $ Int i, SOME arrays) => (
        case oEL n arrays of
          SOME l =>
            if 0 ≤ i ∧ i < & LENGTH l then
              value (EL (Num i) l) st k
            else
              error st k
        | _ => error st k)
    | _ => error st k) ∧
  application Update env vs st k = (
    case (EL 0 vs, EL 1 vs, st) of
      (Atom $ Loc n, Atom $ Int i, SOME arrays) => (
        case oEL n arrays of
          SOME l =>
            if 0 ≤ i ∧ i < & LENGTH l then
              value
                (Constructor "" [])
                (SOME (LUPDATE (LUPDATE (EL 2 vs) (Num i) l) n arrays))
                k
            else
              (Exn (Constructor "Subscript" []), st, k)
        | _ => error st k)
    | _ => error st k) ∧
  application UnsafeUpdate env vs st k = (
    case (EL 0 vs, EL 1 vs, st) of
      (Atom $ Loc n, Atom $ Int i, SOME arrays) => (
        case oEL n arrays of
          SOME l =>
            if 0 ≤ i ∧ i < & LENGTH l then
              value
                (Constructor "" [])
                (SOME (LUPDATE (LUPDATE (EL 2 vs) (Num i) l) n arrays))
                k
            else
              error st k
        | _ => error st k)
    | _ => error st k) ∧
  application (FFI channel) env vs st k = (
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
    application sop env vs st k) ∧
  return v st (AppK env sop vs (e::es) :: k) =
    continue env e st (AppK env sop (v::vs) es :: k) ∧
  return v st (ForceK1 :: k) =
    (case dest_anyThunk v of
     | NONE => error st k
     | SOME (INL v, _) => value v st k
     | SOME (INR (env, x), fns) => continue (mk_rec_env fns env) x NONE (ForceK2 st :: k)) ∧
  return v temp_st (ForceK2 st :: k) = value v st k ∧
  return v st (BoxK :: k) = value (Thunk $ INL v) st k
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
        application sop env [] st k
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

Theorem step_n_unfold:
  (∃n. k = n + 1 ∧ step_n n (step st c sr) = res) ⇒
  step_n k (sr,st,c) = res
Proof
  Cases_on ‘k’ >- fs []
  \\ rewrite_tac [step_n_def,FUNPOW]
  \\ fs [ADD1]
  \\ Cases_on ‘step st c sr’ \\ Cases_on ‘r’
  \\ fs [step_n_def]
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
  application p env vs st k = (Action channel content,st1,k1) ⇒
  p = FFI channel ∧ ∃st1. st = SOME st1
Proof
  fs [application_def |> DefnBase.one_line_ify NONE, AllCaseEqs(), error_def, value_def]
  \\ rw [] \\ fs []
  \\ fs [continue_def]
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
  ∀sop env vs st k x y z k'.
  application sop env vs st k = (x,y,z) ∧ num_args_ok sop (LENGTH vs) ∧ k' ≼ k ⇒
  ∃x' y' z'. application sop env vs st k' = (x',y',z') ∧
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

Definition forceK2_none_def[simp]:
  forceK2_none (ForceK2 _) = ForceK2 NONE ∧
  forceK2_none y = y
End

Theorem application_NONE:
  application Alloc env [v1;v2] NONE s = (Error,NONE,s) ∧
  application Ref env vs NONE s = (Error,NONE,s) ∧
  application Length env [v1] NONE s = (Error,NONE,s) ∧
  application Sub env [v1;v2] NONE s = (Error,NONE,s) ∧
  application UnsafeSub env [v1;v2] NONE s = (Error,NONE,s) ∧
  application Update env [v1;v2;v3] NONE s = (Error,NONE,s) ∧
  application UnsafeUpdate env [v1;v2;v3] NONE s = (Error,NONE,s) ∧
  application (FFI f) env [v1] NONE s = (Error,NONE,s)
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
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
    \\ strip_tac \\ fs [])
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
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ impl_tac >- fs []
    \\ strip_tac \\ fs [])
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
  >~ [‘Ref’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  >~ [‘Length’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  >~ [‘Sub’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  >~ [‘UnsafeSub’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  >~ [‘Update’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ Cases_on ‘vs’ \\ fs [] \\ Cases_on ‘t'’ \\ fs [] \\ Cases_on ‘t''’ \\ fs []
    \\ gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  >~ [‘UnsafeUpdate’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ Cases_on ‘vs’ \\ fs [] \\ Cases_on ‘t'’ \\ fs [] \\ Cases_on ‘t''’ \\ fs []
    \\ gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
  >~ [‘FFI’] >-
   (gvs [application_NONE,num_args_ok_def,LENGTH_EQ_NUM_compute,value_def]
    \\ fs [step_n_Val,step_n_Error,error_def,GSYM step_n_def])
QED

Theorem application_set_cont[local]:
  ∀sop env vs st k' sr k x y z.
  application sop env vs st k' = (x,y,z) ∧ x ≠ Error ∧ (∀v. x = Exn v ⇒ z ≠ []) ⇒ k' ≼ k ⇒
  application sop env vs st k = (x,y,z ++ DROP (LENGTH k') k)
Proof
  Cases >> rw[step] >>
  gvs[AllCaseEqs(),dest_Closure_def,quantHeuristicsTheory.LIST_LENGTH_1,
        rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.DROP_APPEND2,
        APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)]
QED

Theorem step_pres_cons_NIL:
  step ts [] (Exp l e) = (res,ts1,[]) ⇒
  step ts k (Exp l e) = (res,ts1,k)
Proof
  Cases_on ‘e’
  \\ fs [step_def,error_def,value_def,continue_def,AllCaseEqs(),push_def]
  \\ rw [] \\ fs []
  \\ Cases_on ‘s’ \\ fs [num_args_ok_def]
  \\ fs [application_def,value_def]
  \\ every_case_tac \\ fs [error_def,return_def]
QED

Theorem step_inc_cont:
  step ts (k0::k1) te = (x0,x1,k2) ∧ LENGTH k1 + 1 < LENGTH k2 ⇒
  ∃k. k2 = k::k0::k1 ∧ ∀k3. step ts (k0::k3) te = (x0,x1,k::k0::k3)
Proof
  Cases_on ‘te’ \\ fs [step_def] \\ fs [error_def]
  >~ [‘Exp l e’] >-
   (Cases_on ‘e’
    \\ fs [step_def] \\ fs [error_def,value_def,continue_def,push_def]
    \\ rw [] \\ fs []
    \\ gvs [AllCaseEqs()]
    \\ Cases_on ‘s’ \\ gvs [num_args_ok_def,LENGTH_EQ_NUM_compute]
    \\ gvs [application_def,value_def,AllCaseEqs(),error_def,return_def])
  >~ [‘Exn’] >-
   (Cases_on ‘k0’ \\ fs [continue_def,push_def] \\ rw[] \\ gvs[])
  \\ rw [] \\ fs []
  \\ Cases_on ‘k0’ \\ fs [return_def]
  \\ gvs [AllCaseEqs(),continue_def,error_def,value_def]
  \\ gvs [return_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
  \\ gvs [AllCaseEqs(),continue_def,error_def,value_def]
  \\ Cases_on ‘s’ \\ gvs [num_args_ok_def,LENGTH_EQ_NUM_compute]
  \\ gvs [application_def,AllCaseEqs(),error_def,continue_def,value_def]
QED

Theorem step_inc_nil:
  step ts [] te = (x0,x1,h::t) ∧ ¬is_halt (te,ts,[]:cont list) ⇒
  t = [] ∧ ∀k. step ts k te = (x0,x1,h::k)
Proof
  Cases_on ‘te’ \\ strip_tac
  \\ gvs [step_def,error_def]
  \\ Cases_on ‘e’ \\ gvs [step_def,AllCaseEqs(),error_def,value_def,push_def,continue_def]
  \\ Cases_on ‘s’ \\ gvs [num_args_ok_def,LENGTH_EQ_NUM_compute]
  \\ gvs [application_def,value_def,AllCaseEqs(),error_def,value_def,push_def,continue_def]
QED

Theorem step_dec_cont:
  step ts k1 te = (x0,x1,k2) ∧ LENGTH k2 < LENGTH k1 ⇒
  ∃k. k1 = k::k2 ∧ ∀k3. step ts (k::k3) te = (x0,x1,k3)
Proof
  Cases_on ‘te’ \\ fs [step_def,error_def]
  >~ [‘Exp l e’] >-
   (Cases_on ‘e’
    >~ [‘Var’] >-
     (fs [step_def] \\ CASE_TAC \\ fs [error_def,value_def])
    \\ fs [step_def] \\ fs [error_def,value_def,continue_def,push_def]
    \\ rw [] \\ fs []
    \\ gvs [AllCaseEqs()]
    \\ Cases_on ‘s’ \\ gvs [num_args_ok_def,LENGTH_EQ_NUM_compute]
    \\ gvs [application_def,value_def,AllCaseEqs(),error_def,return_def])
  >~ [‘Exn’] >-
   (Cases_on ‘k1’ \\ fs [step_def,error_def]
    \\ Cases_on ‘h’ \\ fs [continue_def,push_def] \\ rw[] \\ gvs[])
  \\ Cases_on ‘k1’ \\ fs []
  \\ Cases_on ‘h’
  \\ fs [return_def]
  \\ rw []
  \\ fs [continue_def,error_def,value_def]
  \\ rw [] \\ gvs [AllCaseEqs(),value_def]
  \\ gvs [return_def|>DefnBase.one_line_ify NONE, AllCaseEqs(),error_def,
          continue_def,value_def]
  \\ Cases_on ‘s’ \\ gvs [num_args_ok_def,LENGTH_EQ_NUM_compute]
  \\ gvs [application_def,value_def,AllCaseEqs(),error_def,return_def]
  \\ gvs [continue_def,value_def]
QED

Theorem step_eq_cont:
  step ts (k::k1) te = (x0,x1,x2) ∧ LENGTH x2 = LENGTH (k::k1) ⇒
  ∃d. x2 = d::k1 ∧ ∀k3. step ts (k::k3) te = (x0,x1,d::k3)
Proof
  Cases_on ‘te’ \\ fs [step_def,error_def]
  >~ [‘Exp l e’] >-
   (Cases_on ‘e’
    \\ fs [step_def] \\ fs [error_def,value_def,continue_def,push_def]
    \\ rw [] \\ fs []
    \\ gvs [AllCaseEqs()]
    \\ CCONTR_TAC \\ gvs []
    \\ Cases_on ‘s’ \\ gvs [num_args_ok_def,LENGTH_EQ_NUM_compute]
    \\ gvs [application_def,value_def,AllCaseEqs(),error_def,return_def])
  >~ [‘Exn’] >-
   (rw [] \\ fs []
    \\ gvs [AllCaseEqs(),continue_def,push_def])
  \\ gvs [return_def|>DefnBase.one_line_ify NONE, AllCaseEqs(),error_def,
          continue_def,value_def] \\ rw []
  \\ fs [continue_def,error_def,value_def]
  \\ Cases_on ‘sop’ \\ gvs [num_args_ok_def,LENGTH_EQ_NUM_compute]
  \\ gvs [application_def,value_def,AllCaseEqs(),error_def,return_def]
  \\ gvs [continue_def,value_def]
QED

Triviality step_n_cont_swap_lemma:
  ∀n x0 x1 k k1 res ts1 k2.
    FUNPOW (λ(sr,st,k). step st k sr) n (x0,x1,k::k1) = (res,ts1,k2) ∧
    LENGTH k2 ≤ LENGTH k1 ⇒
    ∃m res7 ts7 k7.
      m ≤ n ∧
      FUNPOW (λ(sr,st,k). step st k sr) m (x0,x1,k::k1) = (res7,ts7,k7) ∧
      LENGTH k1 = LENGTH k7 ∧
      (∀i. i < m ⇒
        ∃res7 ts7 k7.
           FUNPOW (λ(sr,st,k). step st k sr) i (x0,x1,k::k1) = (res7,ts7,k7) ∧
           LENGTH k1 < LENGTH k7)
Proof
  completeInduct_on ‘n’
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on ‘n’ \\ fs [] \\ gvs []
  \\ fs [step_n_def,FUNPOW]
  \\ ‘∃y. step x1 (k::k1) x0 = y’ by fs [] \\ PairCases_on ‘y’ \\ fs []
  \\ Cases_on ‘LENGTH y2 < LENGTH (k::k1)’
  >-
   (drule_all step_dec_cont \\ fs [] \\ strip_tac \\ gvs []
    \\ qexists_tac ‘SUC 0’ \\ fs [])
  \\ reverse (Cases_on ‘LENGTH (k::k1) < LENGTH y2’)
  >-
   (‘LENGTH y2 = LENGTH (k::k1)’ by fs []
    \\ drule_all step_eq_cont \\ strip_tac \\ gvs []
    \\ first_x_assum $ drule_at $ Pos $ el 2
    \\ impl_tac >- fs []
    \\ strip_tac \\ fs []
    \\ qexists_tac ‘SUC m’ \\ fs [FUNPOW]
    \\ Cases \\ fs [FUNPOW]
    \\ rw [] \\ res_tac \\ fs [])
  \\ fs [ADD1]
  \\ drule_all step_inc_cont
  \\ strip_tac \\ gvs []
  \\ rename [‘FUNPOW _ n’]
  \\ last_assum $ qspec_then ‘n’ mp_tac
  \\ impl_tac >- fs []
  \\ disch_then drule
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ ‘FUNPOW (λ(sr,st,k). step st k sr) n =
      FUNPOW (λ(sr,st,k). step st k sr) ((n - m) + m)’ by fs []
  \\ full_simp_tac std_ss [FUNPOW_ADD]
  \\ pop_assum kall_tac
  \\ Cases_on ‘k7’ \\ fs []
  \\ qpat_x_assum ‘_ = (res,ts1,k2)’ assume_tac
  \\ first_x_assum $ drule_at $ Pos $ el 2
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ qexists_tac ‘SUC (m' + m)’
  \\ rewrite_tac [FUNPOW_ADD,FUNPOW]
  \\ fs []
  \\ Cases \\ fs [FUNPOW]
  \\ rw []
  \\ Cases_on ‘n' < m’ \\ res_tac \\ fs []
  \\ ‘FUNPOW (λ(sr,st,k). step st k sr) n' =
      FUNPOW (λ(sr,st,k). step st k sr) ((n' - m) + m)’ by fs []
  \\ asm_rewrite_tac [FUNPOW_ADD]
  \\ pop_assum kall_tac
  \\ gvs []
QED

Theorem step_n_cont_swap:
  ∀n te ts k k1 res ts1 k2.
    step_n n (te,ts,k::k1) = (res,ts1,k2) ∧ LENGTH k1 = LENGTH k2 ∧
    (∀m res ts1 k0.
       m < n ∧ step_n m (te,ts,k::k1) = (res,ts1,k0) ⇒ LENGTH k1 < LENGTH k0) ⇒
    ∀k3. k2 = k1 ∧ step_n n (te,ts,k::k3) = (res,ts1,k3)
Proof
  completeInduct_on ‘n’
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on ‘n’ \\ fs [] \\ gvs []
  \\ fs [step_n_def,FUNPOW]
  \\ ‘∃x. step ts (k::k1) te = x’ by fs [] \\ PairCases_on ‘x’ \\ fs []
  \\ Cases_on ‘LENGTH x2 < LENGTH (k::k1)’
  >-
   (drule_all step_dec_cont \\ fs [] \\ strip_tac \\ gvs []
    \\ Cases_on ‘n'’ \\ fs []
    \\ first_x_assum $ qspec_then ‘SUC 0’ mp_tac
    \\ fs [])
  \\ reverse (Cases_on ‘LENGTH (k::k1) < LENGTH x2’)
  >-
   (‘LENGTH x2 = LENGTH (k::k1)’ by fs []
    \\ drule_all step_eq_cont \\ strip_tac
    \\ gvs []
    \\ first_x_assum $ drule_at $ Pos $ el 2
    \\ ntac 2 strip_tac
    \\ first_x_assum irule
    \\ rw []
    \\ first_x_assum $ qspec_then ‘SUC m'’ mp_tac
    \\ fs [FUNPOW])
  \\ fs [ADD1]
  \\ drule_all step_inc_cont
  \\ strip_tac \\ gvs []
  \\ rename [‘FUNPOW _ n’]
  \\ drule step_n_cont_swap_lemma
  \\ fs [] \\ strip_tac
  \\ Cases_on ‘k7’ \\ fs [ADD1]
  \\ last_assum $ qspec_then ‘m’ mp_tac
  \\ impl_tac >- fs []
  \\ disch_then $ qspecl_then [‘x0’,‘x1’,‘k'’,‘k::k1’] mp_tac
  \\ fs [FUNPOW]
  \\ impl_tac >- (rw [] \\ res_tac \\ fs [] \\ gvs [])
  \\ strip_tac
  \\ gvs [GSYM PULL_FORALL]
  \\ last_x_assum $ qspec_then ‘n - m’ mp_tac
  \\ impl_tac >- fs []
  \\ disch_then $ qspecl_then [‘res7’,‘ts7’,‘h’,‘k1’] mp_tac
  \\ ‘FUNPOW (λ(sr,st,k). step st k sr) n =
      FUNPOW (λ(sr,st,k). step st k sr) (m + (n - m))’ by fs []
  \\ full_simp_tac std_ss []
  \\ pop_assum kall_tac
  \\ last_x_assum mp_tac
  \\ rewrite_tac [FUNPOW_ADD |> ONCE_REWRITE_RULE [ADD_COMM],PULL_FORALL]
  \\ simp [] \\ strip_tac
  \\ disch_then irule
  \\ rw []
  \\ last_x_assum irule
  \\ qexists_tac ‘SUC (m' + m)’
  \\ rewrite_tac [FUNPOW_ADD,FUNPOW]
  \\ fs []
QED

Theorem step_n_set_cont:
  step_n n (Exp tenv1 te,ts,[]) = (Val res,ts1,[]) ⇒
  ∃n5. n5 ≤ n ∧ ∀k. step_n n5 (Exp tenv1 te,ts,k) = (Val res,ts1,k)
Proof
  qsuff_tac ‘
    ∀n te ts res ts1.
      step_n n (te,ts,[]) = (Val res,ts1,[]) ∧ ~is_halt (te,ts,[]:cont list) ⇒
      ∃n5. n5 ≤ n ∧ ∀k. step_n n5 (te,ts,k) = (Val res,ts1,k)’
  >- (rw [] \\ res_tac \\ fs [])
  \\ completeInduct_on ‘n’ \\ rw []
  \\ Cases_on ‘n’ \\ fs [step_n_def,FUNPOW] \\ rw []
  \\ ‘∃x. step ts [] te = x’ by fs [] \\ PairCases_on ‘x’ \\ fs []
  \\ Cases_on ‘is_halt (x0,x1,x2)’ >-
   (gvs [GSYM step_n_def,is_halt_step_n_same]
    \\ qexists_tac ‘SUC 0’ \\ fs [] \\ rw []
    \\ last_x_assum kall_tac
    \\ Cases_on ‘te’ \\ fs []
    \\ Cases_on ‘e’
    \\ gvs [step_def,AllCaseEqs(),error_def,value_def,push_def,continue_def]
    \\ Cases_on ‘s’ \\ gvs [num_args_ok_def,LENGTH_EQ_NUM_compute]
    \\ gvs [application_def,value_def,AllCaseEqs(),error_def,get_atoms_def])
  \\ Cases_on ‘x2’ \\ fs []
  >-
   (rename [‘FUNPOW _ n’]
    \\ last_x_assum $ qspec_then ‘n’ mp_tac \\ fs []
    \\ disch_then drule \\ fs [] \\ strip_tac
    \\ qexists_tac ‘SUC n5’ \\ fs [] \\ fs [FUNPOW]
    \\ qsuff_tac ‘∀k. step ts k te = (x0,x1,k)’ >- fs []
    \\ Cases_on ‘te’ \\ gvs []
    \\ Cases_on ‘e’ \\ gvs [step_def,AllCaseEqs(),error_def,value_def,push_def,continue_def]
    \\ Cases_on ‘s’ \\ gvs [num_args_ok_def,LENGTH_EQ_NUM_compute]
    \\ gvs [application_def,value_def,error_def,AllCaseEqs(),push_def])
  \\ drule_all step_inc_nil
  \\ strip_tac \\ gvs []
  \\ drule step_n_cont_swap_lemma \\ fs [] \\ strip_tac
  \\ rename [‘m ≤ n’]
  \\ fs [GSYM step_n_def]
  \\ drule step_n_cont_swap \\ fs [GSYM PULL_FORALL]
  \\ impl_tac >- (rw [] \\ res_tac \\ fs [] \\ gvs [])
  \\ strip_tac \\ fs []
  \\ ‘step_n n = step_n ((n - m) + m)’ by fs []
  \\ full_simp_tac std_ss [step_n_add] \\ gvs []
  \\ Cases_on ‘is_halt (res7,ts7,[]:cont list)’
  >-
   (qexists_tac ‘SUC m’ \\ fs [step_n_SUC]
    \\ gvs [GSYM step_n_def,is_halt_step_n_same])
  \\ first_x_assum $ drule_at $ Pos $ el 2
  \\ impl_tac >- fs []
  \\ rw []
  \\ qexists_tac ‘SUC (n5 + m)’
  \\ full_simp_tac std_ss [step_n_add,step_n_SUC] \\ gvs []
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

Theorem step_NONE_Val:
  step NONE (forceK2_none h::xs) (Val v) = (x0,x1,x2) ∧ x0 ≠ Error ⇒
  ∃xs1. x2 = MAP forceK2_none xs1 ++ xs ∧ x1 = NONE ∧
        (∀e. x0 ≠ Exn e) ∧ (∀e a. x0 ≠ Action e a) ∧
        ∀ys. step NONE (forceK2_none h::ys) (Val v) =
               (x0,x1,MAP forceK2_none xs1 ++ ys)
Proof
  Cases_on ‘h’ \\ fs [] \\ fs [step_def] \\ strip_tac
  \\ gvs [return_def |> DefnBase.one_line_ify NONE,AllCaseEqs(),
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

Theorem step_n_NONE_split:
  step_n n (Exp env x,NONE,k::tk) = (r,z) ∧ is_halt (r,z) ∧ r ≠ Error ⇒
  ∃m1 m2 v.
    step_n m1 (Exp env x,NONE,[]) = (Val v,NONE,[]) ∧ m1 < n ∧
    step_n m2 (Val v,NONE,k::tk) = (r,z) ∧ m2 ≤ n
Proof
  qsuff_tac ‘
    ∀n xs te k tk r z.
      step_n n (te,NONE,MAP forceK2_none xs ++ k::tk) = (r,z) ∧ te ≠ Error ∧
      ~is_halt (te,NONE,MAP forceK2_none xs) ∧
      (∀e. te ≠ Exn e) ∧ (∀e a. te ≠ Action e a) ∧ is_halt (r,z) ∧ r ≠ Error ⇒
      ∃m1 m2 v.
        step_n m1 (te,NONE,MAP forceK2_none xs) = (Val v,NONE,[]) ∧ m1 < n ∧
        step_n m2 (Val v,NONE,k::tk) = (r,z) ∧ m2 ≤ n’
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
    \\ gvs [] \\ Cases_on ‘n’ \\ gvs [step_n_SUC]
    \\ ‘∃x. step NONE (forceK2_none h::(MAP forceK2_none t ++ k::tk))
              (Val v) = x’ by fs []
    \\ PairCases_on ‘x’ \\ fs []
    \\ Cases_on ‘x0 = Error’
    >-
     (‘is_halt (Error,x1,x2)’ by fs []
      \\ qpat_x_assum ‘_ = (r,_)’ mp_tac
      \\ DEP_REWRITE_TAC [is_halt_step_n_same] \\ fs [])
    \\ drule_all step_NONE_Val \\ strip_tac \\ gvs []
    \\ Q.REFINE_EXISTS_TAC ‘SUC m3’ \\ fs [step_n_SUC]
    \\ rename [‘step_n n’]
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
  \\ Cases_on ‘n’ \\ gvs [step_n_SUC]
  \\ rename [‘step_n n’]
  \\ ‘∃x. step NONE (MAP forceK2_none xs ++ k::tk) (Exp l e) = x’ by fs []
  \\ PairCases_on ‘x’ \\ fs []
  \\ Cases_on ‘x0 = Error’
  >-
   (‘is_halt (Error,x1,x2)’ by fs []
    \\ qpat_x_assum ‘_ = (r,_)’ mp_tac
    \\ DEP_REWRITE_TAC [is_halt_step_n_same] \\ fs [])
  \\ drule_all step_NONE_Exp \\ strip_tac \\ gvs []
  \\ Q.REFINE_EXISTS_TAC ‘SUC m3’ \\ fs [step_n_SUC]
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

(* meaning of cexp *)

Definition sop_of_def[simp]:
  sop_of (AppOp:csop) = (AppOp:sop) ∧
  sop_of (Cons n) = Cons (explode n) ∧
  sop_of (AtomOp m) = AtomOp m ∧
  sop_of Alloc = Alloc ∧
  sop_of Ref = Ref ∧
  sop_of Length = Length ∧
  sop_of Sub = Sub ∧
  sop_of UnsafeSub = UnsafeSub ∧
  sop_of Length = Length ∧
  sop_of Update = Update ∧
  sop_of UnsafeUpdate = UnsafeUpdate ∧
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

Theorem exp_of_def[simp] = exp_of_def |> CONV_RULE (DEPTH_CONV ETA_CONV);

val _ = export_theory ();
