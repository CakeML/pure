(*
   envLang.
   ~~~~~~~~~~

   envLang is the next language in the compiler after thunkLang. It differs
   from thunkLang in that it has an environment-based semantics, and it lacks
   the clock-tampering operations MkTick/DoTick.

   See [thunkLangScript.sml] for the thunkLang semantics.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory thunkLang_primitivesTheory
     pure_miscTheory mlstringTheory env_cexpTheory;

val _ = new_theory "envLang";

val _ = numLib.prefer_num();

Type vname = “:string”

Datatype:
  exp = Var vname                            (* variable                *)
      | Prim op (exp list)                   (* primitive operations    *)
      | Monad mop (exp list)                 (* monadic operations      *)
      | App exp exp                          (* function application    *)
      | Lam vname exp                        (* lambda                  *)
      | Letrec ((vname # exp) list) exp      (* mutually recursive exps *)
      | Let (vname option) exp exp           (* non-recursive let       *)
      | If exp exp exp                       (* if-then-else            *)
      | Delay exp                            (* suspend in a Thunk      *)
      | Box exp                              (* wrap result in a Thunk  *)
      | Force exp                            (* evaluates a Thunk       *)
End

Definition op_of_def[simp]:
  op_of ((Cons n):cop) = (Cons (explode n)):op ∧
  op_of (AtomOp m) = AtomOp m
End

Overload True[local] = “Prim (Cons "True") []”;
Overload False[local] = “Prim (Cons "False") []”;
Overload Unit[local] = “Prim (Cons "") []”;
Overload Fail = “Prim (AtomOp Add) []”;

Definition lets_for_def:
  lets_for l cn v [] b = b ∧
  lets_for l cn v ((n,w)::ws) b =
    Let NONE (If (Prim (IsEq cn l T) [Var v]) Unit Fail) $
      Let (SOME w) (Prim (Proj cn n) [Var v]) (lets_for l cn v ws b)
End

Definition Disj_def:
  Disj v [] = False ∧
  Disj v ((cn,l)::xs) = If (Prim (IsEq cn l T) [Var v]) True (Disj v xs)
End

Definition rows_of_def:
  rows_of v [] d =
    (case d of
     | NONE => Prim (AtomOp Add) []
     | SOME (alts,e) => If (Disj v alts) e Fail) ∧
  rows_of v ((cn,vs,b)::rest) d =
    If (Prim (IsEq cn (LENGTH vs) T) [Var v])
       (lets_for (LENGTH vs) cn v (MAPi (λi v. (i,v)) vs) b)
       (rows_of v rest d)
End

Definition exp_of_def:
  exp_of ((Var n):cexp) = (Var (explode n)):envLang$exp ∧
  exp_of (Prim p xs) = Prim (op_of p) (MAP exp_of xs) ∧
  exp_of (App x y) = App (exp_of x) (exp_of y) ∧
  exp_of (Lam v x) = Lam (explode v) (exp_of x) ∧
  exp_of (Letrec fs x) = Letrec (MAP (λ(n,y). (explode n,exp_of y)) fs) (exp_of x) ∧
  exp_of (Let v x y) = Let (OPTION_MAP explode v) (exp_of x) (exp_of y) ∧
  exp_of (If x y z) = If (exp_of x) (exp_of y) (exp_of z) ∧
  exp_of (Delay x) = Delay (exp_of x) ∧
  exp_of (Box x) = Box (exp_of x) ∧
  exp_of (Force x) = Force (exp_of x) ∧
  exp_of (Case v rs d) = rows_of (explode v)
                           (MAP (λ(cn,vs,e). (explode cn, MAP explode vs, exp_of e)) rs)
                           (OPTION_MAP (λ(a,e). (MAP (explode ## I) a, exp_of e)) d) ∧
  (* monads *)
  exp_of (Ret x)        = Monad Ret    [exp_of x] ∧
  exp_of (Raise x)      = Monad Raise  [exp_of x] ∧
  exp_of (Bind x y)     = Monad Bind   [exp_of x; exp_of y] ∧
  exp_of (Handle x y)   = Monad Handle [exp_of x; exp_of y] ∧
  exp_of (Act x)        = Monad Act    [exp_of x] ∧
  exp_of (Length x)     = Monad Length [exp_of x] ∧
  exp_of (Alloc x y)    = Monad Alloc  [exp_of x; exp_of y] ∧
  exp_of (Deref x y)    = Monad Deref  [exp_of x; exp_of y] ∧
  exp_of (Update x y z) = Monad Update [exp_of x; exp_of y; exp_of z]
Termination
  WF_REL_TAC ‘measure cexp_size’
End

Theorem exp_of_def[simp,allow_rebind] = exp_of_def |> CONV_RULE (DEPTH_CONV ETA_CONV);

Definition Lams_def:
  Lams [] e = e ∧
  Lams (x::xs) e = Lam x (Lams xs e)
End

Definition Apps_def:
  Apps e [] = e ∧
  Apps e (x::xs) = Apps (App e x) xs
End

Datatype:
  v = Constructor string (v list)
    | Monadic ((vname # v) list) mop (exp list)
    | Closure vname ((vname # v) list) exp
    | Recclosure ((vname # exp) list) ((vname # v) list) vname
    | Thunk (v + (vname # v) list # exp)
    | Atom lit
End

Type env[pp] = ``:(vname # v) list``;
Type thk[pp] = ``:v + env # exp``;

Definition mk_rec_env_def[simp]:
  mk_rec_env funs env =
    MAP (λ(fn, _). (fn, Recclosure funs env fn)) funs ++ env
End

Definition dest_Closure_def[simp]:
  dest_Closure (Closure s env x) = return (s, env, x) ∧
  dest_Closure _ = fail Type_error
End

Definition dest_Recclosure_def[simp]:
  dest_Recclosure (Recclosure funs env fn) = return (funs, env, fn) ∧
  dest_Recclosure _ = fail Type_error
End

Definition dest_anyClosure_def:
  dest_anyClosure v =
    dest_Closure v ++
    do
      (f, env, n) <- dest_Recclosure v;
      case ALOOKUP f n of
        SOME (Lam s x) => return (s, mk_rec_env f env, x)
      | _ => fail Type_error
    od
End

Definition dest_Thunk_def[simp]:
  dest_Thunk (Thunk x) = return x ∧
  dest_Thunk _ = fail Type_error
End

Definition dest_anyThunk_def:
  dest_anyThunk v =
    do
      w <- dest_Thunk v;
      return (w, [])
    od ++
    do
      (f, env, n) <- dest_Recclosure v;
      case ALOOKUP f n of
        SOME (Delay x) => return (INR (env, x), f)
      | _ => fail Type_error
    od
End

Definition dest_Constructor_def[simp]:
  dest_Constructor (Constructor s vs) = return (s, vs) ∧
  dest_Constructor _ = fail Type_error
End

Definition unit_def:
  unit = Constructor "" []
End

Definition freevars_def:
  freevars (Var n) = {n} ∧
  freevars (Prim op xs) = (BIGUNION (set (MAP freevars xs))) ∧
  freevars (Monad mop xs) = (BIGUNION (set (MAP freevars xs))) ∧
  freevars (If x y z)  = freevars x ∪ freevars y ∪ freevars z ∧
  freevars (App x y) = freevars x ∪ freevars y ∧
  freevars (Lam s b) = freevars b DIFF {s} ∧
  freevars (Let NONE x y) = freevars x ∪ freevars y ∧
  freevars (Let (SOME s) x y) = freevars x ∪ (freevars y DIFF {s}) ∧
  freevars (Letrec f x) =
    ((freevars x ∪ BIGUNION (set (MAP (λ(n, x). freevars x) f))) DIFF
     set (MAP FST f)) ∧
  freevars (Delay x) = freevars x ∧
  freevars (Box x) = freevars x ∧
  freevars (Force x) = freevars x
Termination
  WF_REL_TAC ‘measure exp_size’
  \\ rw []
  \\ rename1 ‘MEM _ xs’
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [fetch "-" "exp_size_def"]
End

Definition closed_def:
  closed e ⇔ freevars e = ∅
End

Definition eval_to_def:
  eval_to k env (Var n) =
    (case ALOOKUP env n of
       SOME v => return v
     | NONE => fail Type_error) ∧
  eval_to k env (App f x) =
    (do
       xv <- eval_to k env x;
       fv <- eval_to k env f;
       (s, env, body) <- dest_anyClosure fv;
       if k = 0 then fail Diverge else eval_to (k - 1) ((s,xv)::env) body
     od) ∧
  eval_to k env (Lam s x) = return (Closure s env x) ∧
  eval_to k env (Let NONE x y) =
    (if k = 0 then fail Diverge else
       do
         eval_to (k - 1) env x;
         eval_to (k - 1) env y
       od) ∧
  eval_to k env (Let (SOME n) x y) =
    (if k = 0 then fail Diverge else
       do
         v <- eval_to (k - 1) env x;
         eval_to (k - 1) ((n,v)::env) y
       od) ∧
  eval_to k env (If x y z) =
    (if k = 0 then fail Diverge else
       do
         v <- eval_to (k - 1) env x;
         if v = Constructor "True" [] then
           eval_to (k - 1) env y
         else if v = Constructor "False" [] then
           eval_to (k - 1) env z
         else
           fail Type_error
       od) ∧
  eval_to k env (Letrec funs x) =
    (if k = 0 then fail Diverge else
       eval_to (k - 1) (mk_rec_env funs env) x) ∧
  eval_to k env (Delay x) = return (Thunk (INR (env, x))) ∧
  eval_to k env (Box x) =
    (do
       v <- eval_to k env x;
       return (Thunk (INL v))
     od) ∧
  eval_to k env (Force x) =
    (if k = 0 then fail Diverge else
       do
         v <- eval_to k env x;
         (wx, binds) <- dest_anyThunk v;
         case wx of
           INL v => return v
         | INR (env, y) => eval_to (k - 1) (mk_rec_env binds env) y
       od) ∧
  eval_to k env (Prim op xs) =
    (case op of
       Cons s =>
           do
             vs <- result_map (λx. eval_to k env x) xs;
             return (Constructor s vs)
           od
       | If => fail Type_error
       | Seq => fail Type_error
       | Proj s i =>
           do
             assert (LENGTH xs = 1);
             v <- if k = 0 then fail Diverge else eval_to (k - 1) env (HD xs);
             (t, ys) <- dest_Constructor v;
             assert (t = s ∧ i < LENGTH ys);
             return (EL i ys)
           od
       | IsEq s i a =>
           do
             assert (LENGTH xs = 1);
             v <- if k = 0 then fail Diverge else eval_to (k - 1) env (HD xs);
             (t, ys) <- dest_Constructor v;
             assert ((t = s ⇒ i = LENGTH ys) ∧ t ∉ monad_cns);
             return (Constructor (if t ≠ s then "False" else "True") [])
           od
       | AtomOp aop =>
           do
             ys <- result_map (λx. if k = 0 then fail Diverge else
                                     case eval_to (k - 1) env x of
                                       INR (Atom l) => return l
                                     | INL err => fail err
                                     | _ => fail Type_error) xs;
             case eval_op aop ys of
               SOME (INL v) => return (Atom v)
             | SOME (INR b) =>
               return (Constructor (if b then "True" else "False") [])
             | NONE => fail Type_error
           od) ∧
  eval_to k env (Monad mop xs) = return (Monadic env mop xs)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λ(k, c, x). (k, exp_size x))’ \\ rw []
  \\ Induct_on ‘xs’ \\ rw [] \\ fs [fetch "-" "exp_size_def"]
End

Definition eval_def:
  eval env x =
    case some k. eval_to k env x ≠ INL Diverge of
      NONE => fail Diverge
    | SOME k => eval_to k env x
End

Theorem eval_to_mono:
  ∀k env x j.
    eval_to k env x ≠ INL Diverge ∧
    k ≤ j ⇒
      eval_to j env x = eval_to k env x
Proof
  qsuff_tac ‘
    ∀k env x j.
      eval_to k env x ≠ INL Diverge ∧
      k < j ⇒
        eval_to j env x = eval_to k env x’
  >- (
    rw []
    \\ Cases_on ‘k = j’ \\ gs [])
  \\ ho_match_mp_tac eval_to_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- ((* Value *)
    simp [eval_to_def])
  >- ((* App *)
    rename1 ‘App x y’
    \\ rw [eval_to_def]
    \\ Cases_on ‘eval_to k env x’ \\ fs []
    \\ Cases_on ‘eval_to k env y’ \\ fs []
    \\ rename1 ‘dest_anyClosure z’
    \\ Cases_on ‘dest_anyClosure z’ \\ fs []
    \\ pairarg_tac \\ gvs []
    \\ IF_CASES_TAC \\ fs [])
  >- ((* Lam *)
    simp [eval_to_def])
  >- ((* Let NONE *)
    rw [eval_to_def]
    \\ Cases_on ‘eval_to (k - 1) env x’ \\ fs []
    \\ IF_CASES_TAC \\ fs [])
  >- ((* Let SOME *)
    rw [eval_to_def]
    \\ Cases_on ‘eval_to (k - 1) env x’ \\ fs []
    \\ IF_CASES_TAC \\ fs [])
  >- ((* If *)
    rename1 ‘If x y z’
    \\ rw [eval_to_def]
    \\ Cases_on ‘eval_to (k - 1) env x’ \\ fs []
    \\ rw [] \\ fs [])
  >- ((* Letrec *)
    rw [eval_to_def])
  >- ((* Delay *)
    rw [eval_to_def]
    \\ Cases_on ‘eval_to k env x’ \\ fs [])
  >- ((* Box *)
    rw [eval_to_def]
    \\ Cases_on ‘eval_to k env x’ \\ fs [])
  >- ((* Force *)
    rw []
    \\ gs [Once eval_to_def]
    \\ simp [SimpLHS, Once eval_to_def]
    \\ simp [SimpRHS, Once eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ Cases_on ‘eval_to k env x’ \\ fs []
    \\ Cases_on ‘dest_anyThunk y’ \\ gs []
    \\ pairarg_tac \\ gvs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs [])
  >- ((* Prim *)
    dsimp []
    \\ strip_tac
    \\ strip_tac
    \\ Cases_on ‘op’ \\ rw [eval_to_def] \\ gs []
    >- ((* Cons *)
      last_x_assum mp_tac
      \\ gs [result_map_def, MEM_MAP]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_then (drule_at_then Any assume_tac))
        \\ rw [] \\ gs [])
      \\ fs [DECIDE “A ⇒ ¬MEM a b ⇔ MEM a b ⇒ ¬A”]
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_then (drule_at_then Any assume_tac))
        \\ rw [] \\ gs [])
      \\ fs [DECIDE “A ⇒ ¬MEM a b ⇔ MEM a b ⇒ ¬A”]
      \\ IF_CASES_TAC \\ gs []
      \\ rw [MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f])
    >- ((* IsEq *)
      gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘eval_to (k - 1) env x’
      \\ ‘eval_to (k - 1) env x ≠ INL Diverge’ by (strip_tac \\ fs [])
      \\ gs [])
    >- ((* Proj *)
      gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘eval_to (k - 1) env x’
      \\ ‘eval_to (k - 1) env x ≠ INL Diverge’ by (strip_tac \\ fs [])
      \\ gs [])
    >- ((* AtomOp *)
      qmatch_goalsub_abbrev_tac ‘result_map f xs’
      \\ qmatch_asmsub_abbrev_tac ‘result_map g xs’
      \\ last_x_assum mp_tac
      \\ Cases_on ‘k = 0’ \\ gs []
      >- (
        gs [result_map_def, MEM_MAP]
        \\ Cases_on ‘xs = []’ \\ gs []
        \\ gs [pure_miscTheory.NIL_iff_NOT_MEM, Abbr ‘f’, Abbr ‘g’]
        \\ rw [] \\ gs [])
      \\ gs [result_map_def, MEM_MAP]
      \\ IF_CASES_TAC \\ gs []
      >- (
        rw [] \\ gs [Abbr ‘f’, Abbr ‘g’]
        \\ pop_assum kall_tac
        \\ ‘eval_to (k - 1) env y ≠ INL Diverge’
          by (strip_tac \\ gs [])
        \\ first_x_assum (qspec_then ‘y’ assume_tac)
        \\ gs [])
      \\ fs [DECIDE “A ⇒ ¬MEM a b ⇔ MEM a b ⇒ ¬A”]
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      >- (
        rw [] \\ gs [Abbr ‘f’, Abbr ‘g’]
        \\ ‘eval_to (k - 1) env y ≠ INL Diverge’
          by (strip_tac \\ gs [])
        \\ first_x_assum (qspec_then ‘y’ assume_tac) \\ gs [])
      \\ fs [DECIDE “A ⇒ ¬MEM a b ⇔ MEM a b ⇒ ¬A”]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ gs [Abbr ‘f’, Abbr ‘g’]
        \\ first_x_assum (drule_then (qspec_then ‘j - 1’ assume_tac)) \\ gs []
        \\ Cases_on ‘eval_to (k - 1) env y’ \\ gs [])
      \\ fs [DECIDE “A ⇒ ¬MEM a b ⇔ MEM a b ⇒ ¬A”]
      \\ ‘MAP (OUTR o f) xs = MAP (OUTR o g) xs’
        suffices_by rw [combinTheory.o_DEF, MAP_MAP_o]
      \\ rw [MAP_EQ_f]
      \\ ntac 4 (first_x_assum (qspec_then ‘e’ assume_tac))
      \\ Cases_on ‘f e’ \\ gs []
      >- (
        rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs [])
      \\ Cases_on ‘g e’ \\ gs []
      >- (
        rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs [])
      \\ gs [Abbr ‘f’, Abbr ‘g’, CaseEq "sum"]))
  >- rw[eval_to_def]
QED

Theorem eval_eq_Diverge:
  eval env x = INL Diverge ⇔
  ∀k. eval_to k env x = INL Diverge
Proof
  fs [eval_def]
  \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
  \\ first_x_assum $ irule_at Any
QED

Theorem eval_neq_Diverge:
  eval env x = res ∧ res ≠ INL Diverge ⇒
  ∃k. eval_to k env x = res
Proof
  rw [] \\ fs [eval_eq_Diverge] \\ fs [eval_def]
  \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
  \\ metis_tac []
QED

Theorem dest_anyThunk_INL:
  dest_anyThunk th1 = INL x ⇒ x = Type_error
Proof
  fs [dest_anyThunk_def]
  \\ Cases_on ‘dest_Thunk th1’ \\ fs []
  \\ Cases_on ‘dest_Recclosure th1’ \\ fs []
  \\ rw [] \\ gvs []
  \\ gvs [UNCURRY,AllCaseEqs()]
  \\ Cases_on ‘th1’ \\ fs [dest_Thunk_def]
QED

Definition cexp_wf_def[simp]:
  cexp_wf ((Lam v x):env_cexp$cexp) = cexp_wf x ∧
  cexp_wf (Force x) = cexp_wf x ∧
  cexp_wf (Box x) = cexp_wf x ∧
  cexp_wf (Delay x) = cexp_wf x ∧
  cexp_wf (Length x) = cexp_wf x ∧
  cexp_wf (Act x) = cexp_wf x ∧
  cexp_wf (Ret x) = cexp_wf x ∧
  cexp_wf (Raise x) = cexp_wf x ∧
  cexp_wf (If x y z) = (cexp_wf x ∧ cexp_wf y ∧ cexp_wf z) ∧
  cexp_wf (Let _ x y) = (cexp_wf x ∧ cexp_wf y) ∧
  cexp_wf (Bind x y) = (cexp_wf x ∧ cexp_wf y) ∧
  cexp_wf (Handle x y) = (cexp_wf x ∧ cexp_wf y) ∧
  cexp_wf (Alloc x y) = (cexp_wf x ∧ cexp_wf y) ∧
  cexp_wf (Deref x y) = (cexp_wf x ∧ cexp_wf y) ∧
  cexp_wf (Update x y z) = (cexp_wf x ∧ cexp_wf y ∧ cexp_wf z) ∧
  cexp_wf (App x y) = (cexp_wf x ∧ cexp_wf y) ∧
  cexp_wf (Letrec fs x) =
    (EVERY I (MAP (λ(_,x). cexp_wf x) fs) ∧ cexp_wf x ∧
     ALL_DISTINCT (MAP (λx. explode (FST x)) fs) ∧
     EVERY (λ(_,x). ∃n m. x = Lam n m ∨ x = Delay m) fs) ∧
  cexp_wf (Case v rs x) =
    (EVERY I (MAP (λ(_,vs,x). ALL_DISTINCT vs ∧ cexp_wf x) rs) ∧ rs ≠ [] ∧
     OPTION_ALL (λ(a,x). cexp_wf x ∧
          DISJOINT (set (MAP (explode o FST) a)) monad_cns ∧
          a ≠ []) x ∧
     DISJOINT (set (MAP (explode o FST) rs)) monad_cns ∧
     ALL_DISTINCT (MAP FST rs ++ case x of NONE => [] | SOME (a,_) => MAP FST a) ∧
     ~MEM v (FLAT (MAP (FST o SND) rs))) ∧
  cexp_wf (Prim p xs) =
    (EVERY cexp_wf xs ∧
     (case p of
      | Cons m => T
      | AtomOp b => (∀m. b = Message m ⇒ LENGTH xs = 1 ∧ m ≠ "") ∧
                    num_atomop_args_ok b (LENGTH xs) ∧
                    (∀s1 s2. b ≠ Lit (Msg s1 s2)) ∧ (∀l. b ≠ Lit (Loc l)))) ∧
  cexp_wf _ = T
Termination
  WF_REL_TAC ‘measure cexp_size’
End

val _ = export_theory ();
