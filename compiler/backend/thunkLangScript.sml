(*
   thunkLang.
   ~~~~~~~~~~

   thunkLang is the next language in the compiler after pureLang.
   - It has a call-by-value semantics.
   - It extends the pureLang syntax with explicit syntax for delaying and
     forcing computations (“Delay” and “Force”) and “Thunk” values.
   - This version has an environment-based semantics. See
     [thunkLang_substScript.sml] for a substitution-based version.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory thunkLang_primitivesTheory;

val _ = new_theory "thunkLang";

val _ = numLib.prefer_num();

Datatype:
  exp = Var vname                                (* variable                *)
      | Prim op (exp list)                       (* primitive operations    *)
      | App exp exp                              (* function application    *)
      | Lam vname exp                            (* lambda                  *)
      | Letrec ((vname #  exp) list) exp         (* mutually recursive exps *)
      | Let vname exp exp                        (* non-recursive let       *)
      | If exp exp exp                           (* if-then-else            *)
      | Delay exp                                (* suspend in a Thunk      *)
      | Box exp                                  (* wrap result in a Thunk  *)
      | Force exp                                (* evaluates a Thunk       *)
End

Datatype:
  v = Constructor string (v list)
    | Closure vname ((vname # v) list) exp
    | Recclosure ((vname # exp) list) ((vname # v) list) vname
    | Thunk (v + (vname # v) list # exp)
    | Atom lit
End

Definition bind_funs_def[simp]:
  bind_funs funs env =
    env ++ MAP (λ(fn, _). (fn, Recclosure funs env fn)) funs
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
      case ALOOKUP (REVERSE f) n of
        SOME (Lam s x) => return (s, bind_funs f env, x)
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
      case ALOOKUP (REVERSE f) n of
        SOME (Delay x) => return (INR (env, x), f)
      | SOME (Box x) => return (INR (env, x), f)
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
  freevars (If x y z)  = freevars x ∪ freevars y ∪ freevars z ∧
  freevars (App x y) = freevars x ∪ freevars y ∧
  freevars (Lam s b) = freevars b DIFF {s} ∧
  freevars (Let s x y) = freevars x ∪ (freevars y DIFF {s}) ∧
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
    (case ALOOKUP (REVERSE env) n of
       SOME v => return v
     | NONE => fail Type_error) ∧
  eval_to k env (App f x) =
    (do
       fv <- eval_to k env f;
       xv <- eval_to k env x;
       (s, env, body) <- dest_anyClosure fv;
       if k = 0 then fail Diverge else
         do
           assert (closed x);
           eval_to (k - 1) (env ++ [(s,xv)]) body
         od
     od) ∧
  eval_to k env (Lam s x) = return (Closure s env x) ∧
  eval_to k env (Let n x y) =
    (if k = 0 then fail Diverge else
       do
         v <- eval_to (k - 1) env x;
         eval_to (k - 1) (env ++ [(n,v)]) y
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
       eval_to (k - 1) (bind_funs funs env) x) ∧
  eval_to k env (Delay x) = return (Thunk (INR (env, x))) ∧
  eval_to k env (Box x) =
    (do
       v <- eval_to k env x;
       return (Thunk (INL v))
     od) ∧
  eval_to k env (Force x) =
    (do
       v <- eval_to k env x;
       (wx, binds) <- dest_anyThunk v;
       case wx of
         INL v => return v
       | INR (env, y) => if k = 0 then fail Diverge else
                           eval_to (k - 1) (bind_funs binds env) y
     od) ∧
  eval_to k env (Prim op xs) =
    (case op of
       Cons s =>
           do
             vs <- map (λx. eval_to k env x) xs;
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
       | IsEq s i =>
           do
             assert (LENGTH xs = 1);
             v <- if k = 0 then fail Diverge else eval_to (k - 1) env (HD xs);
             (t, ys) <- dest_Constructor v;
             assert (t = s ⇒ i = LENGTH ys);
             return (Constructor (if t ≠ s then "False" else "True") [])
           od
       | AtomOp aop =>
           do
             ys <- map (λx. if k = 0 then fail Diverge else
                              case eval_to (k - 1) env x of
                                INR (Atom l) => return l
                              | INL err => fail err
                              | _ => fail Type_error) xs;
             case eval_op aop ys of
               SOME (INL v) => return (Atom v)
             | SOME (INR b) =>
               return (Constructor (if b then "True" else "False") [])
             | NONE => fail Type_error
           od)
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
    k < j ⇒
      eval_to j env x = eval_to k env x
Proof
  ho_match_mp_tac eval_to_ind
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
  >- ((* Let *)
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
    rw [eval_to_def]
    \\ Cases_on ‘eval_to k env x’ \\ fs []
    \\ Cases_on ‘dest_anyThunk y’ \\ fs []
    \\ pairarg_tac \\ gvs []
    \\ CASE_TAC \\ fs []
    \\ CASE_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs [])
  >- ((* Prim *)
    dsimp []
    \\ strip_tac
    \\ strip_tac
    \\ fs [MEM_EL, PULL_EXISTS]
    \\ Cases_on ‘op’ \\ rw [eval_to_def] \\ gs []
    >- ((* Cons *)
      Cases_on ‘map (λx. eval_to j env x) xs’ \\ fs []
      >- (
        reverse (Cases_on ‘map (λx. eval_to k env x) xs’) \\ fs []
        >- (
          fs [map_INL]
          \\ drule_then assume_tac map_INR
          \\ first_x_assum (drule_then assume_tac) \\ gs [])
        \\ gvs [map_INL]
        \\ rename1 ‘eval_to j env (EL m xs)’
        \\ rename1 ‘eval_to k env (EL n xs)’
        \\ Cases_on ‘m < n’ \\ gs []
        \\ Cases_on ‘m = n’ \\ gs []
        \\ ‘n < m’ by gs []
        \\ first_assum (drule_then assume_tac)
        \\ ‘eval_to k env (EL n xs) ≠ INL Diverge’ by fs []
        \\ first_x_assum (drule_then assume_tac) \\ gs [])
      \\ Cases_on ‘map (λx. eval_to k env x) xs’ \\ fs []
      >- (
        fs [map_INL]
        \\ drule_then assume_tac map_INR
        \\ first_x_assum (drule_then assume_tac) \\ gs [])
      \\ imp_res_tac map_LENGTH
      \\ first_assum (mp_then Any assume_tac map_INR)
      \\ last_assum (mp_then Any assume_tac map_INR)
      \\ irule LIST_EQ \\ rw [] \\ gs [])
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
      qmatch_goalsub_abbrev_tac ‘map f xs’
      \\ qmatch_asmsub_abbrev_tac ‘map g xs’
      \\ Cases_on ‘map f xs’ \\ fs []
      >- (
        reverse (Cases_on ‘map g xs’) \\ fs []
        >- (
          fs [map_INL, Abbr ‘f’, Abbr ‘g’]
          \\ drule_all_then assume_tac map_INR
          \\ gs [CaseEqs ["sum", "v", "bool"]])
        \\ fs [map_INL, Abbr ‘f’, Abbr ‘g’]
        \\ rename1 ‘eval_to (j - 1) env (EL m xs)’
        \\ rename1 ‘eval_to (k - 1) env (EL n xs)’
        \\ Cases_on ‘m < n’ \\ gs []
        >- (
          first_x_assum (drule_then assume_tac)
          \\ gs [CaseEqs ["sum", "bool"]])
        \\ Cases_on ‘m = n’ \\ gs []
        >- (
          gvs [CaseEqs ["sum", "bool"]])
        \\ gvs [CaseEq "bool"]
        \\ ‘n < m’ by gs []
        \\ ‘n < LENGTH xs’ by gs []
        \\ first_assum (drule_then assume_tac)
        \\ ‘eval_to (k - 1) env (EL n xs) ≠ INL Diverge’ by (strip_tac \\ fs [])
        \\ first_x_assum (drule_then (qspec_then ‘j - 1’ mp_tac))
        \\ simp []
        \\ disch_then (assume_tac o SYM) \\ fs [])
      \\ Cases_on ‘map g xs’ \\ fs []
      >- (
        fs [map_INL, Abbr ‘f’, Abbr ‘g’]
        \\ drule_all_then assume_tac map_INR
        \\ gs [CaseEqs ["sum", "bool"]])
      \\ rename1 ‘map f _ = INR v’
      \\ rename1 ‘map g _ = INR w’
      \\ ‘v = w’ suffices_by rw []
      \\ imp_res_tac map_LENGTH
      \\ first_assum (mp_then Any assume_tac map_INR)
      \\ last_assum (mp_then Any assume_tac map_INR)
      \\ unabbrev_all_tac
      \\ Cases_on ‘k = 0’ \\ fs []
      \\ irule LIST_EQ \\ rw [] \\ gs [CaseEqs ["sum", "v"]]))
QED

val _ = export_theory ();

