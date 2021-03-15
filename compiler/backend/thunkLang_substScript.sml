(*
   thunkLang.
   ~~~~~~~~~~

   thunkLang is the next language in the compiler after pureLang.
   - It has a call-by-value semantics.
   - It extends the pureLang syntax with explicit syntax for delaying and
     forcing computations (“Delay” and “Force”) and “Thunk” values. Non-
     suspended thunks can be created with “Box”.
   - Any expression bound by a Letrec must be one of “Lam”, “Delay” or “Box”.
   - This version has a substitution-based semantics. See
     [thunkLangScript.sml] for an environment-based version.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory thunkLang_primitivesTheory;

val _ = new_theory "thunkLang_subst";

val _ = numLib.prefer_num();

Datatype:
  exp = Var vname                                (* variable                *)
      | Prim op (exp list)                       (* primitive operations    *)
      | App exp exp                              (* function application    *)
      | Lam vname exp                            (* lambda                  *)
      | Letrec ((vname # exp) list) exp          (* mutually recursive exps *)
      | Let (vname option) exp exp               (* non-recursive let       *)
      | If exp exp exp                           (* if-then-else            *)
      | Delay exp                                (* suspend in a Thunk      *)
      | Box exp                                  (* wrap result in a Thunk  *)
      | Force exp                                (* evaluates a Thunk       *)
      | Value v;                                 (* for substitution        *)

  v = Constructor string (v list)
    | Closure vname exp
    | Recclosure ((vname # exp) list) vname
    | Thunk (v + exp)
    | Atom lit
End

val exp_size_def = fetch "-" "exp_size_def";

Definition subst_def:
  subst m (Var s) =
    (case ALOOKUP (REVERSE m) s of
       NONE => Var s
     | SOME x => Value x) ∧
  subst m (Prim op xs) = Prim op (MAP (subst m) xs) ∧
  subst m (If x y z) =
    If (subst m x) (subst m y) (subst m z) ∧
  subst m (App x y) = App (subst m x) (subst m y) ∧
  subst m (Lam s x) = Lam s (subst (FILTER (λ(n,x). n ≠ s) m) x) ∧
  subst m (Let NONE x y) = Let NONE (subst m x) (subst m y) ∧
  subst m (Let (SOME s) x y) =
    Let (SOME s) (subst m x) (subst (FILTER (λ(n,x). n ≠ s) m) y) ∧
  subst m (Letrec f x) =
    (let m1 = FILTER (λ(n, v). ¬MEM n (MAP FST f)) m in
       Letrec (MAP (λ(n, x). (n, subst m1 x)) f) (subst m1 x)) ∧
  subst m (Delay x) = Delay (subst m x) ∧
  subst m (Box x) = Box (subst m x) ∧
  subst m (Force x) = Force (subst m x) ∧
  subst m (Value v) = Value v
Termination
  WF_REL_TAC `measure (exp_size o SND)` \\ rw []
  \\ rename1 ‘MEM _ xs’
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [exp_size_def]
End

Overload subst1 = “λname v e. subst [(name,v)] e”;

Theorem subst_empty[simp]:
  subst [] x = x
Proof
  ‘∀m x. m = [] ⇒ subst m x = x’ suffices_by rw []
  \\ ho_match_mp_tac subst_ind
  \\ rw [subst_def]
  \\ rename1 ‘MAP _ xs’
  \\ Induct_on ‘xs’ \\ fs [FORALL_PROD, SF SFY_ss]
QED

Theorem subst1_def:
  subst1 n v (Var s) = (if n = s then Value v else Var s) ∧
  subst1 n v (Prim op xs) = Prim op (MAP (subst1 n v) xs) ∧
  subst1 n v (If x y z) =
    If (subst1 n v x) (subst1 n v y) (subst1 n v z) ∧
  subst1 n v (App x y) = App (subst1 n v x) (subst1 n v y) ∧
  subst1 n v (Lam s x) = (if n = s then Lam s x else Lam s (subst1 n v x)) ∧
  subst1 n v (Let NONE x y) =
    Let NONE (subst1 n v x) (subst1 n v y) ∧
  subst1 n v (Let (SOME s) x y) =
    Let (SOME s) (subst1 n v x) (if n = s then y else subst1 n v y) ∧
  subst1 n v (Letrec f x) =
    (if MEM n (MAP FST f) then
       Letrec f x
     else
       Letrec (MAP (λ(f, x). (f, subst1 n v x)) f) (subst1 n v x)) ∧
  subst1 n v (Delay x) = Delay (subst1 n v x) ∧
  subst1 n v (Box x) = Box (subst1 n v x) ∧
  subst1 n v (Force x) = Force (subst1 n v x) ∧
  subst1 n v (Value w) = Value w
Proof
  rw [subst_def, COND_RAND, subst_empty, ELIM_UNCURRY]
QED

Definition subst_funs_def:
  subst_funs f = subst (MAP (λ(g, x). (g, Recclosure f g)) f)
End

Definition dest_Closure_def[simp]:
  dest_Closure (Closure s x) = return (s, x) ∧
  dest_Closure _ = fail Type_error
End

Definition dest_Recclosure_def[simp]:
  dest_Recclosure (Recclosure f n) = return (f, n) ∧
  dest_Recclosure _ = fail Type_error
End

Definition dest_anyClosure_def:
  dest_anyClosure v =
    do
      (s, x) <- dest_Closure v;
       return (s, x, [])
    od ++
    do
      (f, n) <- dest_Recclosure v;
      case ALOOKUP (REVERSE f) n of
        SOME (Lam s x) => return (s, x, MAP (λ(g, x). (g, Recclosure f g)) f)
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
      (f, n) <- dest_Recclosure v;
      case ALOOKUP (REVERSE f) n of
        SOME (Delay x) => return (INR x, f)
      | SOME (Box x) => return (INR x, f)
      | _ => fail Type_error
    od
End

Definition dest_Constructor_def[simp]:
  dest_Constructor (Constructor s vs) = return (s, vs) ∧
  dest_Constructor _ = fail Type_error
End

Definition freevars_def:
  freevars (Var n) = {n} ∧
  freevars (Prim op xs) = (BIGUNION (set (MAP freevars xs))) ∧
  freevars (If x y z) = freevars x ∪ freevars y ∪ freevars z ∧
  freevars (App x y) = freevars x ∪ freevars y ∧
  freevars (Lam s b) = freevars b DIFF {s} ∧
  freevars (Let NONE x y) = freevars x ∪ freevars y ∧
  freevars (Let (SOME s) x y) = freevars x ∪ (freevars y DIFF {s}) ∧
  freevars (Letrec f x) =
    ((freevars x ∪ BIGUNION (set (MAP (λ(n, x). freevars x) f))) DIFF
     set (MAP FST f)) ∧
  freevars (Delay x) = freevars x ∧
  freevars (Box x) = freevars x ∧
  freevars (Force x) = freevars x ∧
  freevars (Value v) = ∅
Termination
  WF_REL_TAC ‘measure exp_size’
  \\ rw []
  \\ rename1 ‘MEM _ xs’
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [exp_size_def]
End

Definition closed_def:
  closed e ⇔ freevars e = ∅
End

Definition unit_def:
  unit = Constructor "" []
End

Definition eval_to_def:
  eval_to k (Value v) = return v ∧
  eval_to k (Var n) = fail Type_error ∧
  eval_to k (App f x) =
    (do
       fv <- eval_to k f;
       xv <- eval_to k x;
       (s, body, binds) <- dest_anyClosure fv;
       y <<- subst (binds ++ [(s, xv)]) body;
       if k = 0 then fail Diverge else eval_to (k - 1) y
     od) ∧
  eval_to k (Lam s x) = return (Closure s x) ∧
  eval_to k (Let NONE x y) =
    (if k = 0 then fail Diverge else
       do
         eval_to (k - 1) x;
         eval_to (k - 1) y
       od) ∧
  eval_to k (Let (SOME n) x y) =
    (if k = 0 then fail Diverge else
       do
         v <- eval_to (k - 1) x;
         eval_to (k - 1) (subst1 n v y)
       od) ∧
  eval_to k (If x y z) =
    (if k = 0 then fail Diverge else
       do
         v <- eval_to (k - 1) x;
         if v = Constructor "True" [] then
           eval_to (k - 1) y
         else if v = Constructor "False" [] then
           eval_to (k - 1) z
         else
           fail Type_error
       od) ∧
  eval_to k (Letrec funs x) =
    (if k = 0 then fail Diverge else
       eval_to (k - 1) (subst_funs funs x)) ∧
  eval_to k (Delay x) = return (Thunk (INR x)) ∧
  eval_to k (Box x) =
    (do
       v <- eval_to k x;
       return (Thunk (INL v))
     od) ∧
  eval_to k (Force x) =
    (do
       v <- eval_to k x;
       (wx, binds) <- dest_anyThunk v;
       case wx of
         INL v => return v
       | INR y => if k = 0 then fail Diverge else
                    eval_to (k - 1) (subst_funs binds y)
     od) ∧
  eval_to k (Prim op xs) =
    (case op of
       Cons s =>
           do
             vs <- map (λx. eval_to k x) xs;
             return (Constructor s vs)
           od
       | If => fail Type_error
       | Seq => fail Type_error
       | Proj s i =>
           do
             assert (LENGTH xs = 1);
             v <- if k = 0 then fail Diverge else eval_to (k - 1) (HD xs);
             (t, ys) <- dest_Constructor v;
             assert (t = s ∧ i < LENGTH ys);
             return (EL i ys)
           od
       | IsEq s i =>
           do
             assert (LENGTH xs = 1);
             v <- if k = 0 then fail Diverge else eval_to (k - 1) (HD xs);
             (t, ys) <- dest_Constructor v;
             assert (t = s ⇒ i = LENGTH ys);
             return (Constructor (if t ≠ s then "False" else "True") [])
           od
       | AtomOp aop =>
           do
             ys <- map (λx. if k = 0 then fail Diverge else
                              case eval_to (k - 1) x of
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
  WF_REL_TAC ‘inv_image ($< LEX $<) (I ## exp_size)’ \\ rw []
  \\ Induct_on ‘xs’ \\ rw [] \\ fs [exp_size_def]
End

Definition eval_def:
  eval x =
    case some k. eval_to k x ≠ INL Diverge of
      NONE => fail Diverge
    | SOME k => eval_to k x
End

Theorem eval_to_subst_mono:
  ∀k x j.
    eval_to k x ≠ INL Diverge ∧
    k < j ⇒
      eval_to j x = eval_to k x
Proof
  ho_match_mp_tac eval_to_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- ((* Value *)
    simp [eval_to_def])
  >- ((* Var *)
    simp [eval_to_def])
  >- ((* App *)
    rename1 ‘App x y’
    \\ rw [eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ fs []
    \\ Cases_on ‘eval_to k y’ \\ fs []
    \\ rename1 ‘dest_anyClosure z’
    \\ Cases_on ‘dest_anyClosure z’ \\ fs []
    \\ pairarg_tac \\ gvs []
    \\ IF_CASES_TAC \\ fs [])
  >- ((* Lam *)
    simp [eval_to_def])
  >- ((* Let NONE *)
    rw [eval_to_def]
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ IF_CASES_TAC \\ fs [])
  >- ((* Let SOME *)
    rw [eval_to_def]
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ IF_CASES_TAC \\ fs [])
  >- ((* If *)
    rename1 ‘If x y z’
    \\ rw [eval_to_def]
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ rw [] \\ fs [])
  >- ((* Letrec *)
    rw [eval_to_def, subst_funs_def])
  >- ((* Delay *)
    rw [eval_to_def])
  >- ((* Box *)
    rw [eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ fs [])
  >- ((* Force *)
    rw [eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ fs []
    \\ Cases_on ‘dest_anyThunk y’ \\ fs []
    \\ pairarg_tac \\ gvs []
    \\ CASE_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs [])
  >- ((* Prim *)
    dsimp []
    \\ strip_tac
    \\ strip_tac
    \\ fs [MEM_EL, PULL_EXISTS]
    \\ Cases_on ‘op’ \\ rw [eval_to_def] \\ gs []
    >- ((* Cons *)
      Cases_on ‘map (λx. eval_to j x) xs’ \\ fs []
      >- (
        reverse (Cases_on ‘map (λx. eval_to k x) xs’) \\ fs []
        >- (
          fs [map_INL]
          \\ drule_then assume_tac map_INR
          \\ first_x_assum (drule_then assume_tac) \\ gs [])
        \\ gvs [map_INL]
        \\ rename1 ‘eval_to j (EL m xs) = INL d’
        \\ rename1 ‘eval_to k (EL n xs) = INL e’
        \\ Cases_on ‘m < n’ \\ gs []
        \\ Cases_on ‘m = n’ \\ gs []
        \\ ‘n < m’ by gs []
        \\ first_assum (drule_then assume_tac)
        \\ ‘eval_to k (EL n xs) ≠ INL Diverge’ by fs []
        \\ first_x_assum (drule_then assume_tac) \\ gs [])
      \\ Cases_on ‘map (λx. eval_to k x) xs’ \\ fs []
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
      \\ rename1 ‘eval_to (k - 1) x’
      \\ ‘eval_to (k - 1) x ≠ INL Diverge’ by (strip_tac \\ fs [])
      \\ gs [])
    >- ((* Proj *)
      gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘eval_to (k - 1) x’
      \\ ‘eval_to (k - 1) x ≠ INL Diverge’ by (strip_tac \\ fs [])
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
        \\ rename1 ‘sum_CASE (eval_to (j - 1) (EL m xs)) _ _’
        \\ rename1 ‘sum_CASE (eval_to (k - 1) (EL n xs)) _ _’
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
        \\ ‘eval_to (k - 1) (EL n xs) ≠ INL Diverge’ by (strip_tac \\ fs [])
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

