(*
   thunkLang.
   ~~~~~~~~~~

   thunkLang is the next language in the compiler after pureLang.
   - It has a call-by-value semantics.
   - It extends the pureLang syntax with explicit syntax for delaying and
     forcing computations (“Delay” and “Force”) and “Thunk” values. Non-
     suspended thunks can be created with “Box”.
   - Suspended computations can be wrapped in “MkTick” to cause the suspended
     evaluation to consume one extra clock tick by producing a value wrapped in
     “DoTick”.
   - Any expression bound by a Letrec must be one of “Lam”, “Delay” or “Box”.
   - thunkLang has a substitution-based semantics. See [envLangScript.sml]
     for the next language in the compiler, which has an environment-based
     semantics.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory thunkLang_primitivesTheory pure_miscTheory;

val _ = new_theory "thunkLang";

val _ = set_grammar_ancestry ["thunkLang_primitives", "pure_misc", "pure_exp"];

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
      | Value v                                  (* for substitution        *)
      | MkTick exp;                              (* creates a delayed Tick  *)

  v = Constructor string (v list)
    | Closure vname exp
    | Recclosure ((vname # exp) list) vname
    | Thunk (v + exp)
    | Atom lit
    | DoTick v                                   (* extra clock when forced *)
End

Overload Tick = “λx. Letrec [] x”;
Overload Lit = “λl. Prim (AtomOp (Lit l)) []”;
Overload Cons = “λs xs. Prim (Cons s) xs”;
Overload IsEq = “λs i t x. Prim (IsEq s i t) [x]”;
Overload Proj = “λs i x. Prim (Proj s i) [x]”;
Overload Seq = “λx. λy. Let NONE x y”;
Overload Unit = “Prim (Cons "") []”;
Overload Fail = “Prim (AtomOp Add) []”;
Overload Lams = “λvL e. FOLDR Lam e vL”;
Overload Apps = “FOLDL App”;

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
  subst m (Value v) = Value v ∧
  subst m (MkTick x) = MkTick (subst m x)
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
  subst1 n v (Value w) = Value w ∧
  subst1 n v (MkTick x) = MkTick (subst1 n v x)
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

Definition dest_Tick_def[simp]:
  dest_Tick (DoTick v) = SOME v ∧
  dest_Tick _ = NONE
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
  freevars (Value v) = ∅ ∧
  freevars (MkTick x) = freevars x
Termination
  WF_REL_TAC ‘measure exp_size’
  \\ rw []
  \\ rename1 ‘MEM _ xs’
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [exp_size_def]
End

Definition boundvars_def:
  boundvars (Var n) = {} ∧
  boundvars (Prim op xs) = (BIGUNION (set (MAP boundvars xs))) ∧
  boundvars (If x y z) = boundvars x ∪ boundvars y ∪ boundvars z ∧
  boundvars (App x y) = boundvars x ∪ boundvars y ∧
  boundvars (Lam s b) = boundvars b ∪ {s} ∧
  boundvars (Let NONE x y) = boundvars x ∪ boundvars y ∧
  boundvars (Let (SOME s) x y) = boundvars x ∪ boundvars y ∪ {s} ∧
  boundvars (Letrec f x) =
    ((boundvars x ∪ BIGUNION (set (MAP (λ(n, x). boundvars x) f))) ∪
     set (MAP FST f)) ∧
  boundvars (Delay x) = boundvars x ∧
  boundvars (Box x) = boundvars x ∧
  boundvars (Force x) = boundvars x ∧
  boundvars (Value v) = ∅ ∧
  boundvars (MkTick x) = boundvars x
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

Definition eval_to_def:
  eval_to k (Value v) = return v ∧
  eval_to k (Var n) = fail Type_error ∧
  eval_to k (App f x) =
    (do
       xv <- eval_to k x;
       fv <- eval_to k f;
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
    (if k = 0 then fail Diverge else
       do
         v <- eval_to k x;
         case dest_Tick v of
           SOME w => eval_to (k - 1) (Force (Value w))
         | NONE =>
             do (wx, binds) <- dest_anyThunk v;
                case wx of
                  INL v => return v
                | INR y => eval_to (k - 1) (subst_funs binds y)
             od
       od) ∧
  eval_to k (MkTick x) =
    (do
       v <- eval_to k x;
       return (DoTick v)
     od) ∧
  eval_to k (Prim op xs) =
    (case op of
       Cons s =>
           do
             vs <- result_map (λx. eval_to k x) xs;
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
       | IsEq s i a =>
           do
             assert (LENGTH xs = 1);
             v <- if k = 0 then fail Diverge else eval_to (k - 1) (HD xs);
             (t, ys) <- dest_Constructor v;
             assert ((t = s ⇒ i = LENGTH ys) ∧ t ∉ monad_cns);
             return (Constructor (if t ≠ s then "False" else "True") [])
           od
       | AtomOp aop =>
           do
             ys <- result_map (λx. if k = 0 then fail Diverge else
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

Theorem eval_to_ind:
  ∀P.
    (∀k v. P k (Value v)) ∧
    (∀k n. P k (Var n)) ∧
    (∀k f x.
       (∀y binds s xv body.
          y = subst (binds ⧺ [(s,xv)]) body ∧ k ≠ 0 ⇒ P (k − 1) y) ∧
       P k f ∧ P k x ⇒
       P k (App f x)) ∧
    (∀k s x. P k (Lam s x)) ∧
    (∀k x y.
       (k ≠ 0 ⇒ P (k − 1) x) ∧ (k ≠ 0 ⇒ P (k − 1) y) ⇒
       P k (Let NONE x y)) ∧
    (∀k n x y.
       (∀v. k ≠ 0 ⇒ P (k − 1) (subst1 n v y)) ∧
       (k ≠ 0 ⇒ P (k − 1) x) ⇒
         P k (Let (SOME n) x y)) ∧
    (∀k x y z.
      (∀v. k ≠ 0 ∧
           v ≠ Constructor "True" [] ∧
           v = Constructor "False" [] ⇒
             P (k − 1) z) ∧
      (∀v. k ≠ 0 ∧ v = Constructor "True" [] ⇒ P (k − 1) y) ∧
      (k ≠ 0 ⇒ P (k − 1) x) ⇒
        P k (If x y z)) ∧
    (∀k funs x.
      (k ≠ 0 ⇒ P (k − 1) (subst_funs funs x)) ⇒ P k (Letrec funs x)) ∧
    (∀k x. P k (Delay x)) ∧
    (∀k x. P k x ⇒ P k (Box x)) ∧
    (∀k x.
      (∀y binds.
         k ≠ 0 ⇒
           P (k − 1) (subst_funs binds y)) ∧
      (∀w.
         k ≠ 0 ⇒
           P (k − 1) (Force (Value w))) ∧
      (k ≠ 0 ⇒ P k x) ⇒
        P k (Force x)) ∧
    (∀k x. P k x ⇒ P k (MkTick x)) ∧
    (∀k op xs.
      (∀aop x.
         op = AtomOp aop ∧
         MEM x xs ∧
         k ≠ 0 ⇒
           P (k − 1) x) ∧
      (∀s x.
         op = Cons s ∧
         MEM x xs ⇒
           P k x) ∧
      (∀s'' i' a.
         op = IsEq s'' i' a ∧
         k ≠ 0 ⇒
           P (k − 1) (HD xs)) ∧
      (∀s' i.
         op = Proj s' i ∧
         k ≠ 0 ⇒
           P (k − 1) (HD xs)) ⇒
            P k (Prim op xs)) ⇒
        ∀v v1. P v v1
Proof
  rw []
  \\ irule eval_to_ind \\ rw []
  \\ last_x_assum irule \\ rw []
  >- (
    first_x_assum irule \\ gs []
    \\ qexists_tac ‘Atom foo’ \\ gs [])
  \\ first_x_assum irule \\ gs []
  \\ qexists_tac ‘DoTick w’ \\ gs []
QED

Definition eval_def:
  eval x =
    case some k. eval_to k x ≠ INL Diverge of
      NONE => fail Diverge
    | SOME k => eval_to k x
End

Theorem eval_to_mono:
  ∀k x j.
    eval_to k x ≠ INL Diverge ∧
    k ≤ j ⇒
      eval_to j x = eval_to k x
Proof
  qsuff_tac ‘
    ∀k x j.
      eval_to k x ≠ INL Diverge ∧
      k < j ⇒
        eval_to j x = eval_to k x’
  >- (
    rw []
    \\ Cases_on ‘k = j’ \\ gs [])
  \\ ho_match_mp_tac eval_to_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- ((* Value *)
    simp [eval_to_def])
  >- ((* Var *)
    simp [eval_to_def])
  >- ((* App *)
    rename1 ‘App x y’
    \\ rw [eval_to_def]
    \\ Cases_on ‘eval_to k y’ \\ fs []
    \\ Cases_on ‘eval_to k x’ \\ fs []
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
    rw []
    \\ rgs [Once eval_to_def]
    \\ simp [SimpLHS, Once eval_to_def]
    \\ simp [SimpRHS, Once eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ Cases_on ‘eval_to k x’ \\ fs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ Cases_on ‘dest_anyThunk y’ \\ gs []
    \\ pairarg_tac \\ gvs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs [])
  >- ((* MkTick *)
    rw [eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ fs [])
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
      \\ rename1 ‘eval_to (k - 1) x’
      \\ ‘eval_to (k - 1) x ≠ INL Diverge’ by (strip_tac \\ fs [])
      \\ gs [])
    >- ((* Proj *)
      gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘eval_to (k - 1) x’
      \\ ‘eval_to (k - 1) x ≠ INL Diverge’ by (strip_tac \\ fs [])
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
        \\ ‘eval_to (k - 1) y ≠ INL Diverge’
          by (strip_tac \\ gs [])
        \\ first_x_assum (qspec_then ‘y’ assume_tac)
        \\ gs [])
      \\ fs [DECIDE “A ⇒ ¬MEM a b ⇔ MEM a b ⇒ ¬A”]
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      >- (
        rw [] \\ gs [Abbr ‘f’, Abbr ‘g’]
        \\ ‘eval_to (k - 1) y ≠ INL Diverge’
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
        \\ Cases_on ‘eval_to (k - 1) y’ \\ gs [])
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
QED

Definition is_Lam_def[simp]:
  (is_Lam (Lam _ _) = T) ∧
  (is_Lam _ = F)
End

Definition ok_bind_def[simp]:
  (ok_bind (Lam _ _) = T) ∧
  (ok_bind (Delay _) = T) ∧
  (ok_bind _ = F)
End

val _ = export_theory ();
