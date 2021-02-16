(*
   thunkLang.
   ~~~~~~~~~~

   thunkLang is the next language in the compiler after pureLang.
   - It has a call-by-value semantics.
   - It extends the pureLang syntax with explicit syntax for delaying and
     forcing computations (“Delay” and “Force”) and “Thunk” values.
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
      | Letrec ((vname # vname # exp) list) exp  (* mutually recursive exps *)
      | If exp exp exp                           (* if-then-else            *)
      | Delay bool exp                           (* delays a computation    *)
      | Force exp                                (* evaluates a Thunk       *)
      | Value v;                                 (* for substitution        *)

  v = Constructor string (v list)
    | Closure vname exp
    | Recclosure ((vname # vname # exp) list) vname
    | Thunk bool v
    | Atom lit
End

val exp_size_def = fetch "-" "exp_size_def";

Definition get_lits_def:
  get_lits [] = return [] ∧
  get_lits (x::xs) =
    (do
       y <- case x of Atom l => return l | _ => fail Type_error ;
       ys <- get_lits xs ;
       return (y::ys)
     od)
End

Definition do_prim_def:
  do_prim op vs =
    case op of
      Cons s => return (Constructor s vs)
    | If => fail Type_error
    | Proj s i =>
        (if LENGTH vs ≠ 1 then fail Type_error else
           case HD vs of
             Constructor t ys =>
               if t = s ∧ i < LENGTH ys then
                 return (EL i ys)
               else
                 fail Type_error
           | _ => fail Type_error)
    | IsEq s i =>
        (if LENGTH vs ≠ 1 then fail Type_error else
           case HD vs of
             Constructor t ys =>
               if t ≠ s then
                 return (Constructor "False" [])
               else if i = LENGTH ys then
                 return (Constructor "True" [])
               else
                 fail Type_error
           | _ => fail Type_error)
    | Lit l => if vs = [] then return (Atom l) else fail Type_error
    | AtomOp x =>
        do
          xs <- get_lits vs;
          case config.parAtomOp x xs of
            SOME v => return (Atom v)
          | NONE => fail Type_error
        od
End

Definition subst_def:
  subst m (Var s) =
    (case ALOOKUP m s of
       NONE => Var s
     | SOME x => Value x) ∧
  subst m (Prim op xs) = Prim op (MAP (subst m) xs) ∧
  subst m (If x y z) =
    If (subst m x) (subst m y) (subst m z) ∧
  subst m (App x y) = App (subst m x) (subst m y) ∧
  subst m (Lam s x) = Lam s (subst (FILTER (λ(n, x). n ≠ s) m) x) ∧
  subst m (Letrec f x) =
    (let m1 =
       FILTER (λ(n, x). ¬MEM n (MAP FST f)) m in
         Letrec (MAP (λ(f,xn,e).
                  (f,xn,subst (FILTER (λ(n,x). n ≠ xn) m1) e)) f)
                (subst m1 x)) ∧
  subst m (Delay b x) = Delay b (subst m x) ∧
  subst m (Force x) = Force (subst m x) ∧
  subst m (Value v) = Value v
Termination
  WF_REL_TAC `measure (exp_size o SND)` \\ rw []
  \\ rename1 ‘MEM _ xs’
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [exp_size_def]
End

Overload subst1 = “λname v e. subst [(name,v)] e”;

Definition bind_def:
  bind m v = subst m v
End

Overload bind1 = “λname v e. bind [(name,v)] e”;

Definition subst_funs_def:
  subst_funs f = bind (MAP (λ(g,v,x). (g, Recclosure f g)) f)
End

Definition dest_Closure_def:
  dest_Closure (Closure s x) = return (s, x) ∧
  dest_Closure _ = fail Type_error
End

Definition dest_Thunk_def:
  dest_Thunk (Thunk nf x) = return (nf, x) ∧
  dest_Thunk _ = fail Type_error
End

Definition dest_Recclosure_def:
  dest_Recclosure (Recclosure funs fn) = return (funs, fn) ∧
  dest_Recclosure _ = fail Type_error
End

Definition dest_anyClosure_def:
  dest_anyClosure v =
    do
      (s, bod) <- dest_Closure v;
       return (s, bod, [])
    od ++
    do
      (funs, fn) <- dest_Recclosure v;
      case ALOOKUP funs fn of
        SOME (var, bod) =>
          return (var, bod, MAP (λ(g,v,x). (g, Recclosure funs g)) funs)
      | NONE => fail Type_error
    od
End

Definition freevars_def:
  freevars (Var n) = {n} ∧
  freevars (Prim op xs) = (BIGUNION (set (MAP freevars xs))) ∧
  freevars (If x y z)  = freevars x ∪ freevars y ∪ freevars z ∧
  freevars (App x y) = freevars x ∪ freevars y ∧
  freevars (Lam s b)   = freevars b DIFF {s} ∧
  freevars (Letrec f x) =
    freevars x DIFF set (MAP FST f ++ MAP (FST o SND) f) ∧
  freevars (Delay f x) = freevars x ∧
  freevars (Force x) = freevars x ∧
  freevars (Value v) = ∅
Termination
  WF_REL_TAC ‘measure exp_size’
  \\ fs [] \\ gen_tac
  \\ Induct \\ rw []
  \\ res_tac
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
  eval_to k (Prim op xs) =
    (if k = 0 then fail Diverge else
       do
         vs <- map (eval_to (k - 1)) xs;
         do_prim op vs
       od) ∧
  eval_to k (App f x) =
    (do
       fv <- eval_to k f;
       xv <- eval_to k x;
       (s, body, post) <- dest_anyClosure fv;
       y <<- bind ((s, xv)::post) body;
       if k = 0 then fail Diverge else eval_to (k - 1) y
     od) ∧
  eval_to k (Lam s x) = return (Closure s x) ∧
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
       do
         y <<- subst_funs funs x;
         eval_to (k - 1) y
       od) ∧
  eval_to k (Delay f x) =
    (do
       v <- eval_to k x;
       return (Thunk f v)
     od) ∧
  eval_to k (Force x) =
    (do
       v <- eval_to k x;
       (nf, w) <- dest_Thunk v;
       if nf then return w else
         do
           (s, body, post) <- dest_anyClosure w;
           y <<- bind ((s, unit)::post) body;
           if k = 0 then fail Diverge else eval_to (k - 1) y
         od
     od)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λ(k, x). (k, exp_size x))’
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
  >- ((* Prim *)
    rw [eval_to_def]
    \\ Cases_on ‘map (λx. eval_to (k - 1) x) xs’ \\ fs []
    >- (
      ‘map (λx. eval_to (j - 1) x) xs = INL x’ suffices_by rw []
      \\ fs [map_INL]
      \\ first_assum (irule_at Any) \\ fs [])
    \\ Cases_on ‘map (λx. eval_to (j - 1) x) xs’ \\ fs []
    >- (
      ‘F’ suffices_by rw []
      \\ gvs [map_INL]
      \\ drule_then assume_tac map_INR
      \\ first_x_assum (drule_then strip_assume_tac) \\ fs []
      \\ ‘eval_to (k - 1) (EL n xs) ≠ INL Diverge’ by fs []
      \\ first_x_assum (drule_then (qspec_then ‘j - 1’ assume_tac)) \\ gs [])
    \\ ‘map (λx. eval_to (j - 1) x) xs = map (λx. eval_to (k - 1) x) xs’
      suffices_by rw []
    \\ irule map_EQ_f \\ rw []
    \\ first_x_assum irule \\ fs []
    \\ last_x_assum (mp_then Any mp_tac map_INR)
    \\ fs [MEM_EL]
    \\ disch_then (drule_then strip_assume_tac) \\ fs [])
  >- ((* App *)
    rename1 ‘App x y’
    \\ rw [eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ fs []
    \\ Cases_on ‘eval_to k y’ \\ fs []
    \\ rename1 ‘dest_anyClosure z’
    \\ Cases_on ‘dest_anyClosure z’ \\ fs []
    \\ pairarg_tac \\ gvs [bind_def]
    \\ IF_CASES_TAC \\ fs [])
  >- ((* Lam *)
    simp [eval_to_def])
  >- ((* If *)
    rename1 ‘If x y z’
    \\ rw [eval_to_def]
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ rw [] \\ fs [])
  >- ((* Letrec *)
    rw [eval_to_def, subst_funs_def, bind_def])
  >- ((* Delay *)
    rw [eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ fs [])
  >- ((* Force *)
    rw [eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ fs []
    \\ Cases_on ‘dest_Thunk y’ \\ fs []
    \\ pairarg_tac \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘dest_anyClosure w’ \\ fs []
    \\ pairarg_tac \\ gvs [bind_def]
    \\ IF_CASES_TAC \\ fs [])
QED

val _ = export_theory ();

