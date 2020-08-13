
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     ltreeTheory llistTheory denotation_consTheory io_treeTheory;

val _ = new_theory "denotation_io";

Datatype:
  result = SilentDivergence
         | Termination
         | TypeError
End

Definition dest_Num_def:
  dest_Num v =
    case v of
    | Num n => SOME n
    | _ => NONE
End

Definition dest_Closure_def:
  dest_Closure v =
    case v of
    | Closure n x => SOME (n,x)
    | _ => NONE
End

Definition dest_Vis_def:
  dest_Vis v =
    case v of
    | Constructor "Vis" cs =>
        (case (LNTH 0 cs, LNTH 1 cs) of
         | (SOME x, SOME y) =>
             (case (dest_Num x, dest_Closure y) of
              | (SOME n, SOME (v,e)) => SOME (n,v,e)
              | _ => NONE)
         | _ => NONE)
    | _ => NONE
End

Definition eval_io_def:
  eval_io =
    io_unfold
      (λx. let v = eval x in
             if v = Diverge then Ret' SilentDivergence else
             if v = Constructor "Ret" [] then Ret' Termination else
               case dest_Vis v of
               | NONE => Ret' TypeError
               | SOME (n,v,e) => Vis' n (λk. subst v (Lit k) e))
End

(*

(*
  get_io (Return x, f) = f x
  get_io (Action e, f) = Vis e f
  get_io (Bind t c, f) = get_io (t, get_io (c, f))

  get_io (Bind (Action Read) (λv. Action (Print v)), λx. Ret)
=
  get_io (Action Read, λv. get_io (Action (Print v), λx. Ret))
=
  Vis Read (λv. Vis (Print v) (λx. Ret))

*)

Overload Match1 = “λv c p1 x y. If (IsEq c v) (Let p1 (Proj c 0 v) x) y”
Overload Match2 = “λv c p1 p2 x. Let p1 (Proj c 0 v) (Let p2 (Proj c 1 v) x)”

Overload Pair = “λx y. Cons "pair" [x;y]”
Overload Return = “λx. Cons "Return" [x]”
Overload Bind = “λx y. Cons "Bind" [x;y]”

Definition GET_IO_def:
  GET_IO =
     Rec "get_in" "a"
       (Match2 (Var "a") "pair" "a1" "f"
          (Match1 (Var "a1") "Return" "x" (App (Var "f") (Var "x"))
             (Match1 (Var "a1") "Action" "e" (Cons "Vis" [Var "e"; Var "f"])
                (Match2 (Var "a1") "Bind" "t" "c"
                   (App (Var "get_io")
                      (Pair (Var "t")
                         (App (Var "get_io") (Pair (Var "c") (Var "f")))))))))
End

Definition get_io_def:
  get_io x = App GET_IO (Cons "pair" [x; Lam "x" (Cons "Ret" [])])
End

Definition semantics_def:
  semantics exp = eval_io (get_io exp)
End

Theorem Match1_Return:
  eval (Match1 (Return x) "Return" "x" t y) =
  eval (subst "x" (Proj "Return" 0 (Return x)) t)
Proof
  ntac 11 (simp [Once eval_thm,is_eq_def,subst_def])
  \\ once_rewrite_tac [eval_thm]
QED

Triviality LNTH_lemma:
  LNTH 0 (x:::ts) = SOME x ∧
  LNTH 1 (x:::y:::ts) = SOME y
Proof
  rewrite_tac [LNTH,DECIDE “1 = SUC 0”] \\ fs []
QED

Theorem semantics_Return:
  semantics (Return x) = Ret Termination
Proof
  fs [semantics_def]
  \\ fs [get_io_def,eval_io_def]
  \\ simp [Once io_unfold,AllCaseEqs()]
  \\ fs [io_distinct]
  \\ conj_asm2_tac THEN1 fs []
  \\ simp [GET_IO_def]
  \\ simp [Once eval_thm]
  \\ once_rewrite_tac [eval_thm]
  \\ simp [subst_def]
  \\ ntac 55 (simp [Once eval_thm,dest_Closure_def,subst_def,
       subst_opt_def,el_def,is_eq_def,Match1_Return,LNTH_lemma])
QED

Overload Get_io = “λx f. App GET_IO (Pair x f)”

Theorem eval_GET_IO_Bind:
  (Get_io (Bind t (Lam v c)) f) =
  (Get_io t (Lam v (Get_io c f)))
Proof
  cheat (*
  fs [eval_thm] \\ IF_CASES_TAC \\ fs []
  \\ fs [GET_IO_def,dest_Closure_def]
  \\ once_rewrite_tac [eval_thm] \\ simp [subst_def]
  \\ fs [GSYM GET_IO_def]
  \\ cheat *)
QED

Theorem semantics_Bind_assoc:
  semantics (Bind (Bind x (Lam v y)) (Lam u z)) =
  semantics (Bind x (Lam v (Bind y (Lam u z))))
Proof
  fs [semantics_def,get_io_def]
  \\ qmatch_goalsub_abbrev_tac ‘_ rhs = _ lhs’
  \\ simp [eval_io_def]
  \\ once_rewrite_tac [io_unfold] \\ fs []
  \\ qsuff_tac ‘eval lhs = eval rhs’ THEN1 fs []
  \\ unabbrev_all_tac
  \\ rewrite_tac [eval_GET_IO_Bind]
  \\ cheat
QED

*)

val _ = export_theory();
