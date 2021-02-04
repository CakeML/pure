(*
  Semantics primitives shared between [thunkLangScript.sml] and
  [thunkLang_substScript.sml].

 *)
open HolKernel Parse boolLib bossLib term_tactic monadsyntax
     sumTheory;

val _ = new_theory "thunkLang_primitives";

Datatype:
  err = Type_error
      | Diverge
End

Definition sum_bind_def:
  sum_bind m f =
    case m of
      INL e => INL e
    | INR x => f x
End

Definition sum_ignore_bind_def:
  sum_ignore_bind m x = sum_bind m (K x)
End

Definition sum_choice_def:
  sum_choice (m1: 'a + 'b) (m2: 'a + 'b) =
    case m1 of
      INL _ => m2
    | INR _ => m1
End

Definition return_def[simp]:
  return = INR
End

Definition fail_def[simp]:
  fail = INL
End

val sum_monadinfo : monadinfo = {
  bind = “sum_bind”,
  ignorebind = SOME “sum_ignore_bind”,
  unit = “return”,
  fail = SOME “fail”,
  choice = SOME “sum_choice”,
  guard = NONE
  };

val _ = declare_monad ("sum", sum_monadinfo);
val _ = enable_monadsyntax ();
val _ = enable_monad "sum";

Definition map_def:
  map f [] = return [] ∧
  map f (x::xs) =
    do
      y <- f x;
      ys <- map f xs;
      return (y::ys)
    od
End

Definition can_def:
  can f x =
    case f x of
      INL _ => F
    | INR _ => T
End

Theorem map_MAP:
  map f (MAP g xs) = map (f o g) xs
Proof
  Induct_on ‘xs’ \\ simp [map_def]
QED

Theorem map_INL:
  map f xs = INL err ⇔
    ∃n. n < LENGTH xs ∧
        f (EL n xs) = INL err ∧
        ∀m. m < n ⇒ ∀e. f (EL m xs) ≠ INL e
Proof
  eq_tac
  >- (
    qid_spec_tac ‘err’
    \\ Induct_on ‘xs’
    \\ simp [map_def, sum_bind_def]
    \\ rw [CaseEq "sum"]
    >- (
      qexists_tac ‘0’
      \\ simp [])
    >- (
      first_x_assum (drule_then strip_assume_tac)
      \\ qexists_tac ‘SUC n’ \\ simp []
      \\ Cases \\ fs []))
  >- (
    simp [PULL_EXISTS]
    \\ qid_spec_tac ‘err’
    \\ Induct_on ‘xs’
    \\ simp [map_def, sum_bind_def]
    \\ gen_tac
    \\ gen_tac
    \\ Cases \\ simp []
    \\ rename1 ‘n < LENGTH xs’
    \\ rw [CaseEq "sum", DISJ_EQ_IMP]
    \\ first_x_assum (drule_then (drule_then strip_assume_tac))
    \\ simp [GSYM PULL_EXISTS]
    \\ conj_tac
    >- (
      first_assum (qspec_then ‘0’ mp_tac)
      \\ impl_tac >- simp []
      \\ strip_tac \\ fs []
      \\ Cases_on ‘f h’ \\ fs [])
    \\ first_x_assum irule
    \\ rw []
    \\ ‘SUC m < SUC n’ by fs []
    \\ first_x_assum drule \\ simp [])
QED

Theorem map_INR:
  map f xs = INR ys ⇒
    ∀n. n < LENGTH xs ⇒
        ∃y. f (EL n xs) = INR y
Proof
  qid_spec_tac ‘ys’
  \\ Induct_on ‘xs’
  \\ simp [map_def, sum_bind_def]
  \\ rpt gen_tac
  \\ simp [CaseEq "sum"]
  \\ strip_tac
  \\ Cases \\ fs []
QED

Theorem map_LENGTH:
  ∀xs ys.
    map f xs = INR ys ⇒ LENGTH ys = LENGTH xs
Proof
  Induct
  \\ simp [map_def, sum_bind_def]
  \\ gen_tac
  \\ Cases \\ simp []
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ rw [] \\ fs []
QED

(* TODO Urk *)
Theorem map_LIST_REL_mono:
  ∀xs ys vs ws.
    map f xs = INR vs ∧
    map g ys = INR ws ∧
    LIST_REL R xs ys ∧
    LIST_REL (λx y. R x y ⇒ Q (OUTR (f x)) (OUTR (g y))) xs ys ⇒
      LIST_REL Q vs ws
Proof
  Induct \\ simp [map_def]
  \\ gen_tac
  \\ Cases \\ simp [map_def, sum_bind_def]
  \\ rw [CaseEq "sum"] \\ fs []
  \\ first_x_assum (irule_at Any) \\ fs []
  \\ first_x_assum (irule_at Any) \\ fs []
  \\ first_x_assum drule \\ fs []
QED

val _ = export_theory ();

