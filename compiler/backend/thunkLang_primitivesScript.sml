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

Definition sum_bind_def[simp]:
  sum_bind (INL e) f = INL e ∧
  sum_bind (INR x) f = f x
End

Definition sum_choice_def[simp]:
  sum_choice (INL v: 'a + 'b) (m2: 'a + 'b) = m2 ∧
  sum_choice (INR x) m2 = INR x
End

Definition return_def[simp]:
  return = INR
End

Definition fail_def[simp]:
  fail = INL
End

Theorem sum_bind_assoc:
  sum_bind (sum_bind m f) g = sum_bind m (λx. sum_bind (f x) g)
Proof
  Cases_on ‘m’ \\ simp []
QED

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
    \\ Induct_on ‘xs’ \\ simp [map_def]
    \\ rpt gen_tac
    \\ Cases_on ‘f h’ \\ rw []
    >- (
       qexists_tac ‘0’
       \\ simp [])
    \\ Cases_on ‘map f xs’ \\ rw [] \\ fs []
    \\ qexists_tac ‘SUC n’ \\ simp []
    \\ Cases \\ fs [])
  >- (
    simp [PULL_EXISTS]
    \\ qid_spec_tac ‘err’
    \\ Induct_on ‘xs’ \\ simp [map_def]
    \\ gen_tac
    \\ gen_tac
    \\ Cases \\ simp []
    \\ rename1 ‘n < LENGTH xs’
    \\ Cases_on ‘f h’ \\ rw []
    >- (
      first_x_assum drule
      \\ simp []
      \\ impl_tac \\ rw []
      >- (
        ‘SUC m < SUC n’ by fs []
        \\ first_x_assum drule
        \\ simp [])
      \\ ‘0 < SUC n’ by fs []
      \\ first_x_assum drule
      \\ simp [])
    \\ reverse (Cases_on ‘map f xs’) \\ rw [] \\ fs []
    >- (
      pop_assum mp_tac
      \\ simp []
      \\ first_assum (irule_at Any) \\ simp []
      \\ rw [DISJ_EQ_IMP]
      \\ ‘SUC m < SUC n’ by fs []
      \\ first_x_assum drule
      \\ simp [])
    \\ first_x_assum irule
    \\ first_assum (irule_at Any) \\ rw []
    \\ ‘SUC m < SUC n’ by fs []
    \\ first_x_assum drule \\ simp [])
QED

Theorem map_INR:
  map f xs = INR ys ⇒
    ∀n. n < LENGTH xs ⇒ f (EL n xs) = INR (EL n ys)
Proof
  qid_spec_tac ‘ys’
  \\ Induct_on ‘xs’ \\ simp [map_def]
  \\ rpt gen_tac \\ strip_tac \\ Cases
  \\ Cases_on ‘f h’ \\ fs []
  \\ Cases_on ‘map f xs’ \\ gvs []
QED

Theorem map_LENGTH:
  ∀xs ys.
    map f xs = INR ys ⇒ LENGTH ys = LENGTH xs
Proof
  Induct \\ simp [map_def] \\ rw []
  \\ Cases_on `f h` \\ fs []
  \\ Cases_on `map f xs` \\ gvs []
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
  Induct \\ Cases_on ‘ys’ \\ simp [map_def]
  \\ qx_gen_tac ‘h1’
  \\ Cases_on `f h1` \\ fs []
  \\ Cases_on ‘g h’ \\ fs []
  \\ Cases_on ‘map f xs’ \\ fs []
  \\ Cases_on ‘map g t’ \\ fs [] \\ rw []
  \\ first_x_assum (irule_at Any) \\ fs []
  \\ first_x_assum (irule_at Any) \\ fs []
QED

Theorem map_EQ_f:
  ∀xs.
    (∀x. MEM x xs ⇒ f x = g x) ⇒
      map f xs = map g xs
Proof
  Induct \\ simp [map_def, sum_bind_def] \\ rw []
QED

val _ = export_theory ();

