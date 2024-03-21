open HolKernel Parse boolLib bossLib BasicProvers;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory;
open mlstringTheory;
open pure_configTheory;
open typeclass_typesTheory typeclass_env_impl_mapTheory
typeclass_tcexpTheory;

val _ = new_theory "typeclass_dict_construct";

Inductive dict_rel:
[~taut_lie]
  lie E v = SOME t ⇒ dict_rel_poly E (v,t) v
[~taut_spec]
  dict_rel_poly (v,t) v ∧ ⇒ dict_construct_over (v,t) v
[]
End











Inductive dict_construct_exp:
[~taut]
  dict_construct_poly_exp (Var v,t) (Var v,t)
[~spec]
  dict_construct_poly_exp env (Var v,t) ∧
  ⇒
  dict_construct_over_exp env (apply_arg as v)
End

val _ = export_theory ();
