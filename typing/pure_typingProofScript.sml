open HolKernel Parse boolLib bossLib BasicProvers;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory;
open pure_cexpTheory pure_configTheory pure_typingTheory pure_typingPropsTheory

val _ = new_theory "pure_typingProof";

Theorem eval_op_type_safe:
  (type_atom_op op ts t ∧ t ≠ Bool ∧
   LIST_REL type_lit ls ts ⇒
  ∃res.
    eval_op op ls = SOME (INL res) ∧
    type_lit res t) ∧
  (type_atom_op op ts Bool ∧
   LIST_REL type_lit ls ts ⇒
  ∃res.
    eval_op op ls = SOME (INR res))
Proof
  rw[type_atom_op_cases, type_lit_cases] >> gvs[type_lit_cases, PULL_EXISTS]
  >- (
    ntac 2 $ last_x_assum mp_tac >> map_every qid_spec_tac [`ts`,`ls`] >>
    Induct_on `LIST_REL` >> rw[] >> gvs[type_lit_cases, concat_def]
    )
  >- (
    ntac 2 $ last_x_assum mp_tac >> map_every qid_spec_tac [`ts`,`ls`] >>
    Induct_on `LIST_REL` >> rw[] >> gvs[type_lit_cases, implode_def]
    )
  >- (IF_CASES_TAC >> gvs[])
QED


(********************)

val _ = export_theory();
