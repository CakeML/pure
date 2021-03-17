
open HolKernel Parse boolLib bossLib term_tactic BasicProvers;
open arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory pred_setTheory;
open pure_miscTheory pure_cexpTheory pure_exp_lemmasTheory;

val _ = new_theory "pure_cexp_lemmas";

Theorem freevars_cexp_equiv:
  ∀ce. freevars_cexp ce = set (freevars_cexp_l ce)
Proof
  recInduct freevars_cexp_ind >> rw[]
  >- (
    gvs[LIST_TO_SET_FLAT, LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF] >>
    AP_TERM_TAC >> rw[EXTENSION] >> metis_tac[]
    )
  >- (
    gvs[LIST_TO_SET_FLAT, LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF] >>
    AP_TERM_TAC >> rw[EXTENSION] >> metis_tac[]
    )
  >- (
    simp[LIST_TO_SET_FILTER] >> rw[EXTENSION] >> eq_tac >> rw[]
    )
  >- (
    simp[LIST_TO_SET_FILTER, LIST_TO_SET_FLAT, LIST_TO_SET_MAP, FORALL_PROD] >>
    simp[IMAGE_IMAGE, combinTheory.o_DEF, LAMBDA_PROD] >>
    rw[EXTENSION, EXISTS_PROD] >> metis_tac[]
    )
  >- (
    simp[LIST_TO_SET_FILTER, LIST_TO_SET_FLAT, LIST_TO_SET_MAP, FORALL_PROD] >>
    simp[IMAGE_IMAGE, combinTheory.o_DEF, LAMBDA_PROD] >>
    rw[EXTENSION, EXISTS_PROD] >> metis_tac[]
    )
  >- (
    AP_TERM_TAC >>
    simp[LIST_TO_SET_FILTER, LIST_TO_SET_FLAT, LIST_TO_SET_MAP, FORALL_PROD] >>
    simp[IMAGE_IMAGE, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[LIST_TO_SET_FILTER] >>
    rw[EXTENSION, EXISTS_PROD, PULL_EXISTS] >> metis_tac[]
    )
QED

Theorem freevars_lets_for:
  ∀c v l b. freevars (lets_for c v l b) =
    case l of
      [] => freevars b DIFF set (MAP SND l)
    | _ => v INSERT (freevars b DIFF set (MAP SND l))
Proof
  recInduct lets_for_ind >> rw[lets_for_def] >>
  CASE_TAC >> gvs[] >> simp[EXTENSION] >> metis_tac[]
QED

Triviality MAPi_ID[simp]:
  ∀l. MAPi (λn v. v) l = l
Proof
  Induct >> rw[combinTheory.o_DEF]
QED

Theorem freevars_rows_of:
  ∀v l. freevars (rows_of v l) =
    case l of
      [] => {}
    | _ => v INSERT BIGUNION (set (MAP (λ(cn,vs,b). freevars b DIFF set vs) l))
Proof
  recInduct rows_of_ind >> rw[rows_of_def] >> simp[freevars_lets_for] >>
  Cases_on `rest` >> gvs[combinTheory.o_DEF] >>
  CASE_TAC >> gvs[EXTENSION] >> metis_tac[]
QED

Theorem freevars_exp_of:
  ∀ce. freevars (exp_of ce) = freevars_cexp ce
Proof
  recInduct freevars_cexp_ind >> rw[exp_of_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF]
  >- (ntac 2 AP_TERM_TAC >> rw[MAP_EQ_f])
  >- (ntac 3 AP_TERM_TAC >> rw[MAP_EQ_f])
  >- simp[UNION_COMM]
  >- (
    simp[LAMBDA_PROD, GSYM FST_THM] >>
    AP_THM_TAC >> ntac 4 AP_TERM_TAC >> rw[MAP_EQ_f] >>
    pairarg_tac >> gvs[] >> res_tac
    )
  >- (
    simp[Once UNION_COMM] >> AP_TERM_TAC >>
    simp[freevars_rows_of] >> Cases_on `css` >> gvs[] >>
    PairCases_on `h` >> gvs[] >> rw[EXTENSION, PULL_EXISTS] >>
    simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> metis_tac[]
    )
QED

val _ = export_theory();
