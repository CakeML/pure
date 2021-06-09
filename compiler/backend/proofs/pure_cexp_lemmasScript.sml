
open HolKernel Parse boolLib bossLib term_tactic BasicProvers;
open arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory pred_setTheory finite_mapTheory;
open pure_miscTheory pure_cexpTheory pure_expTheory pure_exp_lemmasTheory;

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

Theorem subst_lets_for:
  ∀cn v l e f.  v ∉ FDOM f ⇒
    subst f (lets_for cn v l e) =
    lets_for cn v l (subst (FDIFF f (set (MAP SND l))) e)
Proof
  recInduct lets_for_ind >> rw[lets_for_def, subst_def] >>
  simp[FLOOKUP_DEF, fdiff_fdomsub_INSERT]
QED

Theorem subst_rows_of:
  ∀v l f.  v ∉ FDOM f ⇒
    subst f (rows_of v l) =
    rows_of v (MAP (λ(a,b,c). (a,b, subst (FDIFF f (set b)) c)) l)
Proof
  recInduct rows_of_ind >> rw[rows_of_def, subst_def]
  >- simp[FLOOKUP_DEF] >>
  simp[subst_lets_for, combinTheory.o_DEF]
QED

Theorem subst_exp_of:
  ∀f ce.
    exp_of (substc f ce) =
    subst (FMAP_MAP2 (λ(k,v). exp_of v) f) (exp_of ce)
Proof
  recInduct substc_ind >> rw[subst_def, substc_def, exp_of_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
  >- (simp[FLOOKUP_FMAP_MAP2] >> CASE_TAC >> gvs[exp_of_def])
  >- rw[MAP_EQ_f]
  >- (
    simp[subst_Apps] >> AP_TERM_TAC >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >> rw[MAP_EQ_f]
    )
  >- (simp[subst_Lams] >> AP_TERM_TAC >> simp[FDIFF_FMAP_MAP2])
  >- simp[DOMSUB_FMAP_MAP2]
  >- (
    rw[MAP_EQ_f] >> pairarg_tac >> rw[] >>
    first_x_assum drule >> rw[FDIFF_FMAP_MAP2]
    )
  >- simp[FDIFF_FMAP_MAP2]
  >- (
    simp[subst_rows_of, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    AP_TERM_TAC >> rw[MAP_EQ_f] >> pairarg_tac >> rw[] >>
    first_x_assum drule >> rw[] >>
    simp[fdiff_fdomsub_INSERT, FDIFF_FMAP_MAP2]
    )
QED

Theorem lets_for_APPEND:
  ∀ws1 ws2 cn ar v n w b.
    lets_for cn v (ws1 ++ ws2) b =
      lets_for cn v ws1 (lets_for cn v ws2 b)
Proof
  Induct >> rw[lets_for_def] >>
  PairCases_on `h` >> simp[lets_for_def]
QED


val _ = export_theory();
