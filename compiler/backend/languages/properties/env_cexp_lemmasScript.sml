Theory env_cexp_lemmas
Ancestors
  arithmetic list string alist option pair pred_set finite_map
  envLang pure_misc env_cexp
Libs
  BasicProvers dep_rewrite

val freevars_def = envLangTheory.freevars_def;
val Lams_def = envLangTheory.Lams_def;
val Apps_def = envLangTheory.Apps_def;

Theorem freevars_Lams[simp]:
  ∀vs e. freevars (Lams vs e) = freevars e DIFF set vs
Proof
  Induct >> rw[Lams_def, freevars_def] >> gvs[EXTENSION] >> rw[] >> metis_tac[]
QED

Theorem Lams_SNOC:
  (∀e. Lams [] e = e) ∧
  (∀vs v. Lams (SNOC v vs) e = Lams vs (Lam v e))
Proof
  conj_tac >- rw[Lams_def] >>
  Induct >> rw[Lams_def]
QED

Theorem freevars_Apps[simp]:
  ∀es e. freevars (Apps e es) = freevars e ∪ BIGUNION (set (MAP freevars es))
Proof
  Induct >> rw[Apps_def, freevars_def] >> simp[UNION_ASSOC]
QED

Theorem Apps_SNOC:
  (∀x. Apps x [] = x) ∧
  (∀ys x y. Apps x (SNOC y ys) = App (Apps x ys) y)
Proof
  conj_tac >- rw[Apps_def] >>
  Induct >> rw[Apps_def]
QED

Theorem freevars_lets_for:
  ∀n c v l b. freevars (lets_for n c v l b) =
    case l of
      [] => freevars b
    | _ => v INSERT (freevars b DIFF set (MAP SND l))
Proof
  recInduct lets_for_ind >> rw[lets_for_def, freevars_def] >>
  rpt (CASE_TAC >> gvs[lets_for_def]) >> simp[EXTENSION] >>
  metis_tac[]
QED

Theorem MAPi_ID[local,simp]:
  ∀l. MAPi (λn v. v) l = l
Proof
  Induct >> rw[combinTheory.o_DEF]
QED

Theorem freevars_Disj:
  freevars (Disj v cns) = if cns = [] then {} else {v}
Proof
  Induct_on `cns` >> rw[Disj_def, freevars_def] >>
  PairCases_on `h` >> rw[Disj_def, freevars_def]
QED

Theorem freevars_rows_of:
  ∀v l eopt. freevars (rows_of v l eopt) =
    case l of
    | [] => (
        case eopt of
        | NONE => {}
        | SOME ([],e) => freevars e
        | SOME (_, e) => v INSERT freevars e)
    | _ => v INSERT (case eopt of NONE => {} | SOME (_,e) => freevars e) ∪
           BIGUNION (set (MAP (λ(cn,vs,b). freevars b DIFF set vs) l))
Proof
  recInduct rows_of_ind >> rw[rows_of_def, freevars_def]
  >- (
    rpt CASE_TAC >> gvs[freevars_def, freevars_Disj] >> simp[GSYM INSERT_SING_UNION]
    ) >>
  Cases_on `rest` >> gvs[combinTheory.o_DEF, rows_of_def, freevars_def] >>
  simp[freevars_lets_for] >>
  rpt CASE_TAC >> gvs[EXTENSION, combinTheory.o_DEF, rows_of_def, freevars_def] >>
  Cases_on `vs` >> gvs[] >> metis_tac[]
QED

(* TODO There's nothing called freevars_cexp for envLang? *)

(*
Theorem freevars_exp_of:
  ∀ce. freevars (exp_of ce) = freevars_cexp ce
Proof
  recInduct freevars_cexp_ind >> rw[exp_of_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, freevars_def]
  >- (ntac 2 AP_TERM_TAC >> rw[MAP_EQ_f])
  >- (ntac 3 AP_TERM_TAC >> rw[MAP_EQ_f])
  >- (
    simp[LAMBDA_PROD, GSYM FST_THM] >>
    AP_THM_TAC >> ntac 4 AP_TERM_TAC >> rw[MAP_EQ_f] >>
    pairarg_tac >> gvs[] >> res_tac
    )
  >- simp[DELETE_DEF]
  >- (
    AP_TERM_TAC >> simp[freevars_rows_of] >> Cases_on `css` >> gvs[] >>
    PairCases_on `h` >> gvs[] >> rw[EXTENSION, PULL_EXISTS] >>
    simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> metis_tac[]
    )
QED
 *)

