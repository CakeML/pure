(*
   Verification of pure_letrec_fun, i.e. simplification of Letrec.
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open arithmeticTheory listTheory alistTheory optionTheory pairTheory dep_rewrite
     pred_setTheory relationTheory rich_listTheory finite_mapTheory wordsTheory;
open pure_expTheory pure_exp_lemmasTheory pure_exp_relTheory pure_evalTheory
     pure_congruenceTheory pure_miscTheory pure_eval_lemmasTheory
     pure_letrecTheory topological_sortTheory;

val _ = new_theory "pure_letrec_funProof";

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

(******************** Definitions ********************)

(* the input is a variable specification: recursive calls will be made
   with these arguments in this order:
    - NONE indicates var value can change,
    - SOME (n,v) indicates that variable is n and will always have value v *)
Definition make_subst_def:
  make_subst [] = FEMPTY ∧
  make_subst (a::args) =
    case a of
    | NONE => make_subst args
    | SOME (n,v) => make_subst args |+ (n,v)
End

(* the first list is the arg specification
   the second list is the long form (must be same length as first list)
   the third list is the short form (only contains values for NONE vars) *)
Inductive args_rel:
  (args_rel [] [] [])
  ∧
  (∀args x xs ys.
     args_rel args xs ys ⇒
     args_rel (NONE::args) (x::xs) (x::ys))
  ∧
  (∀v w args xs ys.
     args_rel args xs ys ⇒
     args_rel (SOME (v,w)::args) (Var v::xs) ys)
End

Inductive body_rel:
  (* recursive function f does not appear *)
  (∀x.
     f ∉ freevars x ⇒
     body_rel f args x (subst (make_subst args) x))
  ∧
  (* This is the recursive call function: short form on LHS; long form on RHS *)
  (∀xs ys.
     args_rel args xs ys ⇒
     body_rel f args (Apps (Var f) ys)
                     (Apps (Var f) xs))
  ∧
  (* Lam - one must not bind the vars that are not to change *)
  (∀v x y.
     (∀n z. MEM (SOME (n,z)) args ⇒ v ≠ n) ∧
     body_rel f args x y ⇒
     body_rel f args (Lam v x) (Lam v y))
  ∧
  (* Var - when we have a "constant" variable *)
  (∀v w. MEM (SOME (v,w)) args ⇒
    body_rel f args w (Var v))
  ∧
  (* Var - when we have a regular variable*)
  (∀v.
    (∀w. ¬ MEM (SOME (v,w)) args) ⇒
    body_rel f args (Var v) (Var v))
  ∧
  (* Prim *)
  (∀p xs ys.
     LIST_REL (body_rel f args) xs ys ⇒
     body_rel f args (Prim p xs) (Prim p ys))
  ∧
  (* Letrec - no shadowing, just as in Lam case *)
  (∀xs x ys y.
    (∀n z v. MEM (SOME (n,z)) args ∧ MEM v (MAP FST xs) ⇒ v ≠ n) ∧
    MAP FST xs = MAP FST ys ∧
    LIST_REL (body_rel f args) (MAP SND xs) (MAP SND ys) ∧
    body_rel f args x y ⇒
    body_rel f args (Letrec xs x) (Letrec ys y))
  ∧
  (* App (when not a recursive call) *)
  (∀x1 x2 y1 y2.
    (∀es. App x1 x2 ≠ Apps (Var f) es ∧ App y1 y2 ≠ Apps (Var f) es) ∧
    body_rel f args x1 y1 ∧
    body_rel f args x2 y2 ⇒
    body_rel f args (App x1 x2) (App y1 y2))
End

Inductive letrec_fun:
  (* this what the optimisation wants to achieve in reverse -- but it might
     not be provable directly ...
  (∀vs b b1 f args.
    body_rel f args a b ∧
    ALL_DISTINCT vs ∧
    LIST_REL (λa v. case a of NONE => T | SOME (n,w) => w = Var n ∧ n = v)) args vs
    args_rel args (MAP Var vs) (MAP Var ws) ∧
    closed (Letrec [(f,Lams vs b)] y) ∧
    letrec_fun x y ⇒
    letrec_fun
      (Let f (Lams vs (Letrec [(f,Lams ws a)] (Apps (Var f) (MAP Var ws)))) x)
      (Letrec [(f,Lams vs b)] y))

  i.e.:
    Letrec map = λf xs. ... map f ys ... in
    map g [a,b,c]
  becomes:
    Let map = (λf xs. (Letrec map = (λxs. ... map ys ...) in map xs)) in
    map g [a,b,c]
  because:
    args = [SOME ("f", Var f); NONE] ⇒
    args_rel args (MAP Var [f,ys]) (MAP Var [ys])
    ∧
    body_rel "map" args (... map f ys ...) (... map ys ...)
      if no shadowing/other recursive calls etc.
      by recursion + args_rel args (MAP Var [f,ys]) (MAP Var [ys])
    ∧
    letrec_fun (map g [a,b,c]) (map g [a,b,c]) ∧ LIST_REL ... args vs ∧ closed ...
    trivially

    ... so how about this one instead: *)
  (∀vs ws a b f args.
    body_rel f args a b ∧
    ALL_DISTINCT vs ∧
    args_rel args (MAP Var vs) (MAP Var ws) ∧
    freevars (Lams vs b) ⊆ {f} ⇒
    letrec_fun
      (Letrec [(f,Lams ws (subst (make_subst args) a))]
                 (Lams ws (subst (make_subst args) a)))
      (Letrec [(f,Lams vs b)] (Lams vs b)))
  ∧
  (∀vs ws a b f args xs ys.
    body_rel f args a b ∧
    args_rel args xs ys ∧
    ALL_DISTINCT vs ∧
    args_rel args (MAP Var vs) (MAP Var ws) ∧
    freevars (Lams vs b) ⊆ {f} ⇒
    letrec_fun
      (Apps (Letrec [(f,Lams ws (subst (make_subst args) a))]
                       (Lams ws (subst (make_subst args) a))) xs)
      (Apps (Letrec [(f,Lams vs b)] (Lams vs b)) ys))
  ∧

  (* cases below are just recursion *)
  (∀n.
    letrec_fun (Var n) (Var n))
  ∧
  (∀n x y.
    letrec_fun x y ⇒
    letrec_fun (Lam n x) (Lam n y))
  ∧
  (∀f g x y.
    letrec_fun f g ∧ letrec_fun x y ⇒
    letrec_fun (App f x) (App g y))
  ∧
  (∀n xs ys.
    LIST_REL letrec_fun xs ys ⇒
    letrec_fun (Prim n xs) (Prim n ys))
  ∧
  (∀xs ys x y.
    LIST_REL letrec_fun (MAP SND xs) (MAP SND ys) ∧
    MAP FST xs = MAP FST ys ∧ letrec_fun x y ⇒
    letrec_fun (Letrec xs x) (Letrec ys y))
End


(******************** Lemmas ********************)

Theorem subst_make_subst_unchanged:
    (∀n v. MEM (SOME (n,v)) args ⇒ v = Var n)
  ⇒ subst (make_subst args) e = e
Proof
  rw[] >> irule subst_id >>
  pop_assum mp_tac >> qid_spec_tac `args` >>
  Induct >> rw[make_subst_def] >>
  Cases_on `h` >> gvs[] >> Cases_on `x` >> gvs[FLOOKUP_UPDATE] >>
  FULL_CASE_TAC >> gvs[]
QED

Theorem args_rel_LENGTH:
  ∀l xs ys.
    args_rel l xs ys
  ⇒ LENGTH l = LENGTH xs ∧ LENGTH ys ≤ LENGTH l
Proof
  Induct_on `args_rel` >> rw[]
QED

Theorem args_rel_imp_LIST_REL:
  ∀l xs ys.
    args_rel l xs ys
  ⇒ LIST_REL (λa x. case a of NONE => T | SOME (v,w) => Var v = x) l xs
Proof
  Induct_on `args_rel` >> rw[] >> gvs[MAP_EQ_CONS]
QED

Theorem args_rel_empty_args[simp]:
  ∀xs ys. args_rel [] xs ys ⇔ xs = [] ∧ ys = []
Proof
  rw[Once args_rel_cases]
QED

Theorem body_rel_empty_args[simp]:
  ∀f a b. body_rel f [] a b ⇒ a = b
Proof
  strip_tac >> Induct_on `body_rel` >> rw[make_subst_def] >>
  gvs[LIST_REL_EL_EQN, EL_MAP] >> simp[LIST_EQ_REWRITE] >> rw[] >>
  rename1 `n < _` >> first_x_assum drule >> strip_tac >>
  Cases_on `EL n xs` >> Cases_on `EL n ys` >> gvs[] >>
  last_x_assum mp_tac >> simp[Once LIST_EQ_REWRITE, EL_MAP] >>
  disch_then drule >> simp[]
QED

Theorem letrec_fun_refl:
  ∀x. letrec_fun x x
Proof
  recInduct freevars_ind >> rw[]
  >- simp[Once letrec_fun_cases]
  >- (
    simp[Once letrec_fun_cases] >> disj2_tac >>
    rw[LIST_REL_EL_EQN] >> first_x_assum irule >> simp[EL_MEM]
    )
  >- simp[Once letrec_fun_cases]
  >- simp[Once letrec_fun_cases]
  >- (
    simp[Once letrec_fun_cases] >> ntac 2 disj2_tac >>
    rw[LIST_REL_EL_EQN, EL_MAP] >> first_x_assum irule >>
    qexists_tac `FST (EL n lcs)` >> simp[EL_MEM]
    )
QED

(* TODO not sure if these are currently true *)
Theorem letrec_fun_freevars:
  ∀x y. letrec_fun x y ⇒ freevars x = freevars y
Proof
  cheat (* TODO *)
QED

Theorem letrec_fun_subst1:
  ∀x y a b s.
    letrec_fun x y ∧ letrec_fun a b
  ⇒ letrec_fun (subst1 s a x) (subst1 s b y)
Proof
  cheat (* TODO *)
QED

Theorem letrec_fun_subst:
  ∀x y. letrec_fun x y ⇒
    ∀f g. fmap_rel letrec_fun f g
  ⇒ letrec_fun (subst f x) (subst g y)
Proof
  cheat (* TODO *)
QED


(******************** Theorems ********************)

Theorem letrec_fun_correct:
  letrec_fun a b ∧ closed a ∧ closed b ⇒ (a ≃ b) T
Proof
  rw[] >> irule eval_to_sim_thm >> gvs[] >>
  qexists_tac `letrec_fun` >> gvs[] >>
  simp[eval_to_sim_def] >> rpt (pop_assum kall_tac) >>
  simp[Once SWAP_FORALL_THM] >>
  recInduct eval_wh_to_ind >> rw[]
  >- (
    rename1 `Lam v e` >>
    qpat_x_assum `letrec_fun _ _` mp_tac >> simp[Once letrec_fun_cases] >> rw[]
    >- (Cases_on `xs` using SNOC_CASES >> gvs[Apps_SNOC]) >>
    simp[eval_wh_to_def] >> rw[] >>
    irule letrec_fun_subst1 >> simp[letrec_fun_refl]
    )
  >- (
    rename1 `App a b` >>
    qpat_x_assum `letrec_fun _ _` mp_tac >>
    simp[Once letrec_fun_cases] >> reverse (rw[])
    >- (
      simp[eval_wh_to_def] >> IF_CASES_TAC >> gvs[] >- metis_tac[] >>
      first_x_assum drule_all >> rw[] >>
      Cases_on `dest_wh_Closure (eval_wh_to k a)` >> gvs[]
      >- (qexists_tac `ck` >> Cases_on `eval_wh_to k a` >> gvs[]) >>
      Cases_on `eval_wh_to k a` >> gvs[] >>
      rename1 `eval_wh_to _ a = wh_Closure s ea` >>
      rename1 `eval_wh_to _ g = wh_Closure _ eg` >>
      IF_CASES_TAC >> gvs[]
      >- (
        qexists_tac `0` >> simp[] >> IF_CASES_TAC >> gvs[] >>
        drule eval_wh_inc >> disch_then $ qspec_then `ck` $ assume_tac o GSYM >>
        gvs[]
        ) >>
      gvs[bind1_def] >>
      last_x_assum $ qspec_then `subst1 s y eg` mp_tac >> impl_keep_tac
      >- (
        simp[closed_def] >> once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
        DEP_REWRITE_TAC[freevars_subst] >> simp[SUBSET_DIFF_EMPTY, SUBSET_DEF] >>
        imp_res_tac eval_wh_to_Closure_freevars_SUBSET >>
        gvs[closed_def, NIL_iff_NOT_MEM] >>
        irule letrec_fun_subst1 >> simp[]
        ) >>
      strip_tac >> gvs[] >>
      Cases_on `eval_wh_to (k - 1) (subst1 s b ea) = wh_Diverge` >> gvs[]
      >- (
        qexists_tac `ck'` >> IF_CASES_TAC >> gvs[] >>
        drule eval_wh_to_agree >>
        disch_then $ qspec_then `ck + k` $ assume_tac o GSYM >> gvs[]
        ) >>
      qexists_tac `ck + ck'` >> gvs[] >>
      qspecl_then [`ck + (ck' + k)`,`g`,`ck + k`] assume_tac eval_wh_inc >> gvs[] >>
      qspecl_then [`ck + (ck' + k) - 1`,`subst1 s y eg`,`ck' + k - 1`]
        assume_tac eval_wh_inc >>
      gvs[] >>
      Cases_on `eval_wh_to (k - 1) (subst1 s b ea)` >> gvs[]
      ) >>
    cheat (* TODO *)
    )
  >- (
    rename1 `Letrec fns e` >>
    qpat_x_assum `letrec_fun _ _` mp_tac >>
    simp[Once letrec_fun_cases] >> reverse (rw[])
    >- (
      simp[eval_wh_to_def] >> IF_CASES_TAC >> gvs[]
      >- (qexists_tac `0` >> simp[]) >>
      last_x_assum irule >>
      DEP_REWRITE_TAC[subst_funs_eq_subst] >> simp[] >>
      DEP_REWRITE_TAC[IMP_closed_subst] >>
      simp[FDOM_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      simp[GSYM FST_THM] >> reverse (rpt conj_tac)
      >- (
        irule letrec_fun_subst >> simp[] >>
        irule fmap_rel_FUPDATE_LIST_same >>
        simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
        gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
        map_every qpat_abbrev_tac [`a = EL n fns`,`b = EL n ys`] >>
        PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
        simp[Once letrec_fun_cases] >> disj2_tac >> disj2_tac >>
        simp[LIST_REL_EL_EQN, EL_MAP] >> first_x_assum drule >> simp[]
        ) >>
      ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> simp[] >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >> metis_tac[]
      )
    >- (
      Cases_on `xs` using SNOC_CASES >> gvs[Apps_SNOC] >>
      imp_res_tac args_rel_LENGTH >> gvs[Lams_def, make_subst_def, Apps_def] >>
      simp[eval_wh_to_def] >> IF_CASES_TAC >> gvs[]
      >- (qexists_tac `0` >> simp[]) >>
      last_x_assum irule >>
      imp_res_tac body_rel_empty_args >> gvs[] >> csimp[letrec_fun_refl] >>
      DEP_REWRITE_TAC[subst_funs_eq_subst, IMP_closed_subst] >> simp[] >>
      simp[FDOM_FUPDATE_LIST] >>
      ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> simp[]
      )
    >- (
      simp[eval_wh_to_def] >> IF_CASES_TAC >> gvs[]
      >- (qexists_tac `0` >> simp[]) >>
      first_x_assum irule >>
      DEP_REWRITE_TAC[subst_funs_eq_subst, IMP_closed_subst] >>
      simp[EVERY_MAP, FDOM_FUPDATE_LIST] >> rpt conj_tac
      >- (ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> simp[])
      >- (ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> simp[]) >>
      irule letrec_fun_subst >> irule_at Any fmap_rel_FUPDATE_LIST_same >>
      simp[] >> rw[]
      >- (simp[Once letrec_fun_cases] >> disj1_tac >> metis_tac[]) >>
      cheat (* TODO *)
      )
    ) >>
  rename1 `Prim p xs` >>
  qpat_x_assum `letrec_fun _ _` mp_tac >>
  simp[Once letrec_fun_cases] >> rw[]
  >- (
    rename1 `Prim _ _ = _ _ zs` >>
    Cases_on `zs` using SNOC_CASES >> gvs[Apps_SNOC]
    )
  >- (
    qexists_tac ‘0’
    \\ simp [eval_wh_to_def]
    \\ Cases_on ‘p’ \\ fs [LIST_REL_EL_EQN]
    >- (
      IF_CASES_TAC \\ gvs []
      \\ fs [LENGTH_EQ_NUM_compute])
    >- (
      IF_CASES_TAC \\ gvs []
      \\ fs [LENGTH_EQ_NUM_compute])
    >- (
      IF_CASES_TAC \\ gvs []
      \\ fs [LENGTH_EQ_NUM_compute])
    >- (
      Cases_on ‘ys = []’ \\ fs []
      >- (
        fs [get_atoms_def, AllCaseEqs ()]
        \\ CASE_TAC \\ fs []
        \\ CASE_TAC \\ fs []
        \\ CASE_TAC \\ fs [])
      \\ ‘xs ≠ []’ by (strip_tac \\ fs [])
      \\ simp [get_atoms_MAP_Diverge])
    >- (
      Cases_on ‘ys = []’ \\ fs []
      \\ ‘xs ≠ []’ by (strip_tac \\ fs [])
      \\ simp [MEM_MAP]
      \\ IF_CASES_TAC \\ fs []
      \\ Cases_on `xs` \\ gvs[] \\ Cases_on `ys` \\ gvs[]
      )
    )
  >- (
    rename1 `Prim _ _ = _ _ zs` >>
    Cases_on `zs` using SNOC_CASES >> gvs[Apps_SNOC]
    ) >>
  Cases_on `p` >> gvs[eval_wh_to_def]
  >- (
    IF_CASES_TAC >> gvs[LIST_REL_EL_EQN] >>
    `∃x1 x2 x3. xs = [x1;x2;x3]` by fs[LENGTH_EQ_NUM_compute] >>
    `∃y1 y2 y3. ys = [y1;y2;y3]` by fs[LENGTH_EQ_NUM_compute] >>
    rgs[wordsTheory.NUMERAL_LESS_THM, DISJ_IMP_THM, FORALL_AND_THM] >>
    qpat_x_assum ‘letrec_fun x1 _’ assume_tac >>
    first_assum (drule_all_then strip_assume_tac) >> gvs[] >>
    reverse (Cases_on `eval_wh_to (k - 1) x1`) >> gvs[]
    >- (qexists_tac `ck` >> gvs[])
    >- (qexists_tac `ck` >> gvs[])
    >- (qexists_tac `ck` >> gvs[])
    >- (qexists_tac `ck` >> gvs[]) >>
    reverse (IF_CASES_TAC) >> gvs[]
    >- (
      reverse (IF_CASES_TAC) >> gvs[]
      >- (qexists_tac `ck` >> gvs[])
      >- (
        qexists_tac `ck` >> gvs[] >>
        Cases_on `l` >> gvs[] >> Cases_on `ys'` >> gvs[]
        ) >>
      qpat_x_assum ‘letrec_fun x3 _’ assume_tac >>
      first_assum (drule_all_then strip_assume_tac) >> gvs[] >>
      reverse (Cases_on `eval_wh_to (k - 1) x3`) >> gvs[]
      >- (
        qexists_tac `ck'` >>
        Cases_on `eval_wh_to (ck' + k - 1) y1 = wh_Diverge` >> gvs[] >>
        drule eval_wh_to_agree >>
        disch_then (qspec_then `ck + k - 1` assume_tac) >> gvs[]
        ) >>
      qspecl_then [`ck + ck' + k - 1`,`y1`,`ck + k - 1`] mp_tac eval_wh_inc >>
      gvs[] >> strip_tac >>
      qspecl_then [`ck + ck' + k - 1`,`y3`,`ck' + k - 1`] mp_tac eval_wh_inc >>
      gvs[] >> strip_tac >>
      qexists_tac `ck + ck'` >> gvs[]
      )
    >- (
      qexists_tac `ck` >> gvs[] >>
      Cases_on `l` >> gvs[] >> Cases_on `ys'` >> gvs[]
      )
    >- (
      qpat_x_assum ‘letrec_fun x2 _’ assume_tac >>
      first_assum (drule_all_then strip_assume_tac) >> gvs[] >>
      reverse (Cases_on `eval_wh_to (k - 1) x2`) >> gvs[]
      >- (
        qexists_tac `ck'` >>
        Cases_on `eval_wh_to (ck' + k - 1) y1 = wh_Diverge` >> gvs[] >>
        drule eval_wh_to_agree >>
        disch_then (qspec_then `ck + k - 1` assume_tac) >> gvs[]
        ) >>
      qspecl_then [`ck + ck' + k - 1`,`y1`,`ck + k - 1`] mp_tac eval_wh_inc >>
      gvs[] >> strip_tac >>
      qspecl_then [`ck + ck' + k - 1`,`y2`,`ck' + k - 1`] mp_tac eval_wh_inc >>
      gvs[] >> strip_tac >>
      qexists_tac `ck + ck'` >> gvs[]
      )
    )
  >- (
    IF_CASES_TAC >> gvs[] >> gvs[LIST_REL_EL_EQN] >>
    `∃x. xs = [x]` by fs[LENGTH_EQ_NUM_compute] >>
    `∃y. ys = [y]` by fs[LENGTH_EQ_NUM_compute] >>
    gvs[wordsTheory.NUMERAL_LESS_THM] >>
    first_x_assum drule_all >> rw[] >>
    Cases_on `eval_wh_to (k - 1) x` >> gvs[] >>
    qexists_tac `ck` >> gvs[] >>
    IF_CASES_TAC >> gvs[] >>
    IF_CASES_TAC >> gvs[]
    )
  >- (
    IF_CASES_TAC >> gvs[] >> gvs[LIST_REL_EL_EQN] >>
    `∃x. xs = [x]` by fs[LENGTH_EQ_NUM_compute] >>
    `∃y. ys = [y]` by fs[LENGTH_EQ_NUM_compute] >>
    gvs[wordsTheory.NUMERAL_LESS_THM] >>
    first_assum (drule_all_then strip_assume_tac) >>
    reverse (Cases_on `eval_wh_to (k - 1) x`) >> gvs[]
    >- (qexists_tac `ck` >> gvs[])
    >- (qexists_tac `ck` >> gvs[])
    >- (qexists_tac `ck` >> gvs[])
    >- (qexists_tac `ck` >> gvs[]) >>
    reverse IF_CASES_TAC >> gvs[]
    >- (qexists_tac `ck` >> gvs[])
    >- (qexists_tac `ck` >> gvs[]) >>
    first_x_assum drule >> rw[] >>
    last_x_assum drule >> impl_tac
    >- (
      gvs[closed_def, EMPTY_iff_NOTIN] >>
      CCONTR_TAC >> gvs[] >>
      imp_res_tac eval_wh_to_freevars_SUBSET >> gvs[MEM_MAP]
      >- (
        pop_assum kall_tac >> pop_assum mp_tac >> simp[PULL_EXISTS] >>
        goal_assum drule >> simp[EL_MEM]
        )
      >- (
        pop_assum mp_tac >> simp[PULL_EXISTS] >>
        goal_assum drule >> simp[EL_MEM]
        )
      ) >>
    rw[] >>
    reverse (Cases_on `eval_wh_to (k - 1) (EL n l)`) >> gvs[]
    >- (
      qexists_tac `ck'` >>
      Cases_on `eval_wh_to (ck' + k - 1) y = wh_Diverge` >> gvs[] >>
      drule eval_wh_to_agree >>
      disch_then (qspec_then `ck + k - 1` (assume_tac o GSYM)) >> gvs[]
      ) >>
    qspecl_then [`ck + ck' + k - 1`,`y`,`ck + k - 1`] mp_tac eval_wh_inc >>
    gvs[] >> strip_tac >>
    qspecl_then [`ck + ck' + k - 1`,`EL n ys'`,`ck' + k - 1`]
      mp_tac eval_wh_inc >>
    gvs[] >> strip_tac >>
    qexists_tac `ck + ck'` >> gvs[]
    )
  >- (
    CASE_TAC >> gvs[]
    >- (
      qsuff_tac `get_atoms (MAP (λa. eval_wh_to (k − 1) a) ys) = NONE`
      >- (rw[] >> qexists_tac `0` >> simp[]) >>
      gs [get_atoms_NONE_eq]
      \\ gvs [MEM_MAP, EVERY_MAP, EVERY_MEM, MEM_EL, PULL_EXISTS,
              LIST_REL_EL_EQN]
      \\ simp [RIGHT_EXISTS_AND_THM]
      \\ conj_tac
      >- (
        qx_gen_tac ‘m’
        \\ strip_tac
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_all_then (qx_choose_then ‘ck’ assume_tac))
        \\ strip_tac
        \\ ‘eval_wh_to (k - 1) (EL m ys) ≠ wh_Diverge’
          by (strip_tac \\ gs [])
        \\ drule_then (qspec_then ‘ck + k - 1’ assume_tac) eval_wh_inc \\ gs []
        \\ Cases_on ‘eval_wh_to (k - 1) (EL m xs)’ \\ gs [])
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_all_then (qx_choose_then ‘ck’ assume_tac))
      \\ first_assum (irule_at Any)
      \\ CCONTR_TAC
      \\ drule_then (qspec_then ‘ck + k - 1’ assume_tac) eval_wh_inc \\ gs []
    ) >>
    Cases_on `x` >> gvs[]
    >- (
      gvs[get_atoms_SOME_NONE_eq, EL_MAP] >>
      qsuff_tac
        `∃ck. get_atoms (MAP (λa. eval_wh_to (ck + k − 1) a) ys) = SOME NONE`
      >- (rw[] >> qexists_tac `ck` >> simp[]) >>
      simp[get_atoms_SOME_NONE_eq] >> csimp[] >>
      gvs [EVERY_MEM, EXISTS_MAP, EXISTS_MEM, MEM_EL, PULL_EXISTS,
           LIST_REL_EL_EQN]
      \\ first_assum (irule_at Any)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_all_then (qx_choose_then ‘ck’ assume_tac))
      \\ qexists_tac ‘ck’
      \\ Cases_on ‘eval_wh_to (k - 1) (EL n xs)’ \\ gs []
    ) >>
    rename1 `SOME (SOME as)` >>
    qsuff_tac
      `∃ck. get_atoms (MAP (λa. eval_wh_to (ck + k − 1) a) ys) = SOME (SOME as)`
    >- (
      rw[]
      \\ qexists_tac `ck` \\ simp[]
      \\ CASE_TAC \\ gvs[]
      \\ CASE_TAC \\ gvs[]
      \\ CASE_TAC \\ gvs[]) >>
    gvs [get_atoms_SOME_SOME_eq, EVERY2_MAP, MEM_EL, PULL_EXISTS]
    \\ map_every (fn pat => qpat_x_assum pat mp_tac)
      [`∀e1 n. n < _ ⇒ _`, `LIST_REL _ _ _`, `EVERY _ _`, `EVERY _ _`] >>
    qid_spec_tac `as` >>
    qpat_x_assum `LIST_REL _ _ _` mp_tac >>
    map_every qid_spec_tac [`ys`,`xs`] >>
    ho_match_mp_tac LIST_REL_strongind >> rw[] >>
    rename1 `LIST_REL _ _ as` >>
    qsuff_tac
      `∃ck. LIST_REL (λa a'. eval_wh_to (ck + k − 1) a = wh_Atom a') ys as`
    >- (
      disch_then (qx_choose_then ‘ck’ mp_tac)
      \\ pop_assum (qspec_then `h1` mp_tac) \\ simp[]
      \\ disch_then (qspec_then ‘0’ mp_tac) \\ simp []
      \\ disch_then drule_all \\ rw[]
      \\ qexists_tac `ck + ck'`
      \\ qspecl_then [`ck + ck' + k - 1`,`h2`,`ck' + k - 1`]
        assume_tac eval_wh_inc
      \\ gvs[LIST_REL_EL_EQN] \\ rw[]
      \\ qspecl_then [`ck + ck' + k - 1`,`EL n ys`,`ck + k - 1`]
        assume_tac eval_wh_inc
      \\ gvs[]
      ) >>
    last_x_assum irule >> simp[] \\ rw []
    \\ first_x_assum irule \\ gs []
    \\ qexists_tac ‘n’ \\ gs []
    )
  >- (
    imp_res_tac LIST_REL_LENGTH >>
    IF_CASES_TAC >> gvs[] >>
    `∃x1 x2. xs = [x1;x2]` by gvs[LENGTH_EQ_NUM_compute] >>
    `∃y1 y2. ys = [y1;y2]` by gvs[LENGTH_EQ_NUM_compute] >>
    rgs[DISJ_IMP_THM, FORALL_AND_THM] >>
    first_assum (drule_all_then strip_assume_tac) >>
    qpat_x_assum ‘letrec_fun x2 _’ assume_tac >>
    first_x_assum (dxrule_all_then strip_assume_tac) >>
    Cases_on `eval_wh_to (k - 1) x1 = wh_Diverge` >> gvs[]
    >- (qexists_tac `ck` >> gvs[]) >>
    IF_CASES_TAC >> gvs[]
    >- (qexists_tac `ck` >> gvs[]) >>
    Cases_on `eval_wh_to (k - 1) x2 = wh_Diverge` >> gvs[]
    >- (
      qexists_tac `0` >> gvs[] >> IF_CASES_TAC >> gvs[]
      >- (
        qspecl_then [`ck + k - 1`,`y1`,`k - 1`] assume_tac eval_wh_inc >>
        gvs[] >> EVERY_CASE_TAC >> gvs[]
        )
      >- (
        CCONTR_TAC >> drule eval_wh_inc >>
        disch_then $ qspec_then `ck' + k - 1` assume_tac >> gvs[]
        )
      ) >>
    qexists_tac `ck + ck'` >> simp[] >>
    qspecl_then [`ck + ck' + k - 1`,`y1`,`ck + k - 1`] mp_tac eval_wh_inc >>
    gvs[] >> strip_tac >>
    qspecl_then [`ck + ck' + k - 1`,`y2`,`ck' + k - 1`] mp_tac eval_wh_inc >>
    gvs[] >> strip_tac >>
    EVERY_CASE_TAC >> gvs[]
    )
QED

Theorem Letrec_Lams:
  body_rel g args a b ∧
  ALL_DISTINCT vs ∧
  args_rel args (MAP Var vs) (MAP Var ws) ∧
  closed (Letrec [(g,Lams vs b)] e)
  ⇒ Letrec [(g,Lams vs b)] e ≅
    Let g (Lams vs (Letrec [(g,Lams ws a)] (Apps (Var g) (MAP Var ws)))) e
Proof
  rw[] >> once_rewrite_tac[exp_eq_open_bisimilarity_freevars] >>
  irule open_bisimilarity_suff >> rw[] >>
  cheat (* TODO *)
QED

(**********)

val _ = export_theory();

