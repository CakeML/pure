(*
   Defines a weak-head eval (eval_wh) and an unbounded eval function (eval)
*)
Theory pure_eval
Ancestors
  fixedPoint arithmetic list string alist option pair ltree llist
  bag pred_set relation rich_list finite_map pure_exp pure_value
Libs
  term_tactic dep_rewrite BasicProvers

(* weak-head values *)

Datatype:
  wh = wh_Constructor string (exp list)
     | wh_Closure string exp
     | wh_Atom lit
     | wh_Error
     | wh_Diverge
End

Overload wh_True = ``wh_Constructor "True" []``;
Overload wh_False = ``wh_Constructor "False" []``;

Definition freevars_wh_def[simp]:
  freevars_wh (wh_Constructor s es) = BIGUNION (set (MAP freevars es)) ∧
  freevars_wh (wh_Closure s e)      = freevars e DELETE s ∧
  freevars_wh _                     = {}
End

Definition freevars_wh_l_def[simp]:
  (freevars_wh_l (wh_Constructor s es) = FLAT (MAP freevars_l es)) ∧
  (freevars_wh_l (wh_Closure s e) = FILTER ($≠ s) (freevars_l e)) ∧
  (freevars_wh_l _ = [])
End

(* weak-head evalation *)

Definition dest_wh_Closure_def[simp]:
  dest_wh_Closure (wh_Closure s e) = SOME (s,e) ∧
  dest_wh_Closure _ = NONE
End

Definition dest_Atom_def:
  dest_Atom (wh_Atom x) = x
End

Definition error_Atom_def[simp]:
  error_Atom (wh_Atom x) = F ∧
  error_Atom wh_Diverge = F ∧
  error_Atom _ = T
End

Definition get_atoms_def:
  get_atoms vs =
    if EXISTS error_Atom vs then SOME NONE
    else if MEM wh_Diverge vs then NONE
    else SOME (SOME (MAP dest_Atom vs))
End

Definition is_eq_fail_def[simp]:
  is_eq_fail F t = F ∧
  is_eq_fail T t = (t ∈ monad_cns)
End

Definition eval_wh_to_def:
  eval_wh_to n (Var s) = wh_Error ∧
  eval_wh_to k (Lam s x) = wh_Closure s x ∧
  eval_wh_to k (App x y) =
    (let v = eval_wh_to k x in
       if v = wh_Diverge then wh_Diverge else
         case dest_wh_Closure v of
           NONE => wh_Error
         | SOME (s,body) => if k = 0 then wh_Diverge
                            else eval_wh_to (k − 1) (bind1 s y body)) ∧
  eval_wh_to k (Letrec f y) =
    (if k = 0 then wh_Diverge else eval_wh_to (k − 1) (subst_funs f y)) ∧
  eval_wh_to k (Prim p xs) =
    let vs = MAP (if k = 0n then K wh_Diverge else eval_wh_to (k-1)) xs in
      case p of
      | Cons s => wh_Constructor s xs
      | Proj s i =>
        (if LENGTH xs ≠ 1 then wh_Error else
           case HD vs of
           | wh_Constructor t ys => if t = s ∧ i < LENGTH ys
                                     then eval_wh_to (k-1) (EL i ys)
                                     else wh_Error
           | wh_Diverge => wh_Diverge
           | _ => wh_Error)
      | IsEq s i a =>
        (if LENGTH xs ≠ 1 then wh_Error else
           case HD vs of
           | wh_Constructor t ys => if is_eq_fail a t then wh_Error else
                                    if t ≠ s          then wh_False else
                                    if i = LENGTH ys  then wh_True
                                                      else wh_Error
           | wh_Diverge => wh_Diverge
           | _ => wh_Error)
      | If =>
        (if LENGTH xs ≠ 3 then wh_Error else
           case HD vs of
           | wh_Constructor t ys =>
              (if t = "True" ∧ ys = [] then EL 1 vs else
               if t = "False" ∧ ys = [] then EL 2 vs else wh_Error)
           | wh_Diverge => wh_Diverge
           | _ => wh_Error)
      | Seq =>
        (if LENGTH xs ≠ 2 then wh_Error else
         if HD vs = wh_Diverge ∨ HD vs = wh_Error then HD vs else
         LAST vs)
      | AtomOp op =>
        (case get_atoms vs of
         | NONE => wh_Diverge
         | SOME NONE => wh_Error
         | SOME (SOME as) =>
             case eval_op op as of
             | SOME (INL v) => wh_Atom v
             | SOME (INR T) => wh_True
             | SOME (INR F) => wh_False
             | NONE => wh_Error)
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λ(k,x).(k,(exp_size x)))`
  \\ rw [] \\ Cases_on ‘xs’ \\ fs []
End

Definition eval_wh_def:
  eval_wh e =
    case some k. eval_wh_to k e ≠ wh_Diverge of
    | SOME k => eval_wh_to k e
    | NONE => wh_Diverge
End


Definition no_err_eval_wh_def:
  no_err_eval_wh e = case eval_wh e of
                     | wh_Error => wh_Diverge
                     | wh => wh
End

Theorem eval_wh_to_Fail[simp]:
  eval_wh_to k Fail = wh_Error
Proof
  fs [eval_wh_to_def,get_atoms_def]
QED

Theorem eval_wh_eq_Diverge:
  eval_wh e = wh_Diverge ⇔ ∀k. eval_wh_to k e = wh_Diverge
Proof
  fs [eval_wh_def] \\ DEEP_INTRO_TAC some_intro
  \\ rw [] \\ metis_tac []
QED

Theorem eval_wh_neq_Diverge:
  eval_wh e ≠ wh_Diverge ⇔ ∃k. eval_wh_to k e ≠ wh_Diverge
Proof
  fs [eval_wh_eq_Diverge]
QED

Theorem eval_wh_inc:
  ∀m e n.
    eval_wh_to n e ≠ wh_Diverge ∧ n ≤ m ⇒
    eval_wh_to m e = eval_wh_to n e
Proof
  recInduct eval_wh_to_ind \\ rw []
  \\ fs [eval_wh_to_def]
  THEN1
   (Cases_on ‘eval_wh_to n x = wh_Diverge’ \\ fs []
    \\ first_x_assum drule_all \\ fs []
    \\ TOP_CASE_TAC \\ PairCases_on ‘x'’ \\ fs []
    \\ Cases_on ‘n = 0’ \\ fs [])
  THEN1 (Cases_on ‘n = 0’ \\ fs [])
  \\ Cases_on ‘∃s. p = Cons s’ THEN1 gvs [] \\ gvs []
  \\ Cases_on ‘p = Seq’ \\ gvs []
  THEN1
   (Cases_on ‘n = 0’ \\ fs []
    \\ Cases_on ‘LENGTH xs = 2’ \\ fs []
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ fs [PULL_FORALL]
    \\ full_simp_tac std_ss [SF DNF_ss]
    \\ last_assum (qspecl_then [‘h’,‘n-1’] assume_tac)
    \\ last_x_assum (qspecl_then [‘h'’,‘n-1’] assume_tac)
    \\ gvs []
    \\ Cases_on ‘eval_wh_to (n − 1) h = wh_Error’ \\ fs []
    \\ Cases_on ‘eval_wh_to (n − 1) h' = wh_Error’ \\ fs []
    \\ Cases_on ‘eval_wh_to (n − 1) h = wh_Diverge’ \\ fs []
    \\ Cases_on ‘eval_wh_to (n − 1) h' = wh_Diverge’ \\ fs [])
  \\ Cases_on ‘∃s. p = If’ \\ gvs []
  THEN1
   (Cases_on ‘n = 0’ \\ fs []
    \\ Cases_on ‘LENGTH xs = 3’ \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ first_assum (qspec_then ‘h’ assume_tac) \\ fs []
    \\ ‘n-1 ≤ k-1’ by fs []
    \\ first_x_assum (first_assum o mp_then (Pos last) mp_tac)
    \\ Cases_on ‘eval_wh_to (n − 1) h’ \\ fs []
    \\ rw [] \\ gvs [])
  \\ Cases_on ‘∃s. p = AtomOp s’ \\ gvs []
  THEN1
   (Cases_on ‘n = 0’ \\ fs []
    \\ rpt AP_THM_TAC \\ AP_TERM_TAC
    \\ fs [PULL_FORALL,AND_IMP_INTRO]
    THEN1 (
      gs [get_atoms_def, CaseEq "bool", CaseEq "option", MEM_MAP]
      \\ fs [GSYM pure_miscTheory.NIL_iff_NOT_MEM]
      \\ gs [EXISTS_MAP, combinTheory.o_DEF, EVERY_MAP])
    \\ gs [CaseEqs ["bool", "option", "sum"]]
    \\ qpat_x_assum ‘_ ≠ NONE’ mp_tac
    \\ simp [Once get_atoms_def]
    \\ gs [MEM_MAP, CaseEq "bool", EXISTS_MAP, EXISTS_MEM]
    \\ rw [] \\ gs []
    >- (
      ‘eval_wh_to (n - 1) a ≠ wh_Diverge’
        by (strip_tac \\ gs [])
      \\ ‘n-1 ≤ k-1’ by fs []
      \\ first_x_assum (drule_all_then assume_tac)
      \\ gs [get_atoms_def, MEM_MAP, EXISTS_MAP, EXISTS_MEM]
      \\ metis_tac [])
    \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
    \\ AP_TERM_TAC
    \\ rw [MAP_EQ_f]
    \\ first_x_assum irule
    \\ gs [SF SFY_ss])
  \\ Cases_on ‘∃s i. p = Proj s i’
  THEN1
   (Cases_on ‘n = 0’ \\ gvs []
    \\ Cases_on ‘LENGTH xs = 1’ \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ ‘n-1 ≤ k-1’ by fs []
    \\ rpt (first_x_assum (first_assum o mp_then (Pos last) mp_tac))
    \\ Cases_on ‘eval_wh_to (n − 1) h = wh_Diverge’ \\ fs []
    \\ Cases_on ‘eval_wh_to (n − 1) h’ \\ fs []
    \\ rw [] \\ fs [] \\ fs [AllCaseEqs()] \\ gvs [])
  \\ Cases_on ‘∃s i a. p = IsEq s i a’
  THEN1
   (Cases_on ‘n = 0’ \\ gvs []
    \\ Cases_on ‘LENGTH xs = 1’ \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ ‘n-1 ≤ k-1’ by fs []
    \\ rpt (first_x_assum (first_assum o mp_then (Pos last) mp_tac))
    \\ Cases_on ‘eval_wh_to (n − 1) h = wh_Diverge’ \\ fs [])
  \\ Cases_on ‘p’ \\ fs []
QED

Theorem eval_wh_to_agree:
  eval_wh_to k e ≠ wh_Diverge ∧
  eval_wh_to x e ≠ wh_Diverge ⇒
  eval_wh_to x e = eval_wh_to k e
Proof
  ‘k ≤ x ∨ x ≤ k’ by fs []
  \\ metis_tac [eval_wh_inc]
QED

Theorem eval_wh_eq:
  eval_wh e = v ⇔
    if v = wh_Diverge
    then ∀k. eval_wh_to k e = wh_Diverge
    else ∃k. eval_wh_to k e = v
Proof
  rw [] THEN1 fs [eval_wh_eq_Diverge]
  \\ eq_tac \\ rw []
  THEN1
   (fs [eval_wh_neq_Diverge]
    \\ qexists_tac ‘k’ \\ fs []
    \\ fs [eval_wh_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ match_mp_tac eval_wh_to_agree \\ fs [])
  THEN1
   (fs [eval_wh_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ match_mp_tac eval_wh_to_agree \\ fs [])
QED

Theorem eval_wh_to_IMP_eval_wh:
  eval_wh_to k e = v ∧ v ≠ wh_Diverge ⇒ eval_wh e = v
Proof
  strip_tac \\ gvs [eval_wh_eq]
  \\ qexists_tac ‘k’ \\ fs []
QED

Theorem eval_wh_Bottom:
  eval_wh Bottom = wh_Diverge
Proof
  fs [eval_wh_eq_Diverge,Bottom_def]
  \\ completeInduct_on ‘k’ \\ Cases_on ‘k’ \\ simp [Once eval_wh_to_def]
  \\ fs [subst_funs_def,bind_def,FUPDATE_LIST,FLOOKUP_DEF,closed_def,subst_def]
QED

Theorem eval_wh_Var:
  eval_wh (Var s) = wh_Error
Proof
  fs [eval_wh_eq,eval_wh_to_def]
QED

Theorem eval_wh_Lam:
  eval_wh (Lam s x) = wh_Closure s x
Proof
  fs [eval_wh_eq,eval_wh_to_def]
QED

Theorem eval_wh_App:
  eval_wh (App x y) =
     let v = eval_wh x in
       if v = wh_Diverge then wh_Diverge else
         case dest_wh_Closure v of
           NONE => wh_Error
         | SOME (s,body) => eval_wh (bind1 s y body)
Proof
  fs [] \\ Cases_on ‘eval_wh x = wh_Diverge’ \\ fs []
  THEN1 (fs [eval_wh_eq] \\ fs [eval_wh_to_def])
  \\ Cases_on ‘eval_wh x’ \\ fs [dest_wh_Closure_def]
  \\ TRY (fs [eval_wh_eq] \\ fs [eval_wh_to_def]
          \\ qexists_tac ‘k’ \\ fs [dest_wh_Closure_def] \\ NO_TAC)
  \\ fs [eval_wh_eq] \\ fs [eval_wh_to_def]
  \\ IF_CASES_TAC
  THEN1
   (rw [] \\ fs []
    \\ ‘eval_wh_to k x ≠ wh_Diverge’ by fs []
    \\ drule eval_wh_to_agree \\ pop_assum kall_tac
    \\ disch_then drule \\ fs [dest_wh_Closure_def])
  \\ fs []
  \\ qexists_tac ‘k+k'+1’ \\ fs []
  \\ ‘eval_wh_to (k+k'+1) x = eval_wh_to k x’ by (match_mp_tac eval_wh_inc \\ fs [])
  \\ fs [dest_wh_Closure_def,PULL_EXISTS]
  \\ qexists_tac ‘k+k'’ \\ fs []
  \\ ‘k' ≤ k + k'’ by fs []
  \\ metis_tac [eval_wh_inc]
QED

Theorem eval_wh_Letrec:
  eval_wh (Letrec f y) = eval_wh (subst_funs f y)
Proof
  fs [Once eval_wh_eq] \\ IF_CASES_TAC
  \\ fs [eval_wh_eq_Diverge,eval_wh_to_def]
  \\ qexists_tac ‘k+1’ \\ fs []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [eval_wh_eq] \\ qexists_tac ‘k’ \\ fs []
QED

Theorem eval_wh_Cons:
  eval_wh (Cons s xs) = wh_Constructor s xs
Proof
  fs [Once eval_wh_eq,eval_wh_to_def]
  \\ qexists_tac ‘1’ \\ fs []
QED

Theorem eval_wh_Fail:
  eval_wh Fail = wh_Error
Proof
  fs [eval_wh_def] \\ DEEP_INTRO_TAC some_intro \\ rw[]
QED

Theorem eval_wh_Seq:
  eval_wh (Seq x y) =
    if eval_wh x = wh_Error   then wh_Error   else
    if eval_wh x = wh_Diverge then wh_Diverge else
      eval_wh y
Proof
  fs []
  \\ Cases_on ‘eval_wh x = wh_Error’ \\ fs []
  THEN1 (fs [eval_wh_eq] \\ fs [eval_wh_to_def]
         \\ qexists_tac ‘k+1’ \\ fs [])
  \\ fs [] \\ Cases_on ‘eval_wh x = wh_Diverge’ \\ fs []
  THEN1 (fs [eval_wh_eq] \\ fs [eval_wh_to_def]
         \\ rw [] \\ Cases_on ‘k’ \\ gvs [])
  \\ fs [eval_wh_eq] \\ fs [eval_wh_to_def]
  \\ IF_CASES_TAC \\ fs []
  THEN1 (rw [] \\ gs [])
  \\ qexists_tac ‘k+k'+1’ \\ fs []
  \\ ‘eval_wh_to (k+k') x = eval_wh_to k x’ by (match_mp_tac eval_wh_inc \\ fs [])
  \\ ‘eval_wh_to (k+k') y = eval_wh_to k' y’ by (match_mp_tac eval_wh_inc \\ fs [])
  \\ fs [] \\ qexists_tac ‘k'’ \\ fs []
QED

Theorem eval_wh_If:
  eval_wh (If x y z) =
    if eval_wh x = wh_Diverge then wh_Diverge else
    if eval_wh x = wh_True    then eval_wh y  else
    if eval_wh x = wh_False   then eval_wh z  else wh_Error
Proof
  fs [] \\ Cases_on ‘eval_wh x = wh_Diverge’ \\ fs []
  THEN1 (fs [eval_wh_eq] \\ fs [eval_wh_to_def] \\ rw [])
  \\ Cases_on ‘eval_wh x’ \\ fs []
  \\ TRY (fs [eval_wh_eq] \\ fs [eval_wh_to_def]
          \\ qexists_tac ‘k+1’ \\ fs [] \\ NO_TAC)
  \\ fs [eval_wh_eq] \\ fs [eval_wh_to_def]
  \\ reverse (Cases_on ‘l=[]’) \\ gvs []
  THEN1 (qexists_tac ‘k+1’ \\ fs [])
  \\ Cases_on ‘s ≠ "True" ∧ s ≠ "False"’
  THEN1 (fs [] \\ qexists_tac ‘k+1’ \\ fs [])
  \\ gvs [] \\ rename [‘eval_wh q = wh_Diverge’]
  \\ (Cases_on ‘eval_wh q = wh_Diverge’ \\ fs []
      THEN1
       (Cases \\ fs []
        \\ Cases_on ‘eval_wh_to n x = wh_Diverge’ \\ fs []
        \\ ‘eval_wh_to n x = eval_wh_to k x’ by (irule eval_wh_to_agree \\ fs [])
        \\ gvs [] \\ fs [eval_wh_eq])
      \\ fs [eval_wh_eq]
      \\ qexists_tac ‘k+k'+1’ \\ fs []
      \\ ‘eval_wh_to (k+k') x = eval_wh_to k x’ by (match_mp_tac eval_wh_inc \\ fs [])
      \\ ‘eval_wh_to (k+k') q = eval_wh_to k' q’ by (match_mp_tac eval_wh_inc \\ fs [])
      \\ fs [] \\ qexists_tac ‘k'’ \\ fs [])
QED

Theorem eval_wh_IsEq:
  eval_wh (IsEq s i a x) =
    case eval_wh x of
    | wh_Constructor t ys => if is_eq_fail a t then wh_Error else
                             if t ≠ s          then wh_False else
                             if i = LENGTH ys  then wh_True  else wh_Error
    | wh_Diverge => wh_Diverge
    | _ => wh_Error
Proof
  fs [] \\ Cases_on ‘eval_wh x = wh_Diverge’ \\ fs []
  THEN1 (fs [eval_wh_eq] \\ fs [eval_wh_to_def] \\ rw [])
  \\ Cases_on ‘eval_wh x’ \\ fs []
  \\ TRY (fs [eval_wh_eq] \\ fs [eval_wh_to_def]
          \\ qexists_tac ‘k+1’ \\ fs [] \\ NO_TAC)
  \\ fs [eval_wh_eq] \\ fs [eval_wh_to_def]
  \\ fs [AllCaseEqs()]
  \\ qexists_tac ‘k+1’ \\ fs []
  \\ CCONTR_TAC \\ fs [] \\ gvs []
QED

Theorem eval_wh_Proj:
  eval_wh (Proj s i x) =
    case eval_wh x of
    | wh_Constructor t ys => if t = s ∧ i < LENGTH ys
                             then eval_wh (EL i ys) else wh_Error
    | wh_Diverge => wh_Diverge
    | _ => wh_Error
Proof
  fs [] \\ Cases_on ‘eval_wh x = wh_Diverge’ \\ fs []
  THEN1 (fs [eval_wh_eq] \\ fs [eval_wh_to_def] \\ rw [])
  \\ Cases_on ‘eval_wh x’ \\ fs []
  \\ TRY (fs [eval_wh_eq] \\ fs [eval_wh_to_def]
          \\ qexists_tac ‘k+1’ \\ fs [] \\ NO_TAC)
  \\ fs [eval_wh_eq] \\ fs [eval_wh_to_def]
  \\ Cases_on ‘s ≠ s'’ \\ gvs []
  THEN1 (qexists_tac ‘k+1’ \\ fs [])
  \\ Cases_on ‘LENGTH l ≤ i’ \\ fs []
  THEN1 (qexists_tac ‘k+1’ \\ fs [])
  \\ IF_CASES_TAC
  THEN1
   (Cases \\ fs [GSYM NOT_LESS] \\ fs [eval_wh_eq]
    \\ Cases_on ‘eval_wh_to n x = wh_Diverge’ \\ fs []
    \\ ‘eval_wh_to k x = eval_wh_to n x’ by
      (match_mp_tac eval_wh_to_agree \\ fs [])
    \\ fs [])
  \\ fs [eval_wh_eq]
  \\ qexists_tac ‘k+k'+1’ \\ fs []
  \\ ‘eval_wh_to (k + k') x = eval_wh_to k x’ by (irule eval_wh_inc \\ fs [])
  \\ ‘eval_wh_to (k + k') (EL i l) =
      eval_wh_to k' (EL i l)’ by (irule eval_wh_inc \\ fs [])
  \\ fs [] \\ qexists_tac ‘k+k'’ \\ fs []
QED

Theorem get_atoms_NONE:
  ∀l. get_atoms l = NONE ⇒ MEM wh_Diverge l
Proof
  Induct >> rw[get_atoms_def] >>
  Cases_on `h` >> gvs[] >>
  Cases_on `get_atoms l` >> gvs[] >>
  Cases_on `x` >> gvs[]
QED

Theorem get_atoms_eval_wh_to_inc:
  ∀l as.
    get_atoms (MAP (λa. eval_wh_to k a) l) = SOME as ∧
    k ≤ k'
  ⇒ get_atoms (MAP (λa. eval_wh_to k' a) l) = SOME as
Proof
  rpt strip_tac
  \\ Cases_on ‘as’ \\ gs []
  >- (
    gs [get_atoms_def, MEM_MAP, CaseEq "bool", EXISTS_MAP, EXISTS_MEM]
    \\ `eval_wh_to k a ≠ wh_Diverge`
      by (strip_tac \\ gs [])
    \\ drule_all eval_wh_inc \\ rw []
    \\ first_x_assum (irule_at Any) \\ gs [])
  \\ gs [get_atoms_def, MEM_MAP, CaseEq "bool", EVERY_MAP, EVERY_MEM]
  \\ gvs [DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”, MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
  \\ rw [] \\ gs []
  \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs []
  \\ drule_all eval_wh_inc \\ rw []
QED

Theorem get_atoms_eval_wh_to_SOME:
  ∀l as.
    get_atoms (MAP (λa. eval_wh a) l) = SOME as
  ⇒ ∃k. get_atoms (MAP (λa. eval_wh_to k a) l) = SOME as
Proof
  rpt gen_tac
  \\ Cases_on ‘as’ \\ gs []
  >- (
    gs [get_atoms_def, MEM_MAP, CaseEq "bool", PULL_EXISTS, EXISTS_MAP,
        EXISTS_MEM]
    \\ gen_tac
    \\ simp [eval_wh_def]
    \\ DEEP_INTRO_TAC some_intro
    \\ rw [] \\ gs [SF SFY_ss])
  \\ gs [get_atoms_def, MEM_MAP, CaseEq "bool",
         DECIDE “A ⇒ ¬MEM x y ⇔ MEM x y ⇒ ¬A”,
         EVERY_MAP, EVERY_MEM]
  \\ rw [] \\ gs [MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
  \\ rpt (pop_assum mp_tac)
  \\ Induct_on ‘l’ \\ gs []
  \\ qx_gen_tac ‘x’ \\ rw [] \\ gs [SF DNF_ss]
  \\ qpat_x_assum ‘eval_wh x ≠ _’ mp_tac
  \\ qpat_x_assum ‘¬_ (eval_wh x)’ mp_tac
  \\ simp [Once eval_wh_def]
  \\ simp [Once eval_wh_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ qmatch_asmsub_rename_tac ‘eval_wh_to k1 x’
  \\ drule_then (qspec_then ‘k1 + k’ assume_tac) eval_wh_inc \\ gs []
  \\ ‘∀a. MEM a l ⇒ eval_wh_to (k1 + k) a = eval_wh_to k a’
    by (rw [] \\ irule eval_wh_inc \\ gs [])
  \\ qexists_tac ‘k1 + k’ \\ gs []
  \\ AP_TERM_TAC
  \\ simp [eval_wh_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ irule eval_wh_to_agree \\ gs []
QED

Theorem get_atoms_eval_wh_SOME:
  ∀l k as.
    get_atoms (MAP (λa. eval_wh_to k a) l) = SOME as
  ⇒ get_atoms (MAP (λa. eval_wh a) l) = SOME as
Proof
  rpt gen_tac
  \\ Cases_on ‘as’ \\ gs []
  >- (
    gs [get_atoms_def, MEM_MAP, CaseEq "bool", PULL_EXISTS, EXISTS_MEM] \\ rw []
    \\ first_assum (irule_at Any)
    \\ simp [eval_wh_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    >- (
      drule_then (qspec_then ‘k’ assume_tac) eval_wh_to_agree
      \\ Cases_on ‘eval_wh_to k a’ \\ Cases_on ‘eval_wh_to x a’ \\ gs [])
    \\ qexists_tac ‘k’ \\ gs []
    \\ Cases_on ‘eval_wh_to k a’ \\ gs [])
  \\ gs [get_atoms_def, MEM_MAP, CaseEq "bool", EVERY_MAP, EVERY_MEM,
         DECIDE “A ⇒ ¬MEM x y ⇔ MEM x y ⇒ ¬A”]
  \\ rw [] \\ gs [MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
  \\ simp [eval_wh_def]
  >- (
    DEEP_INTRO_TAC some_intro \\ rw []
    \\ first_x_assum (drule_then assume_tac)
    \\ first_x_assum (drule_then assume_tac)
    \\ drule_then (qspec_then ‘x’ assume_tac) eval_wh_to_agree
    \\ gs [])
  >- (
    DEEP_INTRO_TAC some_intro \\ rw []
    \\ first_x_assum (irule_at Any)
    \\ gs [])
  \\ rw []
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ AP_TERM_TAC
  \\ irule eval_wh_to_agree
  \\ gs []
QED

Theorem get_atoms_eval_wh_NONE:
  ∀l.
    (∀k. get_atoms (MAP (λa. eval_wh_to k a) l) = NONE)
  ⇒ get_atoms (MAP (λa. eval_wh a) l) = NONE
Proof
  rw [get_atoms_def, EXISTS_MAP, EXISTS_MEM, MEM_MAP] \\ gs []
  >- (
    pop_assum mp_tac
    \\ simp [eval_wh_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ qexists_tac ‘x’
    \\ rw [] \\ gs [DISJ_EQ_IMP])
  \\ gs [DECIDE “A ⇒ ¬MEM a b ⇔ MEM a b ⇒ ¬A”, DISJ_EQ_IMP] >>
  gvs[SF DNF_ss] >> last_x_assum kall_tac >>
  simp[eval_wh_eq, PULL_FORALL] >>
  Induct_on ‘l’ >> rw[] >> gvs[SF DNF_ss] >>
  gvs[DISJ_EQ_IMP] >> rw[] >> rename1 ‘eval_wh_to k1’ >>
  last_x_assum irule >> rw[] >> rename1 ‘eval_wh_to k2’ >>
  last_x_assum $ qspec_then ‘k1 + k2’ assume_tac >>
  drule eval_wh_inc >>
  disch_then $ qspec_then ‘k1 + k2’ assume_tac >> gvs[] >>
  goal_assum $ drule_at Any >>
  CCONTR_TAC >> gvs[] >> drule eval_wh_inc >>
  disch_then $ qspec_then ‘k1 + k2’ assume_tac >> gvs[]
QED

Theorem get_atoms_SOME_SOME_eq:
  ∀ls as.
    get_atoms ls = SOME (SOME as) ⇔
    LIST_REL (λl a. l = wh_Atom a) ls as
Proof
  rw [get_atoms_def, EXISTS_MEM] \\ gs [DISJ_EQ_IMP]
  \\ gs [LIST_REL_EL_EQN, MEM_EL] \\ rw [EQ_IMP_THM] \\ gs []
  >- (
    first_x_assum (irule_at Any) \\ strip_tac \\ gs [])
  >- (
    first_x_assum (irule_at Any) \\ strip_tac \\ gs [])
  >- (
    gs [EL_MAP, PULL_EXISTS, DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”]
    \\ rpt (first_x_assum (drule_then assume_tac))
    \\ Cases_on ‘EL n ls’ \\ gs [dest_Atom_def])
  \\ irule LIST_EQ
  \\ gs [SF CONJ_ss, EL_MAP, PULL_EXISTS, dest_Atom_def]
QED

Theorem get_atoms_SOME_NONE_eq:
  ∀ls.
    get_atoms ls = SOME NONE ⇔ EXISTS error_Atom ls
Proof
  rw [get_atoms_def]
QED

Theorem get_atoms_NONE_eq:
  ∀l. get_atoms l = NONE ⇔ EVERY (λx. ¬error_Atom x) l ∧ MEM wh_Diverge l
Proof
  rw [get_atoms_def, combinTheory.o_DEF, EXISTS_MEM, EVERY_MEM]
  \\ gs [DISJ_EQ_IMP]
QED

Theorem get_atoms_MAP_Diverge:
  ys ≠ [] ⇒ get_atoms (MAP (K wh_Diverge) ys) = NONE
Proof
  rw [get_atoms_def, EXISTS_MAP, MEM_MAP]
  \\ gs [pure_miscTheory.NIL_iff_NOT_MEM, SF SFY_ss]
QED

Theorem eval_wh_Prim:
  eval_wh (Prim If xs) =
    (case xs of
        [a;b;c] =>
          if      eval_wh a = wh_Diverge then wh_Diverge else
          if      eval_wh a = wh_True    then eval_wh b
          else if eval_wh a = wh_False   then eval_wh c else wh_Error
      | _ => wh_Error) ∧
  eval_wh (Prim (Cons c) xs) = wh_Constructor c xs ∧
  eval_wh (Prim (IsEq c n a) xs) =
    (case xs of
        [x] =>
          (case eval_wh x of
              wh_Constructor t ys =>
                if is_eq_fail a t then wh_Error
                else if t ≠ c then wh_False
                else if n = LENGTH ys then wh_True
                else wh_Error
            | wh_Diverge => wh_Diverge
            | _ => wh_Error)
      | _   => wh_Error) ∧
  eval_wh (Prim (Proj c n) xs) =
    (case xs of
        [x] =>
          (case eval_wh x of
              wh_Constructor t ys =>
                if t = c ∧ n < LENGTH ys then
                  eval_wh (EL n ys)
                else wh_Error
            | wh_Diverge => wh_Diverge
            | _ => wh_Error)
      | _ => wh_Error) ∧
  (eval_wh (Prim Seq xs) =
      case xs of
      | [x;y] =>
          (if eval_wh x = wh_Error then wh_Error else
           if eval_wh x = wh_Diverge then wh_Diverge else
             eval_wh y)
      | _ => wh_Error) ∧
  eval_wh (Prim (AtomOp op) xs) =
    (let vs = MAP eval_wh xs in
     case get_atoms vs of
        NONE => wh_Diverge
      | SOME NONE => wh_Error
      | SOME (SOME as) =>
        case eval_op op as of
        | SOME (INL v) => wh_Atom v
        | SOME (INR T) => wh_True
        | SOME (INR F) => wh_False
        | NONE => wh_Error)
Proof
  rw[]
  >- (
    Cases_on `xs`
    >- (
      gvs[eval_wh_def, eval_wh_to_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >> qexists_tac `1` >> simp[]
      ) >>
    Cases_on `t`
    >- (
      gvs[eval_wh_def, eval_wh_to_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >> qexists_tac `1` >> simp[]
      ) >>
    Cases_on `t'`
    >- (
      gvs[eval_wh_def, eval_wh_to_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >> qexists_tac `1` >> simp[]
      ) >>
    reverse (Cases_on `t`)
    >- (
      gvs[eval_wh_def, eval_wh_to_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >> qexists_tac `1` >> simp[]
      ) >>
    simp[eval_wh_If]
    )
  >- (
    gvs[eval_wh_def, eval_wh_to_def] >>
    DEEP_INTRO_TAC some_intro >> rw[]
    )
  >- (
    Cases_on `xs`
    >- (
      gvs[eval_wh_def, eval_wh_to_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >> qexists_tac `1` >> simp[]
      ) >>
    reverse (Cases_on `t`)
    >- (
      gvs[eval_wh_def, eval_wh_to_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >> qexists_tac `1` >> simp[]
      ) >>
    simp[eval_wh_IsEq] >> CASE_TAC >> gvs[]
    )
  >- (
    Cases_on `xs`
    >- (
      gvs[eval_wh_def, eval_wh_to_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >> qexists_tac `1` >> simp[]
      ) >>
    reverse (Cases_on `t`)
    >- (
      gvs[eval_wh_def, eval_wh_to_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >> qexists_tac `1` >> simp[]
      ) >>
    simp[eval_wh_Proj]
    )
  >- (
    every_case_tac \\ fs [eval_wh_Seq]
    \\ fs [eval_wh_def,eval_wh_to_def,CaseEq"bool",AllCaseEqs()]
    \\ DEEP_INTRO_TAC some_intro >> rw[])
  >- (
    simp[Once eval_wh_def] >> CASE_TAC
    >- (
      pop_assum mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      gvs[eval_wh_to_def] >>
      `∀k. get_atoms (MAP (λa. eval_wh_to k a) xs) = NONE` by (
        CCONTR_TAC >> gvs[] >>
        first_x_assum (qspec_then `SUC k` assume_tac) >> gvs[] >>
        rpt (FULL_CASE_TAC >> gvs[])) >>
      EVERY_CASE_TAC >> gvs[] >>
      imp_res_tac get_atoms_eval_wh_NONE >> gvs[SF ETA_ss]
      ) >>
    pop_assum mp_tac >>
    DEEP_INTRO_TAC some_intro >> rw[] >>
    gvs[eval_wh_to_def] >>
    IF_CASES_TAC >> gvs[]
    THEN1 (Cases_on ‘xs’ \\ fs [get_atoms_def, EXISTS_MAP]) >>
    TOP_CASE_TAC >> gvs[] >>
    TOP_CASE_TAC >> gvs[] >>
    imp_res_tac get_atoms_eval_wh_SOME >> simp[] >>
    gvs[SF ETA_ss]
    )
QED

Theorem eval_wh_Prim_alt:
  (eval_wh (Prim If xs) =
    if LENGTH xs ≠ 3 then wh_Error else
    let vs = MAP (λa. eval_wh a) xs in
    if      HD vs = wh_Diverge then wh_Diverge else
    if      HD vs = wh_True    then EL 1 vs
    else if HD vs = wh_False   then EL 2 vs else wh_Error) ∧
  eval_wh (Prim (Cons c) xs) = wh_Constructor c xs ∧
  (eval_wh (Prim (IsEq c n a) xs) =
    if LENGTH xs ≠ 1 then wh_Error else
    case eval_wh (HD xs) of
        wh_Constructor t ys =>
          if is_eq_fail a t then wh_Error
          else if t ≠ c then wh_False
          else if n = LENGTH ys then wh_True
          else wh_Error
      | wh_Diverge => wh_Diverge
      | _ => wh_Error) ∧
  (eval_wh (Prim (Proj c n) xs) =
    if LENGTH xs ≠ 1 then wh_Error else
    case eval_wh (HD xs) of
        wh_Constructor t ys =>
          if t = c ∧ n < LENGTH ys then eval_wh (EL n ys) else wh_Error
      | wh_Diverge => wh_Diverge
      | _ => wh_Error) ∧
  eval_wh (Prim (AtomOp op) xs) =
    (let vs = MAP eval_wh xs in
     case get_atoms vs of
        NONE => wh_Diverge
      | SOME NONE => wh_Error
      | SOME (SOME as) =>
        case eval_op op as of
        | SOME (INL v) => wh_Atom v
        | SOME (INR T) => wh_True
        | SOME (INR F) => wh_False
        | NONE => wh_Error) ∧
  eval_wh (Prim Seq xs) =
    if LENGTH xs ≠ 2 then wh_Error else
    if HD (MAP eval_wh xs) = wh_Error then wh_Error else
    if HD (MAP eval_wh xs) = wh_Diverge then wh_Diverge else
    eval_wh (LAST xs)
Proof
  reverse $ rw[eval_wh_Prim] >> gvs[LENGTH_EQ_NUM_compute] >>
  Cases_on `xs` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >> Cases_on `t` >> gvs[]
QED

Theorem eval_wh_thm:
  eval_wh (Var s) = wh_Error ∧
  eval_wh (Lam s x) = wh_Closure s x ∧
  eval_wh (App x y) =
    (let v = eval_wh x in
       if v = wh_Diverge then wh_Diverge else
         case dest_wh_Closure v of
           NONE => wh_Error
         | SOME (s,body) => eval_wh (bind1 s y body)) ∧
  eval_wh (Letrec f y) = eval_wh (subst_funs f y) ∧
  eval_wh (Cons s xs) = wh_Constructor s xs ∧
  eval_wh (Proj s i x) =
    (case eval_wh x of
    | wh_Constructor t ys => if t = s ∧ i < LENGTH ys
                             then eval_wh (EL i ys) else wh_Error
    | wh_Diverge => wh_Diverge
    | _ => wh_Error) ∧
  eval_wh (If x y z) =
    (if eval_wh x = wh_Diverge then wh_Diverge else
     if eval_wh x = wh_True    then eval_wh y  else
     if eval_wh x = wh_False then eval_wh z  else wh_Error) ∧
  eval_wh (IsEq s i a x) =
    (case eval_wh x of
     | wh_Constructor t ys => if is_eq_fail a t then wh_Error
                              else if t ≠ s then wh_False
                              else if i = LENGTH ys then wh_True
                              else wh_Error
     | wh_Diverge => wh_Diverge
     | _ => wh_Error) ∧
  eval_wh (Seq x y) =
    (if eval_wh x = wh_Error then wh_Error
     else if eval_wh x = wh_Diverge then wh_Diverge
     else eval_wh y) ∧
  eval_wh Fail = wh_Error ∧
  eval_wh Bottom = wh_Diverge
Proof
  fs [eval_wh_Lam,eval_wh_Var,eval_wh_App,eval_wh_Letrec,eval_wh_Cons,
      eval_wh_Bottom,eval_wh_Fail,eval_wh_If,eval_wh_IsEq,
      eval_wh_Proj,eval_wh_Seq]
QED

(* unlimitied evaluation *)

Definition follow_path_def:
  follow_path f e [] =
    (case f e of
     | wh_Constructor s xs => (Constructor' s,LENGTH xs)
     | wh_Closure s x => (Closure' s x,0)
     | wh_Atom a => (Atom' a,0)
     | wh_Diverge => (Diverge',0)
     | wh_Error => (Error',0)) ∧
  follow_path f e (n::ns) =
    case f e of
    | wh_Constructor s xs => (
        case oEL n xs of
          NONE => (Error', 0)
        | SOME x => follow_path f x ns)
    | _ => (Error',0)
End

Definition v_unfold_def:
  v_unfold f seed = gen_v (follow_path f seed)
End

Theorem v_unfold:
  v_unfold f x =
    case f x of
    | wh_Constructor s xs => Constructor s (MAP (v_unfold f) xs)
    | wh_Closure s x => Closure s x
    | wh_Atom a => Atom a
    | wh_Diverge => Diverge
    | wh_Error => Error
Proof
  fs [v_unfold_def]
  \\ simp [Once gen_v]
  \\ fs [follow_path_def]
  \\ Cases_on ‘f x’ \\ fs []
  \\ qid_spec_tac ‘l’
  \\ Induct using SNOC_INDUCT \\ rw []
  \\ rewrite_tac [GENLIST,GSYM ADD1]
  \\ fs [SNOC_APPEND,EL_LENGTH_APPEND, oEL_THM]
  \\ fs [v_unfold_def]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
  \\ pop_assum (assume_tac o GSYM)
  \\ fs [GENLIST_FUN_EQ]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ fs [EL_APPEND1]
QED

Definition eval_def:
  eval x = v_unfold eval_wh x
End

Definition no_err_eval_def:
  no_err_eval x = case v_unfold eval_wh x of
			| Error => Diverge
			| rest  => rest
End

Definition dest_Closure_def:
  dest_Closure x =
    case x of Closure s x => SOME (s,x) | _ => NONE
End

Theorem dest_Closure_Closure[simp]:
  dest_Closure (Closure s x) = SOME (s,x)
Proof
  fs [dest_Closure_def]
QED

Theorem dest_Closure_Closure_IMP:
  dest_Closure v = SOME (s,x) ⇒ v = Closure s x
Proof
  rw [] \\ Cases_on ‘v’ \\ gs[dest_Closure_def]
QED

Overload True  = “Constructor "True" []”;
Overload False = “Constructor "False" []”;

Definition el_def:
  el s i x =
    if x = Diverge then Diverge else
      case x of
      | Constructor t xs =>
          if s = t ∧ i < LENGTH xs then EL i xs
          else Error
      | _ => Error
End

Definition is_eq_def:
  is_eq s n a x =
    if x = Diverge then Diverge else
      case x of
        Constructor t xs =>
          if is_eq_fail a t then Error else
          if s = t then
            (if n = LENGTH xs then True else Error)
          else False
      | _ => Error
End

Theorem eval_App:
  eval (App x y) =
    (let v = eval x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (s,body) => eval (bind1 s y body))
Proof
  simp [eval_def,Once v_unfold,eval_wh_thm]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once v_unfold,eval_wh_thm]
  \\ Cases_on ‘eval_wh x’ \\ fs [dest_wh_Closure_def]
  \\ simp [Once v_unfold,eval_wh_thm,dest_wh_Closure_def,dest_Closure_def]
  \\ simp [Once v_unfold,eval_wh_thm,dest_wh_Closure_def,dest_Closure_def]
QED

Theorem eval_Bottom:
  eval Bottom = Diverge
Proof
  simp [eval_def,Once v_unfold,eval_wh_thm]
QED

Theorem eval_Fail:
  eval Fail = Error
Proof
  simp [eval_def,Once v_unfold,eval_wh_thm]
QED

Theorem eval_Var:
  eval (Var s) = Error
Proof
  simp [eval_def,Once v_unfold,eval_wh_thm]
QED

Theorem eval_Cons:
  eval (Cons s xs) = Constructor s (MAP eval xs)
Proof
  simp [eval_def,Once v_unfold,eval_wh_thm,MAP_EQ_f]
QED

Theorem eval_Lam:
  eval (Lam s x) = Closure s x
Proof
  simp [eval_def,Once v_unfold,eval_wh_thm]
QED

Theorem eval_Letrec:
  eval (Letrec f x) = eval (subst_funs f x)
Proof
  simp [eval_def,eval_wh_thm] \\ once_rewrite_tac [v_unfold] \\ fs [eval_wh_thm]
QED

Theorem eval_IsEq:
  eval (IsEq s n a x) = is_eq s n a (eval x)
Proof
  simp [eval_def,is_eq_def]
  \\ once_rewrite_tac [v_unfold]
  \\ Cases_on ‘eval_wh x’ \\ fs [eval_wh_IsEq]
  \\ rw [] \\ fs []
QED

Theorem eval_Proj:
  eval (Proj s i x) = el s i (eval x)
Proof
  simp [eval_def,el_def]
  \\ once_rewrite_tac [v_unfold]
  \\ Cases_on ‘eval_wh x’ \\ fs [eval_wh_Proj,EL_MAP]
  \\ Cases_on ‘s ≠ s'’ \\ gvs []
  \\ Cases_on ‘i < LENGTH l’ \\ gvs []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once v_unfold]
QED

Theorem eval_Let:
  eval (Let s x y) = eval (bind1 s x y)
Proof
  fs [eval_App,eval_Lam]
QED

Theorem eval_If:
  eval (If x y z) =
     if eval x = Diverge then Diverge else
     if eval x = True    then eval y  else
     if eval x = False   then eval z  else Error
Proof
  simp [eval_def]
  \\ once_rewrite_tac [v_unfold]
  \\ Cases_on ‘eval_wh x’ \\ fs [eval_wh_If]
  \\ Cases_on ‘l=[]’ \\ gvs []
  \\ rw [] \\ fs []
QED

Theorem eval_Seq:
  eval (Seq x y) = if eval x = Diverge then Diverge
		   else if eval x = Error then Error
		   else eval y
Proof
  simp [eval_def]
  \\ once_rewrite_tac [v_unfold]
  \\ Cases_on `eval_wh x` \\ fs [eval_wh_Seq]
QED

Theorem eval_thm:
  eval Fail = Error ∧
  eval Bottom = Diverge ∧
  eval (Var s) = Error (* free variables are not allowed *) ∧
  eval (Cons s xs) = Constructor s (MAP eval xs) ∧
  eval (IsEq s n a x) = is_eq s n a (eval x) ∧
  eval (Proj s i x) = el s i (eval x) ∧
  eval (Let s x y) = eval (bind1 s x y) ∧
  eval (If x y z) =
    (if eval x = Diverge then Diverge  else
     if eval x = True    then eval y else
     if eval x = False   then eval z else Error) ∧
  eval (Seq x y) =
    (if eval x = Diverge then Diverge else
     if eval x = Error then Error else eval y) ∧
  eval (Lam s x) = Closure s x ∧
  eval (Letrec f x) = eval (subst_funs f x) ∧
  eval (App x y) =
    (let v = eval x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (s,body) => eval (bind1 s y body))
Proof
  fs [eval_App,eval_Fail,eval_Bottom,eval_Var,eval_Cons,eval_Lam,eval_Letrec,
      eval_If,eval_Proj,eval_IsEq, eval_Seq]
QED

