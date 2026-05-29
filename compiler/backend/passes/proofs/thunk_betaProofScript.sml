(*
  Define a restricted form of beta reduction
 *)

Theory thunk_betaProof
Ancestors
  string option sum pair list alist thunkLang_primitives pure_misc
  finite_map pred_set rich_list thunkLang wellorder
  thunkLangProps pred_set
Libs
  term_tactic monadsyntax dep_rewrite BasicProvers

val _ = numLib.prefer_num ();

Theorem SUM_REL_THM[local,simp] = sumTheory.SUM_REL_THM;

Theorem PAIR_REL_def[local,simp] = pairTheory.PAIR_REL;

Definition optional_force_def:
  (optional_force F (n,NONE) = Var n) ∧
  (optional_force T (n,NONE) = Force (Var n)) ∧
  (optional_force F (n,SOME val) = Value val) ∧
  (optional_force T (n,SOME val) = Force (Value val))
End

Definition Lets_def:
  (Lets [] b = b) ∧
  (Lets ((v,x)::xs) b = thunkLang$Let v x (Lets xs b))
End

(*
[opt:]
  exp_re A B

  means compiler is allowed to optimize A to B
  e.g.,
  compile A = B
*)
Inductive exp_rel:
(* Restricted beta rule *)
[beta:]
  (∀f g vs vs'.
  ALL_DISTINCT (MAP (FST o SND) vs) ∧
  DISJOINT (freevars f) (set (MAP (FST o SND) vs)) ∧
  MAP FST vs = MAP FST vs' ∧
  MAP (FST o SND) vs = MAP (FST o SND) vs' ∧
  LIST_REL (OPTREL v_rel)
    (MAP (SND o SND) vs') (MAP (SND o SND) vs) ∧
  (vs ≠ []) ∧
  exp_rel f g ⇒
  exp_rel
    (Lets
      (MAP (λ(b,v). (SOME (FST v), optional_force b v)) (REVERSE vs'))
      (Apps f (MAP (Var o FST o SND) vs)))
    (Apps g (MAP (λ(b,v). (optional_force b v)) vs)))
(* Boilerplate: *)
[exp_rel_App:]
  (∀f g x y.
     exp_rel f g ∧
     exp_rel x y ⇒
       exp_rel (App f x) (App g y))
[exp_rel_Lam:]
  (∀s x y.
     exp_rel x y ⇒
       exp_rel (Lam s x) (Lam s y))
[exp_rel_Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel x y) f g ∧
     exp_rel x y ⇒
       exp_rel (Letrec f x) (Letrec g y))
[exp_rel_Let:]
  (∀bv x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
       exp_rel (Let bv x1 y1) (Let bv x2 y2))
[exp_rel_If:]
  (∀x1 x2 y1 y2 z1 z2.
     LIST_REL exp_rel [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel (If x1 y1 z1) (If x2 y2 z2))
[exp_rel_Prim:]
  (∀op xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim op xs) (Prim op ys))
[exp_rel_Monad:]
  (∀mop xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Monad mop xs) (Monad mop ys))
[exp_rel_Delay:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Delay x) (Delay y))
[exp_rel_Force:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Force x) (Force y))
[exp_rel_MkTick:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (MkTick x) (MkTick y))
[exp_rel_Var:]
  (∀v.
     exp_rel (Var v) (Var v))
[exp_rel_Value:]
  (∀v w.
     v_rel v w ⇒
     exp_rel (Value v) (Value w))
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x))
[v_rel_Constructor:]
  (∀vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws))
[v_rel_Monadic:]
  (∀mop xs ys.
     LIST_REL exp_rel xs ys ⇒
       v_rel (Monadic mop xs) (Monadic mop ys))
[v_rel_Closure:]
  (∀s x y.
     exp_rel x y ⇒
       v_rel (Closure s x) (Closure s y))
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ⇒
       v_rel (DoTick v) (DoTick w))
[v_rel_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel x y) f g ⇒
       v_rel (Recclosure f n) (Recclosure g n))
[v_rel_Thunk:]
  (∀x y.
     exp_rel x y ⇒
       v_rel (Thunk x) (Thunk y))
End

Theorem v_rel_cases[local] = CONJUNCT2 exp_rel_cases;

(* Boilerplate *)
Theorem v_rel_def[simp] =
  [ “v_rel (Closure s x) z”,
    “v_rel z (Closure s x)”,
    “v_rel (Recclosure s x) z”,
    “v_rel z (Recclosure s x)”,
    “v_rel (Constructor s x) z”,
    “v_rel z (Constructor s x)”,
    “v_rel (Monadic mop xs) z”,
    “v_rel z (Monadic mop ys)”,
    “v_rel (Atom x) z”,
    “v_rel z (Atom x)”,
    “v_rel (Thunk x) z” ]
  |> map (SIMP_CONV (srw_ss()) [Once v_rel_cases])
  |> LIST_CONJ;

Theorem freevars_Lets_cong:
  ∀ls.
  freevars e1 = freevars e2 ⇒
  freevars (Lets ls e1) = freevars (Lets ls e2)
Proof
  Induct>-rw[Lets_def]>>
  Cases>>
  rw[Lets_def,freevars_def]>>
  Cases_on`q`>>rw[freevars_def]
QED

Theorem freevars_Lets_free:
  ∀ls.
  v ∉ set (MAP (FST o SND) ls) ⇒
  freevars
    (Lets (MAP (λ(b,v). (SOME (FST v),optional_force b v)) ls)
       (Apps x (xs ++ [Var v])))
   =
  freevars
    (Lets (MAP (λ(b,v). (SOME (FST v),optional_force b v)) ls)
       (Apps x xs)) ∪ {v}
Proof
  Induct>>rw[Lets_def,freevars_Apps,freevars_def,EXTENSION]
  >- metis_tac[]>>
  pairarg_tac>>fs[Lets_def,freevars_def]>>
  metis_tac[]
QED

Theorem idempotent_diff:
  ∀S. x ∉ S ⇒ S DIFF {x} = S
Proof
  SET_TAC []
QED

Theorem in_bigunion_freevars_optional_force:
  ∀xs. BIGUNION (set (MAP (freevars o (λ(b,v). optional_force b v)) xs))
    SUBSET set (MAP (FST o SND) xs)
Proof
  strip_tac >>
  simp[BIGUNION_SUBSET] >>
  rpt strip_tac >>
  fs[MEM_MAP, SUBSET_DEF] >> rw[] >>
  qexists `y` >>
  Cases_on `((λ(b,v). optional_force b v) y)` >>
  fs[UNCURRY_EQ, freevars_def] >>
  Cases_on `v` >>
  Cases_on `b` >> Cases_on `q` >> Cases_on `r` >>
  fs[optional_force_def, freevars_def] >>
  pop_assum (fn h => assume_tac (GSYM h)) >> fs[freevars_def]
QED

Theorem Lets_append:
  ∀a b y. Lets (a ++ b) y = Lets a (Lets b y)
Proof
  Induct_on `a` \\ rw[Lets_def] \\
  PairCases_on `h` \\ simp[Lets_def]
QED

Theorem freevars_opt_force_eq:
  !b n c c'. OPTREL v_rel c c' ⇒
    freevars (optional_force b (n,c)) = freevars (optional_force b (n, c'))
Proof
  rw [] \\ Cases_on `c` \\ Cases_on `c'` \\
  gvs[OPTREL_def] \\ Cases_on `b` \\ simp[optional_force_def, freevars_def]
QED


Theorem freevars_Lets_SOME:
  ∀ls body.
    ALL_DISTINCT (MAP FST ls) ∧
    DISJOINT (set (MAP FST ls)) (BIGUNION (set (MAP (freevars o SND) ls))) ⇒
      freevars (Lets (MAP (λ(n, e). (SOME n, e)) ls) body) =
      (BIGUNION (set (MAP (freevars o SND) ls))) ∪
      (freevars body DIFF (set (MAP FST ls)))
Proof
  Induct >> rw[Lets_def, freevars_def, MAP_o] >>
  PairCases_on `h` >> rw[Lets_def, freevars_def] >>
  fs[EXTENSION, MEM_MAP, PULL_EXISTS, DISJOINT_DEF, BIGUNION_IMAGE] >>
  metis_tac[]
QED


Theorem freevars_Apps_Vars:
  ∀f vs. freevars (Apps f (MAP (Var ∘ FST ∘ SND) vs)) =
         freevars f ∪ set (MAP (FST ∘ SND) vs)
Proof
  Induct_on `vs` >> rw[freevars_def] >>
  Cases_on `h` >> rename1 `(a, b)` >>
  Cases_on `b` >> rename1 `(s, v)` >>
  SET_TAC [MEM_MAP]
QED

Theorem freevars_Lets:
  ∀body. freevars (Lets ((SOME v, x)::xs) body)
    = freevars x ∪ (freevars (Lets xs body) DIFF {v})
Proof
  Induct \\ simp[freevars_def, Lets_def]
QED

Theorem freevars_optional_force:
  freevars (optional_force a (n, opt)) =
    if opt = NONE then {n}
    else {}
Proof
  rw[oneline optional_force_def, freevars_def] \\
  Cases_on `opt` \\ rw[freevars_def]
QED

Theorem exp_rel_freevars:
  exp_rel x y ⇒ freevars x = freevars y
Proof
  qsuff_tac ‘
    (∀x y. exp_rel x y ⇒ freevars x = freevars y) ∧
    (∀v w. v_rel v w ⇒ T)’
  >- (rw [])
  \\ ho_match_mp_tac exp_rel_strongind
  \\ simp [freevars_def]
  \\ rw []
  >- ((* Beta Case *)
    qpat_x_assum `vs≠[]` kall_tac \\
    qpat_x_assum `exp_rel x y` kall_tac \\
    rpt (pop_assum mp_tac) \\
    simp[freevars_Apps] \\
    qid_spec_tac `vs'` \\ Induct_on `vs` \\ simp[Lets_def] \\
    rw[] \\ gvs[] \\
    Cases_on `vs'` \\ gvs[] \\
    simp[Lets_append] \\
    PairCases_on `h`\\
    PairCases_on `h'`\\
    gvs[] \\
    rename1 `optional_force a (b, c)` \\
    Cases_on `c` \\ gvs[OPTREL_def, OPTREL_NONE, OPTREL_SOME]
    >- (
      qabbrev_tac `L = (MAP (λ(b,v). (SOME (FST v),optional_force b v)) (REVERSE t))` \\
      `freevars
         (Lets L (Lets [(SOME b, optional_force a (b, NONE))]
         (Apps (App x (Var b)) (MAP (Var ∘ FST ∘ SND) vs)))) =
       freevars (Lets L (Apps x (MAP (Var ∘ FST ∘ SND) vs ++ [Var b])))` by (
        irule freevars_Lets_cong \\
        simp[Lets_def,freevars_Apps,freevars_def,freevars_optional_force]\\
        rw[EXTENSION] \\ metis_tac[]) \\
      unabbrev_all_tac \\  pop_assum SUBST1_TAC \\ simp[freevars_optional_force] \\
      DEP_REWRITE_TAC [freevars_Lets_free] \\ fs[MEM_MAP] \\
      rw[EXTENSION] \\ metis_tac [])
    >- (
      qabbrev_tac `L = (MAP (λ(b,v). (SOME (FST v),optional_force b v)) (REVERSE t))` \\
      `freevars (Lets L (Lets [(SOME b, optional_force a (b, SOME x'))]
         (Apps (App x (Var b)) (MAP (Var ∘ FST ∘ SND) vs)))) =
       freevars (Lets L (Apps x (MAP (Var ∘ FST ∘ SND) vs)))` by (
        irule freevars_Lets_cong \\
        simp[Lets_def,freevars_Apps,freevars_def,freevars_optional_force]\\
        rw[EXTENSION] \\ eq_tac
        >- (metis_tac[] \\ gvs[MEM_MAP])
        >- (
          rw[] \\ gvs[MEM_MAP] \\ gvs[freevars_def, optional_force_def]
          >- (metis_tac [])
          >- (
            `MEM (FST (SND y'')) (MAP (FST o SND) vs)` by (
              simp[MEM_MAP] \\ qexists `y''` \\ fs[]) \\
            disj2_tac \\ qexists `freevars (Var (FST (SND y'')))` \\
            fs[freevars_def] \\ qexists `Var (FST (SND y''))` \\
            fs[freevars_def] \\ qexists `y''` \\ simp[])
          >- (
            `MEM (FST (SND y'')) (MAP (FST o SND) t)` by (
              `b ∉ set (MAP (FST o SND) t)` by (
                simp[MEM_MAP] \\ metis_tac[]) \\
              fs[MEM_MAP] \\
              ‘MEM (FST (SND y'')) (MAP (FST ∘ SND) vs)’ by (
                simp [MEM_MAP] \\ metis_tac []) \\
              ‘MEM (FST (SND y'')) (MAP (FST ∘ SND) t)’ by metis_tac [] \\
              gvs[MEM_MAP] \\ metis_tac[]) \\
              gvs[MEM_MAP] \\ metis_tac[]))) \\
      pop_assum SUBST1_TAC \\ simp[freevars_optional_force] \\
      DEP_REWRITE_TAC [freevars_Lets_free] \\ fs[MEM_MAP] \\
      unabbrev_all_tac \\ rw[EXTENSION] \\ metis_tac[]))
  >- (
    rw [EXTENSION, EQ_IMP_THM] \\ gs []
    \\ fs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN, Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
    \\ rw [] \\ gs [EL_MAP, ELIM_UNCURRY, SF CONJ_ss, SF SFY_ss])
  >- (Cases_on ‘bv’ \\ gs [freevars_def])
  >- (
    ‘MAP freevars xs = MAP freevars ys’ suffices_by rw [SF ETA_ss]
    \\ irule LIST_EQ \\ gvs [LIST_REL_EL_EQN, EL_MAP])
QED

Theorem LIST_REL_split:
  ∀l l'.
    LIST_REL
      (λ(fn,v) (gn,w). fn = gn ∧ exp_rel v w) l l' ⇒
      MAP FST l = MAP FST l' ∧
      LIST_REL exp_rel (MAP SND l) (MAP SND l')
Proof
  Induct \\ rw [] \\ gvs []
  \\ rpt $ (pairarg_tac \\ gvs [])
QED

Theorem LIST_REL_ALOOKUP_REVERSE:
  ∀l l'.
    MAP FST l = MAP FST l' ∧
    LIST_REL exp_rel (MAP SND l) (MAP SND l') ⇒
      (ALOOKUP (REVERSE l) s = NONE ⇒
         ALOOKUP (REVERSE l') s = NONE) ∧
      (∀e. ALOOKUP (REVERSE l) s = SOME e ⇒
         ∃e'. ALOOKUP (REVERSE l') s = SOME e' ∧
              exp_rel e e')
Proof
  rw []
  >- gvs [ALOOKUP_NONE, MAP_REVERSE]
  \\ ‘MAP FST (REVERSE l) = MAP FST (REVERSE l')’ by gvs [MAP_EQ_EVERY2]
  \\ drule_all ALOOKUP_SOME_EL_2 \\ rw []
  \\ gvs [SF SFY_ss, LIST_REL_EL_EQN, EL_MAP, EL_REVERSE]
  \\ ‘PRE (LENGTH l' - n) < LENGTH l'’ by gvs []
  \\ first_x_assum drule \\ rw []
QED

Theorem Lets_distinct:
  ∀vs b. vs ≠ [] ⇒
    (∀e.Lets vs b ≠ Delay e) ∧
    (∀s. Lets vs b ≠ Var s) ∧
    (∀op xs. Lets vs b ≠ Prim op xs) ∧
    (∀mop xs. Lets vs b ≠ Monad mop xs) ∧
    (∀x1 x2 x3. Lets vs b ≠ If x1 x2 x3) ∧
    (∀x1 x2. Lets vs b ≠ App x1 x2) ∧
    (∀s x. Lets vs b ≠ Lam s x) ∧
    (∀f x. Lets vs b ≠ Letrec f x) ∧
    (∀x. Lets vs b ≠ Force x) ∧
    (∀v. Lets vs b ≠ Value v) ∧
    (∀x. Lets vs b ≠ MkTick x)
Proof
  strip_tac \\ strip_tac \\ strip_tac
  \\ rpt conj_tac
  \\ Induct_on `vs`
  \\ fs[exp_distinct]
  \\ rpt gen_tac
  \\ Cases_on `vs` \\ Cases_on `h`
  \\ simp[Lets_def]
QED

Theorem Lets_map_seq:
  ∀vs b x1 x2.
    vs ≠ [] ∧
    (∀t. MEM t vs ⇒ FST t ≠ NONE) ⇒
    Lets vs b ≠ Seq x1 x2
Proof
  rpt gen_tac \\ strip_tac \\
  Induct_on `vs` \\ fs[Lets_def] \\
  gen_tac \\ strip_tac \\
  Cases_on `h` \\
  last_x_assum (qspec_then `(q,r)` assume_tac) \\
  gvs[Lets_def]
QED


Theorem Apps_distinct:
  (∀vs f s. vs ≠ [] ⇒ Apps f vs ≠ Var s) ∧
  (∀vs f e. vs ≠ [] ⇒ Apps f vs ≠ Delay e) ∧
  (∀vs f x y. vs ≠ [] ⇒ Apps f vs ≠ Prim x y) ∧
  (∀vs f m l. vs ≠ [] ⇒ Apps f vs ≠ Monad m l) ∧
  (∀vs f m l. vs ≠ [] ⇒ Apps f vs ≠ Monad m l) ∧
  (∀vs f l e. vs ≠ [] ⇒ Apps f vs ≠ Letrec l e)
Proof
  rpt conj_tac
  \\ Induct_on `vs`
  \\ fs[exp_distinct]
  \\ rpt gen_tac
  \\ pop_assum (fn x => qspec_then `(App f h)` assume_tac x)
  \\ Cases_on `vs` \\ simp[]
QED

Theorem v_rel_anyThunk:
  ∀v w. v_rel v w ⇒ (is_anyThunk v ⇔ is_anyThunk w)
Proof
  `(∀v w. exp_rel v w ⇒ T) ∧
   (∀v w. v_rel v w ⇒ (is_anyThunk v ⇔ is_anyThunk w))`
   suffices_by gvs []
  \\ ho_match_mp_tac exp_rel_strongind \\ rw [] \\ gvs []
  \\ rw [is_anyThunk_def, dest_anyThunk_def]
  \\ dxrule LIST_REL_split \\ rpt strip_tac
  \\ rpt CASE_TAC
  \\ drule_all_then (qspec_then ‘n’ mp_tac) LIST_REL_ALOOKUP_REVERSE
  \\ rpt strip_tac
  \\ rgs [Once exp_rel_cases]
  \\ `REVERSE vs' ≠ []` by (
    `vs' ≠ []` suffices_by simp[]
    \\ CCONTR_TAC
    \\ qpat_x_assum `MAP (FST o SND) _ = _` mp_tac \\ fs[])
  \\ gvs[Apps_distinct, Lets_distinct]
QED

Theorem subst_Lets:
  ∀m vs body.
  ALL_DISTINCT (MAP (FST o SND) vs) ⇒
  subst m
  (Lets (MAP (λ(b,v). (SOME (FST v), optional_force b v)) vs) body)
    = Lets (MAP (λ(b,v). (SOME (FST v), subst m (optional_force b v))) vs)
      (subst (FILTER (λ(n,x). n ∉ set (MAP (FST o SND) vs)) m) body)
Proof
  Induct_on `vs`
  >- (
    rw[Lets_def, FILTER_EQ_ID, EVERY_MEM, FORALL_PROD] \\
    `(FILTER (λ(n,x). T) m) = (FILTER (λn. T) m)` by (
      irule (iffLR (GSYM FILTER_EQ)) \\ SET_TAC []) \\
    pop_assum SUBST1_TAC \\ simp [FILTER_T])
  >- (
    PairCases \\ rw [Lets_def, subst_def] \\
    last_x_assum (qspecl_then [`FILTER (λ(n,x). n ≠ h1) m`, `body`] mp_tac) \\
    impl_tac \\ fs[] \\
    disch_then SUBST1_TAC \\
    `∀b q r. MEM (b,q,r) vs ⇒
      subst (FILTER (λ(n,x). n ≠ h1) m) (optional_force b (q,r))
      = subst m (optional_force b (q,r))` by (
      rw[] \\
      qspecl_then [`m`, `optional_force b (q,r)`, `{h1}`] mp_tac subst_remove \\
      impl_tac
      >- (
          Cases_on ‘r’ \\ gvs [freevars_optional_force] \\
          `MEM q (MAP (FST ∘ SND) vs)` by (
            simp [MEM_MAP] \\
            qexists_tac ‘(b, q, NONE)’ \\
            simp []) \\ metis_tac [])
      >- (simp[])) \\
    `MAP (λ(b,v). (SOME (FST v),
    subst (FILTER (λ(n,x). n ≠ h1) m) (optional_force b v))) vs
    = MAP (λ(b,v). (SOME (FST v), subst m (optional_force b v))) vs` by (
      irule LIST_EQ \\ simp[EL_MAP] \\ rw [] \\
      rpt (pairarg_tac \\ gvs[]) \\
      PairCases_on `v` \\ gvs[] \\
      first_x_assum irule \\ metis_tac[MEM_EL]) \\
    `FILTER (λ(n,x). ¬MEM n (MAP (FST ∘ SND) vs))
    (FILTER (λ(n,x). n ≠ h1) m)
    = FILTER (λ(n,x). n ≠ h1 ∧ ¬MEM n (MAP (FST ∘ SND) vs)) m` by (
     simp [FILTER_FILTER, LAMBDA_PROD, AC CONJ_COMM CONJ_ASSOC]) \\
    metis_tac[])
QED

Definition pre_force_subst_def:
  pre_force_subst m v =
    case v of
      (n,NONE) =>
      (case ALOOKUP (REVERSE m) n of
        NONE => (n,NONE) | SOME x => (n,SOME x))
    | _ => v
End

Theorem FST_pre_force_subst[simp]:
  FST (pre_force_subst ws v) = FST v
Proof
  rw[pre_force_subst_def]>>
  BasicProvers.EVERY_CASE_TAC>>fs[]
QED

Theorem subst_optional_force_eq:
  subst ws (optional_force b v) =
  optional_force b (pre_force_subst ws v)
Proof
  simp[oneline optional_force_def,pre_force_subst_def]>>
  rw[]>>
  BasicProvers.EVERY_CASE_TAC>>fs[subst_def]
QED

Theorem MAP_subst_optional_force:
  ∀vs.
  MAP (subst ws) (MAP (λ(b,v). optional_force b v) vs) =
  MAP (λ(b,v). optional_force b v)
    (MAP (λ(b,v). (b,pre_force_subst ws v)) vs)
Proof
  Induct>>rw[]>>
  pairarg_tac>>fs[]>>
  simp[subst_optional_force_eq]
QED


Theorem freevars_subst_SUBSET:
  ∀m x. freevars (subst m x) ⊆ freevars x
Proof
  ho_match_mp_tac subst_ind \\ rw [subst_def, freevars_def]
  >- (CASE_TAC \\ simp [freevars_def])
  >~[`set (MAP FST xs)`] >- (
    `MAP FST (MAP (λ(n,x').
      (n, subst (FILTER (λ(n,v). ¬MEM n (MAP FST f)) m) x')) f)
      = MAP FST f`
      by simp [MAP_MAP_o, combinTheory.o_DEF,
               MAP_EQ_f, FORALL_PROD] \\
    pop_assum SUBST1_TAC \\
    rw [SUBSET_DEF, IN_DIFF, IN_BIGUNION,
        MEM_MAP, PULL_EXISTS,
        FORALL_PROD, EXISTS_PROD] \\
     (qpat_x_assum `∀n x. _ ⇒ freevars (subst _ _) ⊆ _` mp_tac \\
      qpat_x_assum `freevars (subst _ x) ⊆ _` mp_tac \\
      rw [MEM_MAP, EXISTS_PROD] \\
      gs [SUBSET_DEF] \\ metis_tac[]))
    \\ (gs [SUBSET_DEF, MEM_MAP, PULL_EXISTS, MEM_FILTER] \\
    rw [] \\ res_tac \\ gs [] \\
    metis_tac [freevars_def, subst_def, SUBSET_DEF])
QED


Theorem LIST_REL_OPTREL_ALOOKUP:
  ∀xs ys k R.
    LIST_REL R (MAP SND xs) (MAP SND ys) ∧
    MAP FST xs = MAP FST ys ⇒
    OPTREL R (ALOOKUP xs k) (ALOOKUP ys k)
Proof
  Induct \\ rw [] \\
  Cases_on `ys` \\ gvs [] \\
  PairCases_on `h` \\ PairCases_on `h'` \\ gvs [] \\
  IF_CASES_TAC \\ gvs []
QED


Theorem v_rel_pre_force_subst:
  ∀p q vs ws.
    FST p = FST q ∧
    OPTREL v_rel (SND p) (SND q) ∧
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    MAP FST vs = MAP FST ws ⇒
    OPTREL v_rel (SND (pre_force_subst vs p)) (SND (pre_force_subst ws q))
Proof
  rw [] \\ PairCases_on `p` \\ PairCases_on `q` \\
  Cases_on `p1` \\ Cases_on `q1` \\
  gvs [pre_force_subst_def, OPTREL_def] \\
  qsuff_tac `OPTREL v_rel (ALOOKUP (REVERSE vs) p0) (ALOOKUP (REVERSE ws) p0)`
  >- (
    Cases_on `ALOOKUP (REVERSE vs) p0` \\
    Cases_on `ALOOKUP (REVERSE ws) p0` \\
    rw [] \\ gvs [OPTREL_def])
  >- (
    irule LIST_REL_OPTREL_ALOOKUP \\
    gvs [MAP_REVERSE])
QED


Theorem OPTREL_v_rel_pre_force_subst:
  ∀xs ys vs ws.
    LIST_REL (OPTREL v_rel) (MAP (SND ∘ SND) xs) (MAP (SND ∘ SND) ys) ∧
    MAP (FST ∘ SND) xs = MAP (FST ∘ SND) ys ∧
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    MAP FST vs = MAP FST ws ⇒
    LIST_REL (OPTREL v_rel)
      (MAP (SND ∘ SND) (MAP (λ(b,v). (b, pre_force_subst vs v)) xs))
      (MAP (SND ∘ SND) (MAP (λ(b,v). (b, pre_force_subst ws v)) ys))
Proof
  Induct \\ rw [] \\
  Cases_on `ys` \\ gvs [] \\
  PairCases_on `h` \\ PairCases_on `h'` \\ gvs [] \\
  irule v_rel_pre_force_subst \\ gvs []
QED


Theorem exp_rel_subst:
  ∀vs x ws y.
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    MAP FST vs = MAP FST ws ∧
    exp_rel x y ⇒
      exp_rel (subst vs x) (subst ws y)
Proof
  qsuff_tac `(∀x y. exp_rel x y ==> ∀vs ws.
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    MAP FST vs = MAP FST ws ⇒
      exp_rel (subst vs x) (subst ws y)) ∧ ∀v w. v_rel v w ⇒ T`
  >- (rpt strip_tac \\ res_tac) \\
  ho_match_mp_tac exp_rel_strongind \\ rpt strip_tac \\ simp[]
  >- ((*beta*)
      DEP_REWRITE_TAC[subst_Lets]>>
      conj_tac
      >- metis_tac[MAP_REVERSE, ALL_DISTINCT_REVERSE]>>
      simp[subst_Apps,MAP_subst_optional_force]>>
      qmatch_goalsub_abbrev_tac`Apps (subst ws y) (MAP _ vss)`>>
      rename1 `REVERSE vs'`>>
      `MAP (λ(b,v). (SOME (FST v),subst vs'' (optional_force b v)))
        (REVERSE vs') =
        MAP (λ(b,v). (SOME (FST v),(optional_force b v)))
          (REVERSE (MAP (λ(b,v). (b,pre_force_subst vs'' v)) vs'))` by
          (simp[MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f]>>
          rw[]>>pairarg_tac>>fs[subst_optional_force_eq])>>
       pop_assum SUBST1_TAC>>
       DEP_REWRITE_TAC[subst_remove]>>
       conj_tac
       >- (simp[MAP_REVERSE] >> metis_tac[DISJOINT_SYM])
       >- (
         ‘MAP (subst (
          FILTER (λ(n,x). ¬MEM n (MAP (FST ∘ SND) (REVERSE vs'))) vs''))
          (MAP (Var ∘ FST ∘ SND) vs) = MAP (Var ∘ FST ∘ SND) vs’ by (
          rw [MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, FORALL_PROD,
              subst_def, AllCaseEqs(), ALOOKUP_NONE,
              MAP_REVERSE, MAP_FST_FILTER, MEM_FILTER] \\
          ‘MEM (FST (SND (p_1, p_1', p_2))) (MAP (FST ∘ SND) vs)’ by (
            simp [MEM_MAP] \\ qexists `(p_1, p_1', p_2)` \\ fs[]) \\
          gvs[] \\ metis_tac[]) \\
          ‘MAP (Var ∘ FST ∘ SND) vs = MAP (Var ∘ FST ∘ SND) vss’ by (
            simp [Abbr ‘vss’, MAP_MAP_o,
                  combinTheory.o_DEF, MAP_EQ_f,
                  FORALL_PROD]) \\
          pop_assum SUBST1_TAC \\
          ‘MAP (subst (FILTER (λ(n,x).
          ¬MEM n (MAP (FST ∘ SND) (REVERSE vs'))) vs''))
          (MAP (Var ∘ FST ∘ SND) vss) = MAP (Var ∘ FST ∘ SND) vss’ by (
            ‘MAP (Var ∘ FST ∘ SND) vss = MAP (Var ∘ FST ∘ SND) vs’ by (
              simp [Abbr ‘vss’, MAP_MAP_o,
              combinTheory.o_DEF, MAP_EQ_f,
              FORALL_PROD])
            \\ simp []) \\
          pop_assum SUBST1_TAC \\
          irule beta \\
          ‘∀(m: (string # v) list) (xs: (bool # string # v option) list).
            MAP FST (MAP (λ(b,v). (b, pre_force_subst m v)) xs) =
            MAP FST xs ∧
            MAP (FST ∘ SND) (MAP (λ(b,v). (b, pre_force_subst m v)) xs)
            = MAP (FST ∘ SND) xs’ by (
              rw [MAP_MAP_o, combinTheory.o_DEF,
                  MAP_EQ_f, FORALL_PROD]) \\
          gvs [] \\
          rpt conj_tac \\ simp [Abbr `vss`]
          >- ( (*DISJOINT*)
            qpat_x_assum `MAP FST vs = _` (SUBST1_TAC o GSYM) \\
            metis_tac [DISJOINT_SUBSET, DISJOINT_SYM, freevars_subst_SUBSET])
          >- ((*LIST_REL*)
            irule OPTREL_v_rel_pre_force_subst \\
            ‘(λv w. v_rel v w) = v_rel’ by rw [FUN_EQ_THM] \\
            gs [UNCURRY])))

  >- ((*App*)
      rw [Once exp_rel_cases] \\
      disj2_tac \\ disj1_tac \\
      simp[subst_def])

  >- ((*Lam*)
      simp [subst_def] \\
      irule exp_rel_Lam \\
      first_x_assum irule \\
      fs [MAP_FST_FILTER, EVERY2_MAP] \\
      qabbrev_tac `P = λx. x ≠ s` \\ fs [] \\
      irule LIST_REL_FILTER \\ fs [] \\
      irule LIST_REL_mono \\
      first_assum (irule_at Any) \\ gs [])

  >- ((*Letrec*)
      simp [subst_def] \\
      irule exp_rel_Letrec \\
      `MAP FST f = MAP FST g` by (
        irule LIST_EQ \\ gvs [EL_MAP, LIST_REL_EL_EQN, ELIM_UNCURRY]) \\
      qabbrev_tac `vs1 = FILTER (λ(n,v). ¬MEM n (MAP FST g)) vs` \\
      qabbrev_tac `ws1 = FILTER (λ(n,v). ¬MEM n (MAP FST g)) ws` \\
      `LIST_REL v_rel (MAP SND vs1) (MAP SND ws1) ∧ MAP FST vs1 =
      MAP FST ws1` by (
        unabbrev_all_tac \\
        fs [MAP_FST_FILTER, EVERY2_MAP] \\
        qabbrev_tac `P = λx. ¬MEM x (MAP FST g)` \\ fs [] \\
        irule LIST_REL_FILTER \\ fs [] \\
        irule LIST_REL_mono \\
        first_assum (irule_at Any) \\ gs []) \\ conj_tac \\
        qpat_x_assum `LIST_REL _ f g` mp_tac \\ rw [LIST_REL_EL_EQN] \\
        first_x_assum drule \\ rpt (pairarg_tac \\ gvs []) \\ strip_tac \\
        gvs [EL_MAP] \\ first_x_assum drule \\
        rpt (pairarg_tac \\ gvs []) \\ rw [] \\
        first_x_assum irule \\ gvs[LIST_REL_EL_EQN, EL_MAP])

  >- ((*Let NONE and SOME*)
      simp [subst_def] \\ Cases_on ‘bv’ \\ simp [subst_def] \\
      irule exp_rel_Let \\ conj_tac \\
      first_x_assum irule \\ gs [] \\ conj_tac
      >- (metis_tac [MAP_FST_FILTER])
      >- (
        fs [MAP_FST_FILTER, EVERY2_MAP]
        \\ qabbrev_tac ‘P = λn. n ≠ x''’ \\ fs []
        \\ irule LIST_REL_FILTER \\ fs []
        \\ irule LIST_REL_mono
        \\ first_assum (irule_at Any) \\ gs []))

  >- ((*If*)
      simp[subst_def] \\ irule exp_rel_If \\ gvs[])

  >- ((*Prim*)
      simp[subst_def] \\ irule exp_rel_Prim \\ gvs[EVERY2_MAP] \\
      irule LIST_REL_mono \\ first_assum (irule_at Any) \\ rw[])

  >- ((*Monad*)
      simp[subst_def] \\ irule exp_rel_Monad \\ gvs[EVERY2_MAP] \\
      irule LIST_REL_mono \\ first_assum (irule_at Any) \\ rw[])

  >- ((*Delay*)
      simp[subst_def] \\ irule exp_rel_Delay \\ gvs[EVERY2_MAP] \\
      irule LIST_REL_mono \\ first_assum (irule_at Any) \\ rw[])

  >- ((*Force*)
      simp[subst_def] \\ irule exp_rel_Force \\ gvs[EVERY2_MAP] \\
      irule LIST_REL_mono \\ first_assum (irule_at Any) \\ rw[])

  >- ((*MkTick*)
      simp[subst_def] \\ irule exp_rel_MkTick \\ gvs[EVERY2_MAP] \\
      irule LIST_REL_mono \\ first_assum (irule_at Any) \\ rw[])

  >- ((*Var*)
      simp [subst_def] \\
      `OPTREL v_rel (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)` by (
        irule LIST_REL_OPTREL_ALOOKUP \\ gvs [MAP_REVERSE]) \\ 
      every_case_tac \\ gs[OPTREL_def, exp_rel_Var, exp_rel_Value])

  >- ((*Value*)
      metis_tac [subst_def, exp_rel_Value])
QED


Definition d2b_goal_def:
  d2b_goal k x =
    ∀y.
      exp_rel x y ∧
      (∀k. eval_to k x ≠ INL Type_error) ⇒
      ∃j.
        ($= +++ v_rel)
          (eval_to (j + k) x)
          (eval_to k y)
End

Theorem eval_to_WF_IND[local] =
  WF_IND
  |> GEN_ALL
  |> Q.ISPEC ‘eval_to_wo’
  |> REWRITE_RULE [eval_to_wo_WF]
  |> Q.SPEC ‘UNCURRY d2b_goal’
  |> SIMP_RULE std_ss [FORALL_PROD]


Theorem eval_to_Apps_not_Val_Lams_not_0:
  ∀vL eL e k. vL ≠ [] ∧ LENGTH vL = LENGTH eL ∧ k ≠ 0 ⇒
              eval_to k (Apps (Lams vL e)
                         (MAP Value eL))
              = eval_to (k - 1) (subst (ZIP (vL, eL)) e)
Proof
  Induct using SNOC_INDUCT >> rw [] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  qspecl_then [‘eL’] assume_tac SNOC_CASES >> gs [arithmeticTheory.ADD1] >>
  rename1 ‘SNOC v vL’ >> Cases_on ‘vL’ >> gs []
  >- gs [eval_to_def, dest_anyClosure_def] >>
  gvs [FOLDR_SNOC, FOLDL_APPEND, eval_to_def, SNOC_APPEND] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  gs [subst_def, eval_to_def, dest_anyClosure_def] >>
  AP_TERM_TAC >>
  irule EQ_TRANS >> irule_at (Pos hd) subst_commutes >>
  gs [MEM_FILTER, MAP_FST_FILTER] >>
  qspecl_then [‘ZIP (h::vL, eL)’, ‘subst1 v x' e’, ‘{v}’] assume_tac subst_remove >>
  gs [freevars_subst] >>
  gs [GSYM subst_APPEND] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  Cases_on ‘eL’ >> gs [SNOC_APPEND, GSYM ZIP_APPEND]
QED

Theorem eval_to_Apps_Lams_not_0:
  ∀vL eL e k. vL ≠ [] ∧ LENGTH vL = LENGTH eL ∧ k ≠ 0 ⇒
              eval_to k (Apps (Value (Closure (HD vL) (Lams (TL vL) e)))
                                       (MAP Value eL))
              = eval_to (k - 1) (subst (ZIP (vL, eL)) e)
Proof
  Induct using SNOC_INDUCT >> rw [] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  qspecl_then [‘eL’] assume_tac SNOC_CASES >> gs [arithmeticTheory.ADD1] >>
  rename1 ‘SNOC v vL’ >> Cases_on ‘vL’ >> gs []
  >- gs [eval_to_def, dest_anyClosure_def] >>
  gvs [FOLDR_SNOC, FOLDL_APPEND, eval_to_def, SNOC_APPEND] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  first_x_assum $ qspecl_then [‘eL’, ‘Lam v e’, ‘k’] assume_tac >>
  gvs [subst_def, eval_to_def, dest_anyClosure_def] >>
  AP_TERM_TAC >>
  irule EQ_TRANS >> irule_at Any subst_commutes >>
  conj_tac >- rw [MAP_FST_FILTER, MAP_ZIP, MEM_FILTER] >>
  qspecl_then [‘ZIP (h::vL, eL)’, ‘subst1 v x' e’, ‘{v}’]
    mp_tac subst_remove >> impl_tac
  >- gs [freevars_subst] >>
  rw [GSYM subst_APPEND] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  first_x_assum kall_tac >> first_x_assum kall_tac >>
  once_rewrite_tac [CONS_APPEND] >>
  once_rewrite_tac [APPEND_SNOC] >>
  once_rewrite_tac [SNOC_APPEND] >>
  qspecl_then [‘[h]++vL’, ‘eL’, ‘[v]’, ‘[x']’] assume_tac ZIP_APPEND >>
  gs [ZIP]
QED

Theorem eval_to_Apps_Lams_0:
  ∀vL eL e. vL ≠ [] ∧ LENGTH vL = LENGTH eL ⇒
  eval_to 0 (Apps (Value (Closure (HD vL) (Lams (TL vL) e))) (MAP Value eL))
  = INL Diverge
Proof
  Induct using SNOC_INDUCT >> rw [] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  qspecl_then [‘eL’] assume_tac SNOC_CASES >> gs [arithmeticTheory.ADD1] >>
  rename1 ‘SNOC v vL’ >> Cases_on ‘vL’ >> gs []
  >- (gs [eval_to_def, dest_anyClosure_def]) >>
  gs [FOLDR_SNOC, FOLDL_APPEND, eval_to_def, SNOC_APPEND]
QED

Theorem eval_to_Value:
  ∀k v. eval_to k (Value v) = INR v
Proof
  simp [eval_to_def]
QED

Theorem eval_to_Tick:
  ∀k e. k ≠ 0 ⇒ eval_to k (Tick e) = eval_to (k - 1) e
Proof
  rw [eval_to_def, subst_funs_def, subst_empty]
QED

Theorem eval_to_Apps_no_INL:
  ∀eL e k. eval_to k (Apps e eL) ≠ INL Type_error ∧
  (∀i. i < LENGTH eL ⇒ eval_to k (EL i eL) ≠ INL Diverge)
  ⇒ ∃vL. LIST_REL (λe v. eval_to k e = INR v) eL vL ∧
  eval_to k (Apps e eL) = eval_to k (Apps e (MAP Value vL))
Proof
  Induct using SNOC_INDUCT \\ gs [] \\ rw []
  \\ Q.REFINE_EXISTS_TAC ‘SNOC lst vL’ \\ gs [FOLDL_SNOC, eval_to_def]
  \\ rename1 ‘SNOC x eL’
  \\ Cases_on ‘eval_to k x = INL Type_error’ \\ gs []
  \\ ‘eval_to k x ≠ INL Diverge’ by (
      first_x_assum $ qspec_then ‘LENGTH eL’ assume_tac \\
      gs [EL_LENGTH_SNOC])
  \\ Cases_on ‘eval_to k x’ \\ gs []
  >~[‘value ≠ Type_error’] >- (Cases_on ‘value’ \\ gs [])
  \\ Cases_on ‘eval_to k (Apps e eL) = INL Type_error’ \\ gs []
  \\ last_x_assum $ dxrule_then mp_tac \\ impl_tac
  >- (rw [] \\ rename1 ‘i < _’
      \\ last_x_assum $ qspec_then ‘i’ assume_tac
      \\ gs [EL_SNOC])
  \\ disch_then $ qx_choose_then ‘vL’ assume_tac
  \\ rename1 ‘eval_to k x = INR v’ \\ qexists_tac ‘v’ \\ qexists_tac ‘vL’
  \\ gs [MAP_SNOC, FOLDL_SNOC, eval_to_def,
         GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC]
  \\ rw [] \\ gs [LIST_REL_SNOC]
QED

Theorem eval_to_Apps_LIST_INR:
  ∀eL vL e k. LIST_REL (λe v. ∀j. eval_to (j + k) e = INR v) eL vL
  ⇒ ∀j. k ≤ j ⇒ eval_to j (Apps e eL) = eval_to j (Apps e (MAP Value vL))
Proof
  Induct using SNOC_INDUCT
  \\ gs [LIST_REL_SNOC, PULL_EXISTS, FOLDL_APPEND, FOLDL_SNOC, SNOC_APPEND]
  \\ rw [] \\ last_x_assum $ drule_all_then assume_tac
  \\ gs [eval_to_def]
  \\ first_x_assum $ qspec_then ‘j - k’ assume_tac
  \\ gs []
QED

Theorem eval_to_Apps_arg_Div:
  ∀eL i k e. eval_to k (Apps e eL) ≠  INL Type_error ∧
  i < LENGTH eL ∧
  eval_to k (EL i eL) = INL Diverge
  ⇒ eval_to k (Apps e eL) = INL Diverge
Proof
  Induct using SNOC_INDUCT \\ gs []
  \\ rw [] \\ gs [GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC, FOLDL_SNOC]
  \\ rename1 ‘SNOC x eL’
  \\ gs [EL_SNOC, EL_LENGTH_SNOC, eval_to_def]
  \\ Cases_on ‘eval_to k x’ \\ gs []
  >~[‘INL err’] >- (Cases_on ‘err’ \\ gs [])
  \\ Cases_on ‘eval_to k (Apps e eL) = INL Type_error’ \\ gs []
  \\ last_x_assum $ drule_then assume_tac
  \\ first_x_assum $ qspec_then `i` assume_tac
  \\ `i < LENGTH eL ∧ eval_to k eL❲i❳ = INL Diverge` by (
      `i ≠ LENGTH eL` by (
        CCONTR_TAC \\ qpat_x_assum `eval_to k x = INR y` mp_tac
        \\ simp[] \\ `(SNOC x eL)❲i❳ = x` by metis_tac[EL_LENGTH_SNOC]
        \\ gs[])
        \\ `eval_to k (SNOC x eL)❲i❳ = eval_to k eL❲i❳` by (
          `i < LENGTH eL` by simp[] \\ metis_tac[EL_SNOC])
        \\ gs[]
      )
  \\ gs []
QED

Theorem exp_rel_Apps:
  ∀l1 l2 x y.
  LIST_REL exp_rel l1 l2 ∧ exp_rel x y ⇒
  exp_rel (Apps x l1) (Apps y l2)
Proof
  Induct \\ simp[] \\
  Cases_on `l2` \\ gvs[] \\ rw[] \\
  last_x_assum irule \\ gs[] \\
  irule exp_rel_App \\ metis_tac[]
QED

Theorem exp_rel_eval_to:
  ∀k x. d2b_goal k x
Proof
  ho_match_mp_tac eval_to_WF_IND
  \\ once_rewrite_tac [d2b_goal_def]
  \\ gen_tac
  \\ Cases \\ gs []

  >~ [‘Let bv x1 y1’] >- (
    Cases_on ‘bv’
    >~ [`Seq x1 y1`] >- (
      `∀k e1 e2. (eval_to k e1 = INL Type_error) ⇒
      eval_to (k+1) (Seq e1 e2) = INL Type_error` by (
        simp[eval_to_def])
      \\ strip_tac \\ rw[Once exp_rel_cases]
      >- (
        `REVERSE vs' ≠ []` by (
          `vs ≠ []` suffices_by (
            CCONTR_TAC \\ fs[])
          \\ fs[]) \\
        Cases_on `REVERSE vs'` \\ fs[] \\
        PairCases_on `h` \\ gvs[optional_force_def, Lets_def])
      >- (
          Cases_on `k=0`
          >- (qexists `0` \\ simp[eval_to_def])
          >- (
            simp[eval_to_def] \\
            `∀k. eval_to k x1 ≠ INL Type_error` by (
              metis_tac[eval_to_def]) \\
            first_assum (qspecl_then [`k-1`, `x1`] assume_tac) \\
            `eval_to_wo (k-1, x1) (k, Seq x1 y1)` by simp[eval_to_wo_def] \\
            fs[] \\ first_x_assum (qspec_then `x2` assume_tac) \\
            `∀k. eval_to k x1 ≠ INL Type_error` by (
              CCONTR_TAC \\ fs[] \\
              last_assum (qspecl_then [`k'`, `x1`, `x2`] assume_tac) \\
              fs[] \\ metis_tac[]) \\
            Cases_on `eval_to (k-1) x2`
            >- ((*eval_to (k-1) x2 = INL x*)
              `∃j. ($= +++ v_rel) (eval_to (j + (k − 1)) x1) (INL x)` by (
                first_x_assum irule \\ metis_tac[]) \\
              Cases_on `eval_to (j+k-1) x1` \\
              qexists `j` \\ gs[eval_to_def])
            >- ((*eval_to (k-1) x2 = INR y*)
                `∃j. ($= +++ v_rel) (eval_to (j + (k − 1)) x1) (INR y)` by (
                  first_x_assum irule \\ metis_tac[]) \\
                Cases_on `eval_to (j+k-1) x1`
                >- (
                  qexists `j` \\ simp[eval_to_def] \\
                  Cases_on `eval_to (k-1) y2` \\
                  gs[eval_to_def, SUM_REL_THM])
                >- (
                  `∀k. eval_to k y1 ≠ INL Type_error` by (
                    CCONTR_TAC \\ fs[] \\
                    qpat_x_assum `∀k. eval_to k (Seq x1 y1)
                      ≠ INL Type_error` mp_tac \\ simp[] \\
                    qexists `MAX k' (j+k-1) + 1` \\
                    qabbrev_tac `maximum=MAX k' (j+k-1)` \\
                    simp[eval_to_def] \\
                    `eval_to maximum x1 = eval_to (j+k-1) x1` by (
                      irule eval_to_mono \\ unabbrev_all_tac \\
                      fs[arithmeticTheory.MAX_DEF]) \\
                    `eval_to maximum y1 = eval_to k' y1` by (
                      irule eval_to_mono \\ unabbrev_all_tac \\
                      fs[arithmeticTheory.MAX_DEF]) \\
                    gvs[]) \\ simp[] \\
                    first_assum (qspecl_then [`k - 1`, `y1`] mp_tac) \\
                    impl_tac
                    >- (fs[eval_to_wo_def])
                    >- (
                      disch_then (qspec_then `y2` mp_tac) \\ impl_tac
                      >- (simp[])
                      >- (
                        disch_then (qx_choose_then `j''` assume_tac) \\
                        Cases_on `eval_to (k-1) y2`
                        >- ((*eval_to (k-1) y2 = INL x*)
                          `eval_to (j''+j+k-1) x1 = eval_to (j+k-1) x1` by (
                            irule eval_to_mono \\ fs[]) \\ Cases_on `x`
                          >- ((*x = Type_error*)
                            `eval_to (j'' + (k-1)) y1 = INL Type_error` by (
                              CCONTR_TAC \\
                              qpat_x_assum `($= +++ v_rel) _ _` mp_tac \\
                              Cases_on `eval_to (j'' + (k − 1)) y1` \\ fs[]) \\
                            `eval_to (j'' + j + k - 1) y1
                            = eval_to (j''+k-1) y1` by (
                              irule eval_to_mono \\ fs[] \\
                              metis_tac[]) \\ metis_tac[])
                          >- ((*x = Diverge*)
                            `eval_to (j'' + (k-1)) y1 = INL Diverge` by (
                              Cases_on `eval_to (j'' + (k-1)) y1` \\ fs[]) \\
                            qexists `j''` \\
                            Cases_on `eval_to (j'' + k - 1) x1`
                            >- (Cases_on `x` \\ gvs[])
                            >- (gs[SUM_REL_THM])))

                        >- ((*eval_to (k-1) y2 = INR _*)
                          qexists `j'' + j` \\
                          `eval_to (j'' +j+k-1) x1 = eval_to (j+k-1) x1` by (
                            irule eval_to_mono \\ fs[]) \\ simp[] \\
                          `eval_to (j + (j'' + k) − 1) y1
                          = eval_to (j'' + (k-1)) y1` by (
                            irule eval_to_mono \\ fs[] \\
                            Cases_on `eval_to (j'' + (k-1)) y1` \\
                            fs[cj 4 SUM_REL_THM] \\ gs[]) \\
                          metis_tac[]))))))))

kall_tac []
    >~ [`Let (SOME s) x1 y1`] >- (
      strip_tac \\
      rw [Once exp_rel_cases]
      >- ((*stuck*)
        gvs[] \\
        qpat_x_assum `Let (SOME s) x1 y1 = Lets _ _` (
          fn thm => assume_tac o GSYM $ thm) \\ pop_assum SUBST_ALL_TAC \\
        `EVERY (λ(b,q, option). option ≠ NONE) vs'` by (
          CCONTR_TAC \\
          gvs[EVERY_MEM, FORALL_PROD, MEM_EL, PULL_EXISTS] \\
          first_x_assum (qspec_then `LENGTH vs'` mp_tac) \\
          simp [] \\ (*???*)
cheat
        )
      )

      >- (
        Cases_on `k=0` \\ simp[eval_to_def]
        >- (qexists `0` \\ simp[])
        >- (
            last_assum (qspecl_then [`k-1`, `x1`] assume_tac) \\
            `eval_to_wo (k-1, x1) (k, Let (SOME s) x1 y1)` by (
              simp[eval_to_wo_def]) \\
            fs[] \\ first_x_assum (qspec_then `x2` assume_tac) \\ fs[] \\
            `∀k. eval_to k x1 ≠ INL Type_error` by (
              CCONTR_TAC \\ fs[] \\
              `eval_to (k' + 1) (Let (SOME s) x1 y1) = INL Type_error` by (
                fs[eval_to_def]) \\ metis_tac[]) \\
              first_x_assum drule \\ strip_tac \\
              Cases_on `eval_to (k-1) x2` \\ fs[eval_to_def]
              >- (
                gs[] \\ qexists `j` \\
                `eval_to (j + k-1) x1 = INL x` by (
                  Cases_on `eval_to (j + k-1) x1` \\ simp[SUM_REL_THM]
                  >-(CCONTR_TAC \\ fs[SUM_REL_THM])
                  >-(fs[SUM_REL_THM])) \\ gs[SUM_REL_THM])
              >- (
                `∃j. ($= +++ v_rel) (eval_to (j + (k-1)) x1) (INR y)` by (
                  simp[]) \\
                Cases_on `eval_to (j + k-1) x1`
                >- (CCONTR_TAC \\ gs[SUM_REL_THM])
                >- (
                    `v_rel y' y` by (
                      `eval_to (j+ (k-1)) x1 = INR y'` by fs[] \\
                      fs[SUM_REL_THM]) \\
                    last_x_assum
                      (qspecl_then [`k-1`, `subst1 s y' y1`] mp_tac) \\
                    impl_tac \\ simp[eval_to_wo_def] \\
                    disch_then (qspec_then `subst1 s y y2` mp_tac) \\ impl_tac
                    >- (
                      simp[exp_rel_subst] \\ gen_tac \\
                      `eval_to k' (subst1 s y' y1) ≠ INL Type_error` by (
                        qpat_x_assum `∀k''. _ ≠ INL Type_error`
                          (qspec_then `SUC (k' + j + (k-1))` mp_tac) \\
                        `eval_to (k' + j + (k-1)) x1 = eval_to (j+k-1) x1` by (
                          irule eval_to_mono \\ fs[]) \\ strip_tac \\
                        CCONTR_TAC \\
                        `eval_to k' (subst1 s y' y1) ≠ INL Diverge` by fs[] \\
                        `eval_to (k' + j + (k-1)) (subst1 s y' y1)
                        = eval_to k' (subst1 s y' y1)` by (
                          irule eval_to_mono \\ simp[]) \\
                        last_x_assum
                          (qspec_then `SUC (k' + j + (k-1))` mp_tac) \\
                        gs[]))
                    >- (
                        strip_tac \\
                        `eval_to (j+j'+k-1) x1 = INR y'` by (
                          `eval_to (j+j'+k-1) x1 = eval_to (j + k − 1) x1` by (
                            irule eval_to_mono \\ simp[]) \\ fs[]) \\
                        Cases_on `eval_to (k-1) (subst1 s y y2)` \\ gvs[]
                        >- ((*INL x*)
                          Cases_on `x` \\ gvs[]
                          >- ((*x = Type_error*)
                              qexists `j + j'` \\ fs[] \\
                              `eval_to (j + (j'+k)-1) (subst1 s y' y1)
                              = eval_to (j'+k-1) (subst1 s y' y1)` by (
                                irule eval_to_mono \\ fs[] \\ CCONTR_TAC \\
                              qpat_x_assum `($= +++ v_rel) _ (INL Type_error)`
                                mp_tac \\
                              fs[]) \\ pop_assum SUBST1_TAC \\
                              metis_tac[SUM_REL_THM])
                          >- ((*x = Diverge*)
                              qexists_tac `j'` \\ fs[] \\
                              Cases_on `eval_to (j' + k - 1) x1` \\ gvs[]
                              >- (
                                CCONTR_TAC \\
                                `eval_to (j'+k-1) x1 = INL Type_error` by (
                                  Cases_on `x` \\ gvs[]) \\ metis_tac[])
                              >- (
                                `y'' = y'` by (
                                  qspecl_then [`j'+k-1`, `x1`, `j+(j'+k)-1`]
                                    mp_tac eval_to_mono \\
                                  simp[]) \\ metis_tac[])))
                        >- ((*INR y*)
                            qexists `j + j'` \\ fs[] \\
                            `eval_to (j + (j'+k)-1) (subst1 s y' y1)
                            = eval_to (j' + k − 1) (subst1 s y' y1)` by (
                              irule eval_to_mono \\ fs[] \\
                              CCONTR_TAC \\ metis_tac[SUM_REL_THM]) \\
                            pop_assum SUBST1_TAC
                            \\ metis_tac[SUM_REL_THM])))))))

(* OLD PROOF
      ‘∀k. eval_to k x1 ≠ INL Type_error’
        by (qx_gen_tac ‘j’
            \\ strip_tac
            \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + 1’
            \\ simp [])
      \\ simp [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) x1)
                                 (eval_to (k - 1) x2)’
        by (first_x_assum irule \\ simp [eval_to_wo_def])
      \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
      >- (
        qexists_tac ‘j’
        \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs [])
      \\ ‘∀j1. eval_to (j1 + j + k - 1) x1 = eval_to (j + k - 1) x1’
        by (gen_tac \\ irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
      \\ rename1 ‘v_rel u v’
      \\ ‘∀k. eval_to k (subst1 s u y1) ≠ INL Type_error’
        by (qx_gen_tac ‘j1’
            \\ strip_tac
            \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + j1 + k’ \\ simp []
            \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
            \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to (k - 1) (subst1 s v y2) = INL Diverge’
      >- (
        Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘∀j. eval_to (j + k - 1) x1 = eval_to (k - 1) x1’
          by (gen_tac \\ irule eval_to_mono \\ gs [])
        \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
        \\ ‘∀j. j + k - 1 = j + (k - 1)’ by gs []
        \\ asm_simp_tac std_ss []
        \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
        \\ first_x_assum irule
        \\ rgs [eval_to_wo_def]
        \\ irule exp_rel_subst \\ gs [])
      \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
      \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
      \\ qmatch_goalsub_abbrev_tac ‘(_ +++ _) (eval_to _ lhs) (eval_to _ rhs)’
      \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) lhs)
                                 (eval_to (k - 1) rhs)’
        suffices_by (
          disch_then (qx_choose_then ‘j1’ assume_tac)
          \\ qexists_tac ‘j1’
          \\ ‘eval_to (j + j1 + k - 1) lhs = eval_to (j1 + k - 1) lhs’
            by (irule eval_to_mono \\ gs []
                \\ strip_tac \\ gs []
                \\ Cases_on ‘eval_to (k - 1) rhs’ \\ gs [])
          \\ gs [])
      \\ first_x_assum irule
      \\ unabbrev_all_tac
      \\ gs [eval_to_wo_def, subst1_commutes]
      \\ irule exp_rel_subst \\ gs [])
    \\ strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∀k. eval_to k x1 ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j + 1’
          \\ simp [])
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) x1) (eval_to (k - 1) x2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def])
    \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    >- (
      qexists_tac ‘j’
      \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs [])
    \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
    \\ ‘∀k. eval_to k y1 ≠ INL Type_error’
      by (qx_gen_tac ‘j1’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j1 + j + k’ \\ simp []
          \\ ‘eval_to (j + (j1 + k) - 1) x1 = eval_to (j + k - 1) x1’
            by (irule eval_to_mono \\ gs [])
          \\ simp []
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ irule eval_to_mono \\ simp [])
    \\ Cases_on ‘eval_to (k - 1) y2 = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k - 1) x1 = eval_to (k - 1) x1’
        by (gen_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
      \\ ‘∀j. j + k - 1 = j + (k - 1)’ by gs []
      \\ asm_simp_tac std_ss []
      \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def])
    \\ ‘∀j1. eval_to (j1 + j + k - 1) x1 = eval_to (j + k - 1) x1’
      by (gen_tac \\ irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ Q.REFINE_EXISTS_TAC ‘j + j1’ \\ gs []
    \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
    \\ qmatch_goalsub_abbrev_tac ‘(_ +++ _) (eval_to _ lhs) (eval_to _ rhs)’
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) lhs)
                               (eval_to (k - 1) rhs)’
      suffices_by (
        disch_then (qx_choose_then ‘j1’ assume_tac)
        \\ qexists_tac ‘j1’
        \\ ‘eval_to (j + j1 + k - 1) lhs = eval_to (j1 + k - 1) lhs’
          by (irule eval_to_mono \\ gs []
              \\ strip_tac \\ gs []
              \\ Cases_on ‘eval_to (k - 1) rhs’ \\ gs [])
        \\ gs [])
    \\ first_x_assum irule
    \\ simp [eval_to_wo_def]
*)

  >~ [`Letrec f x`] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ rename1 ‘exp_rel x y’
    \\ ‘∀j. j + k - 1 = j + (k - 1)’
      by gs []
    \\ asm_simp_tac std_ss []
    \\ first_x_assum irule
    \\ simp [eval_to_wo_def, exp_size_def, subst_funs_def]
    \\ irule_at Any exp_rel_subst
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP, LAMBDA_PROD,
             GSYM FST_THM]
    \\ gs [ELIM_UNCURRY, LIST_REL_EL_EQN]
    \\ irule_at Any LIST_EQ
    \\ gs [EL_MAP]
    \\ qx_gen_tac ‘j’
    \\ strip_tac
    \\ qpat_x_assum ‘∀k. eval_to _ (Letrec _ _) ≠ _’ mp_tac
    \\ simp [eval_to_def, subst_funs_def]
    \\ qexists_tac ‘j + 1’ \\ simp [ELIM_UNCURRY])

  >~ [‘Var v’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def])

  >~ [‘App f x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ rename1 ‘exp_rel x y’
    \\ simp [eval_to_def]
    \\ ‘∀k. eval_to k x ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ first_x_assum (qspec_then ‘j’ mp_tac)
          \\ simp [eval_to_def])
    \\ ‘∃j1. ($= +++ v_rel) (eval_to (j1 + k) x) (eval_to k y)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k) x’
      \\ gs [])
    \\ ‘∃u1. eval_to k y = INR u1’
      by (Cases_on ‘eval_to k y’ \\ gs []
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs []
          \\ Cases_on ‘eval_to (j1 + k) x’ \\ gs [])
    \\ simp []
    \\ ‘∀k. eval_to k f ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (App _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ ‘eval_to (j1 + k + j) f = eval_to j f’
            by (irule eval_to_mono \\ gs [])
          \\ ‘eval_to (j1 + k + j) x = eval_to (j1 + k) x’
            by (irule eval_to_mono \\ gs []
                \\ strip_tac \\ gs [])
          \\ qexists_tac ‘j1 + k + j’ \\ simp []
          \\ Cases_on ‘eval_to (j1 + k) x’ \\ gs [])
    \\ ‘∃j2. ($= +++ v_rel) (eval_to (j2 + k) f) (eval_to k g)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ ‘∃u2. eval_to (j1 + k) x = INR u2’
      by (Cases_on ‘eval_to (j1 + k) x’ \\ gs [])
    \\ gs []
    \\ Cases_on ‘eval_to k g’ \\ gs []
    >- (
      rename1 ‘_ = INL err’
      \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (j2 + k) f’ \\ gvs []
      \\ Cases_on ‘eval_to k x = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀i. eval_to (i + k) x = eval_to k x’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k x’ \\ gs []
      \\ Cases_on ‘eval_to k f’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ gs []
        \\ qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀i. eval_to (i + k) f = eval_to k f’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k f’ \\ gs [])
    \\ rename1 ‘eval_to k g = INR v1’
    \\ ‘∃v2. eval_to (j2 + k) f = INR v2’
      by (Cases_on ‘eval_to (j2 + k) f’ \\ gs [])
    \\ gs []
    \\ ‘∀j. eval_to (j + j1 + k) x = eval_to (j1 + k) x’
      by (strip_tac
          \\ irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ ‘∀j. eval_to (j + j2 + k) f = eval_to (j2 + k) f’
      by (strip_tac
          \\ irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ Cases_on ‘dest_anyClosure v1’ \\ gs []
    >- (
      qexists_tac ‘j1 + j2’ \\ gs []
      \\ once_rewrite_tac [DECIDE “j1 + (j2 + k) = j2 + (j1 + k)”]
      \\ gs []
      \\ Cases_on ‘v2’ \\ Cases_on ‘v1’ \\ gvs [dest_anyClosure_def]
      \\ rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL \\ gs [])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ rw [Once exp_rel_cases] \\ gs [])
    \\ pairarg_tac \\ gvs []
    \\ rename1 ‘subst (ws2 ++ [s2,w2]) b2’
    \\ ‘∃b1 ws1. dest_anyClosure v2 = INR (s2,b1,ws1) ∧
                 exp_rel b1 b2 ∧
                 LIST_REL (λ(f,v) (g,w). f = g ∧ v_rel v w) ws1 ws2’
      by (Cases_on ‘v2’ \\ Cases_on ‘v1’ \\ gvs [dest_anyClosure_def]
          \\ rename1 ‘LIST_REL _ xs ys’
          \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s)
                             (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL \\ gs [])
          \\ gs [OPTREL_def]
          \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
          \\ rw [Once exp_rel_cases] \\ gs []
          \\ gvs [EVERY2_MAP, LAMBDA_PROD]
          \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY])
    \\ IF_CASES_TAC \\ gs []
    >- (
      Cases_on ‘eval_to 0 x = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to j x = eval_to 0 x’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ Cases_on ‘eval_to 0 f = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to j f = eval_to 0 f’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ qexists_tac ‘0’ \\ simp [])
    \\ ‘∀k. eval_to k (subst (ws1 ++ [s2,u2]) b1) ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (App _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j1 + j2 + j + k’ \\ gs []
          \\ once_rewrite_tac
            [DECIDE “j + (j1 + (j2 + k)) = (j + j1) + (j2 + k)”] \\ gs []
          \\ once_rewrite_tac
            [DECIDE “j + (j1 + (j2 + k)) = (j + j2) + (j1 + k)”] \\ gs []
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ irule eval_to_mono \\ simp [])
    \\ Cases_on ‘eval_to (k - 1) (subst (ws2 ++ [s2,w2]) b2) = INL Diverge’
    >- (
      Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k) x = eval_to k x’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ Cases_on ‘eval_to k f = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k) f = eval_to k f’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ ‘∀j. j + k - 1 = j + (k - 1)’
        by gs []
      \\ asm_simp_tac bool_ss []
      \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def]
      \\ irule exp_rel_subst
      \\ gs [EVERY2_MAP, LIST_REL_CONJ, ELIM_UNCURRY]
      \\ irule LIST_EQ
      \\ gvs [EL_MAP, LIST_REL_EL_EQN])
    \\ Q.REFINE_EXISTS_TAC ‘j1 + j2 + j’ \\ gs []
    \\ once_rewrite_tac
      [DECIDE “j + (j1 + (j2 + k)) = (j + j2) + (j1 + k)”] \\ gs []
    \\ once_rewrite_tac
      [DECIDE “j + (j1 + (j2 + k)) = (j + j1) + (j2 + k)”] \\ gs []
    \\ qmatch_goalsub_abbrev_tac ‘_ (eval_to _ X1) (eval_to _ X2)’
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) X1) (eval_to (k - 1) X2)’
      by (first_x_assum irule
          \\ gs [Abbr ‘X1’, Abbr ‘X2’, eval_to_wo_def]
          \\ irule exp_rel_subst
          \\ gvs [EVERY2_MAP, LIST_REL_EL_EQN, ELIM_UNCURRY]
          \\ irule LIST_EQ
          \\ gs [EL_MAP])
    \\ qexists_tac ‘j’
    \\ ‘eval_to (j + k - 1) X1 ≠ INL Diverge’
      by (strip_tac \\ Cases_on ‘eval_to (k - 1) X2’ \\ gs [])
    \\ drule_then (qspec_then ‘j + j1 + j2 + k - 1’ assume_tac) eval_to_mono
    \\ gs [])

  >~ [‘Lam s x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def])

  >~ [‘Force x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases]
    \\ rename1 ‘exp_rel x y’
    \\ CONV_TAC (QUANT_CONV (LAND_CONV (SIMP_CONV std_ss [Once eval_to_def])))
    \\ CONV_TAC (QUANT_CONV (RAND_CONV (SIMP_CONV std_ss [Once eval_to_def])))
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + k) x) (eval_to k y)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def]
          \\ qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
          \\ simp [Once eval_to_def]
          \\ qexists_tac ‘j + 1’ \\ simp []
          \\ ‘eval_to (j + 1) x = eval_to j x’
            suffices_by rw []
          \\ irule eval_to_mono \\ gs [])
    \\ Cases_on ‘eval_to k y = INL Diverge’
    >- (
      Cases_on ‘eval_to k x = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k) x = eval_to k x’
        by (gen_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k x’ \\ gs [])
    \\ Cases_on ‘eval_to (j + k) x’ \\ Cases_on ‘eval_to k y’ \\ gvs []
    >- (
      qexists_tac ‘j’
      \\ simp [])
    \\ rename1 ‘v_rel v w’
    \\ ‘OPTREL v_rel (dest_Tick v) (dest_Tick w)’
      by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
          \\ gs [Once (CONJUNCT2 exp_rel_cases)])
    \\ gs [OPTREL_def]
    >~ [‘dest_Tick _ = SOME _’] >- (
      Cases_on ‘eval_to (k - 1) (Force (Value y0)) = INL Diverge’
      >- (
        Cases_on ‘eval_to k x = INL Diverge’
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘∀j. eval_to (j + k) x = eval_to k x’
          by (gen_tac \\ irule eval_to_mono \\ gs [])
        \\ gs []
        \\ ‘∀j. j + k - 1 = j + (k - 1)’
          by gs []
        \\ asm_simp_tac std_ss []
        \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
        \\ first_x_assum irule
        \\ simp [eval_to_wo_def]
        \\ irule_at Any exp_rel_Force
        \\ irule_at Any exp_rel_Value
        \\ gs []
        \\ qx_gen_tac ‘j’
        \\ strip_tac
        \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _ ’ mp_tac
        \\ simp [Once eval_to_def]
        \\ qexists_tac ‘j + k’
        \\ asm_simp_tac std_ss []
        \\ simp []
        \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
        \\ irule eval_to_mono \\ gs [])
      \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
        by (gen_tac \\ irule eval_to_mono \\ gs [])
      \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
      \\ qsuff_tac ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1))
                                           (Force (Value x0)))
                                  (eval_to ( k - 1)
                                           (Force (Value y0)))’
      >- (
        disch_then (qx_choose_then ‘j1’ assume_tac)
        \\ ‘eval_to (j1 + j + k - 1) (Force (Value x0)) =
            eval_to (j1 + k - 1) (Force (Value x0))’
          by (irule eval_to_mono \\ gs []
              \\ strip_tac \\ gs []
              \\ Cases_on ‘eval_to (k - 1) (Force (Value y0))’ \\ gs [])
        \\ qexists_tac ‘j1’ \\ gs [])
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def, exp_size_def]
      \\ irule_at Any exp_rel_Force
      \\ irule_at Any exp_rel_Value \\ gs []
      \\ qx_gen_tac ‘j1’
      \\ strip_tac
      \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _ ’ mp_tac
      \\ simp [Once eval_to_def]
      \\ qexists_tac ‘j + (j1 + k)’
      \\ asm_simp_tac std_ss []
      \\ simp []
      \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
      \\ irule eval_to_mono \\ gs [])
    \\ Cases_on ‘dest_anyThunk w’ \\ gs []
    >- (
      qexists_tac ‘j’ \\ gs []
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
      \\ rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s)
                             (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL \\ gs [])
      \\ gs [OPTREL_def]
      \\ rgs [Once exp_rel_cases])
    \\ pairarg_tac \\ gvs []
    \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
    >- (
      rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s)
                             (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL \\ gs [])
      \\ gs [OPTREL_def]
      \\ rgs [Once exp_rel_cases] \\ rw []
      \\ rename1 ‘exp_rel x1 y1’
      THEN (
        Cases_on ‘eval_to (k - 1) (subst_funs binds y1) = INL Diverge’
        >- (
          Cases_on ‘eval_to k x = INL Diverge’
          >- (
            qexists_tac ‘0’
            \\ simp [])
          \\ ‘∀j1. eval_to (j1 + k) x = eval_to (j + k) x’
            by (gen_tac
                \\ drule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
                \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
                \\ gs [])
          \\ gs []
          \\ ‘∀j. j + k - 1 = j + (k - 1)’ by gs []
          \\ asm_simp_tac std_ss []
          \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
          \\ gvs [PULL_FORALL]
          \\ first_x_assum $ qspecl_then [`k-1`,`subst_funs xs x1`,`subst_funs
              binds y1`] mp_tac
          \\ rewrite_tac [AND_IMP_INTRO]
          \\ reverse impl_tac >- (
            strip_tac
            \\ qexists `j`
            \\ simp [oneline sum_bind_def] \\ CASE_TAC \\ gvs [])
          \\ gvs [GSYM PULL_FORALL]
          \\ gs [eval_to_wo_def, subst_funs_def]
          \\ irule_at Any exp_rel_subst
          \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
                   EVERY2_MAP]
          \\ gvs [LIST_REL_EL_EQN, LIST_REL_CONJ, ELIM_UNCURRY]
          \\ irule_at Any LIST_EQ \\ gvs [EL_MAP]
          \\ qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
          \\ simp [Once eval_to_def]
          \\ qexists_tac ‘j + k’
          \\ simp [dest_anyThunk_def, subst_funs_def, ELIM_UNCURRY]
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ simp [oneline sum_bind_def] \\ CASE_TAC \\ gvs []
          \\ qmatch_asmsub_abbrev_tac `eval_to j exp = INL Type_error`
          \\ `eval_to j exp ≠ INL Diverge` by gvs []
          \\ drule eval_to_mono \\ strip_tac
          \\ first_x_assum $ qspec_then `j + k - 1` assume_tac
          \\ gvs [])
        \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
          by (gen_tac \\ irule eval_to_mono \\ gs [])
        \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
        \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) (subst_funs xs x1))
                                   (eval_to (k - 1) (subst_funs binds y1))’
          suffices_by (
            disch_then (qx_choose_then ‘j1’ assume_tac)
            \\ ‘eval_to (j1 + j + k - 1) (subst_funs xs x1) =
                eval_to (j1 + k - 1) (subst_funs xs x1)’
              by (irule eval_to_mono \\ gs []
                  \\ strip_tac \\ gs []
                  \\ Cases_on ‘eval_to (k - 1) (subst_funs binds y1)’ \\ gs [])
            \\ qexists_tac ‘j1’ \\ gs []
            \\ simp [oneline sum_bind_def] \\ rpt (CASE_TAC \\ gvs [])
            \\ drule v_rel_anyThunk \\ gvs [])
        \\ first_x_assum irule
        \\ gs [eval_to_wo_def, subst_funs_def]
        \\ irule_at Any exp_rel_subst
        \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
                 EVERY2_MAP]
        \\ gvs [LIST_REL_EL_EQN, LIST_REL_CONJ, ELIM_UNCURRY]
        \\ irule_at Any LIST_EQ \\ gvs [EL_MAP]
        \\ qx_gen_tac ‘j1’
        \\ strip_tac
        \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
        \\ simp [Once eval_to_def]
        \\ qexists_tac ‘j + (j1 + k)’
        \\ asm_simp_tac std_ss []
        \\ simp [dest_anyThunk_def, subst_funs_def, ELIM_UNCURRY]
        \\ simp [oneline sum_bind_def] \\ CASE_TAC \\ gvs []
        \\ qmatch_asmsub_abbrev_tac `eval_to j1 exp = INL Type_error`
        \\ `eval_to j1 exp ≠ INL Diverge` by gvs []
        \\ drule eval_to_mono \\ strip_tac
        \\ first_x_assum $ qspec_then `j + (j1 + k) - 1` assume_tac
        \\ gvs []))
    \\ simp [subst_funs_def]
    \\ Cases_on ‘v’ \\ gs [v_rel_def]
    \\ rename1 ‘exp_rel x1 y1’
    \\ Cases_on ‘eval_to (k - 1) y1 = INL Diverge’
    >- (
    Cases_on ‘eval_to k x = INL Diverge’
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∀j. eval_to (j + k) x = eval_to k x’
      by (gen_tac \\ irule eval_to_mono \\ gs [])
    \\ gvs []
    \\ ‘∀j. j + k - 1 = j + (k - 1)’ by gs []
    \\ asm_simp_tac std_ss []
    \\ qpat_assum `_ = INL Diverge` (SUBST1_TAC o SYM)
    \\ gvs [PULL_FORALL]
    \\ first_x_assum $ qspecl_then [`k-1`,`x1`,`y1`] mp_tac
    \\ rewrite_tac [AND_IMP_INTRO]
    \\ reverse impl_tac >- (
      strip_tac
      \\ qexists `j` \\ gvs []
      \\ simp [oneline sum_bind_def] \\ CASE_TAC \\ gvs [])
    \\ gvs [GSYM PULL_FORALL]
    \\ gs [eval_to_wo_def]
    \\ qx_gen_tac ‘j’
    \\ strip_tac
    \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
    \\ simp [Once eval_to_def]
    \\ qexists_tac ‘j + k’
    \\ asm_simp_tac std_ss []
    \\ simp [dest_anyThunk_def, subst_funs_def]
    \\ simp [oneline sum_bind_def] \\ CASE_TAC \\ gvs []
    \\ `eval_to j x1 ≠ INL Diverge` by gvs []
    \\ drule eval_to_mono \\ strip_tac
    \\ first_x_assum $ qspec_then `j + k - 1` assume_tac
    \\ gvs [])
    \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
      by (gen_tac \\ irule eval_to_mono \\ gs [])
    \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) x1)
                           (eval_to (k - 1) y1)’
      suffices_by (
      disch_then (qx_choose_then ‘j1’ assume_tac)
      \\ ‘eval_to (j1 + j + k - 1) x1 =
          eval_to (j1 + k - 1) x1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs []
            \\ Cases_on ‘eval_to (k - 1) y1’ \\ gs [])
      \\ qexists_tac ‘j1’ \\ gs []
      \\ simp [oneline sum_bind_def] \\ rpt (CASE_TAC \\ gvs [])
      \\ drule v_rel_anyThunk \\ gvs [])
    \\ first_x_assum irule
    \\ gs [eval_to_wo_def]
    \\ qx_gen_tac ‘j1’
    \\ strip_tac
    \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
    \\ simp [Once eval_to_def]
    \\ qexists_tac ‘j + (j1 + k)’
    \\ asm_simp_tac std_ss []
    \\ simp [dest_anyThunk_def, subst_funs_def]
    \\ simp [oneline sum_bind_def] \\ CASE_TAC \\ gvs []
    \\ `eval_to j1 x1 ≠ INL Diverge` by gvs []
    \\ drule eval_to_mono \\ strip_tac
    \\ first_x_assum $ qspec_then `j + (j1 + k) - 1` assume_tac
    \\ gvs [])

  >~ [‘If x1 y1 z1’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∀k. eval_to k x1 ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (If _ _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j + 1’ \\ gs [])
    \\ ‘∃j1. ($= +++ v_rel) (eval_to (j1 + (k - 1)) x1)
                                (eval_to (k - 1) x2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def])
    \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    >- (
      rename1 ‘_ = INL err’
      \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gvs []
      \\ qexists_tac ‘j1’ \\ simp [])
    \\ IF_CASES_TAC \\ gs []
    >- (
      ‘∀k. eval_to k y1 ≠ INL Type_error’
        by (qx_gen_tac ‘j’
            \\ strip_tac
            \\ qpat_x_assum ‘∀k. eval_to _ (If _ _ _) ≠ _’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + j1 + k’ \\ gs []
            \\ ‘eval_to (j + (j1 + k) - 1) x1 = eval_to (j1 + k - 1) x1’
              suffices_by (
                rw []
                \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
                \\ qpat_assum ‘eval_to j y1 = _’ (SUBST1_TAC o SYM)
                \\ irule eval_to_mono \\ gs [])
            \\ irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ ‘∃j2. ($= +++ v_rel) (eval_to (j2 + (k - 1)) y1)
                                  (eval_to (k - 1) y2)’
        by (first_x_assum irule \\ simp [eval_to_wo_def])
      \\ Cases_on ‘eval_to (k - 1) y2’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (j2 + k - 1) y1’ \\ gs []
        \\ Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘eval_to (j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
          by (drule_then (qspec_then ‘j1 + k - 1’ assume_tac ) eval_to_mono
              \\ drule_then (qspec_then ‘j2 + k - 1’ assume_tac ) eval_to_mono
              \\ gs [])
        \\ qexists_tac ‘j2’ \\ gs []
        \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs [])
      \\ qexists_tac ‘j1 + j2’
      \\ ‘eval_to (j1 + j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
      \\ ‘eval_to (j1 + j2 + k - 1) y1 = eval_to (j2 + k - 1) y1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j2 + k - 1) y1’ \\ gs [])
    \\ IF_CASES_TAC \\ gs []
    >- (
      ‘∀k. eval_to k z1 ≠ INL Type_error’
        by (qx_gen_tac ‘j’
            \\ strip_tac
            \\ qpat_x_assum ‘∀k. eval_to _ (If _ _ _) ≠ _’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + j1 + k’ \\ gs []
            \\ ‘eval_to (j + (j1 + k) - 1) x1 = eval_to (j1 + k - 1) x1’
              suffices_by (
                rw []
                \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
                \\ qpat_assum ‘eval_to j z1 = _’ (SUBST1_TAC o SYM)
                \\ irule eval_to_mono \\ gs [])
            \\ irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ ‘∃j2. ($= +++ v_rel) (eval_to (j2 + (k - 1)) z1)
                                  (eval_to (k - 1) z2)’
        by (first_x_assum irule \\ simp [eval_to_wo_def])
      \\ Cases_on ‘eval_to (k - 1) z2’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (j2 + k - 1) z1’ \\ gs []
        \\ Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘eval_to (j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
          by (drule_then (qspec_then ‘j1 + k - 1’ assume_tac ) eval_to_mono
              \\ drule_then (qspec_then ‘j2 + k - 1’ assume_tac ) eval_to_mono
              \\ gs [])
        \\ qexists_tac ‘j2’ \\ gs []
        \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs [])
      \\ qexists_tac ‘j1 + j2’
      \\ ‘eval_to (j1 + j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
      \\ ‘eval_to (j1 + j2 + k - 1) z1 = eval_to (j2 + k - 1) z1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j2 + k - 1) z1’ \\ gs [])
    \\ qexists_tac ‘j1’
    \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
    \\ rename1 ‘v_rel v w’
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs [])

  >~ [‘Delay x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def])

  >~ [‘MkTick x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ rename1 ‘exp_rel x y’
    \\ simp [eval_to_def]
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + k) x) (eval_to k y)’
      suffices_by (
        disch_then (qx_choose_then ‘j’ assume_tac)
        \\ qexists_tac ‘j’
        \\ Cases_on ‘eval_to (j + k) x’ \\ Cases_on ‘eval_to k y’ \\ gs []
        \\ irule v_rel_DoTick \\ gs [])
    \\ first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def]
    \\ rpt strip_tac
    \\ first_x_assum (qspec_then ‘k’ mp_tac)
    \\ simp [eval_to_def])

  >~ [‘Value v’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def])

  >~ [‘Prim op xs’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ gvs [LIST_REL_EL_EQN]
    \\ ‘∀n. n < LENGTH xs ⇒ ∀k. eval_to k (EL n xs) ≠ INL Type_error’
      by (ntac 2 strip_tac
          \\ qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ Cases_on ‘op’ \\ gs []
          >- (
            simp [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
            \\ qexists_tac ‘j’
            \\ gs [SF SFY_ss])
          >- (
            IF_CASES_TAC \\ gs []
            \\ gs [DECIDE “n < 1n ⇔ n = 0”]
            \\ gvs [LENGTH_EQ_NUM_compute]
            \\ qexists_tac ‘j + 1’
            \\ simp [])
          >- (
            IF_CASES_TAC \\ gs []
            \\ gs [DECIDE “n < 1n ⇔ n = 0”]
            \\ gvs [LENGTH_EQ_NUM_compute]
            \\ qexists_tac ‘j + 1’
            \\ simp [])
          \\ qexists_tac ‘j + 1’ \\ simp []
          \\ qmatch_goalsub_abbrev_tac ‘result_map f xs’
          \\ ‘result_map f xs = INL Type_error’
            suffices_by rw []
          \\ simp [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
          \\ gs [Abbr ‘f’]
          \\ IF_CASES_TAC \\ gs [])
    \\ ‘∀j. j ≤ k ⇒
          ∀n. n < LENGTH xs ⇒
            ∃m. ($= +++ v_rel) (eval_to (m + j) (EL n xs))
                                   (eval_to j (EL n ys))’
      by (qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ _’ kall_tac
          \\ rpt (pop_assum mp_tac)
          \\ qid_spec_tac ‘ys’
          \\ Induct_on ‘xs’ \\ simp []
          \\ Cases_on ‘ys’ \\ simp []
          \\ qx_gen_tac ‘x’
          \\ rpt strip_tac
          \\ rename1 ‘_ _ (_ _ (EL _ (y::ys)))’
          \\ last_x_assum (qspec_then ‘ys’ mp_tac)
          \\ simp [AND_IMP_INTRO]
          \\ impl_tac
          >- (
            reverse conj_tac
            >- (
              qx_gen_tac ‘m’ \\ strip_tac
              \\ first_x_assum (qspec_then ‘SUC m’ assume_tac)
              \\ gs [])
            \\ reverse conj_tac
            >- (
              qx_gen_tac ‘m’ \\ strip_tac
              \\ first_x_assum (qspec_then ‘SUC m’ assume_tac)
              \\ first_x_assum (qspec_then ‘SUC m’ assume_tac)
              \\ gs [])
            \\ qx_gen_tac ‘k1’ \\ qx_gen_tac ‘x1’ \\ rw []
            \\ gvs [eval_to_wo_def]
            \\ first_x_assum (irule_at Any)
            \\ gs [exp_size_def])
          \\ strip_tac
          \\ Cases_on ‘n’ \\ gs []
          \\ once_rewrite_tac [arithmeticTheory.ADD_COMM]
          \\ first_x_assum (irule_at Any)
          \\ simp [eval_to_wo_def, exp_size_def]
          \\ qpat_x_assum ‘∀n. n < SUC _ ⇒ _’ (qspec_then ‘0’ assume_tac)
          \\ gs []
          \\ qpat_x_assum ‘∀n. n < SUC _ ⇒ _’ (qspec_then ‘0’ assume_tac)
          \\ gs [])
    \\ last_x_assum kall_tac
    \\ Cases_on ‘op’ \\ gs []
    >- ((* Cons *)
      first_x_assum (qspec_then ‘k’ assume_tac) \\ gs []
      \\ qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ _’ kall_tac
      \\ ‘∃j. ($= +++ (LIST_REL v_rel))
                (result_map (λx. eval_to (j + k) x) xs)
                (result_map (λx. eval_to k x) ys)’
        suffices_by (
          disch_then (qx_choose_then ‘j’ assume_tac)
          \\ qexists_tac ‘j’
          \\ Cases_on ‘result_map (λx. eval_to (j + k) x ) xs’
          \\ Cases_on ‘result_map (λx. eval_to k x) ys’ \\ gs []
          \\ rw [EVERY_EL]
          \\ (
            gvs [LIST_REL_EL_EQN]
            \\ ntac 2 (first_x_assum drule \\ rw [])
            \\ drule v_rel_anyThunk \\ rw []))
      \\ ‘result_map (λx. eval_to k x) ys ≠ INL Type_error’
        by (gvs [result_map_def, CaseEq "bool"]
            \\ strip_tac
            \\ gs [Once MEM_EL, PULL_EXISTS, EL_MAP]
            \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
            \\ Cases_on ‘eval_to (j + k) (EL n xs)’ \\ gs [])
      \\ Cases_on ‘result_map (λx. eval_to k x) ys’ \\ gs []
      >- (
        rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs []
        \\ gs [result_map_def, MEM_EL, PULL_EXISTS, CaseEq "bool", EL_MAP,
               SF CONJ_ss]
        \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac)) \\ gs []
        \\ Cases_on ‘eval_to (j + k) (EL n xs)’ \\ gs []
        \\ qexists_tac ‘j’
        \\ simp [SF SFY_ss])
      \\ gs [result_map_def, MEM_EL, PULL_EXISTS, CaseEq "bool", EL_MAP,
             SF CONJ_ss]
      \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ ‘∃m. ∀n. n < LENGTH ys ⇒
                ($= +++ v_rel) (eval_to (k + m) (EL n xs))
                                   (eval_to k (EL n ys))’
        suffices_by (
          disch_then (qx_choose_then ‘m’ assume_tac)
          \\ qexists_tac ‘m’
          \\ IF_CASES_TAC \\ gs []
          >- (
            first_x_assum (drule_then assume_tac) \\ gs []
            \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
          \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
          \\ rw [EVERY2_MAP, LIST_REL_EL_EQN]
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
          >- (
            rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs [])
          \\ Cases_on ‘eval_to (k + m) (EL n xs)’ \\ gs [])
      \\ gvs []
      \\ rpt (pop_assum mp_tac)
      \\ qid_spec_tac ‘ys’
      \\ Induct_on ‘xs’ \\ simp []
      \\ Cases_on ‘ys’ \\ simp []
      \\ qx_gen_tac ‘x’
      \\ rename1 ‘_ (EL _ _) (EL _ (y::ys))’ \\ rw []
      \\ first_x_assum (qspec_then ‘ys’ mp_tac)
      \\ simp [AND_IMP_INTRO]
      \\ impl_tac
      >- (
        rw []
        \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
        \\ res_tac \\ fs []
        \\ gs [SF SFY_ss])
      \\ disch_then (qx_choose_then ‘m’ assume_tac)
      \\ qpat_x_assum ‘∀n. _ ⇒ ∃m. _’ (qspec_then ‘0’ mp_tac)
      \\ simp []
      \\ disch_then (qx_choose_then ‘m1’ assume_tac)
      \\ qexists_tac ‘m + m1’
      \\ Cases \\ gs []
      >- (
        ‘eval_to (k + (m + m1)) x = eval_to (k + m1) x’
          by (irule eval_to_mono \\ simp []
              \\ strip_tac \\ gs []
              \\ Cases_on ‘eval_to k y’ \\ gs []
              \\ ‘0 < SUC (LENGTH ys)’ by gs []
              \\ res_tac \\ fs [])
        \\ gs [])
      \\ strip_tac
      \\ rename1 ‘n < LENGTH ys’
      \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
      \\ res_tac \\ fs []
      \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
      >- (
        rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs [])
      \\ ‘eval_to (k + (m + m1)) (EL n xs) = eval_to (k + m) (EL n xs)’
        by (irule eval_to_mono \\ simp []
            \\ strip_tac \\ gs [])
      \\ gs [])
    >- ((* IsEq *)
      first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
        \\ qexists_tac ‘m’ \\ simp [])
      \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ qexists_tac ‘m’ \\ simp []
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* Proj *)
      first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
        \\ qexists_tac ‘m’ \\ simp [])
      \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ qexists_tac ‘m’ \\ simp []
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* AtomOp *)
      first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
      \\ Cases_on ‘k = 0’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [result_map_def, MEM_MAP, GSYM NOT_NULL_MEM, NULL_EQ]
        \\ Cases_on ‘xs’ \\ Cases_on ‘ys’ \\ gs []
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [])
      \\ qabbrev_tac ‘f = λj x. case eval_to (j + k - 1) x of
                                  INR (Atom l) => INR l
                                | INL err => INL err
                                | _ => INL Type_error’
      \\ qabbrev_tac ‘g = λx. case eval_to (k - 1) x of
                                INR (Atom l) => INR l
                              | INL err => INL err
                              | _ => INL Type_error’
      \\ gs []
      \\ ‘∃j. result_map (f j) xs = result_map g ys’
        suffices_by (
          disch_then (qx_choose_then ‘j’ assume_tac)
          \\ qexists_tac ‘j’
          \\ simp [SF ETA_ss]
          \\ Cases_on ‘result_map g ys’ \\ gs []
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [])
      \\ ‘∀j. result_map (f j) xs ≠ INL Type_error’
        by (rpt strip_tac
            \\ gs [result_map_def, MEM_EL, EL_MAP, SF CONJ_ss,
                   CaseEq "bool", Abbr ‘f’]
            \\ qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ INL _’ mp_tac \\ simp []
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + k’
            \\ simp [result_map_def, MEM_MAP, MEM_EL, PULL_EXISTS]
            \\ IF_CASES_TAC \\ gs [])
      \\ qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ _’ kall_tac
      \\ Cases_on ‘result_map g ys = INL Diverge’ \\ gs []
      >- (
        unabbrev_all_tac \\ gs []
        \\ rgs [result_map_def, CaseEq "bool", MEM_MAP]
        \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ gvs [MEM_EL, PULL_EXISTS]
        \\ first_x_assum drule
        \\ pop_assum mp_tac
        \\ rpt CASE_TAC \\ gvs []
        \\ rw []
        \\ last_x_assum (drule_then assume_tac)
        \\ last_x_assum (drule_then assume_tac)
        \\ last_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
        \\ qexists_tac ‘j’
        \\ qexists_tac ‘n’
        \\ CASE_TAC \\ gs [])
      \\ rgs [result_map_def, MEM_EL, EL_MAP, SF CONJ_ss, Once (CaseEq "bool"),
              DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      >- (
        ‘F’ suffices_by rw []
        \\ unabbrev_all_tac
        \\ gs [CaseEq "bool", DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        \\ first_x_assum (drule_then (qx_choose_then ‘m’ assume_tac))
        \\ Cases_on ‘eval_to (k - 1) (EL n ys)’
        \\ Cases_on ‘eval_to (m + k - 1) (EL n xs)’ \\ gs []
        \\ first_x_assum (drule_then (qspec_then ‘m’ assume_tac))
        \\ rename1 ‘v_rel v w’
        \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [])
      \\ rgs [Once (CaseEq "bool"), DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      \\ ‘∃j. ∀n. n < LENGTH ys ⇒
                ($= +++ v_rel) (eval_to (j + k - 1) (EL n xs))
                                   (eval_to (k - 1) (EL n ys))’
        by (unabbrev_all_tac
            \\ rpt (pop_assum mp_tac)
            \\ qid_spec_tac ‘ys’
            \\ Induct_on ‘xs’ \\ simp []
            \\ qx_gen_tac ‘x’
            \\ Cases \\ simp []
            \\ rename1 ‘eval_to (k - 1) (EL _ (y::ys))’
            \\ rw []
            \\ last_x_assum (qspec_then ‘ys’ mp_tac)
            \\ simp [AND_IMP_INTRO, GSYM CONJ_ASSOC]
            \\ impl_tac
            >- (
              rw []
              \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
              \\ res_tac \\ fs []
              \\ gs [SF SFY_ss])
            \\ disch_then (qx_choose_then ‘j’ assume_tac)
            \\ ‘∃j1. ($= +++ v_rel) (eval_to (j1 + k - 1) x)
                                        (eval_to (k - 1) y)’
              by (‘0 < SUC (LENGTH ys)’ by gs []
                  \\ res_tac \\ fs []
                  \\ qexists_tac ‘m’ \\ simp [])
            \\ qexists_tac ‘j + j1’
            \\ Cases \\ gs []
            >- (
              ‘eval_to (j + (j1 + k) - 1) x = eval_to (j1 + k - 1) x’
                by (irule eval_to_mono \\ gs []
                    \\ strip_tac \\ gs []
                    \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
                    \\ ‘0 < SUC (LENGTH ys)’ by gs []
                    \\ res_tac \\ fs []
                    \\ gs [])
              \\ gs [])
            \\ qmatch_goalsub_rename_tac ‘n < LENGTH ys’
            \\ strip_tac
            \\ ‘eval_to (j + (j1 + k) - 1) (EL n xs) =
                eval_to (j + k - 1) (EL n xs)’
              by (irule eval_to_mono \\ gs []
                  \\ strip_tac \\ gs []
                  \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
                  \\ res_tac \\ fs []
                  \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs [])
            \\ gs [])
      \\ qexists_tac ‘j’
      \\ unabbrev_all_tac
      \\ gs [result_map_def, MEM_MAP, MAP_MAP_o, combinTheory.o_DEF]
      \\ IF_CASES_TAC \\ rgs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      \\ IF_CASES_TAC \\ rgs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      >- (
        first_x_assum (drule_then assume_tac)
        \\ gvs [CaseEqs ["sum", "v", "err"]]
        \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs [])
      \\ rw []
      >- (
        rpt (first_x_assum (drule_then assume_tac))
        \\ first_x_assum (qspec_then ‘j + k - 1’ assume_tac)
        \\ gvs [CaseEqs ["sum", "v", "err"]]
        \\ Cases_on ‘eval_to (j + k - 1) (EL n xs)’
        \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs []
        >- (
          strip_tac \\ gs [])
        \\ rename1 ‘v_rel u v’
        \\ first_x_assum (qspec_then ‘j’ assume_tac) \\ gs []
        \\ Cases_on ‘u’ \\ Cases_on ‘v’ \\ gs [])
      \\ irule_at Any LIST_EQ
      \\ rw [EL_MAP]
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ first_x_assum (qspec_then ‘j’ assume_tac)
      \\ rpt CASE_TAC \\ gs []))

  >~ [`Monad mop xs`] >- (
    strip_tac >> rw[Once exp_rel_cases] >> gvs[eval_to_def])
QED

Theorem exp_rel_eval_to[allow_rebind] =
  REWRITE_RULE [d2b_goal_def] exp_rel_eval_to;

Theorem exp_rel_eval:
  exp_rel x y ∧
  eval x ≠ INL Type_error ⇒
    ($= +++ v_rel) (eval x) (eval y)
Proof
  strip_tac
  \\ dxrule_then assume_tac eval_not_error
  \\ simp [eval_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  >- (
    rename1 ‘_ (eval_to k x) (eval_to j y)’
    \\ drule_all_then
      (qspec_then ‘MAX k j’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to
    \\ ‘eval_to (m + MAX k j) x = eval_to k x’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ ‘eval_to (MAX k j) y = eval_to j y’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ gs [])
  >- (
    rename1 ‘_ _ (eval_to j y)’
    \\ drule_all_then
      (qspec_then ‘j’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to \\ gs [])
  \\ rename1 ‘_ _ (eval_to k x)’
  \\ drule_all_then
    (qspec_then ‘k’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to
  \\ Cases_on ‘eval_to (k + m) x’ \\ gvs []
  \\ drule_then (qspec_then ‘k + m’ assume_tac) eval_to_mono \\ gs []
QED

Theorem d2b_apply_closure[local]:
  exp_rel x y ∧
  v_rel v2 w2 ∧
  apply_closure x v2 f ≠ Err ∧
  f (INL Type_error) = Err ∧
  (∀x y.
     ($= +++ v_rel) x y ∧ f x ≠ Err ⇒
       next_rel v_rel exp_rel (f x) (g y)) ⇒
    next_rel v_rel exp_rel
             (apply_closure x v2 f)
             (apply_closure y w2 g)
Proof
  rw[thunk_semanticsTheory.apply_closure_def] >>
  gvs[thunk_semanticsTheory.with_value_def] >>
  `eval x ≠ INL Type_error` by (CCONTR_TAC >> gvs[]) >>
  dxrule_all_then assume_tac exp_rel_eval >>
  Cases_on `eval x` >> Cases_on `eval y` >> gvs[] >- (CASE_TAC >> gvs[]) >>
  rename1 `eval x = INR v1` >> rename1 `eval y = INR w1`
  \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [dest_anyClosure_def]
  >- (
    first_x_assum irule \\ gs []
    \\ irule exp_rel_eval
    \\ gs [closed_subst]
    \\ irule_at Any exp_rel_subst \\ gs []
    \\ strip_tac \\ gs [])
  \\ rename1 ‘LIST_REL _ xs ys’
  \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
    by (irule LIST_REL_OPTREL
        \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY])
  \\ gs [OPTREL_def]
  \\ qpat_x_assum ‘exp_rel x0 y0’ mp_tac
  \\ rw [Once exp_rel_cases] \\ gs []
  \\ first_x_assum irule \\ gs []
  \\ irule exp_rel_eval
  \\ irule_at Any exp_rel_subst
  \\ gs [EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
  \\ irule_at Any LIST_EQ
  \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
  \\ strip_tac \\ gs []
QED

Theorem d2b_rel_ok[local]:
  rel_ok F v_rel exp_rel
Proof
  rw [rel_ok_def]
  >- ((* ∀x. f x ≠ Err from rel_ok prevents this case *)
    simp [d2b_apply_closure])
  >- ((* Equal literals are related *)
    simp [exp_rel_Prim])
  >- ((* Equal 0-arity conses are related *)
    simp [exp_rel_Prim])
  >- ((* v_rel x y ⇒ exp_rel (Value x) (Value y) *)
    simp [exp_rel_Value])
QED

Theorem d2b_sim_ok[local]:
  sim_ok F v_rel exp_rel
Proof
  rw [sim_ok_def]
  \\ simp [exp_rel_eval]
  \\ irule exp_rel_subst \\ gs []
QED

Theorem case_d2b_semantics:
  exp_rel x y ∧
  closed x ∧
  pure_semantics$safe_itree (semantics x Done []) ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ irule sim_ok_semantics
  \\ irule_at Any d2b_sim_ok
  \\ irule_at Any d2b_rel_ok \\ gs []
QED
