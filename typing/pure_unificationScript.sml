(*
  Adapt unification from HOL/examples/algorithms/unification for use in PureCake
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     pred_setTheory relationTheory listTheory alistTheory finite_mapTheory;
open unifPropsTheory unifDefTheory walkTheory walkstarTheory collapseTheory substTheory;
open pure_typingTheory pure_inference_commonTheory;

val _ = new_theory "pure_unification";

Datatype:
  utype = uDBVar num
        | uPrimTy prim_ty
        | uException
        | uTypeCons num
        | uTuple
        | uFunction
        | uArray
        | uM
        | uNone
End

Definition encode_itype_def[nocompute]:
  encode_itype (DBVar n) = Const (uDBVar n) ∧
  encode_itype (PrimTy p) = Const (uPrimTy p) ∧
  encode_itype  Exception = Const (uException) ∧
  encode_itype (TypeCons c ts) = Pair (Const (uTypeCons c)) (encode_itypes ts) ∧
  encode_itype (Tuple ts) = Pair (Const uTuple) (encode_itypes ts) ∧
  encode_itype (Function t1 t2) =
    Pair (Const uFunction) (Pair (encode_itype t1) (encode_itype t2)) ∧
  encode_itype (Array t) = Pair (Const uArray) (encode_itype t) ∧
  encode_itype (M t) = Pair (Const uM) (encode_itype t) ∧
  encode_itype (CVar n) = Var n ∧

  encode_itypes [] = Const uNone ∧
  encode_itypes (t::ts) = Pair (encode_itype t) (encode_itypes ts)
End

Definition decode_utype_def[nocompute]:
  decode_utype (Var n) = SOME $ CVar n ∧
  decode_utype (Const (uDBVar n)) = SOME $ DBVar n ∧
  decode_utype (Const (uPrimTy p)) = SOME $ PrimTy p ∧
  decode_utype (Const  uException) = SOME $ Exception ∧
  decode_utype (Pair (Const (uTypeCons n)) uts) =
    OPTION_MAP (TypeCons n) (decode_utypes uts) ∧
  decode_utype (Pair (Const  uTuple) uts) = OPTION_MAP Tuple (decode_utypes uts) ∧
  decode_utype (Pair (Const uFunction) (Pair ut1 ut2)) = (
    OPTION_BIND (decode_utype ut1) $ λt1.
      OPTION_BIND (decode_utype ut2) $ λt2. SOME $ Function t1 t2) ∧
  decode_utype (Pair (Const  uArray) ut1) = OPTION_MAP Array (decode_utype ut1) ∧
  decode_utype (Pair (Const  uM) ut1) = OPTION_MAP M (decode_utype ut1) ∧
  decode_utype _ = NONE ∧

  decode_utypes (Const uNone) = SOME [] ∧
  decode_utypes (Pair u1 u2) = (
    OPTION_BIND (decode_utype u1) $ λt.
      OPTION_BIND (decode_utypes u2) $ λts. SOME $ t::ts) ∧
  decode_utypes _ = NONE
End

Triviality I_o_f:
  ∀m. I o_f m = m
Proof
  rw[GSYM fmap_EQ_THM]
QED

Triviality option_map_case:
  ∀f opt. OPTION_MAP f opt = case opt of NONE => NONE | SOME a => SOME $ f a
Proof
  gen_tac >> Cases >> simp[]
QED

Triviality option_bind_case:
  ∀x f. OPTION_BIND x f = case x of NONE => NONE | SOME y => f y
Proof
  Cases >> simp[]
QED

Theorem decode_encode:
  (∀it. decode_utype (encode_itype it) = SOME it) ∧
  (∀its. decode_utypes (encode_itypes its) = SOME its)
Proof
  Induct >> rw[encode_itype_def, decode_utype_def]
QED

Definition pure_wfs_def[nocompute]:
  pure_wfs s = wfs (encode_itype o_f s)
End

Definition pure_vwalk_def[nocompute]:
  pure_vwalk s v = THE $ decode_utype (vwalk (encode_itype o_f s) v)
End

Theorem pure_vwalk_ind:
  ∀s. pure_wfs s ⇒
    ∀P. (∀v. (∀w u. FLOOKUP s v = SOME (CVar u) ⇒ P u) ⇒ P v) ⇒ ∀v. P v
Proof
  ntac 4 strip_tac >> gvs[pure_wfs_def] >>
  drule $ DISCH_ALL vwalk_ind >> disch_then irule >> rw[] >>
  last_x_assum irule >> rw[] >>
  first_x_assum irule >>
  rw[FLOOKUP_o_f, encode_itype_def]
QED

Theorem pure_vwalk:
  ∀s. pure_wfs s ⇒
    ∀v.
      pure_vwalk s v =
        case FLOOKUP s v of
        | NONE => CVar v
        | SOME (CVar w) => pure_vwalk s w
        | SOME t => t
Proof
  rw[pure_vwalk_def, pure_wfs_def] >>
  CASE_TAC >> gvs[] >>
  simp[Once vwalk_def, FLOOKUP_o_f, decode_utype_def] >>
  Cases_on `x` >> gvs[encode_itype_def, decode_utype_def, decode_encode]
QED

Definition pure_walk_def[nocompute]:
  pure_walk s t = THE $ decode_utype (walk (encode_itype o_f s) (encode_itype t))
End

Theorem pure_walk:
  ∀s t. pure_walk s t =
    case t of
    | CVar v => pure_vwalk s v
    | t => t
Proof
  rw[pure_walk_def, pure_vwalk_def, walk_def] >>
  Cases_on `t` >> gvs[decode_utype_def, encode_itype_def, decode_encode]
QED

Definition pure_oc_def[nocompute]:
  pure_oc s t v = oc (encode_itype o_f s) (encode_itype t) v
End

Definition pure_vars_def[nocompute]:
  pure_vars t = vars (encode_itype t)
End

Theorem encode_vwalk:
  ∀s. pure_wfs s ⇒
    ∀u. vwalk (encode_itype o_f s) u = encode_itype (pure_vwalk s u)
Proof
  ntac 2 strip_tac >>
  recInduct $ (UNDISCH o Q.SPEC `s`) pure_vwalk_ind >> rw[] >>
  `wfs (encode_itype o_f s)` by metis_tac [pure_wfs_def] >>
  rw [Once vwalk_def, Once pure_vwalk, FLOOKUP_o_f] >>
  Cases_on `FLOOKUP s v` >> rw [encode_itype_def] >>
  Cases_on `x` >> rw[encode_itype_def]
QED

Theorem pure_oc_lemma:
  ∀l v s.
    oc (encode_itype o_f s) (encode_itypes l) v ⇔
    EXISTS (λt. oc (encode_itype o_f s) (encode_itype t) v) l
Proof
  Induct >> rw[encode_itype_def]
QED

Theorem pure_oc:
  ∀s. pure_wfs s ⇒
    ∀t v.
      pure_oc s t v =
        case pure_walk s t of
        | CVar u => v = u
        | TypeCons n its => EXISTS (λit. pure_oc s it v) its
        | Tuple its => EXISTS (λit. pure_oc s it v) its
        | Function it1 it2 => EXISTS (λit. pure_oc s it v) [it1;it2]
        | Array it => pure_oc s it v
        | M it => pure_oc s it v
        | _ => F
Proof
  rw[pure_oc_def] >>
  `wfs (encode_itype o_f s)` by fs [pure_wfs_def] >>
  rw[Once oc_walking, pure_walk_def] >>
  Cases_on `t` >>
  rw[walk_def, encode_itype_def, decode_utype_def, decode_encode,
     encode_vwalk, pure_oc_lemma] >>
  Cases_on `pure_vwalk s n` >> rw[encode_itype_def, pure_oc_lemma] >> gvs[] >>
  simp[decode_encode] >>
  Cases_on `x` >> gvs[encode_itype_def, pure_oc_lemma]
QED

Definition pure_ext_s_check_def[nocompute]:
  pure_ext_s_check s v t =
    OPTION_MAP ((o_f) (THE o decode_utype)) $
      ext_s_check (encode_itype o_f s) v (encode_itype t)
End

Theorem pure_ext_s_check:
  ∀s v t.
    pure_ext_s_check s v t = if pure_oc s t v then NONE else SOME (s |+ (v,t))
Proof
  rw[pure_ext_s_check_def, pure_oc_def, I_o_f,
     combinTheory.o_DEF, decode_encode]
QED

Definition pure_unify_def[nocompute]:
  pure_unify s t1 t2 =
    OPTION_MAP ((o_f) (THE o decode_utype)) $
      unify (encode_itype o_f s) (encode_itype t1) (encode_itype t2)
End

Definition pure_unifyl_def:
  pure_unifyl s [] [] = SOME s ∧
  pure_unifyl s (t1::ts1) (t2::ts2) = (
    case pure_unify s t1 t2 of
    | NONE => NONE
    | SOME s' => pure_unifyl s' ts1 ts2) ∧
  pure_unifyl s _ _ = NONE
End

Theorem encode_walk:
  ∀s. pure_wfs s ⇒
    ∀t. walk (encode_itype o_f s) (encode_itype t) =
        encode_itype (pure_walk s t)
Proof
  rw[walk_def] >>
  imp_res_tac encode_vwalk >> simp[] >>
  every_case_tac >> rw[pure_walk_def, decode_encode] >> gvs[] >>
  pop_assum $ SUBST_ALL_TAC o GSYM >> simp[decode_encode]
QED

Theorem encode_pair_cases:
  ∀t t1 t2. encode_itype t = Pair t1 t2 ⇒
    (∃c ts. t1 = Const (uTypeCons c) ∧ t2 = encode_itypes ts) ∨
    (∃ts. t1 = Const uTuple ∧ t2 = encode_itypes ts) ∨
    (∃it1 it2. t1 = Const uFunction ∧
               t2 = Pair (encode_itype it1) (encode_itype it2)) ∨
    (∃t. t1 = Const uArray ∧ t2 = encode_itype t) ∨
    (∃t. t1 = Const uM ∧ t2 = encode_itype t)
Proof
  Cases >> rw[encode_itype_def] >> rpt $ irule_at Any EQ_REFL
QED

Theorem encode_itype_injective:
  (∀t1 t2. encode_itype t1 = encode_itype t2 ⇔ t1 = t2) ∧
  (∀t1s t2s. encode_itypes t1s = encode_itypes t2s ⇔ t1s = t2s)
Proof
  rw[] >> eq_tac >> rw[] >>
  irule $ iffLR SOME_11 >> once_rewrite_tac[GSYM decode_encode] >> simp[]
QED

Theorem encode_itype_o_f_injective:
  ∀s1 s2. encode_itype o_f s1 = encode_itype o_f s2 ⇔ s1 = s2
Proof
  rw[] >> eq_tac >> rw[] >>
  gvs[fmap_eq_flookup, FLOOKUP_o_f] >> rw[] >>
  pop_assum $ qspec_then `x` assume_tac >>
  every_case_tac >> gvs[encode_itype_injective]
QED

Theorem encode_unify_lemma:
  ∀s t1 t2 s' t1' t2'.
    s = encode_itype o_f s' ∧
    pure_wfs s' ∧
    (
      (t1 = encode_itype t1' ∧ t2 = encode_itype t2') ∨
      (∃c. t1 = Const c ∧ t2 = Const c ∧ t1' = t2') ∨
      (∃c ts1 ts2.
        t1 = Pair (Const c) (encode_itypes ts1) ∧
        t2 = Pair (Const c) (encode_itypes ts2) ∧
          ((t1' = TypeCons ARB ts1 ∧ t2' = TypeCons ARB ts2) ∨
           (t1' = Tuple ts1 ∧ t2' = Tuple ts2))) ∨
      (∃c t11 t12 t21 t22.
        t1 = Pair (Const c) (Pair (encode_itype t11) (encode_itype t12)) ∧
        t2 = Pair (Const c) (Pair (encode_itype t21) (encode_itype t22)) ∧
        t1' = Function t11 t12 ∧ t2' = Function t21 t22) ∨
      (∃c ta tb.
        t1 = Pair (Const c) (encode_itype ta) ∧
        t2 = Pair (Const c) (encode_itype tb) ∧
        ((t1' = Array ta ∧ t2' = Array tb) ∨
         (t1' = M ta ∧ t2' = M tb))) ∨

      (∃ts1 ts2.
        t1 = encode_itypes ts1 ∧
        t2 = encode_itypes ts2 ∧
          ((t1' = TypeCons ARB ts1 ∧ t2' = TypeCons ARB ts2) ∨
           (t1' = Tuple ts1 ∧ t2' = Tuple ts2))) ∨
      (∃t11 t12 t21 t22.
        t1 = Pair (encode_itype t11) (encode_itype t12) ∧
        t2 = Pair (encode_itype t21) (encode_itype t22) ∧
        t1' = Function t11 t12 ∧ t2' = Function t21 t22) ∨
      (∃ta tb.
        t1 = encode_itype ta ∧
        t2 = encode_itype tb ∧
          ((t1' = Array ta ∧ t2' = Array tb) ∨
           (t1' = M ta ∧ t2' = M tb)))
    )
  ⇒ unify s t1 t2 = OPTION_MAP ((o_f) encode_itype) (pure_unify s' t1' t2')
Proof
  recInduct unify_ind >> simp[] >>
  rw[pure_unify_def] >> gvs[pure_wfs_def, option_map_case] >>
  qmatch_assum_abbrev_tac `wfs es`
  >- (
    qmatch_goalsub_abbrev_tac `unify es e1 e2` >>
    Cases_on `unify es e1 e2` >> gvs[combinTheory.o_DEF] >>
    qsuff_tac `∃s. x = encode_itype o_f s`
    >- (strip_tac >> rw[GSYM fmap_EQ_THM, decode_encode]) >>
    pop_assum mp_tac >> simp[Once unify_def] >>
    Cases_on `walk es e1` >> Cases_on `walk es e2` >> gvs[]
    >- (
      unabbrev_all_tac >> rw[]
      >- (irule_at Any EQ_REFL) >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (
      unabbrev_all_tac >> rw[] >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (
      unabbrev_all_tac >> rw[] >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (
      unabbrev_all_tac >> rw[] >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (
      rw[] >> gvs[] >>
      qmatch_assum_rename_tac `walk es e1 = Pair t1a t1d` >>
      qmatch_assum_rename_tac `walk es e2 = Pair t2a t2d` >>
      `Pair t1a t1d = encode_itype (pure_walk s' t1')` by
        metis_tac[encode_walk,pure_wfs_def] >>
      `Pair t2a t2d = encode_itype (pure_walk s' t2')` by
        metis_tac[encode_walk,pure_wfs_def] >>
      `wfs sx` by metis_tac[unify_unifier] >>
      `∀c1 c2.
        ((t1a = Const c1 ∧ t2a = Const c2) ∨
         (t2d = Const c1 ∧ t2d = Const c2)) ⇒ c1 = c2` by (
          rw[] >> ntac 2 $ qpat_x_assum `unify _ _ _ = _` mp_tac >>
          simp[Once unify_def] >> strip_tac >> simp[Once unify_def]) >>
      pop_assum mp_tac >> simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
      qspecl_then [`pure_walk s' t1'`,`t1a`,`t1d`] mp_tac encode_pair_cases >>
      qspecl_then [`pure_walk s' t2'`,`t2a`,`t2d`] mp_tac encode_pair_cases >>
      simp[] >> strip_tac >> strip_tac >> gvs[] >>
      rpt $ qpat_x_assum `Pair _ _ = _` $ assume_tac o GSYM
      >- (
        last_x_assum $
          qspecl_then[`s'`,`TypeCons ARB ts'`,`TypeCons ARB ts`] mp_tac >>
        simp[] >> CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      >- (
        last_x_assum $
          qspecl_then[`s'`,`Tuple ts'`,`Tuple ts`] mp_tac >>
        simp[] >> CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      >- (
        last_x_assum $
          qspecl_then[`s'`,`Function it1' it2'`,`Function it1 it2`] mp_tac >>
        simp[encode_itype_def] >>
        CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      >- (
        last_x_assum $
          qspecl_then[`s'`,`Array t'`,`Array t`] mp_tac >>
        simp[encode_itype_def] >> CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      >- (
        last_x_assum $
          qspecl_then[`s'`,`M t'`,`M t`] mp_tac >>
        simp[encode_itype_def] >> CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      )
    >- (
      unabbrev_all_tac >> rw[] >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (unabbrev_all_tac >> rw[] >> irule_at Any EQ_REFL)
    )
  >- simp[decode_encode, SF ETA_ss, combinTheory.o_DEF]
  >- (unabbrev_all_tac >> rw[Once unify_def])
  >- (unabbrev_all_tac >> rw[Once unify_def])
  >- (unabbrev_all_tac >> rw[Once unify_def])
  >- (unabbrev_all_tac >> rw[Once unify_def])
  >- (unabbrev_all_tac >> rw[Once unify_def])
  >- (
    simp[encode_itype_def] >>
    simp[Once unify_def, SimpRHS] >> CASE_TAC >> pop_assum mp_tac >>
    Cases_on `ts1` >> Cases_on `ts2` >> simp[encode_itype_def, Once unify_def]
    >- (
      rw[Abbr `es`] >>
      simp[o_f_o_f, combinTheory.o_DEF, decode_encode, SF ETA_ss]
      ) >>
    rw[] >> gvs[encode_itype_def] >>
    first_x_assum $ qspecl_then [`s'`,`h`,`h'`] mp_tac >> simp[] >> rw[] >>
    `wfs sx` by metis_tac[unify_unifier] >>
    qabbrev_tac `dx = decode_utype o_f sx` >> simp[combinTheory.o_DEF] >>
    `sx = encode_itype o_f THE o_f dx` by rw[Abbr `dx`] >>
    first_x_assum $ qspecl_then
      [`THE o_f dx`,`TypeCons ARB t`,`TypeCons ARB t'`] mp_tac >>
    pop_assum $ SUBST1_TAC o GSYM >> simp[encode_itype_def] >>
    simp[Once unify_def, combinTheory.o_DEF]
    )
  >- (
    simp[encode_itype_def] >>
    simp[Once unify_def, SimpRHS] >> CASE_TAC >> pop_assum mp_tac >>
    Cases_on `ts1` >> Cases_on `ts2` >> simp[encode_itype_def, Once unify_def]
    >- (
      rw[Abbr `es`] >>
      simp[o_f_o_f, combinTheory.o_DEF, decode_encode, SF ETA_ss]
      ) >>
    rw[] >> gvs[encode_itype_def] >>
    first_x_assum $ qspecl_then [`s'`,`h`,`h'`] mp_tac >> simp[] >> rw[] >>
    `wfs sx` by metis_tac[unify_unifier] >>
    qabbrev_tac `dx = decode_utype o_f sx` >> simp[combinTheory.o_DEF] >>
    `sx = encode_itype o_f THE o_f dx` by rw[Abbr `dx`] >>
    first_x_assum $ qspecl_then [`THE o_f dx`,`Tuple t`,`Tuple t'`] mp_tac >>
    pop_assum $ SUBST1_TAC o GSYM >> simp[encode_itype_def] >>
    simp[Once unify_def, combinTheory.o_DEF]
    )
  >- (
    simp[encode_itype_def] >>
    simp[Once unify_def, SimpRHS] >> CASE_TAC >> pop_assum mp_tac >>
    simp[Once unify_def] >> rw[] >> gvs[encode_itype_def] >>
    first_x_assum $ qspecl_then [`s'`,`t11`,`t21`] mp_tac >> simp[] >> rw[] >>
    `wfs sx` by metis_tac[unify_unifier] >>
    qabbrev_tac `dx = decode_utype o_f sx` >> simp[combinTheory.o_DEF] >>
    `sx = encode_itype o_f THE o_f dx` by rw[Abbr `dx`] >>
    first_x_assum $ qspecl_then [`THE o_f dx`,`t12`,`t22`] mp_tac >>
    pop_assum $ SUBST1_TAC o GSYM >> simp[] >>
    simp[Once unify_def, combinTheory.o_DEF]
    )
  >- (
    simp[encode_itype_def] >>
    simp[Once unify_def, SimpRHS] >>
    qmatch_goalsub_abbrev_tac `unify es e1 e2` >> CASE_TAC >>
    qsuff_tac `∃s. x = encode_itype o_f s`
    >- (strip_tac >> rw[GSYM fmap_EQ_THM, decode_encode]) >>
    pop_assum mp_tac >> simp[Once unify_def] >>
    Cases_on `walk es e1` >> Cases_on `walk es e2` >> gvs[]
    >- (
      unabbrev_all_tac >> rw[]
      >- (irule_at Any EQ_REFL) >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (
      unabbrev_all_tac >> rw[] >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (
      unabbrev_all_tac >> rw[] >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (
      unabbrev_all_tac >> rw[] >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (
      rw[] >> gvs[] >>
      qmatch_assum_rename_tac `walk es e1 = Pair t1a t1d` >>
      qmatch_assum_rename_tac `walk es e2 = Pair t2a t2d` >>
      `Pair t1a t1d = encode_itype (pure_walk s' ta)` by
        metis_tac[encode_walk,pure_wfs_def] >>
      `Pair t2a t2d = encode_itype (pure_walk s' tb)` by
        metis_tac[encode_walk,pure_wfs_def] >>
      `wfs sx` by metis_tac[unify_unifier] >>
      `∀c1 c2.
        ((t1a = Const c1 ∧ t2a = Const c2) ∨
         (t2d = Const c1 ∧ t2d = Const c2)) ⇒ c1 = c2` by (
          rw[] >> ntac 2 $ qpat_x_assum `unify _ _ _ = _` mp_tac >>
          simp[Once unify_def] >> strip_tac >> simp[Once unify_def]) >>
      pop_assum mp_tac >> simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
      qspecl_then [`pure_walk s' ta`,`t1a`,`t1d`] mp_tac encode_pair_cases >>
      qspecl_then [`pure_walk s' tb`,`t2a`,`t2d`] mp_tac encode_pair_cases >>
      simp[] >> strip_tac >> strip_tac >> gvs[] >>
      rpt $ qpat_x_assum `Pair _ _ = _` $ assume_tac o GSYM
      >- (
        last_x_assum $
          qspecl_then[`s'`,`TypeCons ARB ts'`,`TypeCons ARB ts`] mp_tac >>
        simp[] >> CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      >- (
        last_x_assum $
          qspecl_then[`s'`,`Tuple ts'`,`Tuple ts`] mp_tac >>
        simp[] >> CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      >- (
        last_x_assum $
          qspecl_then[`s'`,`Function it1' it2'`,`Function it1 it2`] mp_tac >>
        simp[encode_itype_def] >>
        CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      >- (
        last_x_assum $
          qspecl_then[`s'`,`Array t'`,`Array t`] mp_tac >>
        simp[encode_itype_def] >> CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      >- (
        last_x_assum $
          qspecl_then[`s'`,`M t'`,`M t`] mp_tac >>
        simp[encode_itype_def] >> CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      )
    >- (
      unabbrev_all_tac >> rw[] >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (unabbrev_all_tac >> rw[] >> irule_at Any EQ_REFL)
    )
  >- (
    simp[encode_itype_def] >>
    simp[Once unify_def, SimpRHS] >>
    qmatch_goalsub_abbrev_tac `unify es e1 e2` >> CASE_TAC >>
    qsuff_tac `∃s. x = encode_itype o_f s`
    >- (strip_tac >> rw[GSYM fmap_EQ_THM, decode_encode]) >>
    pop_assum mp_tac >> simp[Once unify_def] >>
    Cases_on `walk es e1` >> Cases_on `walk es e2` >> gvs[]
    >- (
      unabbrev_all_tac >> rw[]
      >- (irule_at Any EQ_REFL) >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (
      unabbrev_all_tac >> rw[] >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (
      unabbrev_all_tac >> rw[] >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (
      unabbrev_all_tac >> rw[] >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (
      rw[] >> gvs[] >>
      qmatch_assum_rename_tac `walk es e1 = Pair t1a t1d` >>
      qmatch_assum_rename_tac `walk es e2 = Pair t2a t2d` >>
      `Pair t1a t1d = encode_itype (pure_walk s' ta)` by
        metis_tac[encode_walk,pure_wfs_def] >>
      `Pair t2a t2d = encode_itype (pure_walk s' tb)` by
        metis_tac[encode_walk,pure_wfs_def] >>
      `wfs sx` by metis_tac[unify_unifier] >>
      `∀c1 c2.
        ((t1a = Const c1 ∧ t2a = Const c2) ∨
         (t2d = Const c1 ∧ t2d = Const c2)) ⇒ c1 = c2` by (
          rw[] >> ntac 2 $ qpat_x_assum `unify _ _ _ = _` mp_tac >>
          simp[Once unify_def] >> strip_tac >> simp[Once unify_def]) >>
      pop_assum mp_tac >> simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
      qspecl_then [`pure_walk s' ta`,`t1a`,`t1d`] mp_tac encode_pair_cases >>
      qspecl_then [`pure_walk s' tb`,`t2a`,`t2d`] mp_tac encode_pair_cases >>
      simp[] >> strip_tac >> strip_tac >> gvs[] >>
      rpt $ qpat_x_assum `Pair _ _ = _` $ assume_tac o GSYM
      >- (
        last_x_assum $
          qspecl_then[`s'`,`TypeCons ARB ts'`,`TypeCons ARB ts`] mp_tac >>
        simp[] >> CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      >- (
        last_x_assum $
          qspecl_then[`s'`,`Tuple ts'`,`Tuple ts`] mp_tac >>
        simp[] >> CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      >- (
        last_x_assum $
          qspecl_then[`s'`,`Function it1' it2'`,`Function it1 it2`] mp_tac >>
        simp[encode_itype_def] >>
        CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      >- (
        last_x_assum $
          qspecl_then[`s'`,`Array t'`,`Array t`] mp_tac >>
        simp[encode_itype_def] >> CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      >- (
        last_x_assum $
          qspecl_then[`s'`,`M t'`,`M t`] mp_tac >>
        simp[encode_itype_def] >> CASE_TAC >> simp[] >> metis_tac[o_f_o_f]
        )
      )
    >- (
      unabbrev_all_tac >> rw[] >>
      mp_tac encode_walk >> simp[pure_wfs_def] >>
      disch_then imp_res_tac >> gvs[] >> gvs[pure_walk_def] >>
      qmatch_goalsub_abbrev_tac ` _ m |+ (k,v)` >>
      qmatch_asmsub_abbrev_tac `encode_itype foo = v` >>
      qexists_tac `m |+ (k,foo)` >> rw[]
      )
    >- (unabbrev_all_tac >> rw[] >> irule_at Any EQ_REFL)
    )
QED

Theorem encode_unify:
  ∀s t1 t2 s' t1' t2'.
    s = encode_itype o_f s' ∧
    t1 = encode_itype t1' ∧
    t2 = encode_itype t2' ∧
    pure_wfs s'
  ⇒ unify s t1 t2 = OPTION_MAP ((o_f) encode_itype) (pure_unify s' t1' t2')
Proof
  metis_tac[encode_unify_lemma]
QED

Theorem encode_unify_alt:
  ∀s t1 t2. pure_wfs s ⇒
    unify (encode_itype o_f s) (encode_itype t1) (encode_itype t2) =
    OPTION_MAP ((o_f) encode_itype) (pure_unify s t1 t2)
Proof
  metis_tac[encode_unify_lemma]
QED

Theorem wfs_unify:
  ∀s t1 t2 s'. wfs s ∧ unify s t1 t2 = SOME s' ⇒ wfs s'
Proof
  metis_tac[unify_unifier]
QED

Theorem pure_unifyl:
  ∀s l1 l2.
    pure_wfs s ⇒
      pure_unifyl s l1 l2 =
        OPTION_MAP ((o_f) (THE o decode_utype)) $
          unify (encode_itype o_f s) (encode_itypes l1) (encode_itypes l2)
Proof
  Induct_on `l1` >> Cases_on `l2` >> rw[pure_unifyl_def, encode_itype_def] >>
  imp_res_tac pure_wfs_def >>
  gvs[OPTION_MAP_CASE, combinTheory.o_DEF, decode_encode]
  >- rw[Once unify_def] >- rw[Once unify_def] >>
  rw[Once unify_def] >> rw[pure_unify_def, combinTheory.o_DEF] >>
  simp[OPTION_MAP_CASE, combinTheory.o_DEF] >>
  CASE_TAC >> simp[] >>
  imp_res_tac encode_unify_alt >> gvs[combinTheory.o_DEF, decode_encode] >>
  last_x_assum irule >> gvs[pure_wfs_def, pure_unify_def] >>
  irule wfs_unify >> goal_assum drule >>
  irule_at Any EQ_TRANS >> pop_assum $ irule_at Any >> simp[PULL_EXISTS] >>
  goal_assum drule >> simp[]
QED

Theorem pure_unify:
  ∀t1 t2 s.
    pure_wfs s ⇒
    pure_unify s t1 t2 =
      case (pure_walk s t1, pure_walk s t2) of
      | (CVar v1, CVar v2) =>
          SOME (if v1 = v2 then s else s |+ (v1, CVar v2))
      | (CVar v1, t2) => pure_ext_s_check s v1 t2
      | (t1, CVar v2) => pure_ext_s_check s v2 t1
      | (TypeCons c1 ts1, TypeCons c2 ts2) =>
          if c1 = c2 then pure_unifyl s ts1 ts2 else NONE
      | (Tuple ts1, Tuple ts2) => pure_unifyl s ts1 ts2
      | (Function t11 t12, Function t21 t22) =>
          pure_unifyl s [t11;t12] [t21;t22]
      | (Array t1, Array t2) => pure_unify s t1 t2
      | (M t1, M t2) => pure_unify s t1 t2
      | (DBVar db1, DBVar db2) => if db1 = db2 then SOME s else NONE
      | (PrimTy pty1, PrimTy pty2) => if pty1 = pty2 then SOME s else NONE
      | (Exception, Exception) => SOME s
      | (t1, t2) => NONE
Proof
  rw[pure_unify_def] >> imp_res_tac pure_wfs_def >>
  rw [Once unify_def, pure_walk_def] >>
  Cases_on `t1` >> Cases_on `t2` >>
  rw[encode_itype_def, decode_utype_def, option_map_case, option_bind_case,
     combinTheory.o_DEF, decode_encode, encode_vwalk, pure_unifyl, pure_oc_lemma]
  >- (
    Cases_on `pure_vwalk s n'` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- (
    Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- (
    Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- (
    simp[Once unify_def] >>
    Cases_on `pure_vwalk s n'` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- (
    simp[Once unify_def] >>
    Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- (
    simp[Once unify_def, SimpRHS] >> simp[Once unify_def, option_bind_case] >>
    CASE_TAC >> drule_all wfs_unify >> strip_tac >>
    simp[Once unify_def, SimpRHS, option_bind_case] >>
    CASE_TAC >> drule_all wfs_unify >> strip_tac >> simp[Once unify_def]
    )
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- (
    ntac 2 $ simp[Once unify_def, option_bind_case] >>
    Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[]
    >- (
      simp[Once unify_def, option_bind_case] >>
      CASE_TAC >> drule_all wfs_unify >> strip_tac >>
      simp[Once unify_def, SimpRHS, option_bind_case] >>
      CASE_TAC >> drule_all wfs_unify >> strip_tac >> simp[Once unify_def]
      ) >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- (
    simp[Once unify_def] >>
    Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- simp[Once unify_def]
  >- (
    simp[Once unify_def] >>
    Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- (
    simp[Once unify_def] >>
    Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- (
    simp[Once unify_def] >>
    Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- (
    simp[Once unify_def] >>
    Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- (
    simp[Once unify_def] >>
    Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- (
    simp[Once unify_def] >>
    Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- (
    simp[Once unify_def] >>
    Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
    simp[Once unify_def, option_bind_case] >>
    simp[encode_itype_def] >> rw[]
    >- (
      simp[Once unify_def, option_bind_case] >>
      CASE_TAC >> drule_all wfs_unify >> strip_tac >>
      simp[Once unify_def, SimpRHS, option_bind_case] >>
      CASE_TAC >> drule_all wfs_unify >> strip_tac >> simp[Once unify_def]
      ) >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- (
    simp[Once unify_def] >>
    Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- (
    simp[Once unify_def] >>
    Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    ) >>
  Cases_on `pure_vwalk s n` >> gvs[decode_encode] >>
  simp[encode_itype_def] >> rw[]
  >- (
    Cases_on `pure_vwalk s n'` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- (
    Cases_on `pure_vwalk s n'` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- (
    Cases_on `pure_vwalk s n'` >> gvs[decode_encode] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- (
    Cases_on `pure_vwalk s n'` >> gvs[decode_encode] >>
    simp[Once unify_def] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode, pure_oc_lemma]
    )
  >- (
    Cases_on `pure_vwalk s n'` >> gvs[decode_encode] >>
    simp[Once unify_def] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode, pure_oc_lemma]
    )
  >- (
    Cases_on `pure_vwalk s n'` >> gvs[decode_encode] >>
    ntac 2 $ simp[Once unify_def, option_bind_case] >>
    simp[encode_itype_def] >> rw[]
    >- (
      simp[Once unify_def, option_bind_case] >>
      CASE_TAC >> drule_all wfs_unify >> strip_tac >>
      simp[Once unify_def, SimpRHS, option_bind_case] >>
      CASE_TAC >> drule_all wfs_unify >> strip_tac >> simp[Once unify_def]
      ) >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode]
    )
  >- (
    Cases_on `pure_vwalk s n'` >> gvs[decode_encode] >>
    simp[Once unify_def] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode, pure_oc_lemma]
    )
  >- (
    Cases_on `pure_vwalk s n'` >> gvs[decode_encode] >>
    simp[Once unify_def] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode, pure_oc_lemma]
    )
  >- (
    Cases_on `pure_vwalk s n'` >> gvs[decode_encode] >>
    simp[Once unify_def] >>
    simp[encode_itype_def] >> rw[] >>
    simp[pure_ext_s_check, Once pure_oc, pure_walk, decode_utype_def, pure_oc_def] >>
    gvs[combinTheory.o_DEF, decode_encode, pure_oc_lemma]
    )
QED

Theorem pure_unify_ind:
  ∀P0 P1.
    (∀s t1 t2.
      (∀ts1 ts2 c1 c2.
        pure_walk s t1 = TypeCons c1 ts1 ∧
        pure_walk s t2 = TypeCons c2 ts2
       ⇒ P1 s ts1 ts2)
     ⇒ P0 s t1 t2) ∧
    (∀s t1 t2.
      (∀ts1 ts2.
        pure_walk s t1 = Tuple ts1 ∧
        pure_walk s t2 = Tuple ts2
       ⇒ P1 s ts1 ts2)
     ⇒ P0 s t1 t2) ∧
    (∀s t1 t2.
      (∀t11 t12 t21 t22.
        pure_walk s t1 = Function t11 t12 ∧
        pure_walk s t2 = Function t21 t22
       ⇒ P1 s [t11;t12] [t21;t22])
     ⇒ P0 s t1 t2) ∧
    (∀s t1 t2.
      (∀ta tb.
        pure_walk s t1 = Array ta ∧
        pure_walk s t2 = Array tb
       ⇒ P0 s ta tb)
     ⇒ P0 s t1 t2) ∧
    (∀s t1 t2.
      (∀ta tb.
        pure_walk s t1 = M ta ∧
        pure_walk s t2 = M tb
       ⇒ P0 s ta tb)
     ⇒ P0 s t1 t2) ∧
    (∀s ts1 ts2.
      (∀t1 ts1' t2 ts2' s'.
        ts1 = t1::ts1' ∧ ts2 = t2::ts2' ∧
        pure_unify s t1 t2 = SOME s'
       ⇒ P1 s' ts1' ts2') ∧
      (∀t1 ts1' t2 ts2'.
        ts1 = t1::ts1' ∧ ts2 = t2::ts2'
       ⇒ P0 s t1 t2)
     ⇒ P1 s ts1 ts2)
  ⇒ (∀s t1 t2. pure_wfs s ⇒ P0 s t1 t2) ∧
    (∀s ts1 ts2. pure_wfs s ⇒ P1 s ts1 ts2)
Proof
  rpt gen_tac >> strip_tac >>
  (fn qt => qspec_then qt strip_assume_tac unify_ind)
    `λs t1 t2.
      (∀us u1 u2.
        wfs s ∧ s = encode_itype o_f us ∧
        t1 = encode_itype u1 ∧ t2 = encode_itype u2
       ⇒ P0 us u1 u2) ∧
      (∀us tag us1 us2 c.
        wfs s ∧ s = encode_itype o_f us ∧
        (c = uTypeCons tag ∨ c = uTuple) ∧
        t1 = Pair (Const c) (encode_itypes us1) ∧
        t2 = Pair (Const c) (encode_itypes us2)
       ⇒ P1 us us1 us2) ∧
      (∀us u11 u12 u21 u22.
        wfs s ∧ s = encode_itype o_f us ∧
        t1 = Pair (Const uFunction) (Pair (encode_itype u11) (encode_itype u12)) ∧
        t2 = Pair (Const uFunction) (Pair (encode_itype u21) (encode_itype u22))
       ⇒ P1 us [u11;u12] [u21;u22]) ∧
      (∀us u1 u2 c.
        wfs s ∧ s = encode_itype o_f us ∧
        (c = uArray ∨ c = uM) ∧
        t1 = Pair (Const c) (encode_itype u1) ∧
        t2 = Pair (Const c) (encode_itype u2)
       ⇒ P0 us u1 u2) ∧

      (∀us v1 u1 v2 u2.
        wfs s ∧ s = encode_itype o_f us ∧
        t1 = Pair (encode_itype v1) (encode_itypes u1) ∧
        t2 = Pair (encode_itype v2) (encode_itypes u2)
       ⇒ P0 us v1 v2 ∧
         (∀usx.
            unify s (encode_itype v1) (encode_itype v2) =
              SOME (encode_itype o_f usx)
          ⇒ P1 usx u1 u2)) ∧
      (∀us v1 u1 v2 u2.
        wfs s ∧ s = encode_itype o_f us ∧
        t1 = Pair (encode_itype v1) (encode_itype u1) ∧
        t2 = Pair (encode_itype v2) (encode_itype u2)
       ⇒ P0 us v1 v2 ∧
         (∀usx.
            unify s (encode_itype v1) (encode_itype v2) =
              SOME (encode_itype o_f usx)
          ⇒ P1 usx [u1] [u2]))` >>
  qmatch_assum_abbrev_tac `P ⇒ Q` >> qsuff_tac `P`
  >- (
    strip_tac >> `Q` by res_tac >> pop_assum mp_tac >>
    unabbrev_all_tac >> rpt $ pop_assum kall_tac >>
    CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >> rw[] >>
    gvs[encode_itype_injective, encode_itype_o_f_injective, pure_wfs_def]
    ) >>
  qpat_x_assum `P ⇒ Q` kall_tac >> unabbrev_all_tac >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (rw[] >> fs[encode_walk, pure_wfs_def, encode_itype_def])
  >- (
    rw[] >> first_x_assum irule >> rw[] >>
    fs[encode_itype_def, encode_itype_injective, encode_itype_o_f_injective] >>
    first_x_assum irule >> simp[pure_wfs_def, encode_unify_alt]
    )
  >- (
    rw[] >> first_x_assum irule >> rw[] >>
    fs[encode_itype_def, encode_itype_injective, encode_itype_o_f_injective] >>
    first_x_assum irule >> simp[pure_wfs_def, encode_unify_alt]
    )
  >- (rpt gen_tac >> strip_tac >> rw[])
  >- (
    rw[] >> first_x_assum match_mp_tac >> imp_res_tac wfs_unify >>
    fs[encode_itype_injective, encode_itype_o_f_injective] >>
    rw[] >> fs[encode_itype_def, encode_itype_injective] >>
    simp[pure_wfs_def, encode_unify_alt]
    )
  >- (
    rw[] >> first_assum irule >> imp_res_tac wfs_unify >>
    fs[encode_itype_injective, encode_itype_o_f_injective]
    )
QED

Definition pure_apply_subst_def[nocompute]:
  pure_apply_subst s t =
    THE $ decode_utype $ subst_APPLY (encode_itype o_f s) (encode_itype t)
End

Theorem pure_apply_subst_wf:
  (∀t s. decode_utype $
            subst_APPLY (encode_itype o_f s) (encode_itype t) ≠ NONE) ∧
  (∀ts s. decode_utypes $
            subst_APPLY (encode_itype o_f s) (encode_itypes ts) ≠ NONE)
Proof
  Induct >> rw[encode_itype_def, decode_utype_def, FLOOKUP_o_f] >>
  CASE_TAC >> simp[decode_encode, decode_utype_def]
QED

Theorem pure_apply_subst:
  (∀s n.
    pure_apply_subst s (CVar n) =
      case FLOOKUP s n of | NONE => CVar n | SOME t => t) ∧
  (∀s c ts.
    pure_apply_subst s (TypeCons c ts) = TypeCons c (MAP (pure_apply_subst s) ts)) ∧
  (∀s ts.
    pure_apply_subst s (Tuple ts) = Tuple (MAP (pure_apply_subst s) ts)) ∧
  (∀s t1 t2.
    pure_apply_subst s (Function t1 t2) =
      Function (pure_apply_subst s t1) (pure_apply_subst s t2)) ∧
  (∀s t.
    pure_apply_subst s (Array t) = Array (pure_apply_subst s t)) ∧
  (∀s t.
    pure_apply_subst s (M t) = M (pure_apply_subst s t)) ∧
  (∀s n. pure_apply_subst s (DBVar n) = DBVar n) ∧
  (∀s p. pure_apply_subst s (PrimTy p) = PrimTy p) ∧
  (∀s. pure_apply_subst s Exception = Exception)
Proof
  rw[pure_apply_subst_def, encode_itype_def, FLOOKUP_o_f, decode_utype_def] >>
  every_case_tac >> rw[decode_encode, decode_utype_def]
  >- (
    Induct_on `ts` >> rw[encode_itype_def, decode_utype_def] >>
    rw[pure_apply_subst_def, option_bind_case] >>
    TOP_CASE_TAC >> gvs[pure_apply_subst_wf] >>
    TOP_CASE_TAC >> gvs[pure_apply_subst_wf]
    )
  >- (
    Induct_on `ts` >> rw[encode_itype_def, decode_utype_def] >>
    rw[pure_apply_subst_def, option_bind_case] >>
    TOP_CASE_TAC >> gvs[pure_apply_subst_wf] >>
    TOP_CASE_TAC >> gvs[pure_apply_subst_wf]
    )
  >- (
    rw[option_bind_case] >>
    TOP_CASE_TAC >> gvs[pure_apply_subst_wf] >>
    TOP_CASE_TAC >> gvs[pure_apply_subst_wf]
    )
  >- (
    rw[option_bind_case] >>
    qmatch_goalsub_abbrev_tac `decode_utype enc` >>
    Cases_on `decode_utype enc` >> unabbrev_all_tac >> gvs[pure_apply_subst_wf]
    )
  >- (
    rw[option_bind_case] >>
    qmatch_goalsub_abbrev_tac `decode_utype enc` >>
    Cases_on `decode_utype enc` >> unabbrev_all_tac >> gvs[pure_apply_subst_wf]
    )
QED

Theorem walkstar_strongind:
  ∀P.
    (∀s t.
      (∀t1 t2. wfs s ∧ walk s t = Pair t1 t2 ⇒ P s t2) ∧
      (∀t1 t2. wfs s ∧ walk s t = Pair t1 t2 ⇒ P s t1)
     ⇒ P s t)
  ⇒ ∀s t. wfs s ⇒ P s t
Proof
  ntac 5 strip_tac >>
  qid_spec_tac `t` >>
  ho_match_mp_tac walkstar_ind >> rw[]
QED

Definition pure_walkstar_def[nocompute]:
  pure_walkstar s t =
    THE o decode_utype $ walkstar (encode_itype o_f s) (encode_itype t)
End

Theorem pure_walkstar_ind:
 ∀s. pure_wfs s ⇒
  ∀P.
    (∀t.
      (∀c ts a. pure_walk s t = TypeCons c ts ∧ MEM a ts ⇒ P a) ∧
      (∀ts a. pure_walk s t = Tuple ts ∧ MEM a ts ⇒ P a) ∧
      (∀t1 t2. pure_walk s t = Function t1 t2 ⇒ P t1 ∧ P t2) ∧
      (∀t'. pure_walk s t = Array t' ⇒ P t') ∧
      (∀t'. pure_walk s t = M t' ⇒ P t')
     ⇒ P t)
  ⇒ ∀t. P t
Proof
  rw[] >> imp_res_tac pure_wfs_def >>
  imp_res_tac $ GEN_ALL $ DISCH_ALL walkstar_ind >>
  qsuff_tac `(λx.
    (∀u. x = encode_itype u ⇒ P u) ∧
    (∀c us. x = Pair (Const (uTypeCons c)) (encode_itypes us) ⇒ EVERY P us) ∧
    (∀us. x = Pair (Const uTuple) (encode_itypes us) ⇒ EVERY P us) ∧
    (∀u1 u2. x = Pair (Const uFunction)
                  (Pair (encode_itype u1) (encode_itype u2)) ⇒ P u1 ∧ P u2) ∧
    (∀u. x = Pair (Const uArray) (encode_itype u) ⇒ P u) ∧
    (∀u. x = Pair (Const uM) (encode_itype u) ⇒ P u) ∧
    (∀u1 u2. x = Pair (encode_itype u1) (encode_itype u2) ⇒ P u1 ∧ P u2) ∧
    (∀u us. x = Pair (encode_itype u) (encode_itypes us) ⇒ EVERY P (u::us)))
      (encode_itype t)`
  >- simp[decode_encode] >>
  pop_assum irule >> BETA_TAC >> rw[decode_encode]
  >- (
    rfs[encode_walk] >> first_x_assum irule >> rw[] >>
    gvs[encode_walk, encode_itype_def, encode_itype_injective, EVERY_MEM] >>
    Cases_on `ts` >> gvs[encode_itype_def, encode_itype_injective, EVERY_MEM]
    )
  >- (Cases_on `us` >> fs[encode_itype_def, encode_itype_injective])
  >- (Cases_on `us` >> fs[encode_itype_def, encode_itype_injective]) >>
  rfs[encode_walk, encode_itype_injective] >>
  Cases_on `us` >> fs[encode_itype_def, encode_itype_injective]
QED

Theorem pure_walkstar_wf_lemma:
  ∀s. pure_wfs s ⇒
    ∀t. decode_utype $ walkstar (encode_itype o_f s) (encode_itype t) ≠ NONE
Proof
  strip_tac >> strip_tac >>
  imp_res_tac pure_walkstar_ind >> pop_assum ho_match_mp_tac >> rw[] >>
  imp_res_tac pure_wfs_def >> simp[Once walkstar_def, encode_walk] >>
  Cases_on `pure_walk s t` >> gvs[encode_itype_def, decode_utype_def] >>
  pop_assum kall_tac >> Induct_on `l` >> rw[encode_itype_def, decode_utype_def]
QED

Theorem pure_walkstar_wf:
  (∀t s. pure_wfs s ⇒
    decode_utype $
      walkstar (encode_itype o_f s) (encode_itype t) ≠ NONE) ∧
  (∀ts s. pure_wfs s ⇒
    decode_utypes $
      walkstar (encode_itype o_f s) (encode_itypes ts) ≠ NONE)
Proof
  conj_tac >- simp[pure_walkstar_wf_lemma] >>
  Induct >> rw[] >> imp_res_tac pure_wfs_def >>
  simp[encode_itype_def, decode_utype_def, Once walkstar_def] >>
  irule pure_walkstar_wf_lemma >> simp[]
QED

Theorem pure_walkstar_ts_lemma:
  ∀l s. pure_wfs s ⇒
    decode_utypes ((encode_itype o_f s) ◁ encode_itypes l) =
    SOME $ MAP (pure_walkstar s) l
Proof
  Induct >> rw[encode_itype_def] >> imp_res_tac pure_wfs_def >>
  gvs[Once apply_ts_thm, decode_utype_def, pure_walkstar_def] >>
  assume_tac pure_walkstar_wf >> gvs[] >>
  Cases_on `decode_utype (encode_itype o_f s ◁ encode_itype h)` >> gvs[]
QED

Theorem pure_walkstar_ts_lemma_alt:
  ∀l s. pure_wfs s ⇒
    MAP (pure_walkstar s) l =
    THE $ decode_utypes ((encode_itype o_f s) ◁ encode_itypes l)
Proof
  rw[] >> DEP_REWRITE_TAC[pure_walkstar_ts_lemma] >> simp[]
QED

Theorem pure_walkstar:
  ∀s. pure_wfs s ⇒
    ∀t. pure_walkstar s t =
        case pure_walk s t of
        | CVar v => CVar v
        | TypeCons c ts => TypeCons c (MAP (pure_walkstar s) ts)
        | Tuple ts => Tuple (MAP (pure_walkstar s) ts)
        | Function t1 t2 =>
            Function (pure_walkstar s t1) (pure_walkstar s t2)
        | Array t => Array (pure_walkstar s t)
        | M t => M (pure_walkstar s t)
        | t => t
Proof
  rw[pure_walkstar_def] >> imp_res_tac pure_wfs_def >>
  rw[Once walkstar_def, pure_walk_def] >>
  Cases_on `t` >>
  gvs[encode_itype_def, decode_utype_def, decode_encode, encode_vwalk] >>
  gvs[pure_walkstar_ts_lemma, option_bind_case] >>
  assume_tac pure_walkstar_wf >> gvs[]
  >- (CASE_TAC >> CASE_TAC >> gvs[])
  >- (
    Cases_on `decode_utype (encode_itype o_f s ◁ encode_itype i)` >> gvs[]
    )
  >- (
    Cases_on `decode_utype (encode_itype o_f s ◁ encode_itype i)` >> gvs[]
    ) >>
  Cases_on `pure_vwalk s n` >>
  gvs[encode_itype_def, decode_utype_def, pure_walkstar_ts_lemma, option_bind_case]
  >- (CASE_TAC >> CASE_TAC >> gvs[])
  >- (
    Cases_on `decode_utype (encode_itype o_f s ◁ encode_itype i)` >> gvs[]
    )
  >- (
    Cases_on `decode_utype (encode_itype o_f s ◁ encode_itype i)` >> gvs[]
    )
QED

Theorem pure_walkstar_alt:
  ∀s. pure_wfs s ⇒
    (∀v. pure_walkstar s (DBVar v) = DBVar v) ∧
    (∀pty. pure_walkstar s (PrimTy pty) = PrimTy pty) ∧
    (pure_walkstar s Exception = Exception) ∧
    (∀id ts. pure_walkstar s (TypeCons id ts) =
              TypeCons id (MAP (pure_walkstar s) ts)) ∧
    (∀ts. pure_walkstar s (Tuple ts) = Tuple (MAP (pure_walkstar s) ts)) ∧
    (∀t1 t2. pure_walkstar s (Function t1 t2) =
              Function (pure_walkstar s t1) (pure_walkstar s t2)) ∧
    (∀t. pure_walkstar s (Array t) = Array (pure_walkstar s t)) ∧
    (∀t. pure_walkstar s (M t) = M (pure_walkstar s t)) ∧
    (∀v. pure_walkstar s (CVar v) =
      case FLOOKUP s v of
      | NONE => CVar v
      | SOME t => pure_walkstar s t)
Proof
  rw[] >> simp[Once pure_walkstar, Once pure_walk] >>
  simp[Once pure_vwalk] >>
  CASE_TAC >> gvs[] >> CASE_TAC >> gvs[] >>
  simp[SimpRHS, Once pure_walkstar, Once pure_walk]
QED

Theorem encode_walkstar:
  ∀s t. pure_wfs s ⇒
    walkstar (encode_itype o_f s) (encode_itype t) =
    encode_itype (pure_walkstar s t)
Proof
  rw[] >> imp_res_tac pure_walkstar_ind >>
  qid_spec_tac `t` >> pop_assum ho_match_mp_tac >> rw[] >>
  rw[Once pure_walkstar] >> imp_res_tac pure_wfs_def >>
  rw[Once walkstar_def, Once encode_walk] >>
  Cases_on `pure_walk s t` >> rw[encode_itype_def] >>
  qpat_x_assum `pure_walk _ _ = _` kall_tac >>
  Induct_on `l` >> rw[encode_itype_def]
QED

Definition pure_collapse_def[nocompute]:
  pure_collapse s = (THE o decode_utype) o_f collapse (encode_itype o_f s)
End

Theorem pure_collapse:
  ∀s. pure_collapse s = FUN_FMAP (λv. pure_walkstar s (CVar v)) (FDOM s)
Proof
  rw[collapse_def, pure_collapse_def, pure_walkstar_def,
     encode_itype_def, walkstar_def] >>
  rw[GSYM fmap_EQ_THM, FUN_FMAP_DEF]
QED

Theorem pure_unify_unifier:
   pure_wfs s ∧
   pure_unify s t1 t2 = SOME sx
   ⇒ pure_wfs sx ∧ s ⊑ sx ∧ pure_walkstar sx t1 = pure_walkstar sx t2
Proof
  simp[pure_unify_def] >> strip_tac >>
  qmatch_assum_abbrev_tac `unify us ut1 ut2 = SOME uz` >>
  qspecl_then [`us`,`ut1`,`ut2`,`s`,`t1`,`t2`] mp_tac encode_unify >> simp[] >>
  disch_then $ qx_choose_then `w` assume_tac >> gvs[] >>
  imp_res_tac pure_wfs_def >> gvs[] >> imp_res_tac unify_unifier >> gvs[] >>
  unabbrev_all_tac >> simp[decode_encode, combinTheory.o_DEF] >>
  simp[pure_wfs_def, pure_walkstar_def] >> gvs[SUBMAP_DEF] >>
  metis_tac[encode_itype_injective, o_f_FAPPLY]
QED

Theorem pure_unify_strongind:
  ∀P0 P1.
    (∀s t1 t2.
      pure_wfs s ∧
      (∀ts1 ts2 c1 c2.
        pure_walk s t1 = TypeCons c1 ts1 ∧
        pure_walk s t2 = TypeCons c2 ts2
       ⇒ P1 s ts1 ts2)
     ⇒ P0 s t1 t2) ∧
    (∀s t1 t2.
      pure_wfs s ∧
      (∀ts1 ts2.
        pure_walk s t1 = Tuple ts1 ∧
        pure_walk s t2 = Tuple ts2
       ⇒ P1 s ts1 ts2)
     ⇒ P0 s t1 t2) ∧
    (∀s t1 t2.
      pure_wfs s ∧
      (∀t11 t12 t21 t22.
        pure_walk s t1 = Function t11 t12 ∧
        pure_walk s t2 = Function t21 t22
       ⇒ P1 s [t11;t12] [t21;t22])
     ⇒ P0 s t1 t2) ∧
    (∀s t1 t2.
      pure_wfs s ∧
      (∀ta tb.
        pure_walk s t1 = Array ta ∧
        pure_walk s t2 = Array tb
       ⇒ P0 s ta tb)
     ⇒ P0 s t1 t2) ∧
    (∀s t1 t2.
      pure_wfs s ∧
      (∀ta tb.
        pure_walk s t1 = M ta ∧
        pure_walk s t2 = M tb
       ⇒ P0 s ta tb)
     ⇒ P0 s t1 t2) ∧
    (∀s ts1 ts2.
      pure_wfs s ∧
      (∀t1 ts1' t2 ts2' s'.
        ts1 = t1::ts1' ∧ ts2 = t2::ts2' ∧
        pure_unify s t1 t2 = SOME s'
       ⇒ P1 s' ts1' ts2') ∧
      (∀t1 ts1' t2 ts2'.
        ts1 = t1::ts1' ∧ ts2 = t2::ts2'
       ⇒ P0 s t1 t2)
     ⇒ P1 s ts1 ts2)
  ⇒ (∀s t1 t2. pure_wfs s ⇒ P0 s t1 t2) ∧
    (∀s ts1 ts2. pure_wfs s ⇒ P1 s ts1 ts2)
Proof
  ntac 3 strip_tac >>
  qsuff_tac
    `(∀s t1 t2. pure_wfs s ⇒ pure_wfs s ⇒ P0 s t1 t2) ∧
     (∀s ts1 ts2. pure_wfs s ⇒ pure_wfs s ⇒ P1 s ts1 ts2)`
  >- (rpt $ pop_assum kall_tac >> simp[]) >>
  ho_match_mp_tac pure_unify_ind >> rw[] >>
  Cases_on `ts1` >> Cases_on `ts2` >> fs[] >>
  last_x_assum irule >> rw[] >>
  metis_tac[pure_unify_unifier]
QED

Theorem pure_walkstar_FEMPTY:
 ∀t. pure_walkstar FEMPTY t = t
Proof
  rw[pure_walkstar_def, decode_encode]
QED

Theorem pure_wfs_SUBMAP:
  ∀s1 s2. pure_wfs s2 ∧ s1 ⊑ s2 ⇒ pure_wfs s1
Proof
  rw[pure_wfs_def] >>
  irule wfs_SUBMAP >> goal_assum $ drule >> gvs[SUBMAP_DEF]
QED

Theorem pure_walkstar_SUBMAP:
  ∀s1 s2 t. s1 ⊑ s2 ∧ pure_wfs s2 ⇒
  pure_walkstar s2 t = pure_walkstar s2 (pure_walkstar s1 t)
Proof
  rw[pure_walkstar_def] >> imp_res_tac pure_wfs_def >>
  drule_all pure_wfs_SUBMAP >> strip_tac >>
  `encode_itype o_f s1 ⊑ encode_itype o_f s2` by gvs[SUBMAP_DEF] >>
  drule_all walkstar_SUBMAP >> disch_then $ simp o single o Once >>
  rw[encode_walkstar, decode_encode]
QED

Definition pure_vR_def[nocompute]:
  pure_vR s = vR (encode_itype o_f s)
End

Theorem pure_vR:
  ∀s x y. pure_vR s y x = case FLOOKUP s x of SOME t => y ∈ pure_vars t | _ => F
Proof
  rw[pure_vR_def, vR_def, FLOOKUP_o_f] >>
  CASE_TAC >> gvs[pure_vars_def]
QED

Theorem pure_wfs:
  ∀s. pure_wfs s = WF (pure_vR s)
Proof
  rw[wfs_def, pure_wfs_def, pure_vR, WF_DEF, vR_def, FLOOKUP_o_f, pure_vars_def] >>
  eq_tac >> rw[] >> res_tac >>
  goal_assum drule >> simp[] >> CASE_TAC >> gvs[]
QED

Definition pure_rangevars_def[nocompute]:
  pure_rangevars s = rangevars (encode_itype o_f s)
End

Theorem pure_rangevars:
  ∀s. pure_rangevars s = BIGUNION (IMAGE pure_vars $ FRANGE s)
Proof
  rw[pure_rangevars_def, rangevars_def, EXTENSION] >>
  eq_tac >> rw[pure_vars_def, FRANGE_DEF, o_f_FAPPLY] >>
  metis_tac[o_f_FAPPLY]
QED

Theorem pure_vars:
  (∀n. pure_vars (DBVar n) = {}) ∧
  (∀p. pure_vars (PrimTy p) = {}) ∧
  (pure_vars (Exception) = {}) ∧
  (∀c ts. pure_vars (TypeCons c ts) = BIGUNION (set $ MAP pure_vars ts)) ∧
  (∀ts. pure_vars (Tuple ts) = BIGUNION (set $ MAP pure_vars ts)) ∧
  (∀t1 t2. pure_vars (Function t1 t2) = pure_vars t1 ∪ pure_vars t2) ∧
  (∀t. pure_vars (Array t) = pure_vars t) ∧
  (∀t. pure_vars (M t) = pure_vars t) ∧
  (∀n. pure_vars (CVar n) = {n})
Proof
  rw[pure_vars_def, encode_itype_def] >>
  Induct_on `ts` >> rw[encode_itype_def, pure_vars_def]
QED

Theorem pure_vwalk_to_var:
  pure_wfs s ⇒ ∀v u. pure_vwalk s v = CVar u ⇒ u ∉ FDOM s
Proof
  rw[pure_wfs_def, pure_vwalk_def] >>
  drule vwalk_to_var >> simp[] >> disch_then irule >>
  qexists_tac `v` >> DEP_REWRITE_TAC[encode_vwalk] >>
  simp[pure_vwalk_def, encode_itype_def, pure_wfs_def]
QED

Theorem pure_walkstar_vars_notin:
  ∀s. pure_wfs s ⇒
    ∀t x. x ∈ pure_vars (pure_walkstar s t) ⇒ x ∉ FDOM s
Proof
  ntac 2 $ strip_tac >>
  imp_res_tac pure_walkstar_ind >> pop_assum ho_match_mp_tac >> gen_tac >>
  imp_res_tac pure_walkstar >> pop_assum $ once_rewrite_tac o single >>
  reverse $ Cases_on `pure_walk s t` >> rw[] >>
  pop_assum mp_tac >> rw[pure_vars, MEM_MAP, PULL_EXISTS] >>
  gvs[GSYM pure_walkstar] >> res_tac >>
  Cases_on `t` >> gvs[pure_walk, pure_vars] >> metis_tac[pure_vwalk_to_var]
QED

Theorem pure_walkstar_vars_in:
  ∀s. pure_wfs s ⇒
    ∀t. pure_vars (pure_walkstar s t) ⊆
          pure_vars t ∪ BIGUNION (FRANGE (pure_vars o_f s))
Proof
  rw[pure_walkstar_def, pure_vars_def] >> imp_res_tac pure_wfs_def >>
  imp_res_tac vars_walkstar >> gvs[SUBSET_DEF] >> rw[] >>
  gvs[combinTheory.o_DEF] >>
  first_x_assum $ qspec_then `encode_itype t` assume_tac >>
  gvs[encode_walkstar, decode_encode, GSYM IMAGE_FRANGE, pure_vars_def]
QED

Theorem pure_walkstar_idempotent:
  ∀s. pure_wfs s ⇒
    ∀t. pure_walkstar s (pure_walkstar s t) = pure_walkstar s t
Proof
  rw[] >> imp_res_tac pure_wfs_def >>
  drule $ GSYM walkstar_idempotent >>
  disch_then $ qspec_then `encode_itype t` assume_tac >>
  gvs[encode_walkstar, decode_encode, encode_itype_injective]
QED

Theorem pure_walkstar_alt_ind:
 ∀s. pure_wfs s ⇒
  ∀P.
    (∀v. P (DBVar v)) ∧ (∀p. P (PrimTy p)) ∧ (P Exception) ∧
    (∀c ts. (∀a. MEM a ts ⇒ P a) ⇒ P (TypeCons c ts)) ∧
    (∀ts. (∀a. MEM a ts ⇒ P a) ⇒ P (Tuple ts)) ∧
    (∀t1 t2. P t1 ∧ P t2 ⇒ P (Function t1 t2)) ∧
    (∀t. P t ⇒ P (Array t)) ∧ (∀t. P t ⇒ P (M t)) ∧
    (∀v. (∀t. FLOOKUP s v = SOME t ⇒ P t) ⇒ P (CVar v))
  ⇒ ∀t. P t
Proof
  gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  imp_res_tac pure_walkstar_ind >>
  pop_assum irule >> rw[] >>
  Cases_on `t` >> gvs[pure_walk] >>
  `∀t. pure_vwalk s n = t ⇒ P t` by (
    rw[] >> Cases_on `pure_vwalk s n` >> gvs[] >>
    drule pure_vwalk_to_var >> disch_then drule >> rw[] >>
    first_x_assum irule >> simp[FLOOKUP_DEF]) >>
  pop_assum mp_tac >> ntac 5 $ pop_assum kall_tac >> rw[] >>
  imp_res_tac pure_vwalk_ind >>
  pop_assum $ qspec_then ` λn. P (pure_vwalk s n) ⇒ P (CVar n)` mp_tac >> simp[] >>
  disch_then irule >> rw[] >> gvs[Once pure_vwalk] >>
  Cases_on `FLOOKUP s v` >> gvs[] >> Cases_on `x` >> gvs[]
QED


(********************* Encoding-independent results ********************)

Theorem pure_unify_apply:
  ∀s1 s2 t1 t2.
    pure_wfs s1 ∧
    pure_unify s1 t1 t2 = SOME s2
  ⇒ pure_walkstar s2 t1 = pure_walkstar s2 t2
Proof
  metis_tac[pure_unify_unifier]
QED

Theorem pure_unify_apply2:
  ∀s1 s2 t1' t2' t1 t2.
    pure_wfs s1 ∧
    pure_unify s1 t1' t2' = SOME s2 ∧
    pure_walkstar s1 t1 = pure_walkstar s1 t2
  ⇒ pure_walkstar s2 t1 = pure_walkstar s2 t2
Proof
  rw[] >>
  `pure_wfs s2 ∧ s1 ⊑ s2` by metis_tac[pure_unify_unifier] >>
  metis_tac[pure_walkstar_SUBMAP]
QED

Theorem pure_unify_wfs:
  ∀s1 t1 t2 s2.
    pure_wfs s1 ∧
    pure_unify s1 t1 t2 = SOME s2
  ⇒ pure_wfs s2
Proof
  metis_tac[pure_unify_unifier]
QED

Theorem finite_pure_rangevars:
  ∀t. FINITE (pure_rangevars t)
Proof
  rw[pure_rangevars, pure_vars_def] >>
  rw[termTheory.FINITE_vars]
QED

Theorem oc_dbvar:
  ∀s uv tvs. pure_wfs s ⇒ ¬pure_oc s (DBVar tvs) uv
Proof
  rw[] >> drule pure_oc >>
  disch_then $ once_rewrite_tac o single >>
  rw[pure_walk]
QED

Theorem oc_unit:
  ∀s uv tc. pure_wfs s ⇒  ¬pure_oc s (Tuple []) uv
Proof
  rw[Once pure_oc] >> simp[pure_walk]
QED

Theorem no_vars_extend_subst_vwalk:
  ∀s. pure_wfs s ⇒
    ∀n s'.
      pure_wfs (s |++ s') ∧
      DISJOINT (FDOM s) (FDOM (FEMPTY |++ s')) ∧
      (∀n'. pure_vwalk s n ≠ CVar n')
    ⇒ pure_vwalk (s |++ s') n = pure_vwalk s n
Proof
  ntac 2 strip_tac >>
  imp_res_tac pure_vwalk_ind >> pop_assum ho_match_mp_tac >> rw[] >>
  pop_assum mp_tac >> imp_res_tac pure_vwalk >>
  ntac 2 $ pop_assum $ once_rewrite_tac o single >> strip_tac >>
  Cases_on `FLOOKUP (s |++ s') n` >> gvs[flookup_fupdate_list]
  >- (every_case_tac >> gvs[]) >>
  pop_assum mp_tac >> CASE_TAC >> rw[] >> gvs[]
  >- (CASE_TAC >> gvs[]) >>
  Cases_on `FLOOKUP s n` >> gvs[] >> irule FALSITY >>
  gvs[FDOM_FUPDATE_LIST, DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
  metis_tac[]
QED

Theorem no_vars_extend_subst:
  ∀s. pure_wfs s ⇒
    ∀t s'.
      pure_wfs (s |++ s') ∧
      DISJOINT (FDOM s) (FDOM (FEMPTY |++ s')) ∧
      pure_vars (pure_walkstar s t) = {}
    ⇒ pure_walkstar (s |++ s') t = pure_walkstar s t
Proof
  ntac 2 $ strip_tac >>
  imp_res_tac pure_walkstar_ind >> pop_assum ho_match_mp_tac >> rw[] >>
  Cases_on `t` >> rw[] >> gvs[pure_walk, pure_walkstar] >>
  pop_assum mp_tac >>
  imp_res_tac pure_walkstar >> ntac 2 $ pop_assum $ once_rewrite_tac o single >>
  simp[pure_walk, pure_vars] >> strip_tac >> gvs[] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF]
  >- (
    rw[MAP_EQ_f] >> first_x_assum irule >> simp[] >>
    gvs[Once EXTENSION, MEM_MAP] >>
    first_x_assum $ irule o iffLR >> goal_assum $ drule_at Any >> simp[]
    )
  >- (
    rw[MAP_EQ_f] >> first_x_assum irule >> simp[] >>
    gvs[Once EXTENSION, MEM_MAP] >>
    first_x_assum $ irule o iffLR >> goal_assum $ drule_at Any >> simp[]
    ) >>
  last_x_assum assume_tac >>
  drule no_vars_extend_subst_vwalk >> disch_then drule >> simp[] >>
  disch_then $ qspec_then `n` mp_tac >> impl_tac
  >- (CCONTR_TAC >> gvs[pure_vars]) >> rw[] >>
  Cases_on `pure_vwalk s n` >> gvs[pure_vars, MAP_MAP_o, combinTheory.o_DEF] >>
  rw[MAP_EQ_f] >> first_x_assum irule >> simp[] >>
  gvs[Once EXTENSION, MEM_MAP] >>
  first_x_assum $ irule o iffLR >> goal_assum $ drule_at Any >> simp[]
QED

(* Theorems about unification for completeness proof *)

Theorem pure_walk_vwalk_id:
  pure_wfs s ⇒
    ∀n. pure_walk s (pure_vwalk s n) = pure_vwalk s n
Proof
  strip_tac >> imp_res_tac pure_vwalk_ind >>
  pop_assum ho_match_mp_tac >> rw[] >>
  Cases_on `FLOOKUP s n` >> simp[pure_walk, Once pure_vwalk] >>
  simp[Once pure_vwalk, SimpRHS] >>
  CASE_TAC >> gvs[] >>
  CASE_TAC >> gvs[] >> gvs[pure_walk]
QED

Theorem pure_walk_walk_id:
  pure_wfs s ⇒
    pure_walk s (pure_walk s h) = pure_walk s h
Proof
  Cases_on `h` >> gvs[pure_walk] >>
  simp[GSYM pure_walk, pure_walk_vwalk_id]
QED

Theorem eqs_pure_unify:
  pure_wfs s ∧ pure_wfs s2 ∧
  pure_walkstar s2 (pure_walkstar s t1) = pure_walkstar s2 (pure_walkstar s t2) ⇒
  ∃sx. pure_unify s t1 t2 = SOME sx
Proof
  rw[pure_unify_def] >> irule $ GEN_ALL eqs_unify >>
  imp_res_tac pure_wfs_def >> simp[] >>
  goal_assum rev_drule >> simp[encode_walkstar]
QED

Theorem encode_walkstar_reverse =
  encode_walkstar |>
    SIMP_RULE (srw_ss()) [pure_walkstar_def, combinTheory.o_DEF] |>
    SPEC_ALL |> UNDISCH|> SYM |> DISCH_ALL |> GEN_ALL;

Theorem pure_unify_mgu:
  ∀s t1 t2 sx s2.
    pure_wfs s ∧ pure_unify s t1 t2 = SOME sx ∧ pure_wfs s2 ∧
    pure_walkstar s2 (pure_walkstar s t1) = pure_walkstar s2 (pure_walkstar s t2)
  ⇒ ∀t. pure_walkstar s2 (pure_walkstar sx t) = pure_walkstar s2 (pure_walkstar s t)
Proof
  rw[] >> drule_all pure_unify_wfs >> strip_tac >>
  gvs[pure_walkstar_def, encode_walkstar_reverse] >>
  AP_TERM_TAC >> AP_TERM_TAC >> irule unify_mgu >>
  imp_res_tac pure_wfs_def >> simp[] >>
  qexistsl_tac [`encode_itype t1`,`encode_itype t2`] >> gvs[encode_unify_alt] >>
  qpat_x_assum `_ = _` mp_tac >> gvs[encode_walkstar, decode_encode]
QED

Theorem pure_walkstar_CVar_props:
  pure_wfs s ⇒
  (uv ∉ FDOM s ⇔ pure_walkstar s (CVar uv) = CVar uv)
Proof
  rw[] >> eq_tac >> rw[]
  >- (
    drule pure_walkstar >> disch_then $ once_rewrite_tac o single >>
    simp[pure_walk, Once pure_vwalk, FLOOKUP_DEF]
    )
  >- (
    irule pure_walkstar_vars_notin >> simp[] >>
    qexists_tac `CVar uv` >> simp[pure_vars]
    )
QED

(* pure_compat theorems *)
Definition pure_compat_def:
  pure_compat s s' ⇔
    pure_wfs s ∧ pure_wfs s' ∧
    ∀t. pure_walkstar s' (pure_walkstar s t) = pure_walkstar s' t
End

Theorem pure_compat_refl:
  pure_wfs s ⇒ pure_compat s s
Proof
  rw[pure_compat_def, pure_walkstar_SUBMAP]
QED

Theorem pure_compat_trans:
  pure_compat a b ∧ pure_compat b c ⇒ pure_compat a c
Proof
  rw[pure_compat_def] >> metis_tac[]
QED

Theorem pure_compat_SUBMAP:
  pure_wfs s' ∧ s ⊑ s' ⇒ pure_compat s s'
Proof
  rw[pure_compat_def, pure_walkstar_SUBMAP] >> metis_tac[pure_wfs_SUBMAP]
QED

(* pure_compat is preserved under certain types of unification (proof as in HOL *)
Theorem pure_compat_eqs_pure_unify:
  ∀s t1 t2 sx.
    pure_compat s sx ∧ pure_walkstar sx t1 = pure_walkstar sx t2
  ⇒ ∃si. pure_unify s t1 t2 = SOME si ∧ pure_compat si sx
Proof
  rw[pure_compat_def] >>
  qspecl_then [`t2`,`t1`,`sx`,`s`] assume_tac $ GEN_ALL eqs_pure_unify >> gvs[] >>
  drule_all pure_unify_wfs >> rw[] >>
  qspecl_then  [`s`,`t1`,`t2`,`sx'`,`sx`] assume_tac pure_unify_mgu >> gvs[]
QED

(********************)

val _ = export_theory();
