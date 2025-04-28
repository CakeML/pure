(*
  Adapt unification from HOL/examples/algorithms/unification for use in PureCake
*)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     pred_setTheory relationTheory listTheory alistTheory finite_mapTheory;
open unifPropsTheory unifDefTheory walkTheory walkstarTheory collapseTheory substTheory;
open typeclass_typesTheory typeclass_inference_commonTheory;
open typeclass_kindCheckTheory;

val _ = new_theory "typeclass_unification";

Definition encode_itype_def[nocompute]:
  encode_itype (iAtom at) = Const at ∧
  encode_itype (iCVar n) = Var n ∧
  encode_itype (iCons it1 it2) = Pair (encode_itype it1) (encode_itype it2)
End

Definition decode_utype_def[nocompute]:
  decode_utype (Pair u1 u2) =
    iCons (decode_utype u1) (decode_utype u2) ∧
  decode_utype (Const $ at) = iAtom at ∧
  decode_utype (Var n) = iCVar n
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
  ∀it. decode_utype (encode_itype it) = it
Proof
  Induct >> rw[encode_itype_def, decode_utype_def]
QED

Theorem encode_decode:
  ∀ut. encode_itype (decode_utype ut) = ut
Proof
  Induct >> rw[encode_itype_def,decode_utype_def]
QED

Definition pure_wfs_def[nocompute]:
  pure_wfs s = wfs (encode_itype o_f s)
End

Definition pure_vwalk_def[nocompute]:
  pure_vwalk s v = decode_utype (vwalk (encode_itype o_f s) v)
End

Theorem pure_vwalk_ind:
  ∀s. pure_wfs s ⇒
    ∀P. (∀v. (∀w u. FLOOKUP s v = SOME (iCVar u) ⇒ P u) ⇒ P v) ⇒ ∀v. P v
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
        | NONE => iCVar v
        | SOME (iCVar w) => pure_vwalk s w
        | SOME t => t
Proof
  rw[pure_vwalk_def, pure_wfs_def] >>
  CASE_TAC >> gvs[] >>
  simp[Once vwalk_def, FLOOKUP_o_f,
    decode_utype_def] >>
  Cases_on `x` >>
  simp[encode_itype_def,decode_utype_def,decode_encode]
QED

Definition pure_walk_def[nocompute]:
  pure_walk s t = decode_utype (walk (encode_itype o_f s) (encode_itype t))
End

Theorem pure_walk:
  ∀s t. pure_walk s t =
    case t of
    | iCVar v => pure_vwalk s v
    | t => t
Proof
  rw[pure_walk_def, pure_vwalk_def, walk_def] >>
  Cases_on `t` >>
  simp[encode_itype_def,decode_utype_def,decode_encode]
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
  Cases_on `x` >>
  simp[encode_itype_def]
QED

Theorem pure_oc:
  ∀s. pure_wfs s ⇒
    ∀t v.
      pure_oc s t v =
        case pure_walk s t of
        | iCVar u => v = u
        | iCons l r => pure_oc s l v ∨ pure_oc s r v
        | iAtom a => F
Proof
  rw[pure_oc_def] >>
  `wfs (encode_itype o_f s)` by fs [pure_wfs_def] >>
  rw[Once oc_walking, pure_walk_def, walk_def] >>
  Cases_on `t` >>
  simp[encode_itype_def,decode_utype_def,
    decode_encode,encode_vwalk] >>
  Cases_on `pure_vwalk s n` >>
  simp[encode_itype_def,encode_vwalk]
QED

Definition pure_ext_s_check_def[nocompute]:
  pure_ext_s_check s v t =
    OPTION_MAP ($o_f decode_utype) $
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
    OPTION_MAP ($o_f decode_utype) $
      unify (encode_itype o_f s) (encode_itype t1) (encode_itype t2)
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
    ∃t1' t2'.
      t1 = (encode_itype t1') ∧
      t2 = (encode_itype t2') ∧
      t = iCons t1' t2'
Proof
  Cases >> rw[encode_itype_def]
QED

Theorem encode_itype_injective:
  (∀t1 t2. encode_itype t1 = encode_itype t2 ⇔ t1 = t2)
Proof
  rw[EQ_IMP_THM] >>
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

Theorem encode_unify:
  ∀s t1 t2 s' t1' t2'.
    s = encode_itype o_f s' ∧
    t1 = encode_itype t1' ∧
    t2 = encode_itype t2' ∧
    pure_wfs s'
  ⇒ unify s t1 t2 = OPTION_MAP ((o_f) encode_itype) (pure_unify s' t1' t2')
Proof
  simp[option_map_case,pure_unify_def] >>
  rw[] >>
  CASE_TAC >>
  simp[o_f_o_f,combinTheory.o_DEF,encode_decode]
QED

Theorem encode_unify_alt:
  ∀s t1 t2. pure_wfs s ⇒
    unify (encode_itype o_f s) (encode_itype t1) (encode_itype t2) =
    OPTION_MAP ((o_f) encode_itype) (pure_unify s t1 t2)
Proof
  metis_tac[encode_unify]
QED

Theorem wfs_unify:
  ∀s t1 t2 s'. wfs s ∧ unify s t1 t2 = SOME s' ⇒ wfs s'
Proof
  metis_tac[unify_unifier]
QED

Theorem pure_unify:
  ∀t1 t2 s.
    pure_wfs s ⇒
    pure_unify s t1 t2 =
      case (pure_walk s t1, pure_walk s t2) of
      | (iCVar v1, iCVar v2) =>
          SOME (if v1 = v2 then s else s |+ (v1, iCVar v2))
      | (iCVar v1, t2) => pure_ext_s_check s v1 t2
      | (t1, iCVar v2) => pure_ext_s_check s v2 t1
      | (iCons l1 r1,iCons l2 r2) =>
          OPTION_BIND (pure_unify s l1 l2)
            ( λs'. pure_unify s' r1 r2)
      | (iAtom a1,iAtom a2) =>
          if a1 = a2 then SOME s else NONE
      | (t1, t2) => NONE
Proof
  rw[pure_unify_def] >> imp_res_tac pure_wfs_def >>
  rw [Once unify_def, pure_walk_def] >>
  Cases_on `t1` >> Cases_on `t2` >>
  rw[encode_itype_def, decode_utype_def, option_map_case, option_bind_case,
     combinTheory.o_DEF, decode_encode, encode_vwalk]
  >- (
    Cases_on `pure_vwalk s n` >>
    gvs[decode_encode,encode_itype_def] >>
    rw[pure_ext_s_check, Once pure_oc, pure_walk,
      decode_utype_def,combinTheory.o_DEF,
      decode_encode,encode_decode]
    )
  >- (
    ntac 2 CASE_TAC >>
    simp[o_f_o_f,encode_decode,combinTheory.o_DEF]
    )
  >- (
    Cases_on `pure_vwalk s n` >>
    gvs[decode_encode,encode_itype_def]
    >- (
      ntac 2 CASE_TAC >>
      simp[o_f_o_f,combinTheory.o_DEF,encode_decode]
      ) >>
    simp[pure_ext_s_check,Once pure_oc,pure_walk] >>
    simp[pure_oc_def] >>
    IF_CASES_TAC >>
    simp[combinTheory.o_DEF,decode_encode,decode_utype_def]
    )
  >- (
    Cases_on `pure_vwalk s n` >>
    gvs[decode_encode,encode_itype_def]
    >- (
      CASE_TAC >>
      simp[o_f_o_f,combinTheory.o_DEF,decode_encode]
      ) >>
    simp[o_f_o_f,combinTheory.o_DEF,decode_encode,
      pure_ext_s_check,decode_utype_def,
      Once pure_oc,pure_walk]
  )
  >- (
    Cases_on `pure_vwalk s n` >>
    gvs[decode_encode,encode_itype_def]
    >- (
      ntac 2 CASE_TAC >>
      simp[o_f_o_f,combinTheory.o_DEF,encode_decode]
      ) >>
    simp[pure_ext_s_check,Once pure_oc,pure_walk] >>
    simp[pure_oc_def] >>
    IF_CASES_TAC >>
    simp[combinTheory.o_DEF,decode_encode,decode_utype_def]
  )
  >- (
    Cases_on `pure_vwalk s n` >>
    gvs[decode_encode,encode_itype_def] >>
    Cases_on `pure_vwalk s n'` >>
    gvs[decode_encode,encode_itype_def,decode_utype_def,
      o_f_o_f,combinTheory.o_DEF,pure_ext_s_check,
      Once pure_oc,pure_walk]
    >- (
      CASE_TAC >>
      simp[decode_encode,o_f_o_f,combinTheory.o_DEF]
      )
    >- (
      ntac 2 CASE_TAC >>
      simp[encode_decode,o_f_o_f,combinTheory.o_DEF]
      )
    >- (
      simp[pure_oc_def] >>
      CASE_TAC >>
      simp[decode_encode,o_f_o_f,combinTheory.o_DEF,
        decode_utype_def]
      )
    >- (
      simp[pure_oc_def] >>
      CASE_TAC >>
      simp[decode_encode,o_f_o_f,combinTheory.o_DEF,
        decode_utype_def]
      )
    >- (
      IF_CASES_TAC >>
      simp[decode_encode,o_f_o_f,combinTheory.o_DEF,
        decode_utype_def]
      )
  )
QED

Triviality pure_unify_ind_lemma:
  ∀P.
    (∀us ut1 ut2 s t1 t2.
       us = encode_itype o_f s ∧
       ut1 = encode_itype t1 ∧
       ut2 = encode_itype t2 ∧
      (∀l1 r1 l2 r2 sx.
       pure_walk s t1 = iCons l1 r1 ∧
       pure_walk s t2 = iCons l2 r2 ∧
       pure_unify s l1 l2 = SOME sx
       ⇒ P sx r1 r2) ∧
      (∀l1 r1 l2 r2.
        pure_walk s t1 = iCons l1 r1 ∧
        pure_walk s t2 = iCons l2 r1
        ⇒ P s l1 l2) ⇒
       P s t1 t2)
  ⇒ ∀us ut1 ut2. ∀s t1 t2.
    us = encode_itype o_f s ∧
    ut1 = encode_itype t1 ∧
    ut2 = encode_itype t2 ∧
    pure_wfs s ⇒ P s t1 t2
Proof
  gen_tac >> strip_tac >>
  ho_match_mp_tac unify_ind >>
  rpt strip_tac >>
  last_x_assum irule >>
  drule_then assume_tac $ iffLR pure_wfs_def >>
  fs[encode_walk] >>
  rw[]
  >- (first_x_assum irule >> simp[encode_itype_def]) >>
  last_x_assum irule >>
  simp[encode_itype_def,encode_unify_alt] >>
  gvs[pure_unify_def] >>
  drule_all_then assume_tac wfs_unify >>
  simp[pure_wfs_def] >>
  gvs[encode_unify_alt,combinTheory.o_DEF,decode_encode] >>
  metis_tac[]
QED

Theorem pure_unify_ind:
  ∀P.
    (∀s t1 t2.
      (∀l1 r1 l2 r2 sx.
       pure_walk s t1 = iCons l1 r1 ∧
       pure_walk s t2 = iCons l2 r2 ∧
       pure_unify s l1 l2 = SOME sx
       ⇒ P sx r1 r2) ∧
      (∀l1 r1 l2 r2.
        pure_walk s t1 = iCons l1 r1 ∧
        pure_walk s t2 = iCons l2 r1
        ⇒ P s l1 l2) ⇒
       P s t1 t2)
  ⇒ (∀s t1 t2. pure_wfs s ⇒ P s t1 t2)
Proof
  rw[] >>
  irule pure_unify_ind_lemma >>
  simp[]
QED

Definition pure_apply_subst_def[nocompute]:
  pure_apply_subst s t =
    decode_utype $ subst_APPLY (encode_itype o_f s) (encode_itype t)
End

Theorem pure_apply_subst:
  (∀s n.
    pure_apply_subst s (iCVar n) =
      case FLOOKUP s n of | NONE => iCVar n | SOME t => t) ∧
  (∀s l r.
    pure_apply_subst s (iCons l r) =
    iCons (pure_apply_subst s l) (pure_apply_subst s r)) ∧
  (∀s t.
    pure_apply_subst s (iAtom t) = iAtom t)
Proof
  rw[pure_apply_subst_def, encode_itype_def, FLOOKUP_o_f, decode_utype_def] >>
  CASE_TAC >>
  rw[decode_encode, decode_utype_def]
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
    decode_utype $ walkstar (encode_itype o_f s) (encode_itype t)
End

Triviality pure_walkstar_ind_lemma:
 ∀s. pure_wfs s ⇒
  ∀P.
    (∀t.
      (∀l r. pure_walk s t = iCons l r ⇒ P l ∧ P r)
     ⇒ P t)
  ⇒ ∀ut. ∀t. ut = encode_itype t ⇒ P t
Proof
  ntac 4 strip_tac >>
  imp_res_tac pure_wfs_def >>
  drule_then assume_tac $ GEN_ALL $ DISCH_ALL walkstar_ind >>
  pop_assum $ qspec_then
    `λut. ∀t. ut = encode_itype t ⇒ P t`
    (assume_tac o SRULE[]) >>
  rpt strip_tac >>
  first_x_assum irule >>
  fs[FORALL_AND_THM,IMP_CONJ_THM] >>
  rw[] >>
  last_x_assum irule >>
  rw[]
  >- (last_x_assum irule >>
    simp[encode_walk,encode_itype_def]) >>
  first_x_assum irule >>
  simp[encode_walk,encode_itype_def]
QED

Theorem pure_walkstar_ind:
  ∀s. pure_wfs s ⇒
  ∀P.
    (∀t.
      (∀l r. pure_walk s t = iCons l r ⇒ P l ∧ P r)
     ⇒ P t)
  ⇒ ∀t. P t
Proof
  rw[] >>
  irule pure_walkstar_ind_lemma >>
  simp[] >>
  metis_tac[]
QED

Theorem pure_walkstar:
  ∀s. pure_wfs s ⇒
    ∀t. pure_walkstar s t =
        case pure_walk s t of
        | iCVar v => iCVar v
        | iCons l r => iCons (pure_walkstar s l) (pure_walkstar s r)
        | t => t
Proof
  rw[pure_walkstar_def] >> imp_res_tac pure_wfs_def >>
  rw[Once walkstar_def, pure_walk_def] >>
  Cases_on `t` >>
  gvs[encode_itype_def, decode_utype_def, decode_encode, encode_vwalk] >>
  Cases_on `pure_vwalk s n` >>
  gvs[encode_itype_def,decode_utype_def,decode_encode]
QED

Theorem pure_walkstar_alt:
  ∀s. pure_wfs s ⇒
    (∀t1 t2. pure_walkstar s (iCons t1 t2) =
      iCons (pure_walkstar s t1) (pure_walkstar s t2)) ∧
    (∀v. pure_walkstar s (iCVar v) =
      case FLOOKUP s v of
      | NONE => iCVar v
      | SOME t => pure_walkstar s t) ∧
    (∀a. pure_walkstar s (iAtom a) = iAtom a)
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
  Cases_on `pure_walk s t` >> rw[encode_itype_def]
QED

Definition pure_collapse_def[nocompute]:
  pure_collapse s = decode_utype o_f collapse (encode_itype o_f s)
End

Theorem pure_collapse:
  ∀s. pure_collapse s = FUN_FMAP (λv. pure_walkstar s (iCVar v)) (FDOM s)
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
  ∀P.
    (∀s t1 t2.
      pure_wfs s ∧
      (∀l1 r1 l2 r2 sx.
        pure_walk s t1 = iCons l1 r1 ∧
        pure_walk s t2 = iCons l2 r2 ∧
        pure_unify s l1 l2 = SOME sx ⇒
        P sx r1 r2) ∧
      (∀l1 r1 l2 r2.
        pure_walk s t1 = iCons l1 r1 ∧ pure_walk s t2 = iCons l2 r1 ⇒
        P s l1 l2) ⇒
    P s t1 t2) ⇒
  ∀s t1 t2. pure_wfs s ⇒ P s t1 t2
Proof
  rpt gen_tac >> strip_tac >>
  qsuff_tac
    `(∀s t1 t2. pure_wfs s ⇒ pure_wfs s ⇒ P s t1 t2)`
  >- (rpt $ pop_assum kall_tac >> simp[]) >>
  ho_match_mp_tac pure_unify_ind >>
  rpt strip_tac >>
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

Theorem pure_wfs_FEMPTY[simp]:
  pure_wfs FEMPTY
Proof
  rw[pure_wfs] >>
  qsuff_tac `pure_vR FEMPTY = EMPTY_REL`
  >- metis_tac[relationTheory.WF_EMPTY_REL] >>
  simp[FUN_EQ_THM, pure_vR]
QED

Theorem WF_alt_def:
  ∀R. WF R ⇔  ∀B. B ≠ {} ⇒ ∃min. B min ∧ ∀b. B b ⇒ ¬R b min
Proof
  rw[relationTheory.WF_DEF, PULL_EXISTS] >> eq_tac >> rw[] >>
  gvs[GSYM MEMBER_NOT_EMPTY, IN_DEF, PULL_EXISTS] >> metis_tac[]
QED

Theorem pure_wfs_alt:
  pure_wfs s ⇔
    ∀B. B ≠ ∅ ⇒
      ∃min. B min ∧
        ∀b. B b ⇒
          ∀t. FLOOKUP s min = SOME t ⇒ b ∉ pure_vars t
Proof
  rw[pure_wfs, WF_alt_def, pure_vR] >> eq_tac >> rw[] >> gvs[] >>
  first_x_assum drule >> rw[] >> goal_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >> CASE_TAC >> gvs[]
QED

Theorem pure_wfs_extend:
  pure_wfs s ∧ v ∉ FDOM s ∧ v ∉ pure_vars (pure_walkstar s t) ⇒ pure_wfs (s |+ (v,t))
Proof
  rw[pure_wfs_def, pure_vars_def, pure_walkstar_def] >>
  irule wfs_extend >> simp[] >>
  gvs[SRULE [pure_wfs_def] encode_walkstar, decode_encode]
QED

Theorem vR_FUNION:
  DISJOINT (FDOM t) (substvars s) ∧ x ∉ FDOM t ⇒
  (vR (FUNION t s) y x ⇔ vR s y x)
Proof
  rw[vR_def, FLOOKUP_FUNION] >>
  `FLOOKUP t x = NONE` by gvs[FLOOKUP_DEF] >> simp[]
QED

Theorem TC_vR_substvars:
  ∀s y x. TC (vR s) y x ⇒ x ∈ FDOM s ∧ y ∈ substvars s
Proof
  gen_tac >> Induct_on `TC` >> rw[vR_def] >>
  every_case_tac >> gvs[FLOOKUP_DEF, substvars_def, rangevars_def] >>
  disj2_tac >> simp[PULL_EXISTS, FRANGE_DEF] >>
  goal_assum drule >> simp[]
QED

Theorem RTC_vR_substvars:
  ∀s y x. RTC (vR s) y x ⇒ (x ∈ FDOM s ∧ y ∈ substvars s) ∨ x = y
Proof
  rw[RTC_CASES_TC] >> imp_res_tac TC_vR_substvars >> simp[]
QED

Theorem TC_vR_FUNION:
  DISJOINT (FDOM t) (substvars s) ∧ x ∉ FDOM t ⇒
  (TC (vR (FUNION t s)) y x ⇔ TC (vR s) y x)
Proof
  rw[] >> eq_tac >> rw[]
  >- (
    ntac 2 $ pop_assum mp_tac >> Induct_on `TC` >> rw[] >> gvs[]
    >- (gvs[vR_FUNION] >> simp[Once TC_CASES1]) >>
    irule $ cj 2 TC_RULES >>
    goal_assum $ drule_at Any >> first_x_assum irule >>
    imp_res_tac TC_vR_substvars >> gvs[DISJOINT_ALT] >> metis_tac[]
    )
  >- (
    ntac 2 $ pop_assum mp_tac >> Induct_on `TC` >> rw[] >> gvs[]
    >- (simp[Once TC_CASES1] >> disj1_tac >> simp[vR_FUNION]) >>
    irule $ cj 2 TC_RULES >>
    goal_assum $ drule_at Any >> first_x_assum irule >>
    imp_res_tac TC_vR_substvars >> gvs[DISJOINT_ALT] >> metis_tac[]
    )
QED

Theorem TC_vR_FUNION_imp:
  ∀y x. TC (vR (FUNION t s)) y x ⇒
    DISJOINT (FDOM t) (substvars s) ⇒
    TC (vR s) y x ∨
    ∃v u. RTC (vR t) v x ∧ v ∈ FDOM t ∧ u ∈ vars (t ' v) ∧ RTC (vR s) y u
Proof
  Induct_on `TC` using TC_STRONG_INDUCT_RIGHT1 >> rw[] >> gvs[]
  >- (
    rw[] >> reverse $ Cases_on `x ∈ FDOM t` >- metis_tac[vR_FUNION, TC_RULES] >>
    disj2_tac >> gvs[vR_def, FLOOKUP_FUNION] >>
    every_case_tac >> gvs[] >>
    qexists_tac `x` >> gvs[FLOOKUP_DEF, SF SFY_ss] >> goal_assum drule >> simp[]
    ) >>
  gvs[vR_def, FLOOKUP_FUNION] >> Cases_on `FLOOKUP t x` >> gvs[]
  >- (
    every_case_tac >> gvs[] >>
    disj1_tac >> simp[Once TC_CASES2, vR_def] >> metis_tac[]
    )
  >- (
    disj2_tac >> gvs[FLOOKUP_DEF] >>
    rpt $ goal_assum $ drule_at Any >> simp[RTC_CASES_TC]
    )
  >- (
    every_case_tac >> gvs[] >>
    disj1_tac >> simp[Once TC_CASES2] >> simp[vR_def] >>
    disj2_tac >> goal_assum $ drule_at Any >> simp[] >>
    irule $ iffLR TC_vR_FUNION >> rpt $ goal_assum $ drule_at Any >>
    CCONTR_TAC >> gvs[DISJOINT_ALT, FLOOKUP_DEF, substvars_def] >>
    first_x_assum drule >> simp[rangevars_def, PULL_EXISTS, FRANGE_DEF] >>
    metis_tac[]
    )
  >- (
    disj2_tac >>
    rpt $ goal_assum $ drule_at Any >>
    simp[Once RTC_CASES2, vR_def] >> disj2_tac >> metis_tac[]
    )
QED

Theorem wfs_FUNION:
  wfs s ∧ wfs t ∧ DISJOINT (FDOM t) (substvars s) ⇒
  wfs (FUNION t s)
Proof
  rw[SF CONJ_ss, oc_eq_vars_walkstar, wfs_no_cycles] >> strip_tac >>
  drule_all TC_vR_FUNION_imp >> strip_tac >> gvs[] >>
  `v ∈ FDOM t` by (CCONTR_TAC >> gvs[TC_vR_FUNION]) >>
  drule RTC_vR_substvars >> strip_tac >> gvs[] >- gvs[DISJOINT_ALT] >>
  qpat_x_assum `∀v. _` mp_tac >> simp[] >>
  simp[Once EXTEND_RTC_TC_EQN] >>
  goal_assum $ drule_at Any >> simp[vR_def, FLOOKUP_DEF]
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

Definition pure_substvars_def[nocompute]:
  pure_substvars s = substvars (encode_itype o_f s)
End

Theorem pure_substvars:
  pure_substvars s = FDOM s ∪ pure_rangevars s
Proof
  rw[pure_substvars_def, substvars_def, pure_rangevars_def]
QED

Theorem pure_substvars_FEMPTY[simp]:
  pure_substvars FEMPTY = {}
Proof
  rw[pure_substvars, pure_rangevars]
QED

Theorem pure_wfs_FUNION:
  ∀t s.
    pure_wfs s ∧ pure_wfs t ∧
    DISJOINT (FDOM t) (pure_substvars s)
  ⇒ pure_wfs (FUNION t s)
Proof
  rw[pure_wfs_def, pure_substvars_def, o_f_FUNION] >>
  irule wfs_FUNION >> simp[]
QED

Definition pure_allvars_def[nocompute]:
  pure_allvars s t1 t2 =
    allvars (encode_itype o_f s) (encode_itype t1) (encode_itype t2)
End

Theorem pure_allvars:
  pure_allvars s t1 t2 = pure_vars t1 ∪ pure_vars t2 ∪ pure_substvars s
Proof
  rw[pure_allvars_def, pure_vars_def, pure_substvars_def, allvars_def]
QED

Definition pure_uP_def[nocompute]:
  pure_uP sx s t1 t2 ⇔
    uP (encode_itype o_f sx) (encode_itype o_f s)
      (encode_itype t1) (encode_itype t2)
End

Theorem pure_uP:
  pure_uP sx s t1 t2 ⇔
    pure_wfs sx ∧ s ⊑ sx ∧ pure_substvars sx ⊆ pure_allvars s t1 t2
Proof
  rw[pure_uP_def, uP_def] >>
  rw[pure_wfs_def, pure_substvars_def, pure_allvars_def] >>
  eq_tac >> rw[] >> gvs[SUBMAP_FLOOKUP_EQN, FLOOKUP_o_f] >> rw[]
  >- (
    first_x_assum $ qspec_then `x` mp_tac >> simp[] >>
    CASE_TAC >> rw[encode_itype_injective]
    )
  >- (
    pop_assum mp_tac >> CASE_TAC >> rw[] >> first_x_assum drule >> simp[]
    )
QED

Theorem pure_unify_uP:
  pure_wfs s ∧ pure_unify s t1 t2 = SOME sx ⇒ pure_uP sx s t1 t2
Proof
  rw[pure_wfs_def, pure_unify_def, pure_uP_def] >>
  drule_all unify_uP >> simp[] >>
  gvs[GSYM pure_wfs_def, encode_unify_alt] >>
  simp[combinTheory.o_DEF, decode_encode, SF ETA_ss]
QED

Theorem pure_vars:
  (∀a. pure_vars (iAtom a) = {}) ∧
  (∀c t. pure_vars (iCons c t) = pure_vars c ∪ pure_vars t) ∧
  (∀n. pure_vars (iCVar n) = {n})
Proof
  rw[pure_vars_def, encode_itype_def]
QED

Theorem pure_vwalk_to_var:
  pure_wfs s ⇒ ∀v u. pure_vwalk s v = iCVar u ⇒ u ∉ FDOM s
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
    (∀a. P (iAtom a)) ∧
    (∀l r. P l ∧ P r ⇒ P (iCons l r)) ∧
    (∀v. (∀t. FLOOKUP s v = SOME t ⇒ P t) ⇒ P (iCVar v))
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
  pop_assum mp_tac >>
  qpat_x_assum `!c. _ ⇒ P (iCVar v)` mp_tac >>
  last_x_assum mp_tac >>
  rpt $ pop_assum kall_tac >>
  rw[] >>
  imp_res_tac pure_vwalk_ind >>
  pop_assum $ qspec_then ` λn. P (pure_vwalk s n) ⇒ P (iCVar n)` mp_tac >> simp[] >>
  disch_then irule >> rw[] >> rgs[Once pure_vwalk] >>
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

Theorem oc_iAtom:
  ∀s uv a. pure_wfs s ⇒ ¬pure_oc s (iAtom a) uv
Proof
  rw[] >> drule pure_oc >>
  disch_then $ once_rewrite_tac o single >>
  rw[pure_walk]
QED

Theorem oc_unit:
  ∀s uv. pure_wfs s ⇒ ¬pure_oc s Unit uv
Proof
  metis_tac[oc_iAtom]
QED

Theorem no_vars_extend_subst_vwalk:
  ∀s. pure_wfs s ⇒
    ∀n s'.
      pure_wfs (s |++ s') ∧
      DISJOINT (FDOM s) (FDOM (FEMPTY |++ s')) ∧
      (∀n'. pure_vwalk s n ≠ iCVar n')
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
  Cases_on `t` >> rw[]
  >- (
    simp[Once pure_walkstar] >>
    simp[Once pure_walk] >>
    simp[Once pure_walkstar] >>
    simp[Once pure_walk]
  )
  >- (
    qpat_x_assum `∀t t'. pure_walk s _ = iCons _ _ ⇒ _` $
      assume_tac o SRULE[Once pure_walk] >>
    qpat_x_assum `pure_vars (pure_walkstar _ _) = ∅ ` $
      mp_tac >>
    simp[Once pure_walkstar] >>
    simp[Once pure_walk] >>
    simp[pure_vars] >>
    strip_tac >>
    simp[Once pure_walkstar] >>
    simp[Once pure_walk] >>
    irule EQ_SYM >>
    simp[Once pure_walkstar] >>
    simp[Once pure_walk]
  )
  >- (
    simp[Once pure_walkstar] >>
    simp[Once pure_walk] >>
    irule EQ_SYM >>
    simp[Once pure_walkstar] >>
    simp[Once pure_walk] >>
    rev_drule_then drule no_vars_extend_subst_vwalk >>
    rw[] >>
    Cases_on `pure_vwalk s n` >>
    simp[]
    >- (
      qpat_x_assum `∀t t'. pure_walk s _ = iCons _ _ ⇒ _` $
       assume_tac o SRULE[pure_walk] >>
      first_x_assum drule >>
      qpat_x_assum `pure_vars (pure_walkstar _ _) = ∅ ` $
        mp_tac >>
      simp[Once pure_walkstar] >>
      simp[Once pure_walk] >>
      rw[pure_vars]
    ) >>
    irule FALSITY >>
    qpat_x_assum `pure_vars (pure_walkstar _ _) = ∅ ` $
      mp_tac >>
    simp[Once pure_walkstar] >>
    simp[Once pure_walk,pure_vars]
  )
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
  AP_TERM_TAC >> irule unify_mgu >>
  imp_res_tac pure_wfs_def >> simp[] >>
  qexistsl_tac [`encode_itype t1`,`encode_itype t2`] >> gvs[encode_unify_alt] >>
  qpat_x_assum `_ = _` mp_tac >> gvs[encode_walkstar, decode_encode]
QED

Theorem pure_walkstar_CVar_props:
  pure_wfs s ⇒
  (uv ∉ FDOM s ⇔ pure_walkstar s (iCVar uv) = iCVar uv)
Proof
  rw[] >> eq_tac >> rw[]
  >- (
    drule pure_walkstar >> disch_then $ once_rewrite_tac o single >>
    simp[pure_walk, Once pure_vwalk, FLOOKUP_DEF]
    )
  >- (
    irule pure_walkstar_vars_notin >> simp[] >>
    qexists_tac `iCVar uv` >> simp[pure_vars]
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
