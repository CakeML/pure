open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory rich_listTheory alistTheory pred_setTheory finite_mapTheory;
open pure_miscTheory pure_configTheory;
open mlstringTheory pure_cexpTheory;
open typeclass_typesTheory typeclass_typesPropsTheory typeclass_texpTheory;
open typeclass_kindCheckTheory;
open typeclass_typingTheory;

val _ = new_theory "typeclass_typingProps";

(******************** Basic lemmas ********************)

Theorem FINITE_reserved_cns[simp]:
  FINITE reserved_cns
Proof
  rw[reserved_cns_def]
QED

Theorem type_atom_op_not_Loc:
  type_atom_op op ts t ⇒ ∀n. op ≠ Lit $ Loc n
Proof
  rw[type_atom_op_cases, type_lit_cases]
QED

Theorem type_atom_op_no_Bool:
  type_atom_op op ts t ⇒ ¬ MEM Bool ts
Proof
  rw[type_atom_op_cases] >> gvs[] >> Induct_on `ts` >> gvs[]
QED

Theorem get_PrimTys_SOME:
  ∀ts pts.
    get_PrimTys ts = SOME pts ⇔ ts = MAP (Atom o PrimTy) pts
Proof
  ho_match_mp_tac get_PrimTys_ind >>
  rw[get_PrimTys_def] >>
  Cases_on `pts` >> gvs[] >> eq_tac >> rw[]
QED

Theorem type_exception_Subscript:
  namespace_ok ns ⇒ type_exception (FST ns) («Subscript», [])
Proof
  PairCases_on `ns` >> rw[type_exception_def, namespace_ok_def] >>
  gvs[ALL_DISTINCT_APPEND] >> drule_all ALOOKUP_ALL_DISTINCT_MEM >> simp[]
QED

(* more extensional and do not need to deal with ++ *)
Theorem kind_ok_subst_db:
  ∀skip ts t tdefs ks k ks'.
    kind_ok tdefs ks' k t ∧
    (∀v k. v < skip ∧ LLOOKUP ks' v = SOME k ⇒
      LLOOKUP ks v = SOME k) ∧
    (∀v k. skip ≤ v ∧ v < skip + LENGTH ts ∧
      LLOOKUP ks' v = SOME k ⇒
      kind_ok tdefs ks k (EL (v - skip) ts)) ∧
    (∀v k. skip + LENGTH ts ≤ v ∧ LLOOKUP ks' v = SOME k ⇒
      LLOOKUP ks (v - LENGTH ts) = SOME k) ⇒
    kind_ok tdefs ks k (subst_db skip ts t)
Proof
  rw[kind_ok_def] >>
  irule kind_wf_subst_db >>
  first_x_assum $ irule_at (Pos last) >>
  rw[]
QED

Theorem kind_ok_subst_db_APPEND:
  ∀skip ts t tdefs ks' k tks ks ks1 ks2.
    kind_ok tdefs ks' k t ∧
    skip = LENGTH ks1 ∧
    ks' = ks1 ++ tks ++ ks2 ∧
    ks = ks1 ++ ks2 ∧
    LIST_REL (kind_ok tdefs ks) tks ts ⇒
    kind_ok tdefs ks k (subst_db skip ts t)
Proof
  rw[kind_ok_def,LIST_REL_EL_EQN] >>
  drule_then irule kind_wf_subst_db >>
  gvs[oEL_THM,EL_APPEND_EQN]
QED

Theorem kind_ok_shift_db:
  ∀skip shift t tdefs ks k ks'.
    kind_ok tdefs ks' k t ∧
    (∀v k. v < skip ∧ LLOOKUP ks' v = SOME k ⇒
      LLOOKUP ks v = SOME k) ∧
    (∀v k. skip ≤ v ∧ LLOOKUP ks' v = SOME k ⇒
      LLOOKUP ks (v + shift) = SOME k) ⇒
    kind_ok tdefs ks k (shift_db skip shift t)
Proof
  rw[kind_ok_def] >>
  irule kind_wf_shift_db >>
  first_x_assum $ irule_at (Pos last) >>
  rw[]
QED

Theorem kind_ok_shift_db_APPEND:
  ∀skip shift t tdefs ks k ks' ks'1 shift_ks ks'2.
    kind_ok tdefs ks' k t ∧
    ks = ks'1 ++ shift_ks ++ ks'2 ∧
    shift = LENGTH shift_ks ∧
    ks' = ks'1 ++ ks'2 ∧
    skip = LENGTH ks'1 ⇒
    kind_ok tdefs ks k (shift_db skip shift t)
Proof
  rw[kind_ok_def] >>
  drule_then irule kind_wf_shift_db >>
  rw[] >>
  gvs[oEL_THM,EL_APPEND_EQN]
QED

Theorem kind_ok_mono:
  ∀tdefs ks k t ks'.
  kind_ok tdefs ks' k t ∧
  LENGTH ks' ≤ LENGTH ks ∧
  (∀v. v < LENGTH ks' ⇒ EL v ks = EL v ks') ⇒
  kind_ok tdefs ks k t
Proof
  rw[kind_ok_def] >>
  irule kind_wf_mono >>
  last_x_assum $ irule_at (Pos last) >>
  simp[oEL_THM]
QED

Theorem kind_ok_APPEND:
  ∀tdefs ks k t ks'.
  kind_ok tdefs ks k t ⇒
  kind_ok tdefs (ks ++ ks') k t
Proof
  rw[] >>
  drule_then irule kind_ok_mono >>
  simp[EL_APPEND_EQN]
QED

Theorem kind_ok_Functions:
  kind_ok tdefs ks k (Functions as r) ⇔
  ((kind_ok tdefs ks k r ∧ as = []) ∨
  (k = kindType ∧ kind_ok tdefs ks kindType r ∧
  ∀arg. MEM arg as ⇒ kind_ok tdefs ks kindType arg))
Proof
  rw[kind_ok_def,kind_wf_Functions,EQ_IMP_THM]
QED

Theorem type_ok_Functions:
  type_ok tdefs ks (Functions as r) ⇔
  (type_ok tdefs ks r ∧
  ∀arg. MEM arg as ⇒ type_ok tdefs ks arg)
Proof
  rw[type_ok_def,kind_ok_Functions,EQ_IMP_THM] >>
  fs[]
QED

Theorem kind_ok:
  (∀tds ks k t1 t2.
    kind_ok tds ks k (Cons t1 t2) ⇔
    ∃k2. kind_ok tds ks k2 t2 ∧
      kind_ok tds ks (kindArrow k2 k) t1) ∧
  (∀tds ks k t.
    kind_ok tds ks k (Atom (PrimTy t)) ⇔ k = kindType) ∧
  (∀tds ks k.
    kind_ok tds ks k (Atom Exception) ⇔ k = kindType) ∧
  (∀tds ks k v.
    kind_ok tds ks k (TypeVar v) ⇔ LLOOKUP ks v = SOME k) ∧
  (∀tds ks k v.
    kind_ok tds ks k (UserType v) ⇔
      ∃tinfo. LLOOKUP tds v = SOME tinfo ∧
        k = kind_arrows (FST tinfo) kindType) ∧
  (∀tds ks k.
    kind_ok tds ks k (Atom (CompPrimTy Function)) ⇔
    k = kindArrow kindType (kindArrow kindType kindType)) ∧
  (∀tds ks k.
    kind_ok tds ks k (Atom (CompPrimTy Array)) ⇔
    k = kindArrow kindType kindType) ∧
  (∀tds ks k. kind_ok tds ks k (Atom (CompPrimTy M)) ⇔
   k = kindArrow kindType kindType) ∧
  ∀tds ks k n. kind_ok tds ks k (Tup n) ⇔
    k = kind_arrows (GENLIST (K kindType) n) kindType
Proof
  rw[kind_ok_def,typedefs_to_cdb_def]
QED

Theorem type_ok:
  (∀tds ks t. type_ok tds ks t ⇔
    kind_ok tds ks kindType t) ∧
  (∀tds ks k t1 t2.
    kind_ok tds ks k (Cons t1 t2) ⇔
    ∃k2. kind_ok tds ks k2 t2 ∧
      kind_ok tds ks (kindArrow k2 k) t1) ∧
  (∀tds ks k t.
    kind_ok tds ks k (Atom (PrimTy t)) ⇔ k = kindType) ∧
  (∀tds ks k.
    kind_ok tds ks k (Atom Exception) ⇔ k = kindType) ∧
  (∀tds ks k v.
    kind_ok tds ks k (TypeVar v) ⇔ LLOOKUP ks v = SOME k) ∧
  (∀tds ks k v.
    kind_ok tds ks k (UserType v) ⇔
      ∃tinfo. LLOOKUP tds v = SOME tinfo ∧
        k = kind_arrows (FST tinfo) kindType) ∧
  (∀tds ks k.
    kind_ok tds ks k (Atom (CompPrimTy Function)) ⇔
    k = kindArrow kindType (kindArrow kindType kindType)) ∧
  (∀tds ks k.
    kind_ok tds ks k (Atom (CompPrimTy Array)) ⇔
    k = kindArrow kindType kindType) ∧
  (∀tds ks k. kind_ok tds ks k (Atom (CompPrimTy M)) ⇔
   k = kindArrow kindType kindType) ∧
  ∀tds ks k n. kind_ok tds ks k (Tup n) ⇔
    k = kind_arrows (GENLIST (K kindType) n) kindType
Proof
  rw[type_ok_def,kind_ok]
QED

Theorem pred_type_kind_ok_alt:
  pred_type_kind_ok clk tdefs ks (Pred cls ty) ⇔
  (kind_ok tdefs ks kindType ty ∧
  ∀cl. MEM cl cls ⇒
    ∃k. clk (FST cl) = SOME k ∧
      kind_ok tdefs ks k (SND cl))
Proof
  simp[pred_type_kind_ok_def,kind_ok_def,
    pred_kind_wf_def]
QED

Theorem pred_type_kind_ok_subst_db_pred:
  ∀skip ts pt clk tdefs ks k ks'.
    pred_type_kind_ok clk tdefs ks' pt ∧
    (∀v k. v < skip ∧ LLOOKUP ks' v = SOME k ⇒
      LLOOKUP ks v = SOME k) ∧
    (∀v k. skip ≤ v ∧ v < skip + LENGTH ts ∧
      LLOOKUP ks' v = SOME k ⇒
      kind_ok tdefs ks k (EL (v - skip) ts)) ∧
    (∀v k. skip + LENGTH ts ≤ v ∧ LLOOKUP ks' v = SOME k ⇒
      LLOOKUP ks (v - LENGTH ts) = SOME k) ⇒
    pred_type_kind_ok clk tdefs ks (subst_db_pred skip ts pt)
Proof
  rw[oneline pred_type_kind_ok_alt] >>
  last_x_assum mp_tac >>
  TOP_CASE_TAC >>
  rw[subst_db_pred_def,MEM_MAP]
  >- (
    drule_then irule kind_ok_subst_db >>
    rw[]) >>
  simp[] >>
  first_x_assum drule >>
  rw[] >>
  first_assum $ irule_at (Pos hd) >>
  drule_then irule kind_ok_subst_db >>
  rw[]
QED

Theorem pred_type_kind_ok_subst_db_pred_APPEND:
  ∀skip ts pt clk tdefs ks k ks' ks1 tks ks2.
    pred_type_kind_ok clk tdefs ks' pt ∧
    skip = LENGTH ks1 ∧
    ks' = ks1 ++ tks ++ ks2 ∧
    ks = ks1 ++ ks2 ∧
    LIST_REL (kind_ok tdefs ks) tks ts
  ⇒
    pred_type_kind_ok clk tdefs ks (subst_db_pred skip ts pt)
Proof
  rw[] >>
  drule_then irule pred_type_kind_ok_subst_db_pred >>
  gvs[oEL_THM,EL_APPEND_EQN,LIST_REL_EL_EQN]
QED

Theorem pred_type_kind_ok_shift_db_pred:
  ∀skip shift pt clk tdefs ks ks'.
    pred_type_kind_ok clk tdefs ks' pt ∧
    (∀v k. v < skip ∧ LLOOKUP ks' v = SOME k ⇒
      LLOOKUP ks v = SOME k) ∧
    (∀v k. skip ≤ v ∧ LLOOKUP ks' v = SOME k ⇒
      LLOOKUP ks (v + shift) = SOME k) ⇒
    pred_type_kind_ok clk tdefs ks (shift_db_pred skip shift pt)
Proof
  rw[oneline pred_type_kind_ok_alt] >>
  last_x_assum mp_tac >>
  TOP_CASE_TAC >>
  rw[shift_db_pred_def,MEM_MAP]
  >- (
    drule_then irule kind_ok_shift_db >>
    rw[]) >>
  simp[] >>
  first_x_assum drule >>
  rw[] >>
  first_assum $ irule_at (Pos hd) >>
  drule_then irule kind_ok_shift_db >>
  rw[]
QED

Theorem pred_type_kind_ok_shift_db_pred_APPEND:
  ∀skip shift pt clk tdefs ks ks' ks'1 shift_ks ks'2.
    pred_type_kind_ok clk tdefs ks' pt ∧
    ks = ks'1 ++ shift_ks ++ ks'2 ∧
    shift = LENGTH shift_ks ∧
    ks' = ks'1 ++ ks'2 ∧
    skip = LENGTH ks'1 ⇒
    pred_type_kind_ok clk tdefs ks (shift_db_pred skip shift pt)
Proof
  rw[] >>
  drule_then irule pred_type_kind_ok_shift_db_pred >>
  gvs[oEL_THM,EL_APPEND_EQN]
QED

Theorem kind_arrows_APPEND:
  kind_arrows (xs ++ ys) k = kind_arrows xs (kind_arrows ys k)
Proof
  Induct_on `xs` >>
  rw[kind_arrows_def]
QED

Theorem kind_wf_cons_types:
  ∀cdb vdb k t ts.
    kind_wf cdb vdb k (cons_types t ts) ⇔
    ∃ks. LIST_REL (kind_wf cdb vdb) ks ts ∧
      kind_wf cdb vdb (kind_arrows ks k) t
Proof
  Induct_on `ts` using SNOC_INDUCT >>
  rw[cons_types_def,kind_arrows_def,kind_arrows_def,
    kind_arrows_APPEND,cons_types_SNOC,LIST_REL_SNOC,
    PULL_EXISTS] >>
  metis_tac[]
QED

Theorem kind_ok_cons_types:
  ∀tdefs db k t ts.
    kind_ok tdefs db k (cons_types t ts) ⇔
    ∃ks. LIST_REL (kind_ok tdefs db) ks ts ∧
      kind_ok tdefs db (kind_arrows ks k) t
Proof
  rw[lambdify kind_ok_def,kind_wf_cons_types,
    EQ_IMP_THM,SF ETA_ss]
QED

Theorem kind_arrows_kindType_EQ:
  ∀ks ks'. kind_arrows ks kindType = kind_arrows ks' kindType ⇔ ks = ks'
Proof
  simp[EQ_IMP_THM] >>
  Induct >>
  simp[kind_arrows_def]
  >- (Induct >> simp[kind_arrows_def]) >>
  strip_tac >>
  Induct >>
  simp[kind_arrows_def]
QED

Theorem monad_args_SUBSET_reserved_cns:
  monad_cns SUBSET reserved_cns DELETE "Subscript"
Proof
  simp[monad_cns_def,reserved_cns_def,SUBSET_DEF]
QED

(******************** Typing judgements ********************)

Theorem type_cepat_type_ok:
  namespace_ok ns ⇒
  ∀p t vts. type_cepat ns db p t vts ⇒
    ∀v t'. kind_ok (SND ns) db kindType t ∧
      MEM (v,t') vts ⇒ kind_ok (SND ns) db kindType t'
Proof
  strip_tac >>
  ho_match_mp_tac type_cepat_ind >>
  rw[] >>
  gvs[MEM_FLAT,LIST_REL3_EL,MEM_EL] >>
  first_x_assum drule >>
  disch_then irule >>
  rw[]
  >- metis_tac[] >>
  qpat_x_assum `destruct_type_cons _ _ _ _ _` mp_tac >>
  simp[oneline destruct_type_cons_def] >>
  TOP_CASE_TAC >>
  TOP_CASE_TAC
  >- (
    strip_tac >>
    fs[type_exception_def,namespace_ok_def,EVERY_EL] >>
    drule_then strip_assume_tac ALOOKUP_SOME_EL >>
    first_x_assum drule >>
    rw[type_ok_def] >>
    irule kind_ok_mono >>
    first_x_assum $ irule_at (Pos last) >>
    simp[]
  ) >>
  rw[split_ty_cons_thm,head_ty_cons_eq_head_ty] >>
  pop_assum mp_tac >>
  every_case_tac
  >- (
    rw[type_cons_def] >>
    gvs[oEL_THM,LIST_REL_EL_EQN,namespace_ok_def,EL_MAP] >>
    gvs[EVERY_EL] >>
    first_x_assum drule >>
    drule_then strip_assume_tac ALOOKUP_SOME_EL >>
    rw[] >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum drule >>
    rw[type_ok_def] >>
    drule_then irule kind_ok_subst_db >>
    rw[]
    >- (
      first_x_assum drule >>
      fs[oEL_THM]
    ) >>
    fs[oEL_THM]
  )
  >- (rw[] >> gvs[]) >>
  rw[] >>
  qpat_x_assum `kind_ok _ _ kindType t` mp_tac >>
  once_rewrite_tac[GSYM cons_types_head_ty_ty_args] >>
  disch_then $ strip_assume_tac o
    SRULE[kind_ok_cons_types] >>
  simp[cons_types_head_ty_ty_args] >>
  gvs[LIST_REL_EL_EQN,kind_ok,kind_arrows_kindType_EQ]
QED

Triviality LIST_REL3_IMP_helper:
  ∀xs ys zs.
  LIST_REL3 (λx y z. P x y z ⇒ Q x y z) xs ys zs ⇒
  LIST_REL3 P xs ys zs ⇒
  LIST_REL3 Q xs ys zs
Proof
  ho_match_mp_tac LIST_REL3_induct >>
  rw[LIST_REL3_def]
QED

Theorem LIST_REL3_IMP =
  SRULE[AND_IMP_INTRO] LIST_REL3_IMP_helper;

Theorem LIST_REL3_EVERY:
  LIST_REL3 R xs ys zs ⇔
  LENGTH ys = LENGTH xs ∧ LENGTH zs = LENGTH xs ∧
  EVERY (UNCURRY (UNCURRY R)) $ ZIP (ZIP (xs,ys),zs)
Proof
  rw[LIST_REL3_EL,EVERY_EL,EQ_IMP_THM,EL_ZIP] >>
  gvs[] >>
  first_x_assum drule >>
  simp[EL_ZIP]
QED

Theorem specialises_db_APPEND:
  specialises tds db t t' ⇒
  specialises tds (db ++ db') t t'
Proof
  rw[oneline specialises_def,pair_CASE_def,LIST_REL_EL_EQN] >>
  first_assum $ irule_at (Pos hd) >>
  rw[] >>
  gvs[] >>
  first_x_assum drule >>
  metis_tac[kind_ok_APPEND]
QED

Theorem specialises_kind_ok:
  specialises tds db t t' ∧
  kind_ok tds (FST t ++ db) k (SND t) ⇒
  kind_ok tds db k t'
Proof
  rw[oneline specialises_def,pair_CASE_def,LIST_REL_EL_EQN] >>
  drule_then irule kind_ok_subst_db >>
  rw[oEL_THM,EL_APPEND_EQN] >>
  gvs[]
QED

Theorem specialises_pred_pred_type_kind_ok:
  specialises_pred tds db pt pt' ∧
  pred_type_kind_ok clk tds (FST pt ++ db) (SND pt) ⇒
  pred_type_kind_ok clk tds db pt'
Proof
  rw[oneline specialises_pred_def,pair_CASE_def,LIST_REL_EL_EQN,
     oneline pred_type_kind_ok_alt,oneline subst_db_pred_def] >>
  every_case_tac >>
  gvs[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
  rw[PULL_EXISTS]
  >- (
    drule_then irule kind_ok_subst_db >>
    gvs[oEL_THM,EL_APPEND_EQN]
  ) >>
  first_x_assum drule >>
  rw[] >>
  gvs[] >>
  drule_then irule kind_ok_subst_db >>
  gvs[oEL_THM,EL_APPEND_EQN]
QED

Theorem type_elaborate_type_ok:
  namespace_ok ns ⇒
  ((∀lie db st env e e' t.
    pred_type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    pred_type_kind_ok clk (SND ns) db t) ∧
  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    EVERY (type_ok (SND ns) db) st ∧
    EVERY (λ(v,scheme). pred_type_kind_scheme_ok clk (SND ns) db scheme) env ⇒
    type_ok (SND ns) db t))
Proof
  strip_tac >>
  ho_match_mp_tac type_elaborate_texp_ind >>
  simp[lambdify type_ok_def,kind_ok_Functions,kind_ok] >>
  rw[]
  >- (
    drule specialises_pred_pred_type_kind_ok >>
    rw[pred_type_kind_ok_alt] >>
    first_x_assum $ irule o cj 1 >>
    gvs[EVERY_MEM] >>
    drule_then (first_x_assum o resolve_then (Pos hd) mp_tac) ALOOKUP_MEM >>
    simp[ELIM_UNCURRY,ALOOKUP_MAP] >>
    metis_tac[]
  )
  >- fs[]
  >- (
    gvs[EVERY_EL,LIST_REL_EL_EQN,MEM_EL,kind_ok_Functions] >>
    rw[]
    >- (
      first_x_assum irule >>
      rw[EL_ZIP,EL_MAP,pred_type_kind_ok_alt]
    ) >>
    metis_tac[]
  )
  >- gvs[EVERY_EL,LIST_REL_EL_EQN,MEM_EL]
  >- (
    first_x_assum irule >>
    simp[] >>
    gvs[LIST_REL3_EL,EVERY_EL] >>
    rw[EL_ZIP] >>
    last_x_assum drule >>
    ntac 3 (pairarg_tac >> gvs[])
  )
  >- (
    simp[tcons_to_type_def,kind_ok_cons_types,kind_ok] >>
    gvs[type_cons_def,LIST_REL3_EL] >>
    metis_tac[]
  )
  >- gvs[kind_ok_cons_types,kind_ok,LIST_REL3_EL,
      kind_arrows_kindType_EQ,LIST_REL_EL_EQN]
  >- simp[kind_arrows_def]
  >- gvs[oEL_THM,EVERY_EL]
  >- (
    first_x_assum irule >>
    simp[EVERY_MAP,pred_type_kind_ok_alt] >>
    fs[] >>
    simp[EVERY_MEM,LAMBDA_PROD,GSYM PFORALL_THM] >>
    rw[pred_type_kind_ok_alt] >>
    drule_then (drule_then irule) type_cepat_type_ok >>
    metis_tac[]
  )
QED

Theorem implodeEQ:
  (implode x = y ⇔ (x = explode y)) ∧
  (y = implode x ⇔ (explode y = x))
Proof
  rw[EQ_IMP_THM] >> simp[]
QED

Theorem monad_args_ok_SOME:
  num_monad_args s = SOME x ⇒ s ∈ monad_cns
Proof
  strip_tac >>
  irule $ iffLR num_monad_args_ok_monad_cns >>
  simp[]
QED

(* TODO move *)
Theorem ALL_DISTINCT_LENGTH_SET:
  LENGTH a = LENGTH b ∧ set a = set b ∧ ALL_DISTINCT a ⇒ ALL_DISTINCT b
Proof
  rw[] >>
  drule PERM_ALL_DISTINCT_LENGTH >>
  disch_then $ qspec_then `b` assume_tac >> gvs[] >>
  metis_tac[sortingTheory.ALL_DISTINCT_PERM]
QED

Theorem type_elaborate_texp_wf:
  namespace_ok ns ⇒
  ((∀lie db st env e e' t.
    pred_type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    texp_wf e) ∧
  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    texp_wf e))
Proof
  strip_tac >>
  ho_match_mp_tac type_elaborate_texp_ind >>
  rw[texp_wf_def,LIST_REL3_EL,EVERY_EL,LIST_REL_EL_EQN]
  >- (Cases_on `vs` >> gvs[])
  >- (
    last_x_assum drule >>
    simp[EL_MAP,ELIM_UNCURRY]
  )
  >- (
    gvs[type_cons_def,oneline namespace_ok_def] >>
    last_x_assum mp_tac >>
    TOP_CASE_TAC >>
    fs[oEL_THM,ALL_DISTINCT_APPEND,MEM_MAP,EVERY_MEM,PULL_EXISTS] >>
    rw[num_args_ok_def] >>
    TOP_CASE_TAC >>
    spose_not_then kall_tac >>
    drule_then strip_assume_tac monad_args_ok_SOME >>
    assume_tac monad_args_SUBSET_reserved_cns >>
    drule_then drule $ iffLR SUBSET_DEF >>
    strip_tac >>
    qpat_x_assum `!e. _ ⇒ ∀y. _ ⇒ ¬MEM y (FLAT (MAP _ _))` $
      qspec_then `cname` mp_tac >>
    fs[implodeEQ] >>
    drule ALOOKUP_SOME_EL >>
    rw[MEM_FLAT,MEM_MAP,MEM_EL,LAMBDA_PROD,
      GSYM PFORALL_THM,GSYM PEXISTS_THM] >>
    simp[PULL_EXISTS] >>
    first_x_assum $ irule_at (Pos last) o GSYM >>
    simp[] >>
    metis_tac[]
  ) >>
  simp[num_args_ok_def,num_monad_args_def,num_atomop_args_ok_def]
  >- (
    simp[GSYM num_monad_args_def] >>
    gvs[type_exception_def,oneline namespace_ok_def] >>
    last_x_assum mp_tac >>
    TOP_CASE_TAC >>
    fs[oEL_THM,ALL_DISTINCT_APPEND,MEM_MAP,EVERY_MEM,PULL_EXISTS] >>
    rw[] >>
    TOP_CASE_TAC >>
    spose_not_then kall_tac >>
    drule_then strip_assume_tac monad_args_ok_SOME >>
    assume_tac monad_args_SUBSET_reserved_cns >>
    drule_then drule $ iffLR SUBSET_DEF >>
    strip_tac >>
    fs[] >>
    qpat_x_assum `∀y. _ ⇒ ∀y'. _ ⇒ ¬MEM y' _` drule >>
    simp[LAMBDA_PROD,GSYM PEXISTS_THM] >>
    metis_tac[ALOOKUP_SOME_EL,MEM_EL]
  )
  >- (
    imp_res_tac get_PrimTys_SOME >> gvs[type_atom_op_cases] >>
    simp[num_atomop_args_ok_def]
  ) >>
  gvs[] >>
  first_x_assum drule >>
  ntac 2 (pairarg_tac >> gvs[]) >>
  rw[EL_MAP]
QED

Inductive elaborated_texp:
[~UserAnnot:]
  elaborated_texp e e' ⇒
  elaborated_texp (UserAnnot t e) e'

[~Var:]
  elaborated_texp (Var l v) (Var l' v)

[~Seq:]
  elaborated_texp e1 e1' ∧ elaborated_texp e2 e2' ⇒
  elaborated_texp (Prim Seq [e1;e2]) (PrimSeq polyt e1' e2')

[~Prim:]
  op ≠ Seq ∧
  LIST_REL elaborated_texp es es' ⇒
  elaborated_texp (Prim op es) (Prim op es')

[~PrimSeq:]
  elaborated_texp e1 e1' ∧ elaborated_texp e2 e2' ∧
  n = LENGTH new ∧ pt = pt' ⇒
  elaborated_texp (PrimSeq (n,pt) e1 e2)
    (PrimSeq (new,pt') e1' e2')

[~App:]
  LIST_REL elaborated_texp es es' ∧ elaborated_texp e e' ⇒
  elaborated_texp (App e es) (App e' es')

[~Lam:]
  elaborated_texp e e' ⇒
  elaborated_texp (Lam vs e) (Lam vs e')

[~Let:]
  elaborated_texp e1 e1' ∧ elaborated_texp e2 e2' ∧
  y' = SOME (new,pt1) ∧ (y = NONE ∨ y = SOME (LENGTH new,pt1)) ⇒
  elaborated_texp (typeclass_texp$Let (x,y) e1 e2) (typeclass_texp$Let (x,y') e1' e2')

[~Letrec:]
  elaborated_texp e e' ∧
  LENGTH fns = LENGTH fns' ∧
  (∀n. n < LENGTH fns' ⇒  FST (FST $ EL n fns) = FST (FST $ EL n fns')) ∧
  LIST_REL (λfn fn'. elaborated_texp (SND fn) (SND fn')) fns fns' ∧
  LIST_REL (λfn fn'. ∃ks pt. SND (FST fn') = SOME (ks,pt) ∧
    (SND (FST fn) = NONE ∨ SND (FST fn) = SOME (LENGTH ks,pt))) fns fns' ⇒
  elaborated_texp (Letrec fns e) (Letrec fns' e')

[~NestedCase:]
  elaborated_texp g g' ∧ elaborated_texp e e' ∧
  LENGTH pes = LENGTH pes' ∧
  (∀n. n < LENGTH pes' ⇒  FST (EL n pes) = FST (EL n pes')) ∧
  LIST_REL (λpe pe'. elaborated_texp (SND pe) (SND pe') ) pes pes' ⇒
  elaborated_texp (NestedCase g gv p e pes) (NestedCase g' gv p e' pes')
End

Theorem type_elaborate_texp_elaborated_texp:
  (∀lie db st env e e' t.
    pred_type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    elaborated_texp e e') ∧
  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    elaborated_texp e e')
Proof
  ho_match_mp_tac type_elaborate_texp_ind >>
  gvs[EVERY_EL,LIST_REL3_EL,EL_MAP] >>
  rw[] >> simp[Once elaborated_texp_cases]
  >- simp[LIST_REL_EL_EQN]
  >- (
    pop_assum $ mp_tac o SRULE[Once elaborated_texp_cases] >>
    rw[]
  )
  >- (
    rw[EL_MAP,LIST_REL_EL_EQN] >>
    last_x_assum drule >>
    ntac 3 (pairarg_tac >> gvs[]) >>
    TOP_CASE_TAC
  )
  >~ [`Prim Seq [_;_]`]
  >- (
    pop_assum $ mp_tac o SRULE[Once elaborated_texp_cases] >>
    simp[]
  ) >>
  gvs[LIST_REL_EL_EQN] >>
  rw[] >>
  last_x_assum drule >>
  ntac 2 (pairarg_tac >> gvs[]) >>
  simp[GSYM PULL_EXISTS]
QED

Theorem elaborated_texp_wf:
  (∀e e'.
    elaborated_texp e e' ⇒
    texp_wf e ⇒ texp_wf e')
Proof
  ho_match_mp_tac elaborated_texp_ind >>
  gvs[texp_wf_def,EVERY_EL,LIST_REL3_EL,LIST_REL_EL_EQN,EL_MAP] >>
  rw[] >>
  gvs[MEM_FLAT,MEM_MAP] >>
  rw[] >>
  last_x_assum $ qspec_then `l` mp_tac >>
  simp[LAMBDA_PROD,GSYM PFORALL_THM] >>
  rw[] >>
  gvs[MEM_EL] >>
  disj1_tac >> rw[] >>
  strip_tac >>
  first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
  rw[] >>
  first_assum $ irule_at (Pos last) >>
  last_x_assum $ drule_then assume_tac >>
  qpat_x_assum `(_,_) = EL _ _` $ assume_tac o GSYM >>
  irule_at Any EQ_SYM >>
  simp[GSYM FST_EQ_EQUIV]
QED

Theorem type_elaborate_texp_freevars_texp:
  (∀lie db st env e e' t.
    pred_type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    freevars_texp e ⊆ set (MAP FST env)) ∧
  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    freevars_texp e ⊆ set (MAP FST env))
Proof
  ho_match_mp_tac type_elaborate_texp_ind >>
  simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >> rw[]
  >- (drule_then (irule_at Any) ALOOKUP_MEM >> simp[])
  >- gvs[LIST_REL3_EL,MEM_EL,SUBSET_INSERT_DELETE,DIFF_SUBSET]
  >- gvs[SUBSET_INSERT_DELETE,DIFF_SUBSET]
  >- gvs[SUBSET_INSERT_DELETE,DIFF_SUBSET,MAP_REVERSE,
    MAP_ZIP,LIST_REL_EL_EQN]
  >- (
    gvs[MAP_REVERSE,MAP_ZIP,MEM_MAP,LIST_REL3_EL,DIFF_SUBSET,LIST_REL3_EL] >>
    gvs[BIGUNION_SUBSET,MEM_MAP,LIST_TO_SET_MAP,PULL_EXISTS] >>
    `IMAGE (FST o FST) (set fns) = IMAGE (FST o FST) (set fns')`
    by (
      simp[GSYM LIST_TO_SET_MAP] >>
      AP_TERM_TAC >>
      irule LIST_EQ >>
      rw[EL_MAP] >>
      last_x_assum drule >>
      ntac 3 (pairarg_tac >> gvs[])
    ) >>
    rw[MEM_EL,PULL_EXISTS] >>
    last_x_assum drule >>
    ntac 3 (pairarg_tac >> gvs[])
  ) >>
  gvs[LIST_REL3_EL,MEM_EL,SUBSET_INSERT_DELETE,DIFF_SUBSET] >>
  gvs[DIFF_SUBSET,BIGUNION_SUBSET,MEM_MAP,PULL_EXISTS,
    GSYM SUBSET_INSERT_DELETE] >>
  rw[]
  >- (
    drule_then assume_tac type_cepat_cepat_vars >>
    gvs[MAP_REVERSE,MAP_MAP_o] >>
    irule SUBSET_TRANS >>
    last_x_assum $ irule_at (Pos hd) >>
    irule $ cj 1 EQ_SUBSET_SUBSET >>
    AP_THM_TAC >> AP_TERM_TAC >>
    first_x_assum $ assume_tac o GSYM >>
    simp[] >>
    AP_TERM_TAC >>
    irule LIST_EQ >>
    rw[EL_MAP] >>
    pairarg_tac >>
    simp[]
  ) >>
  gvs[LIST_REL_EL_EQN,MEM_EL] >>
  last_x_assum drule >>
  ntac 2 (pairarg_tac >> gvs[]) >>
  rw[MAP_REVERSE,MAP_MAP_o,DIFF_SUBSET] >>
  drule type_cepat_cepat_vars >>
  disch_then $ assume_tac o GSYM >>
  simp[] >>
  drule_then irule $ METIS_PROVE [] ``∀a b c. a ⊆ b ∧ b = c ⇒ a ⊆ c`` >>
  AP_THM_TAC >>
  ntac 2 AP_TERM_TAC >>
  irule LIST_EQ >>
  rw[EL_MAP] >>
  pairarg_tac >> simp[]
QED

Theorem elaborated_texp_freevars_texp:
  (∀e e'.
    elaborated_texp e e' ⇒
    freevars_texp e = freevars_texp e')
Proof
  ho_match_mp_tac elaborated_texp_ind >>
  gvs[freevars_texp_def] >>
  rw[]
  >- (
    ntac 2 AP_TERM_TAC >>
    irule LIST_EQ >>
    fs[LIST_REL_EL_EQN,EL_MAP]
  )
  >- (
    ntac 3 AP_TERM_TAC >>
    irule LIST_EQ >>
    fs[LIST_REL_EL_EQN,EL_MAP]
  )
  >- (
    MK_COMB_TAC
    >- (
      ntac 4 AP_TERM_TAC >>
      irule LIST_EQ >>
      gvs[LIST_REL_EL_EQN,EL_MAP] >>
      rw[] >>
      qpat_x_assum `!n. _ ⇒ freevars_texp _ = freevars_texp _` drule >>
      ntac 2 (pairarg_tac >> gvs[])
    ) >>
    AP_TERM_TAC >>
    irule LIST_EQ >>
    gvs[EL_MAP]
  )
  >- (
    AP_TERM_TAC >>
    AP_THM_TAC >>
    ntac 4 AP_TERM_TAC >>
    irule LIST_EQ >>
    gvs[LIST_REL_EL_EQN,EL_MAP] >>
    rw[] >>
    rpt (last_x_assum drule) >>
    ntac 2 (pairarg_tac >> gvs[])
  )
QED

Theorem has_dict_weaken:
  lie ⊆ lie' ⇒
  (∀p.has_dict tdefs db ie lie p ⇒ has_dict tdefs (db ++ db') ie lie' p) ∧
  (∀ps. has_dicts tdefs db ie lie ps ⇒ has_dicts tdefs (db ++ db') ie lie' ps)
Proof
  strip_tac >>
  ho_match_mp_tac has_dict_ind >>
  rw[] >> rw[Once has_dict_cases]
  >- fs[SUBSET_DEF] >>
  disj2_tac >>
  first_assum $ irule_at (Pos last) >>
  first_assum $ irule_at (Pos hd) >>
  qpat_x_assum `specialises_inst _ _ _` mp_tac >>
  gvs[oneline specialises_inst_def] >>
  TOP_CASE_TAC >>
  rw[] >>
  first_assum $ irule_at (Pos $ el 2) >>
  gvs[LIST_REL_EL_EQN] >>
  rw[] >>
  irule kind_ok_APPEND >>
  metis_tac[]
QED

Theorem type_cons_db_APPEND:
  type_cons tds db c t ⇒
  type_cons tds (db ++ db') c t
Proof
  simp[oneline type_cons_def] >>
  rpt TOP_CASE_TAC >>
  rw[] >>
  fs[LIST_REL_EL_EQN] >>
  metis_tac[kind_ok_APPEND]
QED

Theorem destruct_type_cons_db_APPEND:
  destruct_type_cons ns db t c ts ⇒
  destruct_type_cons ns (db ++ db') t c ts
Proof
  rw[oneline destruct_type_cons_def] >>
  every_case_tac >> gvs[] >>
  every_case_tac >>
  metis_tac[type_cons_db_APPEND]
QED

Theorem type_cepat_db_APPEND:
  ∀p t vts.
    type_cepat ns db p t vts ⇒
    type_cepat ns (db ++ db') p t vts
Proof
  ho_match_mp_tac type_cepat_ind >>
  rw[] >>
  simp[Once type_cepat_cases] >>
  fs[SF ETA_ss] >>
  metis_tac[destruct_type_cons_db_APPEND]
QED

Theorem type_elaborate_texp_weaken:
  (∀lie db st env e e' t.
    pred_type_elaborate_texp ns clk ie lie db st env e e' t
  ⇒ ∀lie' db' st' env'. lie ⊆ lie' ∧
    (∀fname fty. fname ∈ freevars_texp e ∧
      ALOOKUP env fname = SOME fty ⇒ ALOOKUP env' fname = SOME fty)
  ⇒ pred_type_elaborate_texp ns clk ie lie'
      (db ++ db') (st ++ st') env' e e' t) ∧
  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t
  ⇒ ∀lie' db' st' env'. lie ⊆ lie' ∧
    (∀fname fty. fname ∈ freevars_texp e ∧
      ALOOKUP env fname = SOME fty ⇒ ALOOKUP env' fname = SOME fty)
  ⇒ type_elaborate_texp ns clk ie lie'
      (db ++ db') (st ++ st') env' e e' t)
Proof
  ho_match_mp_tac type_elaborate_texp_ind >>
  rw[] >> rw[Once type_elaborate_texp_cases] >>
  gvs[DISJ_IMP_THM,FORALL_AND_THM,RIGHT_AND_OVER_OR]
  >- (
    gvs[oneline specialises_pred_def,LIST_REL_EL_EQN,pair_CASE_def] >>
    first_assum $ irule_at (Pos last) >>
    metis_tac[kind_ok_APPEND]
  )
  >- metis_tac[has_dict_weaken]
  >- metis_tac[SUBSET_TRANS,SUBSET_UNION]
  >- (
    gvs[pred_type_kind_ok_alt] >>
    rw[] >>
    metis_tac[kind_ok_APPEND]
  )
  >- (
    first_x_assum $ irule_at (Pos hd) >>
    gvs[LIST_REL3_EL,MEM_MAP] >>
    rw[] >>
    first_x_assum irule >>
    rw[] >>
    first_x_assum $ drule_at_then (Pos last) irule >>
    first_assum $ irule_at (Pos hd) >>
    metis_tac[MEM_EL]
  )
  >- (
    first_x_assum irule >>
    rw[ALOOKUP_MAP] >>
    metis_tac[]
  )
  >- (
    first_assum $ drule_then (irule_at (Pos hd)) >>
    rw[]
  )
  >- (
    irule_at (Pos hd) EQ_REFL >>
    gvs[lambdify type_ok_def,EVERY_MEM] >>
    first_x_assum $ irule_at (Pos last) >>
    rw[ALOOKUP_APPEND]
    >- (
      TOP_CASE_TAC >> gvs[] >>
      first_x_assum $ drule_at_then (Pos last) irule >>
      gvs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP,LIST_REL_EL_EQN]
    ) >>
    metis_tac[kind_ok_APPEND]
  )
  >- (
    first_x_assum $ irule_at (Pos last) >>
    gvs[LIST_REL3_EL,ALOOKUP_APPEND] >>
    qexists `kind_schemes` >>
    rw[]
    >- (
      TOP_CASE_TAC >> gvs[] >>
      first_x_assum $ drule_then irule >>
      gvs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
      gvs[MEM_MAP] >>
      gvs[MEM_EL,LIST_REL3_EL] >>
      rw[] >>
      strip_tac >>
      first_x_assum drule >>
      strip_tac >>
      ntac 3 (pairarg_tac >> gvs[])
    ) >>
    ntac 3 (pairarg_tac >> gvs[]) >>
    qpat_x_assum `!n. n < LENGTH fns ⇒ _` $
        markerLib.ASSUME_NAMED_TAC "LIST_REL3_ASM" >>
    markerLib.LABEL_ASSUM "LIST_REL3_ASM" drule >>
    gvs[] >>
    rw[] >>
    first_x_assum irule >>
    rw[ALOOKUP_APPEND,ALOOKUP_MAP] >>
    TOP_CASE_TAC >> gvs[] >>
    irule_at (Pos last) EQ_REFL >>
    first_x_assum $ drule_at_then (Pos last) irule >>
    gvs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP,LIST_REL3_EL] >>
    first_x_assum $ irule_at (Pos hd) >>
    gvs[MEM_MAP] >>
    conj_tac
    >- (
      gvs[MEM_EL,PULL_EXISTS] >>
      first_x_assum $ irule_at (Pos last) >>
      gvs[]
    ) >>
    gvs[MEM_EL] >>
    rw[] >>
    strip_tac >>
    markerLib.LABEL_ASSUM "LIST_REL3_ASM" drule >>
    strip_tac >>
    ntac 3 (pairarg_tac >> gvs[])
  )
  >- (
    disj1_tac >>
    drule_then (irule_at (Pos $ el 2)) type_cons_db_APPEND >>
    gvs[LIST_REL3_EL] >>
    rw[] >>
    first_x_assum irule >>
    rw[] >>
    first_x_assum $ drule_at_then (Pos last) irule >>
    gvs[MEM_MAP,MEM_EL] >>
    metis_tac[]
  )
  >- (
    disj2_tac >> disj1_tac >>
    irule_at (Pos last) EQ_REFL >>
    gvs[LIST_REL3_EL] >>
    rw[] >>
    first_x_assum irule >>
    rw[] >>
    first_x_assum $ drule_at_then (Pos last) irule >>
    gvs[MEM_MAP,MEM_EL] >>
    metis_tac[]
  )
  >- (
    disj2_tac >>
    first_x_assum $ irule_at (Pos last) >>
    first_x_assum $ irule_at (Pos last) >>
    gvs[]
  )
  >- (
    gvs[type_ok_def,LIST_REL3_EL] >>
    metis_tac[kind_ok_APPEND]
  )
  >- (disj2_tac >> metis_tac[])
  >- (
    disj2_tac >>
    first_x_assum $ irule_at (Pos last) >>
    first_x_assum $ irule_at (Pos last) >>
    metis_tac[]
  )
  >- (
    disj2_tac >> disj2_tac >>
    gvs[LIST_REL3_EL] >>
    first_x_assum $ irule_at (Pos last) >>
    gvs[] >>
    rw[] >>
    first_x_assum irule >>
    rw[] >>
    first_x_assum $ drule_at_then (Pos last) irule >>
    metis_tac[MEM_MAP,MEM_EL]
  )
  >- gvs[oEL_THM,EL_APPEND_EQN]
  >- (
    first_x_assum $ irule_at (Pos $ el 2) >>
    gvs[LIST_REL3_EL] >>
    rw[] >>
    first_x_assum irule >>
    rw[] >>
    first_x_assum $ drule_at_then (Pos last) irule >>
    metis_tac[MEM_MAP,MEM_EL]
  )
  >- (
    first_x_assum irule >>
    gvs[ALOOKUP_MAP] >>
    metis_tac[]
  )
  >- (
    first_assum $ irule_at (Pos hd) >>
    drule_then (irule_at (Pat `type_cepat _ _ _ _ _`))
      type_cepat_db_APPEND >>
    rw[]
    >- (
      last_x_assum irule >>
      rw[ALOOKUP_APPEND] >>
      TOP_CASE_TAC >>
      gvs[] >>
      first_x_assum drule >>
      disch_then irule >>
      simp[] >>
      strip_tac >>
      drule type_cepat_cepat_vars >>
      strip_tac >>
      gvs[LIST_TO_SET_MAP] >>
      pop_assum $ assume_tac o GSYM >>
      fs[ALOOKUP_NONE,MAP_REVERSE,MAP_MAP_o] >>
      fs[MEM_MAP] >>
      qpat_x_assum `MEM _ vts` mp_tac >>
      simp[] >>
      first_x_assum irule >>
      simp[ELIM_UNCURRY]
    ) >>
    gvs[LIST_REL_EL_EQN] >>
    rw[] >>
    first_x_assum drule >>
    ntac 2 (pairarg_tac >> gvs[]) >>
    rw[] >>
    PURE_REWRITE_TAC[Once $ cj 2 $ GSYM APPEND] >>
    drule_then (irule_at Any) type_cepat_db_APPEND >>
    first_x_assum irule >>
    rw[ALOOKUP_APPEND] >>
    TOP_CASE_TAC >>
    gvs[] >>
    first_x_assum irule >>
    rw[PULL_EXISTS,MEM_MAP,MEM_EL] >>
    first_x_assum $ irule_at (Pos last) >>
    simp[] >>
    strip_tac >>
    drule type_cepat_cepat_vars >>
    strip_tac >>
    gvs[LIST_TO_SET_MAP] >>
    pop_assum $ assume_tac o GSYM >>
    gvs[ALOOKUP_NONE,MAP_REVERSE,MAP_MAP_o,MEM_MAP] >>
    qpat_x_assum `MEM _ _` mp_tac >>
    simp[] >>
    first_x_assum irule >>
    simp[ELIM_UNCURRY]
  )
QED

Theorem type_elaborate_texp_env_extensional:
  (∀lie db st env e e' t.
    pred_type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    ∀env'. (∀x. x ∈ freevars_texp e ⇒ ALOOKUP env x = ALOOKUP env' x)
  ⇒ pred_type_elaborate_texp ns clk ie lie db st env' e e' t) ∧
  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    ∀env'. (∀x. x ∈ freevars_texp e ⇒ ALOOKUP env x = ALOOKUP env' x)
  ⇒ type_elaborate_texp ns clk ie lie db st env' e e' t)
Proof
  rw[]
  >- (
    drule $ cj 1 type_elaborate_texp_weaken >>
    disch_then $ resolve_then (Pos hd) assume_tac SUBSET_REFL >>
    first_x_assum $ qspecl_then [`[]`,`env'`,`[]`] $ irule o SRULE[] >>
    rw[] >>
    first_x_assum $ drule_then strip_assume_tac >>
    gvs[]
  ) >>
  drule $ cj 2 type_elaborate_texp_weaken >>
  disch_then $ resolve_then (Pos hd) assume_tac SUBSET_REFL >>
  first_x_assum $ qspecl_then [`[]`,`env'`,`[]`] $ irule o SRULE[] >>
  rw[] >>
  first_x_assum $ drule_then strip_assume_tac >>
  gvs[]
QED

Theorem type_elaborate_texp_weaken_APPEND_env:
  (∀lie db st env e e' t.
    pred_type_elaborate_texp ns clk ie lie db st env e e' t
  ⇒ ∀lie' db' st' env'. lie ⊆ lie'
  ⇒ pred_type_elaborate_texp ns clk ie lie'
      (db ++ db') (st ++ st') (env ++ env') e e' t) ∧
  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t
  ⇒ ∀lie' db' st' env'. lie ⊆ lie'
  ⇒ type_elaborate_texp ns clk ie lie'
      (db ++ db') (st ++ st') (env ++ env') e e' t)
Proof
  rw[]
  >- (
    drule_then irule $ cj 1 type_elaborate_texp_weaken >>
    rw[ALOOKUP_APPEND]
  ) >>
  drule_then irule $ cj 2 type_elaborate_texp_weaken >>
  rw[ALOOKUP_APPEND]
QED

val _ = export_theory();
