open HolKernel Parse boolLib bossLib BasicProvers;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory;
open mlstringTheory pure_configTheory;
open typeclass_typesTheory;

val _ = new_theory "typeclass_typesProps";

Theorem type_ind:
  ∀P.
    (P (Atom Exception)) ∧
    (∀s. P (Atom (TypeCons s))) ∧
    (∀n. P (Atom (VarTypeCons n))) ∧
    (∀t t'. P t ∧ P t' ⇒ P (Cons t t')) ⇒
    (∀t. P t)
Proof
  ntac 2 strip_tac >>
  ho_match_mp_tac type_induction >>
  rw[] >>
  Cases_on `a` >>
  simp[]
QED

Theorem type_full_induction:
  ∀P.
    (P (Atom Exception)) ∧
    (∀n. P (UserType n)) ∧
    (∀c. P (Atom (CompPrimTy c))) ∧
    (∀p. P (Atom (PrimTy p))) ∧
    (∀n. P (Atom (VarTypeCons n))) ∧
    (∀t t'. P t ∧ P t' ⇒ P (Cons t t')) ⇒
    (∀t. P t)
Proof
  ntac 2 strip_tac >>
  ho_match_mp_tac type_ind >>
  rw[] >>
  Cases_on `s` >>
  simp[] >>
  Cases_on `y` >>
  simp[]
QED

Theorem type_size_GT_0[simp]:
  ∀t. 0 < type_size t
Proof
  Cases_on `t` >>
  simp[type_size_def]
QED

(******************** Functions ********************)

Theorem Functions_APPEND:
  ∀as bs a.
    Functions (as ++ bs) a = Functions as (Functions bs a)
Proof
  Induct >> rw[Functions_def]
QED

Theorem Functions_eq_imp:
  ∀as a bs b.
    Functions as a = Functions bs b ⇒
    ∃cs.
      (as = bs ++ cs ∧ b = Functions cs a) ∨
      (bs = as ++ cs ∧ a = Functions cs b)
Proof
  Induct >> rw[Functions_def] >> csimp[Functions_def]
  >- (qexists_tac `bs` >> simp[]) >>
  Cases_on `bs` >> gvs[Functions_def]
QED

Theorem collect_type_vars_Functions:
  collect_type_vars (Functions args ret) =
    BIGUNION (set (MAP collect_type_vars args)) ∪ collect_type_vars ret
Proof
  Induct_on `args` >>
  rw[Functions_def,collect_type_vars_def] >>
  metis_tac[pred_setTheory.UNION_COMM,
    pred_setTheory.UNION_ASSOC]
QED

(******************** Substitutions and shifts ********************)

Theorem shift_db_0[simp]:
  ∀skip. shift_db skip 0 = I
Proof
  simp[FUN_EQ_THM] >>
  Induct_on `x` using type_ind >>
  rw[shift_db_def]
QED

Theorem subst_db_NIL[simp]:
  ∀n. subst_db n [] = I
Proof
  simp[FUN_EQ_THM] >>
  Induct_on `x` using type_ind >>
  rw[subst_db_def]
QED

Theorem subst_db_unchanged:
  ∀skip ts t n.
    freetyvars_ok n t ∧
    n ≤ skip
  ⇒ subst_db skip ts t = t
Proof
  Induct_on `t` using type_ind >>
  rw[subst_db_def,freetyvars_ok_def] >>
  metis_tac[]
QED

Theorem shift_db_unchanged:
  ∀skip shift t n.
    freetyvars_ok n t ∧
    n ≤ skip
  ⇒ shift_db skip shift t = t
Proof
  Induct_on `t` using type_ind >>
  rw[shift_db_def,freetyvars_ok_def] >>
  metis_tac[]
QED

Theorem subst_db_shift_db_unchanged:
  ∀skip shift t ts m.
    (m - skip) + LENGTH ts ≤ shift ∧
    skip ≤ m
  ⇒ subst_db m ts (shift_db skip shift t) =
    shift_db skip (shift - LENGTH ts) t
Proof
  Induct_on `t` using type_ind >>
  rw[subst_db_def, shift_db_def]
QED

Theorem tsubst_tshift:
  ∀shift t ts m.
    LENGTH ts ≤ shift
  ⇒ tsubst ts (tshift shift t) =
    tshift (shift - LENGTH ts) t
Proof
  rw[] >> irule subst_db_shift_db_unchanged >> simp[]
QED

Theorem subst_db_subst_db:
  ∀n tsn t m tsm.
    n ≤ m
  ⇒ subst_db m tsm (subst_db n tsn t) =
    subst_db n (MAP (subst_db m tsm) tsn)
      (subst_db (m + LENGTH tsn) (MAP (shift_db n (LENGTH tsn)) tsm) t)
Proof
  Induct_on `t` using type_ind >>
  rw[subst_db_def, EL_MAP] >>
  gvs[subst_db_shift_db_unchanged]
QED

Theorem shift_db_shift_db:
  ∀m shiftm t n shiftn.
    n ≤ m
  ⇒ shift_db (m + shiftn) shiftm (shift_db n shiftn t) =
    shift_db n shiftn (shift_db m shiftm t)
Proof
  recInduct shift_db_ind >> rw[shift_db_def]
QED

Theorem shift_db_twice:
  ∀k m ty n. shift_db k n (shift_db k m ty) = shift_db k (n + m) ty
Proof
  recInduct shift_db_ind >> rw[shift_db_def]
QED

Theorem tshift_tshift:
  ∀t s1 s2.
    tshift s1 (tshift s2 t) = tshift (s1 + s2) t
Proof
  rw[shift_db_twice]
QED

Theorem subst_db_shift_db_1:
  ∀n ts t m shift.
    m ≤ n
  ⇒ subst_db (n + shift) (MAP (shift_db m shift) ts) (shift_db m shift t) =
    shift_db m shift (subst_db n ts t)
Proof
  recInduct subst_db_ind >> rw[shift_db_def, subst_db_def, EL_MAP]
QED

Theorem subst_db_shift_db_2:
  ∀n ts t m shift.
    n ≤ m
  ⇒ subst_db n (MAP (shift_db m shift) ts) (shift_db (m + LENGTH ts) shift t) =
    shift_db m shift (subst_db n ts t)
Proof
  recInduct subst_db_ind >> rw[shift_db_def, subst_db_def, EL_MAP]
QED

(************ tcons_to_type and split_ty_head ************)
Theorem tcons_to_type_alt:
  (∀tcons. tcons_to_type tcons [] = Atom $ TypeCons tcons) ∧
  (∀tcons t1 targs.
    tcons_to_type tcons (t1::targs) =
      cons_types (Cons (Atom $ TypeCons tcons) t1) targs)
Proof
  rw[tcons_to_type_def] >>
  simp[Once cons_types_def]
QED

Theorem cons_types_APPEND:
   ∀t ts1 ts2.
     cons_types t (ts1 ++ ts2) = cons_types (cons_types t ts1) ts2
Proof
  Induct_on `ts1` >>
  rw[cons_types_def]
QED

Theorem cons_types_APPEND_SINGLE:
  ∀t ts1 t2. cons_types t (ts1 ++ [t2]) = Cons (cons_types t ts1) t2
Proof
  simp[cons_types_APPEND,cons_types_def]
QED

Theorem cons_types_SNOC:
  ∀t ts1 t2. cons_types t (SNOC t2 ts1) = Cons (cons_types t ts1) t2
Proof
  simp[cons_types_APPEND_SINGLE,SNOC_APPEND]
QED

Theorem tcons_to_type_APPEND:
  tcons_to_type tcons (ts1 ++ ts2) = cons_types (tcons_to_type tcons ts1) ts2
Proof
  simp[tcons_to_type_def,cons_types_APPEND]
QED

Theorem tcons_to_type_SNOC:
  tcons_to_type tcons (SNOC t ts1) = Cons (tcons_to_type tcons ts1) t
Proof
  simp[tcons_to_type_APPEND,SNOC_APPEND,cons_types_def]
QED

Theorem type_size_cons_types:
  (∀t targs. type_size (cons_types t []) = type_size t) ∧
  (∀t t' targs. type_size t <
    type_size (cons_types t (t'::targs))) ∧
  (∀t t' targs.
    MEM t targs ⇒
    type_size t < type_size (cons_types t' targs))
Proof
  conj_tac >- simp[cons_types_def] >>
  conj_tac >- (
    Induct_on `targs` >>
    fs[cons_types_def,type_size_def] >>
    rw[] >>
    irule LESS_EQ_LESS_TRANS >>
    first_x_assum $ irule_at (Pos hd) >>
    simp[type_size_def]) >>
  Induct_on `targs` using SNOC_INDUCT >>
  rw[cons_types_SNOC,type_size_def]
  >- rw[] >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
  first_x_assum $ drule_then $ irule_at (Pos hd) >>
  qexists_tac `t'` >>
  DECIDE_TAC
QED

Theorem cons_types_NEQ_Atom:
  cons_types (Cons t t') ts ≠ Atom a
Proof
  Induct_on `ts` using SNOC_INDUCT >>
  simp[cons_types_SNOC,cons_types_def]
QED

Theorem cons_types_EQ_Atom:
  cons_types t ts = Atom a ⇔ (ts = [] ∧ t = Atom a)
Proof
  simp[cons_types_def,EQ_IMP_THM] >>
  Cases_on `ts` >>
  simp[cons_types_def,cons_types_NEQ_Atom]
QED

Theorem Functions_cons_types:
  (∀t. Functions [] t = t) ∧
  (∀at ats t.
    Functions (at::ats) t =
    cons_types
      (Atom $ CompPrimTy Function)
      [at;Functions ats t])
Proof
  simp[Functions_def,cons_types_def]
QED

Theorem cons_types_Atom_EQ:
  ∀a a' ts ts'.
    (cons_types (Atom a) ts = cons_types (Atom a') ts') ⇔
    (a = a' ∧ ts = ts')
Proof
  simp[cons_types_def,EQ_IMP_THM] >>
  Induct_on `ts` using SNOC_INDUCT >>
  gvs[cons_types_def,cons_types_EQ_Atom,cons_types_SNOC] >>
  Cases_on `ts'` using SNOC_CASES >>
  gvs[cons_types_def,cons_types_EQ_Atom,cons_types_SNOC] >>
  metis_tac[]
QED

Theorem type_size_tcons_to_type:
  ∀t targs tcons.
  MEM t targs ⇒
  type_size t < type_size (tcons_to_type tcons targs)
Proof
  rw[tcons_to_type_def,type_size_cons_types]
QED

Theorem tcons_to_type_NEQ_TypeVar:
  ∀v tcons targs. tcons_to_type tcons targs ≠ TypeVar v
Proof
  simp[tcons_to_type_def] >>
  Cases_on `targs` using SNOC_CASES >>
  simp[cons_types_def,cons_types_SNOC]
QED

Theorem ty_args_aux_SNOC:
  ∀t t1 t2 l. t = Cons t1 t2 ⇒ ty_args_aux t l = ty_args_aux t1 [] ++ (t2::l)
Proof
  Induct_on `t` >>
  rw[] >>
  Cases_on `t` >>
  gvs[ty_args_aux_def]
QED

Theorem ty_args_SNOC:
  ty_args (Cons t1 t2) = SNOC t2 (ty_args t1)
Proof
  simp[ty_args_def,ty_args_aux_SNOC]
QED

Theorem ty_args_alt:
  (∀t1 t2. ty_args (Cons t1 t2) = SNOC t2 (ty_args t1)) ∧
  (∀x. ty_args (Atom x) = [])
Proof
  simp[ty_args_SNOC] >> simp[ty_args_def,ty_args_aux_def]
QED

Theorem head_ty_cons_eq_head_ty:
  ∀t c. (head_ty_cons t = SOME c) ⇔ (head_ty t = TypeCons c)
Proof
  Induct_on `t` using type_ind >>
  simp[head_ty_cons_def,head_ty_def]
QED

Theorem split_ty_cons_aux_eq_split_ty_aux:
  ∀t l c targs.
    (split_ty_cons_aux t l = SOME (c,targs)) ⇔
    (split_ty_aux t l = (TypeCons c,targs))
Proof
  Induct_on `t` using type_ind >>
  simp[split_ty_cons_aux_def,split_ty_aux_def]
QED

Theorem split_ty_cons_eq_split_ty:
  ∀t c targs.
    (split_ty_cons t = SOME (c,targs)) ⇔
    (split_ty t = (TypeCons c,targs))
Proof
  simp[split_ty_cons_def,split_ty_def,
    split_ty_cons_aux_eq_split_ty_aux]
QED

Theorem split_ty_aux_thm:
  ∀t l c targs.
    split_ty_aux t l = (c,targs) ⇔
    (head_ty t = c ∧ ty_args_aux t l = targs)
Proof
  Induct_on `t` using type_ind >>
  rw[split_ty_aux_def,head_ty_def,ty_args_aux_def]
QED

Theorem split_ty_thm:
  ∀t c targs.
    split_ty t = (c,targs) ⇔
    (head_ty t = c ∧ ty_args t = targs)
Proof
  simp[split_ty_def,ty_args_def,split_ty_aux_thm]
QED

Theorem split_ty_cons_aux_thm:
  ∀t l tc targs.
    split_ty_cons_aux t l = SOME (tc,targs) ⇔
    (head_ty_cons t = SOME tc ∧ ty_args_aux t l = targs)
Proof
  rw[split_ty_cons_aux_eq_split_ty_aux,
    head_ty_cons_eq_head_ty,split_ty_aux_thm]
QED

Theorem split_ty_cons_thm:
  ∀t tc targs.
    split_ty_cons t = SOME (tc,targs) ⇔
    (head_ty_cons t = SOME tc ∧ ty_args t = targs)
Proof
  simp[split_ty_cons_eq_split_ty,head_ty_cons_eq_head_ty,
    split_ty_thm]
QED

Theorem head_ty_cons_types:
  ∀t targs. head_ty (cons_types t targs) = head_ty t
Proof
  Induct_on `targs` >>
  rw[head_ty_def,cons_types_def]
QED

Theorem head_ty_cons_cons_types:
  ∀t targs. head_ty_cons (cons_types t targs) = head_ty_cons t
Proof
  Induct_on `targs` >>
  rw[head_ty_cons_def,cons_types_def]
QED

Theorem ty_args_cons_types:
  ∀t targs. ty_args (cons_types t targs) = ty_args t ++ targs
Proof
  Induct_on `targs` >>
  rw[cons_types_def,ty_args_alt]
QED

Theorem split_ty_cons_types:
  ∀at targs. split_ty (cons_types (Atom at) targs) = (at, targs)
Proof
  Induct_on `targs` using SNOC_INDUCT >>
  fs[cons_types_def,split_ty_thm] >>
  rw[head_ty_def,ty_args_alt,cons_types_def,
    SNOC_APPEND,cons_types_APPEND]
QED

Theorem split_ty_cons_tcons_to_type:
  split_ty_cons (tcons_to_type tcons targs) = SOME (tcons, targs)
Proof
  simp[split_ty_cons_eq_split_ty,tcons_to_type_def,
    split_ty_cons_types]
QED

Theorem cons_types_head_ty_ty_args:
  cons_types (Atom $ head_ty t) (ty_args t) = t
Proof
  Induct_on `t` using type_ind >>
  fs[cons_types_def,cons_types_SNOC,
    head_ty_def,ty_args_alt]
QED

Theorem tcons_to_type_split_ty_cons:
  ∀t tcons targs.
    split_ty_cons t = SOME (tcons,targs) ⇒
    tcons_to_type tcons targs = t
Proof
  rw[split_ty_cons_thm,tcons_to_type_def,
    head_ty_cons_eq_head_ty] >>
  metis_tac[cons_types_head_ty_ty_args]
QED

Theorem subst_db_cons_types:
  ∀n ts thd targs.
    subst_db n ts (cons_types thd targs) =
    cons_types (subst_db n ts thd) $ MAP (subst_db n ts) targs
Proof
  Induct_on `targs` >>
  rw[cons_types_def,subst_db_def]
QED

Theorem subst_db_tcons_to_type:
  ∀skip ts tcons targs.
  subst_db skip ts (tcons_to_type tcons targs) =
    tcons_to_type tcons $ MAP (subst_db skip ts) targs
Proof
  rw[tcons_to_type_def,subst_db_cons_types,subst_db_def]
QED

Theorem shift_db_cons_types:
  ∀skip n thd targs.
    shift_db skip n (cons_types thd targs) =
    cons_types (shift_db skip n thd) $ MAP (shift_db skip n) targs
Proof
  Induct_on `targs` >>
  rw[cons_types_def,shift_db_def]
QED

Theorem shift_db_tcons_to_type:
  ∀skip n tcons targs.
  shift_db skip n (tcons_to_type tcons targs) =
    tcons_to_type tcons $ MAP (shift_db skip n) targs
Proof
  rw[tcons_to_type_def,shift_db_cons_types,shift_db_def]
QED

Theorem subst_db_head_ty:
  ∀skip ts t.
  head_ty (subst_db skip ts t) =
  case head_ty t of
  | VarTypeCons v =>
      if skip ≤ v ∧ v < skip + LENGTH ts
        then head_ty (EL (v - skip) ts)
      else if skip ≤ v
        then VarTypeCons (v - LENGTH ts)
      else VarTypeCons v
  | a => a
Proof
  ho_match_mp_tac subst_db_ind >>
  rw[subst_db_def,head_ty_def]
QED

Theorem subst_db_ty_args:
  ∀skip ts t.
  ty_args (subst_db skip ts t) =
  case head_ty t of
  | VarTypeCons v =>
      if skip ≤ v ∧ v < skip + LENGTH ts
      then ty_args (EL (v - skip) ts) ++
        MAP (subst_db skip ts) (ty_args t)
      else MAP (subst_db skip ts) (ty_args t)
  | a => MAP (subst_db skip ts) (ty_args t)
Proof
  ho_match_mp_tac subst_db_ind >>
  rw[subst_db_def,ty_args_alt,head_ty_def] >>
  TOP_CASE_TAC >>
  IF_CASES_TAC >>
  rw[]
QED

Theorem shift_db_head_ty:
  ∀skip n t.
  head_ty (shift_db skip n t) =
  case head_ty t of
  | VarTypeCons v =>
      if skip ≤ v
      then VarTypeCons (v + n)
      else VarTypeCons v
  | a => a
Proof
  ho_match_mp_tac shift_db_ind >>
  rw[shift_db_def,head_ty_def]
QED

Theorem shift_db_ty_args:
  ∀skip n t.
  ty_args (shift_db skip n t) =
    MAP (shift_db skip n) (ty_args t)
Proof
  ho_match_mp_tac shift_db_ind >>
  rw[shift_db_def,ty_args_alt]
QED

(******************** Properties of types ********************)

Theorem freetyvars_ok_mono:
  ∀n t m.
    freetyvars_ok n t ∧
    n ≤ m
  ⇒ freetyvars_ok m t
Proof
  recInduct freetyvars_ok_ind >> rw[freetyvars_ok_def]
QED

Theorem freetyvars_ok_subst_db:
  ∀skip ts t n.
    freetyvars_ok (n + LENGTH ts) t ∧
    EVERY (freetyvars_ok n) ts ∧
    skip ≤ n
  ⇒ freetyvars_ok n (subst_db skip ts t)
Proof
  recInduct subst_db_ind >>
  rw[subst_db_def, freetyvars_ok_def] >>
  gvs[EVERY_MEM, MEM_EL, PULL_EXISTS]
QED

Theorem freetyvars_ok_tsubst:
  ∀ts t n.
    freetyvars_ok (n + LENGTH ts) t ∧
    EVERY (freetyvars_ok n) ts
  ⇒ freetyvars_ok n (tsubst ts t)
Proof
  rw[] >> irule freetyvars_ok_subst_db >> simp[]
QED

Theorem freetyvars_ok_shift_db:
  ∀skip shift t n.
    freetyvars_ok n t
  ⇒ freetyvars_ok (n + shift) (shift_db skip shift t)
Proof
  recInduct shift_db_ind >>
  rw[shift_db_def, freetyvars_ok_def]
QED

Theorem freetyvars_ok_Functions:
  ∀ats rt db.
    freetyvars_ok db (Functions ats rt) ⇔
    EVERY (freetyvars_ok db) ats ∧
    freetyvars_ok db rt
Proof
  Induct >> rw[Functions_def, freetyvars_ok_def] >> eq_tac >> rw[]
QED

Theorem subst_db_Functions:
  ∀ats rt n ts.
    subst_db n ts (Functions ats rt) =
    Functions (MAP (subst_db n ts) ats) (subst_db n ts rt)
Proof
  Induct >> rw[Functions_def, subst_db_def]
QED

Theorem shift_db_Functions:
  ∀ats rt skip shift.
    shift_db skip shift (Functions ats rt) =
    Functions (MAP (shift_db skip shift) ats) (shift_db skip shift rt)
Proof
  Induct >> rw[Functions_def, shift_db_def]
QED

val _ = export_theory();
