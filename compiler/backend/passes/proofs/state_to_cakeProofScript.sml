(*
  Correctness for compilation from stateLang to CakeML
*)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     rich_listTheory arithmeticTheory pred_setTheory intLib;
open semanticPrimitivesTheory namespaceTheory namespacePropsTheory primSemEnvTheory
     itree_semanticsTheory itree_semanticsPropsTheory;
open pure_miscTheory pure_configTheory pure_typingTheory
     stateLangTheory state_cexpTheory state_to_cakeTheory;

val _ = intLib.deprecate_int();

val _ = new_theory "state_to_cakeProof";

val _ = set_grammar_ancestry ["state_to_cake", "stateLang", "itree_semanticsProps"]


(* TODO move *)
Theorem ALOOKUP_MAP_MAP:
  (∀x y. f x = f y ⇒ x = y) ⇒
  ALOOKUP (MAP (λ(a,b). (f a, g b)) l) (f x) =
  ALOOKUP (MAP (λ(a,b). (a, g b)) l) x
Proof
  Induct_on `l` >> rw[] >> PairCases_on `h` >> rw[] >> gvs[]
QED

Theorem OPTREL[simp]:
  (∀R x y. OPTREL R (SOME x) y ⇔ ∃z. y = SOME z ∧ R x z) ∧
  (∀R x y. OPTREL R x (SOME y) ⇔ ∃z. x = SOME z ∧ R z y) ∧
  (∀R y.   OPTREL R NONE y ⇔ y = NONE) ∧
  (∀R x.   OPTREL R x NONE ⇔ x = NONE)
Proof
  simp[OPTREL_SOME] >> rw[OPTREL_def]
QED

Theorem string_le_def[simp]:
  string_le [] s2 = T ∧
  string_le (c1::s1) [] = F ∧
  string_le (c1::s1) (c2::s2) =
    if c1 < c2 then T else
    if c1 = c2 then string_le s1 s2
    else F
Proof
  rw[] >> simp[string_le_def, string_lt_def, char_lt_def]
  >- (Cases_on `s2` >> rw[string_lt_def])
  >- (eq_tac >> rw[] >> simp[])
QED

Theorem char_lt_irreflexive[simp]:
  ∀c. ¬char_lt c c
Proof
  rw[char_lt_def]
QED

Theorem char_lt_flip:
  char_lt c1 c2 ∨ c1 = c2 ⇔ ¬char_lt c2 c1
Proof
  rw[char_lt_def, NOT_LESS, LESS_OR_EQ] >> eq_tac >> rw[] >> gvs[ORD_11]
QED

Theorem string_gt_le:
  ∀s1 s2. string_gt s1 s2 ⇔ ¬string_le s1 s2
Proof
  simp[string_gt_def] >>
  Induct >> rw[] >> Cases_on `s2` >> gvs[string_lt_def] >>
  eq_tac >> rw[] >> gvs[] >> metis_tac[char_lt_flip]
QED


(******************** Itree semantics functions/lemmas ********************)

Definition get_ffi_array_def[simp]:
  get_ffi_array (Estep (cenv, cst, ev, ck)) = (
    case store_lookup 0 cst of
    | SOME (W8array ws) => SOME ws
    | _ => NONE) ∧
  get_ffi_array (Effi s conf ws n cenv cst ck) = SOME ws ∧
  get_ffi_array _ = NONE
End

Definition dget_ffi_array_def[simp]:
  dget_ffi_array (Dstep dst _ _) = (
    case store_lookup 0 dst.refs of
    | SOME (W8array ws) => SOME ws
    | _ => NONE) ∧
  dget_ffi_array (Dffi dst (s,conf,ws,n,cenv,cs) locs pat dcs) = SOME ws ∧
  dget_ffi_array _ = NONE
End

Definition cstep_n_def:
  cstep_n 0 e = e ∧
  cstep_n (SUC n) (Estep st) = cstep_n n (estep st) ∧
  cstep_n _ e = e
End

Theorem cstep_n_alt:
  cstep_n 0 e = e ∧
  cstep_n (SUC n) e = (
    case cstep_n n e of
    | Estep st => estep st
    | e => e)
Proof
  rw[cstep_n_def] >>
  qid_spec_tac `e` >> qid_spec_tac `n` >>
  Induct >> Cases >> rewrite_tac[cstep_n_def] >> simp[]
QED

Theorem cstep_n_0[simp] = cj 1 cstep_n_def;

Theorem cstep_n_add:
  ∀a b. cstep_n (a + b) e = cstep_n a (cstep_n b e)
Proof
  Induct >> rw[cstep_n_def] >>
  simp[ADD_CLAUSES, cstep_n_alt]
QED

Theorem same_type_refl[simp]:
  same_type stamp stamp
Proof
  Cases_on `stamp` >> rw[same_type_def]
QED

Theorem cstep_n_to_dstep_n:
  ∀n env dst eve k benv locs p dk cres.
    cstep_n n (Estep (env,dst.refs,dst.fp_state,eve,k)) = cres ∧ cres ≠ Edone ⇒
  ∃fp'.
    step_n benv n (Dstep dst (ExpVal env eve k locs p) dk) =
      case cres of
      | Estep (env',refs',fp',eve',k') =>
        Dstep (dst with <| refs := refs'; fp_state := fp' |>)
          (ExpVal env' eve' k' locs p) dk
      | Etype_error fp' => Dtype_error fp'
      | Effi ch ws1 ws2 n env' refs' k' =>
        Dffi (dst with <| refs := refs'; fp_state := fp' |>)
          (ch,ws1,ws2,n,env',k') locs p dk
Proof
  Induct >> rw[]
  >- simp[itree_semanticsTheory.step_n_def, dstate_component_equality] >>
  gvs[cstep_n_alt] >>
  `cstep_n n (Estep (env,dst.refs,dst.fp_state,eve,k)) ≠ Edone` by gvs[AllCaseEqs()] >>
  last_x_assum drule >>
  disch_then $ qspecl_then [`benv`,`locs`,`p`,`dk`] assume_tac >> gvs[] >>
  simp[itree_semanticsPropsTheory.step_n_alt_def] >>
  reverse $ Cases_on `cstep_n n (Estep (env,dst.refs,dst.fp_state,eve,k))` >> gvs[]
  >- irule_at Any EQ_REFL >>
  rename1 `estep st` >> PairCases_on `st` >> gvs[] >> gvs[estep_to_Edone] >>
  Cases_on `st3` >> gvs[] >> Cases_on `st4` >> gvs[] >> simp[dstep_def] >>
  TOP_CASE_TAC >> gvs[estep_to_Edone] >> irule_at Any EQ_REFL
QED

Triviality dstep_ExpVal_Exp:
  dstep benv st (ExpVal env (Exp e) k locs p) dk =
  case estep (env,st.refs,st.fp_state,Exp e,k) of
  | Estep (env',refs',fp',ev',ec') =>
      dreturn (st with <| refs := refs'; fp_state := fp' |>)
        dk (ExpVal env' ev' ec' locs p)
  | Effi s ws1 ws2 n env'' refs'' ec'' =>
      Dffi (st with refs := refs'') (s,ws1,ws2,n,env'',ec'') locs p dk
  | Edone => Ddone
  | Etype_error fp => Dtype_error fp
Proof
  Cases_on `k` >> simp[dstep_def]
QED

Theorem interp_take_steps:
  interp benv (step_n benv n dr) = interp benv dr
Proof
  once_rewrite_tac[interp] >>
  qsuff_tac
    `∀n dr. step_until_halt benv (step_n benv n dr) = step_until_halt benv dr`
  >- rw[] >>
  Induct >> rw[] >- rw[step_n_alt_def] >>
  Cases_on `dr` >> gvs[] >>
  rw[itree_semanticsTheory.step_n_def] >>
  irule EQ_SYM >> irule step_until_halt_take_step >>
  simp[itree_semanticsTheory.is_halt_def]
QED


(******************** Compilation relation ********************)

Definition var_prefix_def:
  var_prefix v = "pure_" ++ v
End

Inductive opn_rel:
  opn_rel Add Plus ∧
  opn_rel Sub Minus ∧
  opn_rel Mul Times
End

Inductive opb_rel:
  opb_rel pure_config$Lt ast$Lt ∧
  opb_rel Leq Leq ∧
  opb_rel Gt Gt ∧
  opb_rel Geq Geq
End

Inductive atom_op_rel:
  (opn_rel sopn opn ⇒ atom_op_rel sopn (Opn opn)) ∧
  (opb_rel sopb opb ⇒ atom_op_rel sopb (Opb opb)) ∧
  atom_op_rel Eq Equality ∧
  atom_op_rel Len Strlen ∧
  atom_op_rel StrEq Equality
End

Inductive op_rel:
  op_rel AppOp Opapp ∧
  (atom_op_rel aop op ⇒ op_rel (AtomOp aop) op) ∧
  op_rel Length Alength ∧
  op_rel Sub Asub ∧
  op_rel Update Aupdate ∧
  op_rel (AllocMutThunk Evaluated) (ThunkOp $ AllocThunk F) ∧
  op_rel (AllocMutThunk NotEvaluated) (ThunkOp $ AllocThunk T) ∧
  op_rel (UpdateMutThunk Evaluated) (ThunkOp $ UpdateThunk F) ∧
  op_rel (UpdateMutThunk NotEvaluated) (ThunkOp $ UpdateThunk T) ∧
  op_rel ForceMutThunk (ThunkOp ForceThunk)
End

Definition pat_row_def:
  pat_row cn vs =
    (if cn = "" then Pcon NONE else Pcon (SOME $ Short cn))
      (MAP (Pvar o var_prefix) vs)
End

Inductive compile_rel:
[~IntLit:]
  compile_rel cnenv (App (AtomOp (Lit $ Int i)) []) (Lit $ IntLit i)

[~StrLit:]
  compile_rel cnenv (App (AtomOp (Lit $ Str s)) []) (Lit $ StrLit s)

[~Tuple:]
  (LIST_REL (compile_rel cnenv) ses ces
    ⇒ compile_rel cnenv (App (Cons "") ses) (Con NONE ces))

[~Constructor:]
  (LIST_REL (compile_rel cnenv) ses ces ∧
   ALOOKUP cnenv cn = SOME (tyid,ar) ∧
   ar = LENGTH ses ∧ cn ≠ ""
    ⇒ compile_rel cnenv (App (Cons cn) ses) (Con (SOME $ Short cn) ces))

[~Var:]
  compile_rel cnenv (stateLang$Var v) (var (var_prefix v))

[~App:]
  (op_rel sop cop ∧ LIST_REL (compile_rel cnenv) ses ces
    ⇒ compile_rel cnenv (App sop ses) (App cop ces))

[~TwoArgs:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2 ∧
   (if aop = Div then rest = div
    else if aop = Mod then rest = mod
    else if aop = Elem then rest = elem_str
    else if aop = Substring then rest = substring2
    else if aop = StrLeq then rest = strleq
    else if aop = StrLt then rest = strlt
    else if aop = StrGeq then rest = strgeq
    else aop = StrGt ∧ rest = strgt)
    ⇒ compile_rel cnenv (App (AtomOp aop) [se1;se2])
                        (clet "v2" ce2 $ clet "v1" ce1 rest))

[~Concat:]
  (LIST_REL (compile_rel cnenv) ses ces
    ⇒ compile_rel cnenv (App (AtomOp Concat) ses) (App Strcat [list_to_exp ces]))

[~Implode:]
  (LIST_REL (compile_rel cnenv) ses ces
    ⇒ compile_rel cnenv (App (AtomOp Implode) ses)
                        (App Implode [capp (var "char_list") (list_to_exp ces)]))

[~Substring3:]
  (LIST_REL (compile_rel cnenv) [se1;se2;se3] [ce1;ce2;ce3]
    ⇒ compile_rel cnenv (App (AtomOp Substring) [se1; se2; se3])
                        (clet "l" ce3 $ clet "i" ce2 $ clet "s" ce1 substring3))

[~Alloc:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2
    ⇒ compile_rel cnenv (App Alloc [se1;se2])
                        (clet "v2" ce2 $ clet "v1" ce1 alloc))

[~FFI:]
  (compile_rel cnenv se ce ∧ ch ≠ ""
    ⇒ compile_rel cnenv (App (FFI ch) [se])
                        (clet "s" ce $
                          Let NONE (App (FFI ch) [var "s"; var "ffi_array"]) $ ffi))

[~Lam:]
  (compile_rel cnenv se ce
    ⇒ compile_rel cnenv (stateLang$Lam (SOME x) se) (Fun (var_prefix x) ce))

[~Letrec:]
  (LIST_REL
      (λ(sv,se) (cv,cx,ce).
        var_prefix sv = cv ∧
        ∃sx se'. se = Lam (SOME sx) se' ∧ var_prefix sx = cx ∧ compile_rel cnenv se' ce)
      sfuns cfuns ∧
   ALL_DISTINCT (MAP FST cfuns) ∧
   compile_rel cnenv se ce
    ⇒ compile_rel cnenv (stateLang$Letrec sfuns se) (ast$Letrec cfuns ce))

[~Let:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2
    ⇒ compile_rel cnenv (Let (SOME x) se1 se2) (Let (SOME $ var_prefix x) ce1 ce2))

[~If:]
  (LIST_REL (compile_rel cnenv) [se;se1;se2] [ce;ce1;ce2]
    ⇒ compile_rel cnenv (If se se1 se2) (If ce ce1 ce2))

[~CaseNone:]
  (EVERY (λ(cn,vs,_). ALL_DISTINCT vs ∧ ∃stamp'.
    ALOOKUP cnenv cn = SOME (stamp',LENGTH vs) ∧ same_type stamp' stamp) scss ∧
   LIST_REL
    (λ(cn,vs,se) (pat,ce). compile_rel cnenv se ce ∧ pat = pat_row cn vs)
    scss ccss
    ⇒ compile_rel cnenv (Case sv scss NONE)
                        (Mat (var (var_prefix sv)) ccss))

[~CaseSome:]
  (EVERY (λ(cn,vs,_). ALL_DISTINCT vs ∧ ∃stamp'.
    ALOOKUP cnenv cn = SOME (stamp',LENGTH vs) ∧ same_type stamp' stamp) scss ∧
   LIST_REL
    (λ(cn,vs,se) (pat,ce). compile_rel cnenv se ce ∧ pat = pat_row cn vs)
    scss ccss ∧
   EVERY (λ(cn,ar). ∃stamp'.
    ALOOKUP cnenv cn = SOME (stamp',ar) ∧ same_type stamp' stamp) scany ∧
   compile_rel cnenv suse cuse
    ⇒ compile_rel cnenv (Case sv scss (SOME (scany, suse)))
                        (Mat (var (var_prefix sv)) (ccss ++ [Pany,cuse])))

[~TupleCase:]
  (compile_rel cnenv sce cce ∧ ALL_DISTINCT vs
    ⇒ compile_rel cnenv (stateLang$Case sv ["",vs,sce] NONE)
                        (Mat (var (var_prefix sv)) [(pat_row "" vs, cce)]))

[~Raise:]
  (compile_rel cnenv se ce
    ⇒ compile_rel cnenv (Raise se) (Raise ce))

[~Handle:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2
    ⇒ compile_rel cnenv (Handle se1 x se2) (Handle ce1 [(Pvar $ var_prefix x, ce2)]))
End

Definition prim_types_ok_def:
  prim_types_ok senv ⇔
    (* booleans *)
      ALOOKUP senv "True" = SOME (TypeStamp "True" bool_type_num, 0n) ∧
      ALOOKUP senv "False" = SOME (TypeStamp "False" bool_type_num, 0n) ∧
    (* lists *)
      ALOOKUP senv "::" = SOME (TypeStamp "::" list_type_num, 2n) ∧
      ALOOKUP senv "[]" = SOME (TypeStamp "[]" list_type_num, 0n) ∧
    (* subscript exception *)
      ALOOKUP senv "Subscript" = SOME (subscript_stamp, 0n)
End

(*
  A compiled program will look like:
  Dlocal
    Dlet "ffi_array" = _
    Dlet "strle" = _
    Dlet "char_list" = _
  in
    <declare types>
    <compiled program>
  end
*)

Definition cnenv_rel_def:
  cnenv_rel senv cenv ⇔
    prim_types_ok senv ∧
    (* unique stamp for each cn *)
    (∀stamp cn1 cn2 ar1 ar2.
      ALOOKUP senv cn1 = SOME (stamp, ar1) ∧ ALOOKUP senv cn2 = SOME (stamp, ar2)
     ⇒ cn1 = cn2) ∧
    ∀cn tyid ar. ALOOKUP senv cn = SOME (tyid,ar) ⇒
      cn ≠ "" ∧ (* no tuples *)
      nsLookup cenv (Short cn) = SOME (ar,tyid) ∧ (* matching type/arity *)
      (∀cn' id. tyid = TypeStamp cn' id ⇒ cn' = cn) (* type stamp matches cn *)
End

Definition char_list_v_def:
  char_list_v env = Recclosure env char_list_exp "char_list"
End

Definition strle_v_def:
  strle_v env = Recclosure env strle_exp "strle"
End

Theorem char_list_v_def[local] = SRULE [char_list_exp_def] char_list_v_def;
Theorem strle_v_def[local] = SRULE [strle_exp_def] strle_v_def;

Definition env_ok_def:
  env_ok env ⇔
    nsLookup env.v (Short "ffi_array") = SOME (semanticPrimitives$Loc T 0) ∧
    (∃env'.
      nsLookup env.v (Short "strle") = SOME $ strle_v env' ∧
      nsLookup env'.c (Short $ "True") = SOME (0n, TypeStamp "True" bool_type_num) ∧
      nsLookup env'.c (Short $ "False") = SOME (0n, TypeStamp "False" bool_type_num)) ∧
    (∃env'.
      nsLookup env.v (Short "char_list") = SOME $ char_list_v env' ∧
      nsLookup env'.c (Short $ "[]") = SOME (0n, TypeStamp "[]" list_type_num) ∧
      nsLookup env'.c (Short $ "::") = SOME (2n, TypeStamp "::" list_type_num))
End

Inductive v_rel:
[~Tuple:]
  (LIST_REL (v_rel cnenv) svs cvs
    ⇒ v_rel cnenv (Constructor "" svs) (Conv NONE cvs))

[~Constructor:]
  (LIST_REL (v_rel cnenv) svs cvs ∧
   ALOOKUP cnenv cn = SOME (tyid,ar) ∧
   ar = LENGTH svs ∧ cn ≠ ""
    ⇒ v_rel cnenv (Constructor cn svs) (Conv (SOME tyid) cvs))

[~Closure:]
  (compile_rel cnenv se ce ∧ env_rel cnenv senv cenv ∧ env_ok cenv
   ⇒ v_rel cnenv (Closure (SOME sx) senv se) (Closure cenv (var_prefix sx) ce))

[~Recclosure:]
  (compile_rel cnenv se ce ∧ env_rel cnenv senv cenv ∧ env_ok cenv ∧
   LIST_REL (λ(sv,se) (cv,cx,ce).
        var_prefix sv = cv ∧
        ∃sx se'. se = Lam (SOME sx) se' ∧ var_prefix sx = cx ∧ compile_rel cnenv se' ce)
      sfuns cfuns ∧
   ALL_DISTINCT (MAP FST cfuns)
   ⇒ v_rel cnenv (stateLang$Recclosure sfuns senv sx)
                 (Recclosure cenv cfuns (var_prefix sx)))

[~IntLit:]
  v_rel cnenv (Atom $ Int i) (Litv $ IntLit i)

[~StrLit:]
  v_rel cnenv (Atom $ Str s) (Litv $ StrLit s)

[~Loc:]
  v_rel cnenv (Atom $ Loc n) (Loc b (n + 1)) (* leave space for FFI array *)

[~env_rel:]
  (cnenv_rel cnenv cenv.c ∧
   (∀sx sv.
      ALOOKUP senv sx = SOME sv ⇒
      ∃cv. nsLookup cenv.v (Short $ var_prefix sx) = SOME cv ∧ v_rel cnenv sv cv)
    ⇒ env_rel cnenv senv cenv)
End

Theorem env_rel_def = cj 2 v_rel_cases;
Theorem v_rel_cases[allow_rebind] = cj 1 v_rel_cases;

Theorem v_rel_def[simp] = [
  “v_rel cnenv (Constructor cn svs) cv”,
  “v_rel cnenv (Closure sx senv se) cv”,
  “v_rel cnenv (Recclosure sfuns senv sx) cv”,
  “v_rel cnenv (Atom a) cv”] |>
  map (GEN_ALL o SIMP_CONV (srw_ss()) [Once v_rel_cases, SF CONJ_ss]) |>
  LIST_CONJ;

Definition list_to_cont_def:
  list_to_cont env [] = [] ∧
  list_to_cont env (e::es) =
    (Ccon (SOME $ Short "::") [] [e], env) :: (list_to_cont env es)
End

Inductive cont_rel:
  cont_rel cnenv [] []

[~TupleK:]
  (LIST_REL (v_rel cnenv) svs cvs ∧
   LIST_REL (compile_rel cnenv) ses ces ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (Cons "") svs ses :: sk)
                     ((Ccon NONE cvs ces, cenv) :: ck))

[~ConsK:]
  (LIST_REL (v_rel cnenv) svs cvs ∧
   LIST_REL (compile_rel cnenv) ses ces ∧
   ALOOKUP cnenv cn = SOME (tyid,ar) ∧
   ar = LENGTH ses + LENGTH svs + 1 ∧ cn ≠ "" ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (Cons cn) svs ses :: sk)
                     ((Ccon (SOME $ Short cn) cvs ces, cenv) :: ck))

[~AppK:]
  (op_rel sop cop ∧
   LIST_REL (v_rel cnenv) svs cvs ∧
   LIST_REL (compile_rel cnenv) ses ces ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv sop svs ses :: sk)
                     ((Capp cop cvs ces, cenv) :: ck))

[~TwoArgs1:]
  (compile_rel cnenv se1 ce1 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv ∧
   (if aop = Div then rest = div
    else if aop = Mod then rest = mod
    else if aop = Elem then rest = elem_str
    else if aop = Substring then rest = substring2
    else if aop = StrLeq then rest = strleq
    else if aop = StrLt then rest = strlt
    else if aop = StrGeq then rest = strgeq
    else aop = StrGt ∧ rest = strgt)
    ⇒ cont_rel cnenv (AppK senv (AtomOp aop) [] [se1] :: sk)
                     ((Clet (SOME "v2") (clet "v1" ce1 rest), cenv) :: ck))

[~TwoArgs2:]
  (nsLookup cenv.v (Short "v2") = SOME cv2 ∧ v_rel cnenv sv2 cv2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv ∧
   (if aop = Div then rest = div
    else if aop = Mod then rest = mod
    else if aop = Elem then rest = elem_str
    else if aop = Substring then rest = substring2
    else if aop = StrLeq then rest = strleq
    else if aop = StrLt then rest = strlt
    else if aop = StrGeq then rest = strgeq
    else aop = StrGt ∧ rest = strgt)
    ⇒ cont_rel cnenv (AppK senv (AtomOp aop) [sv2] [] :: sk)
                     ((Clet (SOME "v1") rest, cenv) :: ck))

[~Alloc1:]
  (compile_rel cnenv se1 ce1 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv Alloc [] [se1] :: sk)
                     ((Clet (SOME "v2") (clet "v1" ce1 alloc), cenv) :: ck))

[~Alloc2:]
  (nsLookup cenv.v (Short "v2") = SOME cv2 ∧ v_rel cnenv sv2 cv2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv Alloc [sv2] [] :: sk)
                     ((Clet (SOME "v1") alloc, cenv) :: ck))

[~Concat:]
  (LIST_REL (compile_rel cnenv) ses ces ∧
   LIST_REL (v_rel cnenv) svs cvs ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
  ⇒ cont_rel cnenv
    (AppK senv (AtomOp Concat) svs ses :: sk)
    ((Ccon (SOME $ Short "::") [list_to_v cvs] [], cenv)
        :: list_to_cont cenv ces ++ [Capp Strcat [] [], cenv] ++ ck))

[~Implode:]
  (LIST_REL (compile_rel cnenv) ses ces ∧
   LIST_REL (v_rel cnenv) svs cvs ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
  ⇒ cont_rel cnenv
    (AppK senv (AtomOp Implode) svs ses :: sk)
    ((Ccon (SOME $ Short "::") [list_to_v cvs] [], cenv)
        :: list_to_cont cenv ces ++ [Capp Opapp [] [var "char_list"], cenv] ++
           [Capp Implode [] [], cenv] ++ ck))

[~Substring3_1:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Substring) [] [se2;se1] :: sk)
        ((Clet (SOME "l") (clet "i" ce2 $ clet "s" ce1 substring3), cenv) :: ck))

[~Substring3_2:]
  (nsLookup cenv.v (Short "l") = SOME cv3 ∧
   v_rel cnenv sv3 cv3 ∧ compile_rel cnenv se1 ce1 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Substring) [sv3] [se1] :: sk)
                     ((Clet (SOME "i") (clet "s" ce1 substring3), cenv) :: ck))

[~Substring3_3:]
  (nsLookup cenv.v (Short "l") = SOME cv3 ∧ nsLookup cenv.v (Short "i") = SOME cv2 ∧
   v_rel cnenv sv3 cv3 ∧ v_rel cnenv sv2 cv2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Substring) [sv2;sv3] [] :: sk)
                      ((Clet (SOME "s") substring3, cenv) :: ck))

[~FFI:]
  (cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv ∧ ch ≠ ""
    ⇒ cont_rel cnenv (AppK senv (FFI ch) [] [] :: sk)
                     ((Clet (SOME "s") $
                        Let NONE (App (FFI ch) [var "s"; var "ffi_array"]) $ ffi
                       , cenv) :: ck))

[~LetK:]
  (compile_rel cnenv se ce ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (LetK senv (SOME x) se :: sk)
                     ((Clet (SOME $ var_prefix x) ce, cenv) :: ck))

[~IfK:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (IfK senv se1 se2 :: sk)
                     ((Cif ce1 ce2, cenv) :: ck))

[~RaiseK:]
  (cont_rel cnenv sk ck
    ⇒ cont_rel cnenv (RaiseK :: sk) ((Craise, cenv) :: ck))

[~HandleK:]
  (compile_rel cnenv se ce ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (HandleK senv x se :: sk)
                     ((Chandle [(Pvar $ var_prefix x, ce)], cenv) :: ck))

[~ForceMutK:]
  (cont_rel cnenv sk ck
    ⇒ cont_rel cnenv (ForceMutK n :: sk) ((Cforce (n + 1), cenv) :: ck))
End

Definition store_rel_def:
  store_rel cnenv (Array svs) (Varray cvs) = LIST_REL (v_rel cnenv) svs cvs ∧
  store_rel cnenv (ThunkMem Evaluated sv) (Thunk F cv) = v_rel cnenv sv cv ∧
  store_rel cnenv (ThunkMem NotEvaluated sv) (Thunk T cv) = v_rel cnenv sv cv ∧
  store_rel cnenv _ _ = F
End

Definition state_rel_def:
  state_rel cnenv sst (W8array ws :: cst) = (
    (LENGTH ws = max_FFI_return_size + 2) ∧
    LIST_REL (store_rel cnenv) sst cst) ∧
  state_rel cnenv sst _ = F
End

Theorem state_rel:
  state_rel cnenv sst cst ⇔
    ∃ws cst'. cst = W8array ws :: cst' ∧ LENGTH ws = max_FFI_return_size + 2 ∧
      LIST_REL (store_rel cnenv) sst cst'
Proof
  rw[DefnBase.one_line_ify NONE state_rel_def] >>
  TOP_CASE_TAC >> simp[] >> TOP_CASE_TAC >> simp[]
QED

Inductive step_rel:
  (compile_rel cnenv se ce ∧ cont_rel cnenv sk ck ∧
   env_rel cnenv senv cenv ∧ state_rel cnenv sst cst ∧ env_ok cenv
    ⇒ step_rel (Exp senv se, SOME sst, sk) (Estep (cenv, cst, fp, Exp ce, ck))) ∧

  (v_rel cnenv sv cv ∧ cont_rel cnenv sk ck ∧ state_rel cnenv sst cst
    ⇒ step_rel (Val sv, SOME sst, sk) (Estep (cenv, cst, fp, Val cv, ck))) ∧

  (v_rel cnenv sv cv ∧ cont_rel cnenv sk ck ∧ state_rel cnenv sst cst
    ⇒ step_rel (Exn sv, SOME sst, sk) (Estep (cenv, cst, fp, Exn cv, ck))) ∧

  (cont_rel cnenv sk ck ∧ state_rel cnenv sst cst ∧ env_ok cenv ∧
   ws1 = MAP (λc. n2w $ ORD c) (EXPLODE conf) ∧
   store_lookup 0 cst = SOME $ W8array ws2 ∧ s ≠ ""
    ⇒ step_rel (Action s conf, SOME sst, sk)
               (Effi (ExtCall s) ws1 ws2 0 cenv' cst ((Clet NONE ffi, cenv) :: ck)))
End

Inductive dstep_rel:
  (step_rel (seve, SOME sst, sk) (Estep (cenv,dst.refs,dst.fp_state,ceve,ck)) ∧
   ¬is_halt (seve, SOME sst, sk)
    ⇒ dstep_rel (seve, SOME sst, sk)
        (Dstep dst (ExpVal cenv ceve ck locs (Pvar "prog")) [CdlocalG lenv genv (final_gc flag)])) ∧

  dstep_rel (Val sv, SOME sst, []) Ddone ∧

  (v_rel cnenv sv cv ⇒
    dstep_rel (Exn sv, SOME sst, []) (Draise (fp,cv))) ∧

  (step_rel (Action ch conf, SOME sst, sk)
             (Effi (ExtCall ch) ws1 ws2 0 cenv' dst.refs ck)
    ⇒ dstep_rel (Action ch conf, SOME sst, sk)
                (Dffi dst (ExtCall ch,ws1,ws2,0,cenv',ck)
                 locs (Pvar "prog") [CdlocalG lenv genv (final_gc flag)]))
End

Inductive next_res_rel:
  next_res_rel (stateLang$Div) (itree_semantics$Div) ∧
  next_res_rel Ret Ret ∧
  (dstep_rel (Action ch conf, st, sk) (Dffi dst out locs p dk)
      ⇒ next_res_rel (Act (ch, conf) sk st) (Act dst out locs p dk))
End

Definition compile_conf_def:
  compile_conf conf = MAP (λc. n2w (ORD c)) (EXPLODE conf) :word8 list
End

Definition compile_final_ffi_def:
  compile_final_ffi FFI_divergence = FFI_diverged ∧
  compile_final_ffi FFI_failure = FFI_failed
End

Definition compile_input_rel_def:
  compile_input_rel (s :string) (ws :word8 list) ⇔
    ∃junk.
      LENGTH junk = max_FFI_return_size - LENGTH s ∧
      ws = [n2w (LENGTH s); n2w (LENGTH s DIV 256)] ++
              MAP (λc. n2w (ORD c)) (s ++ junk)
End

CoInductive itree_rel:
[~Ret_Termination:]
  itree_rel (Ret Termination) (Ret Termination)

[~Div:]
  itree_rel Div Div

[~Ret_FinalFFI:]
  itree_rel (Ret $ FinalFFI (ch,conf) f)
            (Ret $ FinalFFI (ExtCall ch, compile_conf conf, ws) (compile_final_ffi f))

[~Vis:]
   ((∀s ws'. compile_input_rel s ws'
      ⇒ itree_rel (srest $ INR s) (crest $ INR ws')) ∧

   (∀f. itree_rel (srest $ INL f) (crest $ INL $ compile_final_ffi f))

    ⇒ itree_rel (Vis (ch,conf) srest) (Vis (ExtCall ch, compile_conf conf, ws) crest))
End

Definition ffi_convention_def:
  ffi_convention = SUM_ALL (K T) (λbs. ∃s. compile_input_rel s bs)
End


(******************** Results ********************)

(********** Useful shorthands **********)

Definition get_ffi_ch_def[simp]:
  get_ffi_ch (ast$FFI ch) = SOME ch ∧
  get_ffi_ch _ = NONE
End

Definition get_ffi_args_def[simp]:
  get_ffi_args [Litv (StrLit conf); Loc b lnum] = SOME (conf, lnum) ∧
  get_ffi_args _ = NONE
End

Theorem capplication_thm:
  ∀op env s fp vs c.
    getOpClass op ≠ Icing ∧ getOpClass op ≠ Reals ⇒
    application op env s fp vs c =
    if op = Opapp then
      case do_opapp vs of
      | NONE => Etype_error (fix_fp_state c fp)
      | SOME (env,e) => Estep (env,s,fp,Exp e,c)
    else if op = ThunkOp ForceThunk then
      (case vs of
         [Loc _ n] => (
           case store_lookup n s of
             SOME (Thunk F v) =>
               return env s fp v c
           | SOME (Thunk T f) =>
               application Opapp env s fp [f; Conv NONE []] ((Cforce n,env)::c)
           | _ =>
               Etype_error (fix_fp_state c fp))
       | _ => Etype_error (fix_fp_state c fp))
    else case get_ffi_ch op of
    | SOME n => (
      case get_ffi_args vs of
      | SOME (conf, lnum) => (
          case store_lookup lnum s of
            SOME (W8array ws) =>
              if n = "" then Estep (env, s, fp, Val $ Conv NONE [], c)
              else Effi (ExtCall n) (MAP (λc. n2w $ ORD c) (EXPLODE conf)) ws lnum env s c
          | _ => Etype_error (fix_fp_state c fp))
      | NONE => Etype_error (fix_fp_state c fp))
    | NONE => (
      case do_app s op vs of
      | NONE => Etype_error (fix_fp_state c fp)
      | SOME (v1,Rval v') => return env v1 fp v' c
      | SOME (v1,Rraise v) => Estep (env,v1,fp,Exn v,c))
Proof
  rw[application_thm, evaluateTheory.AppUnit_def] >> gvs[]
  >- gvs[AllCaseEqs()]
  >- rpt (TOP_CASE_TAC >> gvs[]) >>
  Cases_on `op` >> gvs[] >>
  TOP_CASE_TAC >> gvs []
QED

val creturn_def       = itree_semanticsTheory.return_def;
val cpush_def         = itree_semanticsTheory.push_def;
val ccontinue_def     = itree_semanticsTheory.continue_def;
val cexn_continue_def = itree_semanticsTheory.exn_continue_def;
val cstep_ss          = simpLib.named_rewrites "cstep_ss" [
                         creturn_def, cpush_def, ccontinue_def, cexn_continue_def,
                         astTheory.getOpClass_def,
                         capplication_thm, estep_def, cstep_n_def];
val cstep             = SF cstep_ss;

val scontinue_def     = stateLangTheory.continue_def;
val spush_def         = stateLangTheory.push_def;
val svalue_def        = stateLangTheory.value_def;
val serror_def        = stateLangTheory.error_def;
val sapplication_def  = stateLangTheory.application_def;
val sreturn_def       = stateLangTheory.return_def;
val sstep_ss          = simpLib.named_rewrites "sstep_ss" [
                         scontinue_def, spush_def, svalue_def, serror_def,
                         sapplication_def, sreturn_def, step_def,
                         stateLangTheory.get_atoms_def];
val sstep             = SF sstep_ss;

val dstep_ss          = simpLib.named_rewrites "dstep_ss" [
                         dreturn_def, dpush_def, dcontinue_def, dstep_def,
                         dstep_ExpVal_Exp, itree_semanticsTheory.step_n_def];
val dstep             = SF dstep_ss;

val qexists0 = qexists_tac `0`;


(********** Lemmmas **********)

Theorem get_atoms_SOME[simp]:
  ∀l as. get_atoms l = SOME as ⇔ l = MAP Atom as
Proof
  Induct >> rw[get_atoms_def] >> Cases_on `as` >> gvs[] >>
  Cases_on `h` >> gvs[get_atoms_def] >> eq_tac >> rw[]
QED

Theorem num_args_ok_0:
  num_args_ok op 0 ⇔
    (∃s. op = Cons s) ∨ (∃aop. op = AtomOp aop)
Proof
  Cases_on `op` >> gvs[num_args_ok_def]
QED

Theorem v_to_list_list_to_v[simp]:
  v_to_list (list_to_v l) = SOME l
Proof
  Induct_on `l` >> rw[list_to_v_def, v_to_list_def]
QED

Theorem nsLookup_nsBind_var_prefix[simp]:
  nsLookup (nsBind (var_prefix n) v e) (Short (var_prefix n')) =
    if n = n' then SOME v else nsLookup e (Short (var_prefix n'))
Proof
  IF_CASES_TAC >> gvs[] >> simp[var_prefix_def]
QED

Theorem nsOptBind_SOME[simp]:
  nsOptBind (SOME x) = nsBind x
Proof
  rw[FUN_EQ_THM, namespaceTheory.nsOptBind_def]
QED

Triviality cstep_Exn_over_list_to_cont:
  ∀es cenv cst fp cv cenv' env ck'.
  cstep_n (LENGTH es) (Estep (cenv,cst,fp,Exn cv, (list_to_cont env es ++ ck'))) =
        (Estep (cenv,cst,fp,Exn cv,ck'))
Proof
  Induct >> rw[list_to_cont_def] >> simp[cstep] >> CASE_TAC >> gvs[]
QED

Theorem list_to_cont_APPEND:
  list_to_cont env (a ++ b) = list_to_cont env a ++ list_to_cont env b
Proof
  Induct_on `a` >> rw[list_to_cont_def]
QED

Theorem cstep_list_to_exp:
  ∀ces cnenv cenv cst fp ck. cnenv_rel cnenv cenv.c ⇒
    ∃n. cstep_n n (Estep (cenv,cst,fp,Exp (list_to_exp ces), ck)) =
          Estep (cenv,cst,fp,Val (Conv (SOME (TypeStamp "[]" 1)) []),
                 list_to_cont cenv (REVERSE ces) ++ ck)
Proof
  Induct >> rw[] >> gvs[env_ok_def] >> simp[list_to_exp_def, list_to_cont_def]
  >- (
    qrefine `SUC n` >> simp[cstep, do_con_check_def, build_conv_def] >>
    `nsLookup cenv.c (Short "[]") = SOME (0, TypeStamp "[]" 1)` by
      gvs[cnenv_rel_def, prim_types_ok_def, list_type_num_def] >>
    simp[] >> qexists0 >> simp[]
    ) >>
  qrefine `SUC n` >> simp[cstep, do_con_check_def, build_conv_def] >>
  `nsLookup cenv.c (Short "::") = SOME (2, TypeStamp "::" 1)` by
    gvs[cnenv_rel_def, prim_types_ok_def, list_type_num_def] >>
  simp[] >>
  last_x_assum $ drule_all_then assume_tac >>
  pop_assum $ qspecl_then
    [`cst`,`fp`,`(Ccon (SOME (Short "::")) [] [h],cenv)::ck`] assume_tac >> gvs[] >>
  qrefine `m + n` >> simp[cstep_n_add] >>
  qexists0 >> simp[list_to_cont_APPEND, list_to_cont_def]
QED

Theorem step_Case_no_error:
  (∀n st k. step_n n (Exp senv $ stateLang$Case sv scss suse, sst, sk) ≠ (Error,st,k))
  ⇒ ∃cn vs.
      ALOOKUP senv sv = SOME $ Constructor cn vs ∧
      (∃pvs se. ALOOKUP scss cn = SOME (pvs, se) ∧ LENGTH pvs = LENGTH vs) ∨
      (ALOOKUP scss cn = NONE ∧
       ∃pany se. suse = SOME (pany, se) ∧ ALOOKUP pany cn = SOME (LENGTH vs))
Proof
  Induct_on `scss` >> rw[]
  >- (
    Cases_on `suse` >> gvs[] >>
    pop_assum $ qspec_then `1` mp_tac >> simp[sstep, find_match_def] >>
    CASE_TAC >> simp[]
    ) >>
  pop_assum $ qspec_then `SUC n` $ mp_tac o GEN_ALL >> simp[step_n_SUC, sstep] >>
  TOP_CASE_TAC >> simp[]
  >- (disch_then $ qspec_then `0` mp_tac >> simp[]) >>
  simp[find_match_def] >> TOP_CASE_TAC >> simp[]
  >- (disch_then $ qspec_then `0` mp_tac >> simp[]) >>
  gvs[AllCaseEqs()] >> namedCases_on `x'` ["env1 e1"] >> gvs[SF DNF_ss] >>
  gvs[find_match_list_SOME] >> strip_tac >> rpt $ goal_assum drule
QED

Theorem pats_bindings_MAP_Pvar[simp]:
  ∀vs f l. pats_bindings (MAP (Pvar o f) vs) l = REVERSE (MAP f vs) ++ l
Proof
  Induct >> rw[astTheory.pat_bindings_def]
QED

Theorem pat_bindings_pat_row[simp]:
  ∀vs cn v l.
    pat_bindings (pat_row cn vs) l = REVERSE (MAP var_prefix vs) ++ l
Proof
  Induct >> rw[pat_row_def, astTheory.pat_bindings_def] >> simp[MAP_REVERSE]
QED

Theorem var_prefix_11[simp]:
  var_prefix a = var_prefix b ⇔ a = b
Proof
  rw[var_prefix_def]
QED

Triviality ALL_DISTINCT_pat_bindings[simp]:
  ALL_DISTINCT (REVERSE (MAP var_prefix vs) ++ [var_prefix v]) ⇔
  ¬MEM v vs ∧ ALL_DISTINCT vs
Proof
  rw[ALL_DISTINCT_APPEND, MEM_MAP] >> eq_tac >> rw[]
  >- (drule ALL_DISTINCT_MAP >> simp[])
  >- (irule ALL_DISTINCT_MAP_INJ >> simp[])
QED

Theorem state_rel_store_lookup:
  state_rel cnenv sst cst ⇒
  OPTREL (store_rel cnenv) (oEL n sst) (store_lookup (n + 1) cst)
Proof
  rw[state_rel] >> rw[oEL_THM, store_lookup_def] >> gvs[LIST_REL_EL_EQN] >>
  gvs[ADD1] >> first_x_assum drule >> strip_tac >> simp[GSYM ADD1]
QED

Theorem store_lookup_assign_Varray:
  store_lookup n st = SOME (Varray vs) ⇒
  store_assign n (Varray (LUPDATE e i vs)) st =
  SOME $ LUPDATE (Varray (LUPDATE e i vs)) n st
Proof
  rw[store_lookup_def, store_assign_def, store_v_same_type_def]
QED

Theorem store_lookup_assign_Thunk:
  store_lookup n st = SOME (Thunk T a) ⇒
  store_assign n (Thunk b y) st =
  SOME $ LUPDATE (Thunk b y) n st
Proof
  rw[store_lookup_def, store_assign_def, store_v_same_type_def]
QED

Triviality step_until_halt_no_err_step_n:
  step_until_halt s ≠ Err ⇒ ∀n st k. step_n n s ≠ error st k
Proof
  PairCases_on `s` >> simp[step_until_halt_def] >>
  DEEP_INTRO_TAC some_intro >> reverse $ rw[]
  >- (CCONTR_TAC >> gvs[error_def] >> last_x_assum $ qspec_then `n` mp_tac >> simp[]) >>
  CCONTR_TAC >> gvs[] >>
  drule is_halt_imp_eq >> disch_then $ qspec_then `n` assume_tac >> gvs[error_def]
QED

Triviality ALL_DISTINCT_MAP_FSTs:
  ALL_DISTINCT (MAP FST l) ⇒
  ALL_DISTINCT (MAP (λ(x,y,z). x) l)
Proof
  Induct_on `l` >> rw[MEM_MAP] >>
  ntac 2 (pairarg_tac >> gvs[])
QED

(***** cnenv_rel / env_rel / env_ok *****)

Theorem env_rel_lookup:
  ∀v sx cnenv senv cenv.
    env_rel cnenv senv cenv ∧
    ALOOKUP senv v = SOME sx
  ⇒ ∃cx. nsLookup cenv.v (Short (var_prefix v)) = SOME cx ∧ v_rel cnenv sx cx
Proof
  rw[env_rel_def]
QED

Theorem env_rel_check:
  ∀cn tyid ar cnenv senv cenv.
    env_rel cnenv senv cenv ∧
    ALOOKUP cnenv cn = SOME (tyid, ar) ∧ cn ≠ ""
  ⇒ do_con_check cenv.c (SOME (Short cn)) ar
Proof
  rw[env_rel_def, cnenv_rel_def, do_con_check_def] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem cnenv_rel_list_type:
  cnenv_rel cnenv cenv.c ⇒
    nsLookup cenv.c (Short "[]") = SOME (0,TypeStamp "[]" 1) ∧
    nsLookup cenv.c (Short "::") = SOME (2,TypeStamp "::" 1) ∧
    do_con_check cenv.c (SOME (Short "[]")) 0 ∧
    do_con_check cenv.c (SOME (Short "::")) 2 ∧
    build_conv cenv.c (SOME (Short "[]")) [] =
      SOME (Conv (SOME (TypeStamp "[]" 1)) []) ∧
    ∀a b. build_conv cenv.c (SOME (Short "::")) [a;b] =
            SOME (Conv (SOME (TypeStamp "::" 1)) [a;b])
Proof
  rw[cnenv_rel_def, prim_types_ok_def] >>
  rw[do_con_check_def, build_conv_def] >> gvs[list_type_num_def] >>
  res_tac >> simp[]
QED

Theorem env_rel_build:
  ∀vs cn tyid cnenv senv cenv.
    env_rel cnenv senv cenv ∧
    ALOOKUP cnenv cn = SOME (tyid, LENGTH vs) ∧ cn ≠ ""
  ⇒ build_conv cenv.c (SOME (Short cn)) vs = SOME (Conv (SOME tyid) vs)
Proof
  rw[env_rel_def, cnenv_rel_def, build_conv_def] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem env_ok_nsBind[simp]:
  env_ok (cenv with v := nsBind (var_prefix x) v cenv.v) ⇔ env_ok cenv
Proof
  rw[env_ok_def, var_prefix_def]
QED

Theorem env_ok_nsBind_alt:
  env_ok cenv ∧ x ≠ "ffi_array" ∧ x ≠ "strle" ∧ x ≠ "char_list" ⇒
  env_ok (cenv with v := nsBind x v cenv.v)
Proof
  rw[env_ok_def]
QED

Theorem env_rel_nsBind:
  env_rel cnenv senv cenv ∧
  v_rel cnenv sv cv
  ⇒ env_rel cnenv ((s,sv)::senv) (cenv with v := nsBind (var_prefix s) cv cenv.v)
Proof
  rw[env_rel_def] >> IF_CASES_TAC >> gvs[]
QED

Theorem env_rel_nsBind_alt:
  env_rel cnenv senv cenv ∧ (∀x. cx ≠ var_prefix x)
  ⇒ env_rel cnenv senv (cenv with v := nsBind cx cv cenv.v)
Proof
  rw[env_rel_def]
QED

Theorem env_ok_nsAppend_var_prefix:
  (∀n v. nsLookup ns' n = SOME v ⇒ ∃n'. n = Short $ var_prefix n') ∧
  env_ok (cenv with v := ns) ⇒
  env_ok (cenv with v := nsAppend ns' ns)
Proof
  strip_tac >> simp[env_ok_def, namespacePropsTheory.nsLookup_nsAppend_some] >>
  gvs[namespaceTheory.id_to_mods_def] >> rw[DISJ_EQ_IMP] >> gvs[env_ok_def]
  >- (
    Cases_on `nsLookup ns' (Short "ffi_array")` >> gvs[] >>
    first_x_assum drule >> simp[var_prefix_def]
    )
  >- (
    Cases_on `nsLookup ns' (Short "strle")` >> gvs[]
    >- (irule_at Any EQ_REFL >> simp[]) >>
    first_x_assum drule >> simp[var_prefix_def]
    )
  >- (
    Cases_on `nsLookup ns' (Short "char_list")` >> gvs[]
    >- (irule_at Any EQ_REFL >> simp[]) >>
    first_x_assum drule >> simp[var_prefix_def]
    )
QED

Theorem env_rel_nsAppend:
  env_rel cnenv senv cenv ∧
  (∀sx. ALOOKUP senv' sx = NONE ⇒ nsLookup cenv' (Short (var_prefix sx)) = NONE) ∧
  (∀sx sv. ALOOKUP senv' sx = SOME sv ⇒
    ∃cv. nsLookup cenv' (Short (var_prefix sx)) = SOME cv ∧ v_rel cnenv sv cv)
  ⇒ env_rel cnenv (senv' ++ senv) (cenv with v := nsAppend cenv' cenv.v)
Proof
  rw[env_rel_def] >> simp[namespacePropsTheory.nsLookup_nsAppend_some] >>
  simp[namespaceTheory.id_to_mods_def, SF DNF_ss] >>
  gvs[ALOOKUP_APPEND] >> every_case_tac >> gvs[]
QED

Theorem env_ok_Recclosure:
  env_ok cenv ∧
  EVERY (λ(cv,cx,ce). ∃sv. cv = var_prefix sv) cfuns ⇒
  env_ok (cenv with v := build_rec_env cfuns cenv cenv.v)
Proof
  rw[build_rec_env_def] >>
  qsuff_tac `∀fs.
    env_ok (cenv with v :=
      FOLDR (λ(f,x,e) env'. nsBind f (Recclosure cenv fs f) env') cenv.v cfuns)` >>
  rw[] >>
  Induct_on `cfuns` >> rw[] >> pairarg_tac >> gvs[] >>
  gvs[env_ok_def, var_prefix_def] >> rw[] >>
  irule_at Any EQ_REFL >> simp[]
QED

Theorem env_rel_Recclosure:
  env_rel cnenv senv cenv ∧ env_ok cenv ∧
  LIST_REL
    (λ(sv,se) (cv,cx,ce). var_prefix sv = cv ∧
      ∃sx se'. se = Lam (SOME sx) se' ∧ var_prefix sx = cx ∧
               compile_rel cnenv se' ce) sfuns cfuns ∧
  ALL_DISTINCT (MAP FST cfuns)
  ⇒ env_rel cnenv
      (MAP (λ(fn,_). (fn,Recclosure sfuns senv fn)) sfuns ++ senv)
      (cenv with v := build_rec_env cfuns cenv cenv.v)
Proof
  rw[build_rec_env_def] >>
  qsuff_tac `∀sfs cfs.
    LIST_REL
      (λ(sv,se) (cv,cx,ce). var_prefix sv = cv ∧
        ∃sx se'. se = Lam (SOME sx) se' ∧ var_prefix sx = cx ∧
                 compile_rel cnenv se' ce) sfs cfs ∧
    ALL_DISTINCT (MAP FST cfs) ⇒
    env_rel cnenv
      (MAP (λ(fn,_). (fn,Recclosure sfs senv fn)) sfuns ++ senv)
      (cenv with v :=
        FOLDR (λ(f,x,e) env'. nsBind f (Recclosure cenv cfs f) env') cenv.v cfuns)` >>
  rw[] >> pop_assum mp_tac >> qpat_x_assum `LIST_REL _ sfuns _` mp_tac >>
  map_every qid_spec_tac [`cfuns`,`sfuns`] >> ho_match_mp_tac LIST_REL_ind >> rw[] >>
  ntac 2 (pairarg_tac >> gvs[]) >> gvs[env_rel_def] >>
  rw[] >> simp[env_rel_def, SF SFY_ss]
QED

Theorem env_ok_nsBind_Recclosure:
  env_ok cenv ∧ EVERY (λ(cv,cx,ce). ∃sv. cv = var_prefix sv) cfuns ⇒
  env_ok (cenv with v := nsBind (var_prefix x) v (build_rec_env cfuns cenv cenv.v))
Proof
  rw[] >> drule_all env_ok_Recclosure >> strip_tac >>
  gvs[env_ok_def, var_prefix_def] >> rw[] >>
  irule_at Any EQ_REFL >> simp[]
QED

Theorem env_rel_nsBind_Recclosure:
  env_rel cnenv senv cenv ∧ env_ok cenv ∧ v_rel cnenv sv cv ∧
  LIST_REL
    (λ(sv,se) (cv,cx,ce). var_prefix sv = cv ∧
      ∃sx se'. se = Lam (SOME sx) se' ∧ var_prefix sx = cx ∧
               compile_rel cnenv se' ce) sfuns cfuns ∧
  ALL_DISTINCT (MAP FST cfuns)
  ⇒ env_rel cnenv
      ((s,sv)::(MAP (λ(fn,_). (fn,Recclosure sfuns senv fn)) sfuns ++ senv))
      (cenv with v := nsBind (var_prefix s) cv (build_rec_env cfuns cenv cenv.v))
Proof
  rw[] >> drule_all env_rel_Recclosure >> strip_tac >>
  gvs[env_ok_def, env_rel_def] >> rw[] >> simp[]
QED

Theorem env_rel_pmatch:
  env_rel cnenv senv cenv ∧ LIST_REL (v_rel cnenv) svs cvs ∧ LENGTH pvs = LENGTH cvs
  ⇒ env_rel cnenv
      (REVERSE (ZIP (pvs,svs)) ++ senv)
      (cenv with v :=
        nsAppend (alist_to_ns (REVERSE (ZIP (MAP var_prefix pvs,cvs)))) cenv.v)
Proof
  rw[] >> irule_at Any env_rel_nsAppend >> simp[] >>
  simp[namespacePropsTheory.nsLookup_alist_to_ns_some,
       namespacePropsTheory.nsLookup_alist_to_ns_none, PULL_EXISTS] >>
  imp_res_tac LIST_REL_LENGTH >> gvs[] >> rw[ZIP_MAP, ALOOKUP_APPEND]
  >- (
    simp[GSYM MAP_REVERSE, LAMBDA_PROD] >>
    DEP_REWRITE_TAC[ALOOKUP_MAP_MAP] >> simp[] >>
    DEP_REWRITE_TAC[MAP_ID_ON] >> simp[FORALL_PROD] >>
    gvs[REVERSE_ZIP] >> every_case_tac >> gvs[] >>
    drule $ INST_TYPE [beta |-> ``:semanticPrimitives$v``] ALOOKUP_SOME_EL_2 >>
    disch_then $ qspec_then `ZIP (REVERSE pvs,REVERSE cvs)` mp_tac >>
    simp[MAP_ZIP] >> strip_tac >> gvs[EL_ZIP, LIST_REL_EL_EQN, EL_REVERSE]
    )
  >- (
    simp[GSYM MAP_REVERSE, LAMBDA_PROD] >>
    DEP_REWRITE_TAC[ALOOKUP_MAP_MAP] >> simp[] >>
    DEP_REWRITE_TAC[MAP_ID_ON] >> simp[FORALL_PROD] >>
    gvs[REVERSE_ZIP] >> every_case_tac >> gvs[]
    >- (gvs[ALOOKUP_NONE] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP]) >>
    drule $ INST_TYPE [beta |-> ``:semanticPrimitives$v``] ALOOKUP_SOME_EL_2 >>
    disch_then $ qspec_then `ZIP (REVERSE pvs,REVERSE cvs)` mp_tac >>
    simp[MAP_ZIP] >> strip_tac >> gvs[EL_ZIP, LIST_REL_EL_EQN, EL_REVERSE]
    )
QED

Theorem env_ok_pmatch:
  env_ok cenv ∧ LENGTH pvs = LENGTH cvs
  ⇒ env_ok (cenv with v :=
      nsAppend (alist_to_ns (REVERSE (ZIP (MAP var_prefix pvs,cvs)))) cenv.v)
Proof
  rw[] >> irule env_ok_nsAppend_var_prefix >>
  rw[namespacePropsTheory.nsLookup_alist_to_ns_some] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP, EL_MAP]
QED

Theorem env_ok_imps = iffLR env_ok_def |> Q.ID_SPEC |> SRULE [IMP_CONJ_THM];


(***** pmatch *****)

Theorem can_pmatch_all_tuple:
  LENGTH pvs = LENGTH cvs ⇒
  can_pmatch_all cenv.c st [pat_row "" pvs] (Conv NONE cvs)
Proof
  rw[can_pmatch_all_def, pat_row_def, pmatch_def] >>
  rename1 `_ binding ≠ _` >> pop_assum mp_tac >>
  map_every qid_spec_tac [`binding`,`pvs`,`cvs`] >> Induct >> rw[pmatch_def] >>
  Cases_on `pvs` >> gvs[pmatch_def]
QED

Theorem pmatch_no_match:
  cnenv_rel cnenv cenv.c ∧
  ALOOKUP cnenv cn = SOME (tyid,LENGTH cvs) ∧
  ALOOKUP cnenv cn' = SOME (tyid',LENGTH vs) ∧
  same_type tyid' tyid ∧ cn' ≠ cn ⇒
  pmatch cenv.c cst (pat_row cn' vs) (Conv (SOME tyid) cvs) [] = No_match
Proof
  rw[pat_row_def, pmatch_def] >> gvs[cnenv_rel_def] >- metis_tac[] >>
  qpat_x_assum `∀cn. _` imp_res_tac >> simp[] >>
  IF_CASES_TAC >> gvs[same_ctor_def]
QED

Theorem pmatch_match:
  cnenv_rel cnenv cenv.c ∧
  ALOOKUP cnenv cn = SOME (tyid, LENGTH cvs) ∧
  LENGTH pvs = LENGTH cvs ⇒
  pmatch cenv.c cst (pat_row cn pvs) (Conv (SOME tyid) cvs) [] =
    Match $ REVERSE (ZIP (MAP var_prefix pvs,cvs))
Proof
  rw[pat_row_def, pmatch_def] >> gvs[cnenv_rel_def] >- metis_tac[] >>
  first_x_assum drule >> strip_tac >> simp[same_ctor_def] >>
  qsuff_tac `∀cvs pvs foo. LENGTH pvs = LENGTH cvs ⇒
    pmatch_list cenv.c cst (MAP (Pvar ∘ var_prefix) pvs) cvs foo =
      Match (REVERSE (ZIP (MAP var_prefix pvs,cvs)) ++ foo)` >- rw[] >>
  Induct >> rw[pmatch_def] >> Cases_on `pvs'` >> gvs[] >> simp[pmatch_def]
QED

Theorem pmatch_tuple:
  LENGTH pvs = LENGTH cvs ⇒
  pmatch cenv cst (pat_row "" pvs) (Conv NONE cvs) [] =
    Match $ REVERSE (ZIP (MAP var_prefix pvs,cvs))
Proof
  rw[pat_row_def, pmatch_def] >>
  qsuff_tac `∀cvs pvs foo. LENGTH pvs = LENGTH cvs ⇒
    pmatch_list cenv cst (MAP (Pvar ∘ var_prefix) pvs) cvs foo =
      Match (REVERSE (ZIP (MAP var_prefix pvs,cvs)) ++ foo)` >- rw[] >>
  Induct >> rw[pmatch_def] >> Cases_on `pvs'` >> gvs[] >> simp[pmatch_def]
QED

Theorem step1_rel_Case_match:
  LIST_REL
    (λ(cn,vs,se) (pat,ce). compile_rel cnenv se ce ∧ pat = pat_row cn vs)
    scss ccss ⇒
  EVERY (λ(cn,vs,_). ALL_DISTINCT vs ∧ ∃stamp'.
    ALOOKUP cnenv cn = SOME (stamp',LENGTH vs) ∧ same_type stamp' tyid) scss ∧
  ALOOKUP scss cn = SOME (pvs,sce) ∧
  ALOOKUP cnenv cn = SOME (tyid, LENGTH pvs) ∧
  LENGTH pvs = LENGTH cvs ∧
  cnenv_rel cnenv cenv.c
  ⇒ ∃n cce. cstep_n n (Estep (cenv,cst,fp,Val (Conv (SOME tyid) cvs),
                                (Cmat (ccss ++ any) bind_exn_v,cenv)::ck)) =
              Estep (cenv with v := nsAppend
                      (alist_to_ns (REVERSE (ZIP (MAP var_prefix pvs, cvs)))) cenv.v,
                     cst,fp,Exp cce,ck) ∧
          compile_rel cnenv sce cce
Proof
  Induct_on `LIST_REL` >> rw[] >> ntac 2 (pairarg_tac >> gvs[]) >>
  qrefine `SUC n` >> simp[cstep] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    irule FALSITY >> pop_assum mp_tac >> simp[] >>
    irule ALL_DISTINCT_MAP_INJ >> simp[var_prefix_def]
    ) >>
  gvs[AllCaseEqs()]
  >- (drule_all pmatch_match >> strip_tac >> simp[] >> qexists0 >> simp[]) >>
  drule_all pmatch_no_match >> strip_tac >> simp[] >>
  goal_assum drule >> simp[]
QED

Theorem step1_rel_Case_underscore:
  LIST_REL
    (λ(cn,vs,se) (pat,ce). compile_rel cnenv se ce ∧ pat = pat_row cn vs)
    scss ccss ⇒
  EVERY (λ(cn,vs,_). ALL_DISTINCT vs ∧ ∃stamp'.
    ALOOKUP cnenv cn = SOME (stamp',LENGTH vs) ∧ same_type stamp' tyid) scss ∧
  ALOOKUP scss cn = NONE ∧
  ALOOKUP cnenv cn = SOME (tyid, LENGTH cvs) ∧
  cnenv_rel cnenv cenv.c
  ⇒ ∃n. cstep_n n (Estep (cenv,cst,fp,Val (Conv (SOME tyid) cvs),
                            (Cmat (ccss ++ [Pany,cuse]) bind_exn_v,cenv)::ck)) =
              Estep (cenv,cst,fp,Exp cuse,ck)
Proof
  Induct_on `LIST_REL` >> rw[]
  >- (
    qrefine `SUC n` >> simp[cstep, astTheory.pat_bindings_def, pmatch_def] >>
    qexists0 >> simp[]
    ) >>
  ntac 2 (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  qrefine `SUC n` >> simp[cstep] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    irule FALSITY >> pop_assum mp_tac >> simp[] >>
    irule ALL_DISTINCT_MAP_INJ >> simp[var_prefix_def]
    ) >>
  drule_all pmatch_no_match >> strip_tac >> simp[]
QED


(***** compile_rel *****)

(* `ALL_DISTINCT vs` not necessary here, but useful for matching against *)
Theorem compile_rel_can_pmatch_all:
  ∀scss ccss c cn stamp id vs cnenv (cenv:semanticPrimitives$v sem_env) st
    cvs svs cuspat.
    LIST_REL
      (λ(cn,vs,se) (pat,ce). compile_rel cnenv se ce ∧ pat = pat_row cn vs)
      scss ccss ⇒
    EVERY (λ(cn,vs,_). ALL_DISTINCT vs ∧ ∃stamp'.
      ALOOKUP cnenv cn = SOME (stamp',LENGTH vs) ∧ same_type stamp' stamp) scss ∧
    cnenv_rel cnenv cenv.c ∧
    v_rel cnenv (Constructor cn svs) (Conv (SOME stamp) cvs) ∧
    (cuspat ≠ [] ⇒ cuspat = [Pany])
  ⇒ can_pmatch_all cenv.c st (MAP FST ccss ++ cuspat) (Conv (SOME stamp) cvs)
Proof
  Induct >> rw[] >> simp[can_pmatch_all_def]
  >- (Cases_on `cuspat` >> gvs[can_pmatch_all_def, pmatch_def]) >>
  ntac 2 (pairarg_tac >> gvs[]) >> rename1 `compile_rel _ se _` >> gvs[SF DNF_ss] >>
  last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
  simp[pat_row_def] >> gvs[cnenv_rel_def] >>
  qpat_x_assum `∀cn. _` imp_res_tac >> simp[pmatch_def] >>
  IF_CASES_TAC >> gvs[same_ctor_def] >>
  `cn = cn'` by metis_tac[] >> imp_res_tac LIST_REL_LENGTH >> gvs[] >>
  rename1 `pmatch_list _ _ _ _ bindings` >>
  qpat_x_assum `LENGTH vs = _` mp_tac >>
  map_every qid_spec_tac [`bindings`,`vs`,`cvs`] >>
  Induct >> rw[pmatch_def] >> Cases_on `vs'` >> gvs[] >> simp[pmatch_def]
QED

Theorem concat_vs_to_string:
  ∀strs cvs cnenv str.
    LIST_REL (v_rel cnenv) (MAP Atom strs) cvs ∧
    concat strs = SOME str
    ⇒ vs_to_string cvs = SOME str
Proof
  Induct >> rw[] >> gvs[vs_to_string_def, concat_def] >>
  first_x_assum drule >> rw[]
QED

Theorem dstep_rel_is_halt:
  dstep_rel s c ⇒ (is_halt s ⇔ is_halt c)
Proof
  reverse $ rw[dstep_rel_cases] >> simp[itree_semanticsTheory.is_halt_def]
QED


(***** primitive operations *****)

Theorem strle_lemma:
  ∀n s1 s2 len1 len2 env env' st fp c.
    nsLookup env.v (Short "strle") = SOME $ strle_v env' ∧
    nsLookup env'.c (Short $ "True") = SOME (0n, TypeStamp "True" bool_type_num) ∧
    nsLookup env'.c (Short $ "False") = SOME (0n, TypeStamp "False" bool_type_num) ∧
    len1 = LENGTH s1 ∧ len2 = LENGTH s2
  ⇒ ∃k env'. cstep_n k (Estep (env,st,fp, Exp (var "strle"),
        (Capp Opapp [Litv (IntLit &n)] [], env)::
        (Capp Opapp [Litv (StrLit s1)] [], env)::
        (Capp Opapp [Litv (StrLit s2)] [], env)::
        (Capp Opapp [Litv (IntLit &len1)] [], env)::
        (Capp Opapp [Litv (IntLit &len2)] [], env)::c)) =
      Estep (env',st,fp,Val (Boolv (DROP n s1 ≤ DROP n s2)),c)
Proof
  recInduct strle_ind >> rw[] >>
  ntac 2 (qrefine `SUC k` >> simp[cstep]) >>
  simp[do_opapp_def, strle_v_def] >> simp[find_recfun_def, build_rec_env_def] >>
  qmatch_goalsub_abbrev_tac `If _ _ rest` >>
  ntac 15 (qrefine `SUC k` >> simp[cstep, do_opapp_def, do_app_def]) >>
  simp[opb_lookup_def] >> Cases_on `STRLEN s1 ≤ n` >>
  ntac 1 (qrefine `SUC k` >> simp[cstep, do_if_def])
  >- (
    simp[do_con_check_def, build_conv_def] >>
    qexists0 >> simp[Boolv_def] >> IF_CASES_TAC >> simp[] >>
    pop_assum mp_tac >> simp[] >> `DROP n s1 = ""` by rw[DROP_EQ_NIL] >> simp[]
    ) >>
  unabbrev_all_tac >>
  ntac 5 (qrefine `SUC k` >> simp[cstep, do_app_def]) >>
  simp[do_app_def, opb_lookup_def] >> Cases_on `STRLEN s2 ≤ n` >>
  ntac 2 (qrefine `SUC k` >> simp[cstep, do_if_def])
  >- (
    simp[do_con_check_def, build_conv_def] >> qexists0 >> simp[Boolv_def] >>
    `DROP n s2 = ""` by rw[DROP_EQ_NIL] >> simp[] >> Cases_on `DROP n s1` >> gvs[]
    ) >>
  ntac 24 (qrefine `SUC k` >> simp[cstep, do_app_def, IMPLODE_EXPLODE_I]) >>
  gvs[NOT_LESS_EQUAL] >> imp_res_tac DROP_CONS_EL >> gvs[] >>
  simp[opb_lookup_def, do_if_def] >> IF_CASES_TAC >> gvs[]
  >- (
    ntac 1 (qrefine `SUC k` >> simp[cstep]) >>
    simp[do_con_check_def, build_conv_def] >>
    qexists0 >> simp[Boolv_def, char_lt_def]
    ) >>
  ntac 7 (qrefine `SUC k` >> simp[cstep, do_app_def, do_eq_def, lit_same_type_def]) >>
  simp[do_if_def] >> reverse $ IF_CASES_TAC >> gvs[ORD_11]
  >- (
    ntac 1 (qrefine `SUC k` >> simp[cstep]) >>
    simp[do_con_check_def, build_conv_def] >>
    qexists0 >> simp[Boolv_def, char_lt_def]
    ) >>
  ntac 19 (qrefine `SUC k` >> simp[cstep, do_app_def, opn_lookup_def]) >>
  gvs[integerTheory.INT_ADD_CALCULATE, char_lt_def, ADD1] >>
  qpat_abbrev_tac `env'' = env' with v := _` >>
  last_x_assum $ irule_at Any >>
  goal_assum drule >> simp[Abbr `env''`,strle_v_def]
QED

Theorem strle:
  ∀s1 s2 env env' st fp c.
    nsLookup env.v (Short "strle") = SOME $ strle_v env' ∧
    nsLookup env'.c (Short $ "True") = SOME (0n, TypeStamp "True" bool_type_num) ∧
    nsLookup env'.c (Short $ "False") = SOME (0n, TypeStamp "False" bool_type_num)
  ⇒ ∃k env'. cstep_n k (Estep (env,st,fp, Exp (var "strle"),
        (Capp Opapp [Litv (IntLit 0)] [], env)::
        (Capp Opapp [Litv (StrLit s1)] [], env)::
        (Capp Opapp [Litv (StrLit s2)] [], env)::
        (Capp Opapp [Litv (IntLit &LENGTH s1)] [], env)::
        (Capp Opapp [Litv (IntLit &LENGTH s2)] [], env)::c)) =
      Estep (env',st,fp,Val (Boolv (s1 ≤ s2)),c)
Proof
  rw[] >> drule_all $ SRULE [] strle_lemma >>
  disch_then $ qspec_then `0` mp_tac >> simp[]
QED

Theorem char_list:
  ∀l env env' st fp c.
    nsLookup env.v (Short "char_list") = SOME $ char_list_v env' ∧
    nsLookup env'.c (Short $ "[]") = SOME (0n, TypeStamp "[]" list_type_num) ∧
    nsLookup env'.c (Short $ "::") = SOME (2n, TypeStamp "::" list_type_num)
  ⇒ ∃k env'. cstep_n k (Estep (env,st,fp, Exp (var "char_list"),
        (Capp Opapp [list_to_v (MAP (Litv o IntLit) l)] [], env)::c)) =
      Estep (env',st,fp,
        Val (list_to_v (MAP (λi. Litv $ Char $ CHR $ Num $ i % 256) l)),c)
Proof
  Induct >> rw[list_to_v_def]
  >- (
    qrefine `SUC k` >> simp[cstep, char_list_v_def] >>
    qrefine `SUC k` >> simp[cstep, do_opapp_def, find_recfun_def, build_rec_env_def] >>
    ntac 3 (qrefine `SUC k` >> simp[cstep]) >>
    simp[can_pmatch_all_def, pmatch_def, same_ctor_def, same_type_def] >>
    qrefine `SUC k` >> simp[cstep] >>
    simp[astTheory.pat_bindings_def, pmatch_def, same_ctor_def, same_type_def] >>
    qrefine `SUC k` >> simp[cstep] >>
    simp[do_con_check_def, build_conv_def] >>
    qexists0 >> simp[]
    ) >>
  ntac 2 (qrefine `SUC k` >> simp[cstep, char_list_v_def]) >>
  simp[do_opapp_def, find_recfun_def, build_rec_env_def] >>
  ntac 3 (qrefine `SUC k` >> simp[cstep]) >>
  simp[can_pmatch_all_def, pmatch_def, same_ctor_def, same_type_def] >>
  ntac 1 (qrefine `SUC k` >> simp[cstep]) >>
  simp[astTheory.pat_bindings_def, pmatch_def, same_ctor_def, same_type_def] >>
  ntac 1 (qrefine `SUC k` >> simp[cstep]) >>
  simp[astTheory.pat_bindings_def, pmatch_def, same_ctor_def, same_type_def] >>
  ntac 1 (qrefine `SUC k` >> simp[cstep]) >>
  simp[do_con_check_def, build_conv_def] >>
  ntac 3 (qrefine `SUC k` >> simp[cstep]) >>
  qmatch_goalsub_abbrev_tac `(env' with v := new_env, _, _, _, _::c')` >>
  last_x_assum $ qspecl_then [`env' with v := new_env`,`env'`,`st`,`fp`,`c'`] mp_tac >>
  simp[] >> impl_tac >- (unabbrev_all_tac >> simp[char_list_v_def]) >>
  strip_tac >> gvs[] >> qrefine `n + k` >> simp[cstep_n_add] >>
  pop_assum kall_tac >> unabbrev_all_tac >>
  ntac 1 (qrefine `SUC k` >> simp[cstep]) >>
  simp[do_con_check_def] >>
  ntac 6 (qrefine `SUC k` >> simp[cstep]) >>
  simp[do_app_def, opn_lookup_def] >>
  ntac 1 (qrefine `SUC k` >> simp[cstep]) >>
  simp[do_app_def] >> `¬ (h % 256 < 0 ∨ h % 256 > 255)` by ARITH_TAC >> simp[] >>
  ntac 1 (qrefine `SUC k` >> simp[cstep]) >>
  simp[do_con_check_def, build_conv_def] >>
  qexists0 >> simp[] >>
  `ABS (h % 256) = h % 256` by ARITH_TAC >> simp[]
QED

Theorem implode_SOME:
  ∀l s. implode l = SOME s ⇒ ∃il. l = MAP Int il
Proof
  Induct >> rw[] >> Cases_on `h` >> gvs[implode_def] >>
  simp[MAP_EQ_CONS] >> irule_at Any EQ_REFL
QED

Triviality implode_v_to_char_list_list_to_v:
  ∀il. implode (MAP Int il) =
  v_to_char_list (list_to_v (MAP (λi. Litv (Char (CHR (Num (i % 256))))) il))
Proof
  Induct >> rw[implode_def, list_to_v_def, v_to_char_list_def] >>
  TOP_CASE_TAC >> gvs[]
QED


(********** Main results **********)

Theorem step1_rel:
  step_rel s c ∧ ¬is_halt s ∧ (∀n st k. step_n n s ≠ error st k)
  ⇒ ∃n. step_rel (step_n 1 s) (cstep_n (SUC n) c) ∧
        ∀ws. get_ffi_array (cstep_n (SUC n) c) = SOME ws ⇒
             get_ffi_array c = SOME ws
Proof
  rw[Once step_rel_cases] >> gvs[]
  >- ( (* Exp *)
    pop_assum $ qspec_then `1` assume_tac >> gvs[] >>
    gvs[Once compile_rel_cases, sstep, cstep]
    >~ [`Concat`]
    >- ( (* Concat *)
      `cnenv_rel cnenv cenv.c` by gvs[env_rel_def] >>
      drule cnenv_rel_list_type >> strip_tac >>
      TOP_CASE_TAC >> gvs[]
      >- (
        gvs[eval_op_def, concat_def, list_to_exp_def] >>
        ntac 2 (qrefine `SUC n` >> simp[cstep]) >>
        simp[do_app_def, v_to_list_def, v_to_char_list_def,
             list_type_num_def, vs_to_string_def] >>
        qexists0 >> simp[step_rel_cases, SF SFY_ss]
        ) >>
      gvs[SWAP_REVERSE_SYM, LIST_REL_SPLIT1, REVERSE_APPEND] >>
      qspecl_then [`ys1 ++ [y]`,`cnenv`,`cenv`,`cst`,`fp`,`(Capp Strcat [] [],cenv)::ck`]
        assume_tac cstep_list_to_exp >> gvs[] >>
      qrefine `m + n` >> simp[cstep_n_add, REVERSE_APPEND] >>
      qrefine `SUC m` >> simp[cstep, list_to_cont_def] >>
      qexists0 >> simp[step_rel_cases] >> goal_assum drule >>
      simp[Once cont_rel_cases, list_to_v_def, list_type_num_def] >>
      irule_at Any EQ_REFL >> simp[EVERY2_REVERSE1]
      )
    >~ [`Implode`]
    >- ( (* Implode *)
      `cnenv_rel cnenv cenv.c` by gvs[env_rel_def] >>
      drule cnenv_rel_list_type >> strip_tac >>
      TOP_CASE_TAC >> gvs[]
      >- (
        gvs[eval_op_def, implode_def, list_to_exp_def] >>
        ntac 3 (qrefine `SUC n` >> simp[cstep]) >>
        drule $ cj 3 env_ok_imps >> strip_tac >> gvs[] >>
        drule_all char_list >>
        disch_then $ qspecl_then
          [`[]`,`cst`,`fp`,`(Capp Implode [] [], cenv)::ck`] assume_tac >> gvs[] >>
        qrefine `n + k` >> simp[cstep_n_add] >> gvs[list_to_v_def, list_type_num_def] >>
        ntac 1 (qrefine `SUC n` >> simp[cstep]) >>
        simp[do_app_def, v_to_char_list_def, list_type_num_def] >>
        qexists0 >> simp[step_rel_cases, SF SFY_ss]
        ) >>
      gvs[SWAP_REVERSE_SYM, LIST_REL_SPLIT1, REVERSE_APPEND] >>
        ntac 1 (qrefine `SUC n` >> simp[cstep]) >>
        qmatch_goalsub_abbrev_tac `Estep (_,_,_,_,ck')` >>
      qspecl_then [`ys1 ++ [y]`,`cnenv`,`cenv`,`cst`,`fp`,`ck'`]
        assume_tac cstep_list_to_exp >> gvs[] >>
      qrefine `m + n` >> simp[cstep_n_add, REVERSE_APPEND] >>
      qrefine `SUC m` >> simp[cstep, list_to_cont_def] >> unabbrev_all_tac >>
      qexists0 >> simp[step_rel_cases] >> goal_assum drule >>
      simp[Once cont_rel_cases, list_to_v_def, list_type_num_def] >>
      irule_at Any EQ_REFL >> simp[EVERY2_REVERSE1]
      )
    >>~ [`Cmat_check`]
    >- ( (* Case - None *)
      ntac 3 (TOP_CASE_TAC >> gvs[]) >> gvs[find_match_SOME, find_match_list_SOME] >>
      qrefine `SUC n` >> simp[cstep] >> drule_all env_rel_lookup >> strip_tac >> gvs[]
      >- (
        irule FALSITY >> imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM] >>
        first_x_assum drule >> strip_tac >> gvs[] >>
        gvs[env_rel_def, cnenv_rel_def] >> metis_tac[]
        ) >>
      rename1 `_ = LENGTH svs` >> rename1 `ALOOKUP scss _ = SOME (_,sce)` >>
      `same_type tyid stamp` by (
        gvs[EVERY_MEM] >> imp_res_tac ALOOKUP_MEM >> last_x_assum drule >> simp[]) >>
      `EVERY (λ(cn,vs,se). ALL_DISTINCT vs ∧
         ∃stamp'. ALOOKUP cnenv cn = SOME (stamp',LENGTH vs) ∧
            same_type stamp' tyid) scss` by (
          gvs[EVERY_MEM] >> rw[] >> pairarg_tac >> gvs[] >>
          first_x_assum drule >> rw[] >> simp[] >>
          metis_tac[evaluatePropsTheory.same_type_trans,
                    evaluatePropsTheory.same_type_sym]) >>
      pop_assum mp_tac >> pop_assum kall_tac >>
      qpat_x_assum `EVERY _ _` kall_tac >> strip_tac >>
      drule compile_rel_can_pmatch_all >> disch_then drule >> simp[] >>
      rpt $ disch_then $ drule_at Any >> gvs[] >>
      disch_then $ qspecl_then [`cenv`,`cst`,`[]`] mp_tac >>
      impl_keep_tac >- gvs[env_rel_def] >> strip_tac >> gvs[] >>
      qrefine `SUC n` >> simp[cstep] >>
      drule step1_rel_Case_match >> rpt $ disch_then $ drule_at Any >>
      disch_then $ qspecl_then [`fp`,`cvs`,`cst`,`ck`,`[]`] mp_tac >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >> strip_tac >> gvs[] >>
      qexists `n` >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      irule_at Any env_rel_pmatch >> irule_at Any env_ok_pmatch >> simp[]
      )
    >- ( (* Case - Some *)
      ntac 3 (TOP_CASE_TAC >> gvs[]) >>
      qrefine `SUC n` >> simp[cstep] >> drule_all env_rel_lookup >> strip_tac >> gvs[] >>
      gvs[find_match_SOME, find_match_list_SOME]
      >>~- (
        [`ALOOKUP _ ""`],
          irule FALSITY >> imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM] >>
          first_x_assum drule >> strip_tac >> gvs[] >>
          gvs[env_rel_def, cnenv_rel_def] >> metis_tac[]
        )
      >- (
        rename1 `_ = LENGTH svs` >> rename1 `ALOOKUP scss _ = SOME (_,sce)` >>
        `same_type tyid stamp` by (
          gvs[EVERY_MEM] >> imp_res_tac ALOOKUP_MEM >> last_x_assum drule >> simp[]) >>
        `EVERY (λ(cn,vs,se). ALL_DISTINCT vs ∧
           ∃stamp'. ALOOKUP cnenv cn = SOME (stamp',LENGTH vs) ∧
              same_type stamp' tyid) scss` by (
            gvs[EVERY_MEM] >> rw[] >> pairarg_tac >> gvs[] >>
            first_x_assum drule >> rw[] >> simp[] >>
            metis_tac[evaluatePropsTheory.same_type_trans,
                      evaluatePropsTheory.same_type_sym]) >>
        pop_assum mp_tac >> pop_assum kall_tac >>
        qpat_x_assum `EVERY _ _` kall_tac >> strip_tac >>
        drule compile_rel_can_pmatch_all >> disch_then drule >> simp[] >>
        rpt $ disch_then $ drule_at Any >> gvs[] >>
        disch_then $ qspecl_then [`cenv`,`cst`,`[Pany]`] mp_tac >>
        impl_keep_tac >- gvs[env_rel_def] >> strip_tac >> gvs[] >>
        qrefine `SUC n` >> simp[cstep] >>
        drule step1_rel_Case_match >> rpt $ disch_then $ drule_at Any >>
        disch_then $ qspecl_then [`fp`,`cvs`,`cst`,`ck`,`[Pany,cuse]`] mp_tac >>
        imp_res_tac LIST_REL_LENGTH >> gvs[] >> strip_tac >> gvs[] >>
        qexists `n` >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        irule_at Any env_rel_pmatch >> irule_at Any env_ok_pmatch >> simp[]
        )
      >- (
        `same_type tyid stamp` by (
          gvs[EVERY_MEM] >> imp_res_tac ALOOKUP_MEM >> last_x_assum drule >> simp[]) >>
        `EVERY (λ(cn,vs,se). ALL_DISTINCT vs ∧
           ∃stamp'. ALOOKUP cnenv cn = SOME (stamp',LENGTH vs) ∧
              same_type stamp' tyid) scss` by (
            gvs[EVERY_MEM] >> rw[] >> pairarg_tac >> gvs[] >>
            first_x_assum drule >> rw[] >> simp[] >>
            metis_tac[evaluatePropsTheory.same_type_trans,
                      evaluatePropsTheory.same_type_sym]) >>
        pop_assum mp_tac >> pop_assum kall_tac >>
        qpat_x_assum `EVERY _ _` kall_tac >> strip_tac >>
        drule compile_rel_can_pmatch_all >> disch_then drule >> simp[] >>
        rpt $ disch_then $ drule_at Any >> gvs[] >>
        disch_then $ qspecl_then [`cenv`,`cst`,`[Pany]`] mp_tac >>
        impl_keep_tac >- gvs[env_rel_def] >> strip_tac >> gvs[] >>
        qrefine `SUC n` >> simp[cstep] >>
        drule step1_rel_Case_underscore >> rpt $ disch_then $ drule_at Any >>
        disch_then $ qspecl_then [`fp`,`cvs`,`cuse`,`cst`,`ck`] mp_tac >>
        imp_res_tac LIST_REL_LENGTH >> gvs[] >> strip_tac >> gvs[] >>
        qexists `n` >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any
        )
      )
    >- ( (* TupleCase *)
      ntac 3 (TOP_CASE_TAC >> gvs[]) >> gvs[find_match_SOME, find_match_list_SOME] >>
      qrefine `SUC n` >> simp[cstep] >>
      drule_all env_rel_lookup >> strip_tac >> simp[] >>
      qrefine `SUC n` >> simp[cstep] >> gvs[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[can_pmatch_all_tuple] >>
      qrefine `SUC n` >> simp[cstep] >>
      reverse IF_CASES_TAC >> gvs[pmatch_tuple]
      >- (
        irule FALSITY >> pop_assum mp_tac >> simp[] >>
        irule ALL_DISTINCT_MAP_INJ >> simp[var_prefix_def]
        ) >>
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      irule_at Any env_rel_pmatch >> irule_at Any env_ok_pmatch >> simp[]
      ) >>
    qexists0 >> simp[]
    >- simp[step_rel_cases, SF SFY_ss] (* IntLit *)
    >- simp[step_rel_cases, SF SFY_ss] (* StrLit *)
    >- ( (* Tuple *)
      simp[do_con_check_def] >> TOP_CASE_TAC >> gvs[]
      >- (simp[build_conv_def] >> simp[step_rel_cases, SF SFY_ss]) >>
      gvs[SWAP_REVERSE_SYM, LIST_REL_SPLIT1, REVERSE_APPEND] >>
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases, EVERY2_REVERSE1]
      )
    >- ( (* Constructor *)
      drule_all env_rel_check >> strip_tac >> simp[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      TOP_CASE_TAC >> gvs[]
      >- (
        qspec_then `[]` mp_tac env_rel_build >> simp[] >>
        disch_then drule_all >> strip_tac >> simp[step_rel_cases, SF SFY_ss]
        ) >>
      gvs[SWAP_REVERSE_SYM, LIST_REL_SPLIT1, REVERSE_APPEND] >>
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases, EVERY2_REVERSE1]
      )
    >- ( (* Var *)
      CASE_TAC >> gvs[] >> drule_all env_rel_lookup >> strip_tac >> gvs[] >>
      simp[step_rel_cases, SF SFY_ss]
      )
    >- ( (* App *)
      IF_CASES_TAC >> gvs[] >> reverse $ TOP_CASE_TAC >> gvs[]
      >- (
        gvs[SWAP_REVERSE_SYM, LIST_REL_SPLIT1, REVERSE_APPEND] >>
        simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        simp[Once cont_rel_cases, EVERY2_REVERSE1]
        ) >>
      gvs[num_args_ok_0, op_rel_cases] >>
      Cases_on `aop` >> gvs[sstep, eval_op_def] >>
      gvs[atom_op_rel_cases, opn_rel_cases, opb_rel_cases]
      )
    >- ( (* TwoArgs *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    >- ( (* Substring3 *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    >- ( (* Alloc *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    >- ( (* FFI *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    >- simp[step_rel_cases, SF SFY_ss] (* Lam *)
    >- ( (* Letrec *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      irule_at Any env_rel_Recclosure >> irule_at Any env_ok_Recclosure >> simp[] >>
      rw[EVERY_EL] >> gvs[LIST_REL_EL_EQN] >>
      first_x_assum drule >> ntac 2 (pairarg_tac >> simp[]) >>
      rw[] >> irule_at Any EQ_REFL
      )
    >- ( (* Let *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    >- ( (* If *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    >- ( (* Raise *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    >- ( (* Handle *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    )
  >~ [`Exn`]
  >- ( (* Raise *)
    pop_assum $ qspec_then `1` assume_tac >> gvs[] >>
    Cases_on `sk` >> gvs[sstep] >>
    Cases_on `h` >> gvs[Once cont_rel_cases] >> simp[cstep]
    >>~ [`list_to_cont`]
    >- ( (* Concat *)
      qrefine `n + LENGTH ces` >>
      simp[cstep_n_add] >> once_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[cstep_Exn_over_list_to_cont] >>
      qrefine `SUC n` >> simp[cstep] >> qexists0 >> simp[] >>
      simp[step_rel_cases, SF SFY_ss]
      )
    >- ( (* Implode *)
      qrefine `n + LENGTH ces` >>
      simp[cstep_n_add] >> once_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[cstep_Exn_over_list_to_cont] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep]) >>
      qexists0 >> simp[] >> simp[step_rel_cases, SF SFY_ss]
      )
    >~ [`Exp`,`Pvar`]
    >- ( (* HandleK *)
      qrefine `SUC n` >> simp[cstep] >>
      simp[can_pmatch_all_def, pmatch_def] >>
      qrefine `SUC n` >> simp[cstep] >>
      simp[astTheory.pat_bindings_def, pmatch_def] >>
      qexists0 >> simp[step_rel_cases] >>
      rpt $ goal_assum $ drule_at Any >> simp[] >>
      irule env_rel_nsBind >> simp[]
      ) >>
    qexists0 >> simp[] >> simp[step_rel_cases, SF SFY_ss]
    ) >>
  (* Val *)
  Cases_on `sk` >> gvs[sstep] >>
  gvs[DefnBase.one_line_ify NONE return_def] >>
  reverse TOP_CASE_TAC >> gvs[Once cont_rel_cases, sstep, cstep]
  >- ( (* ForceMutK *)
    first_x_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
    Cases_on `n < LENGTH sst` >> gvs[] >>
    Cases_on `store_same_type (EL n sst) (ThunkMem Evaluated sv)` >> gvs[] >>
    qexists0 >> simp[step_rel_cases, SF SFY_ss] >>
    reverse $ rw[store_assign_def]
    >- gvs[state_rel, store_lookup_def, LUPDATE_DEF]
    >- (
      Cases_on `EL n sst` >> gvs[store_same_type_def] >>
      Cases_on `t'` >> gvs[state_rel, LIST_REL_EL_EQN, store_v_same_type_def,
                           EL_CONS, PRE_SUB1] >>
      FULL_CASE_TAC >> first_x_assum $ qspec_then `n` assume_tac >>
      gvs[store_rel_def]
      )
    >- (
      first_assum $ irule_at Any >>
      gvs[state_rel, LUPDATE_DEF, PRE_SUB1] >>
       irule EVERY2_LUPDATE_same >>
      gvs[store_rel_def]
      )
    )
  >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) (* HandleK *)
  >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) (* RaiseK *)
  >- ( (* IfK *)
    first_x_assum $ qspec_then `1` assume_tac >> gvs[sstep, AllCaseEqs()]
    >- (
      `Conv (SOME tyid) [] = Boolv T` by
        gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def, Boolv_def] >>
      simp[do_if_def] >>
      qexists0 >> simp[step_rel_cases, PULL_EXISTS, GSYM CONJ_ASSOC] >>
      rpt $ goal_assum $ drule_at Any >> simp[AllCaseEqs()]
      )
    >- (
      `Conv (SOME tyid) [] = Boolv F` by
        gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def, Boolv_def] >>
      simp[do_if_def] >>
      qexists0 >> simp[step_rel_cases, PULL_EXISTS, GSYM CONJ_ASSOC] >>
      rpt $ goal_assum $ drule_at Any >> simp[AllCaseEqs()]
      )
    )
  >- ( (* LetK *)
    qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
    irule env_rel_nsBind >> simp[]
    )
  >- ( (* TupleK *)
    TOP_CASE_TAC >> gvs[cstep, do_con_check_def, build_conv_def] >>
    qexists0 >> simp[step_rel_cases, SF SFY_ss] >>
    rpt $ goal_assum $ drule_at Any >> simp[Once cont_rel_cases]
    )
  >- ( (* AppK (Cons cn) *)
    drule_all env_rel_check >> strip_tac >>
    imp_res_tac LIST_REL_LENGTH >> gvs[] >>
    reverse TOP_CASE_TAC >> gvs[cstep, ADD1]
    >- ( (* more arguments to evaluate *)
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      ) >>
    qspec_then `cv::cvs` mp_tac env_rel_build >> simp[ADD1] >>
    disch_then drule_all >> strip_tac >> simp[] >>
    qexists0 >> simp[step_rel_cases, ADD1, SF SFY_ss]
    )
  >- ( (* AppK *)
    reverse TOP_CASE_TAC >> gvs[cstep]
    >- ( (* more arguments to evaluate *)
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      ) >>
    Cases_on `s = AppOp` >> gvs[]
    >- (
      gvs[op_rel_cases] >>
      pop_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
      TOP_CASE_TAC >> gvs[dest_anyClosure_def, LENGTH_EQ_NUM_compute] >>
      TOP_CASE_TAC >> gvs[] >> PairCases_on `x` >> gvs[] >>
      reverse $ Cases_on `dest_Closure sv` >> gvs[]
      >- ( (* Closure *)
        Cases_on `sv` >> gvs[opt_bind_def, cstep, do_opapp_def] >>
        qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        irule env_rel_nsBind >> simp[]
        ) >>
      (* Recclosure *)
      Cases_on `dest_Recclosure sv` >> gvs[] >>
      PairCases_on `x` >> rename1 `SOME (f,env,n)` >> gvs[] >>
      Cases_on `ALOOKUP f n` >> gvs[] >> Cases_on `x` >> gvs[] >>
      Cases_on `sv` >> gvs[cstep] >>
      simp[do_opapp_def, semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
      qpat_x_assum `ALL_DISTINCT _` mp_tac >> rw[FST_THM, Once LAMBDA_PROD] >>
      imp_res_tac ALOOKUP_SOME_EL >>
      drule $ iffLR LIST_REL_EL_EQN >> strip_tac >>
      pop_assum drule >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      simp[opt_bind_def] >>
      drule ALOOKUP_ALL_DISTINCT_EL >> rw[FST_THM, Once LAMBDA_PROD] >>
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      irule_at Any env_ok_nsBind_Recclosure >>
      irule_at Any env_rel_nsBind_Recclosure >> simp[FST_THM, LAMBDA_PROD] >>
      rw[EVERY_EL] >> gvs[LIST_REL_EL_EQN] >>
      last_x_assum drule >> simp[] >> ntac 2 (pairarg_tac >> gvs[]) >>
      strip_tac >> simp[] >> qexists_tac `sv` >> simp[]
      ) >>
    `cop ≠ Opapp` by (CCONTR_TAC >> gvs[op_rel_cases, atom_op_rel_cases]) >>
    `get_ffi_ch cop = NONE` by (
      CCONTR_TAC >> Cases_on `cop` >> gvs[op_rel_cases, atom_op_rel_cases]) >>
    simp[] >> first_x_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
    IF_CASES_TAC >> gvs[] >> reverse $ gvs[op_rel_cases, ADD1, cstep]
    >>~- ([`AllocMutThunk`],
        gvs[application_def, sstep] >>
        ntac 2 (TOP_CASE_TAC >> gvs[]) >>
        gvs[do_app_def, thunk_op_def] >>
        pairarg_tac >> gvs[store_alloc_def] >>
        qexists0 >> reverse $ rw[step_rel_cases]
        >- gvs[state_rel, store_lookup_def] >>
        qexists `cnenv` >> gvs[state_rel] >>
        imp_res_tac LIST_REL_LENGTH >> rw[store_rel_def])
    >>~- ([`UpdateMutThunk`],
      `LENGTH l0 = 1` by gvs [] >> gvs[LENGTH_EQ_NUM_compute] >>
      gvs [application_def, sstep] >>
      Cases_on `sv` >> gvs[] >>
      ntac 3 (TOP_CASE_TAC >> gvs[]) >>
      simp[do_app_def] >> drule state_rel_store_lookup >>
      disch_then $ qspec_then `n` assume_tac >> gvs[] >>
      simp [thunk_op_def] >> gvs[] >>
      Cases_on `z` >> gvs[store_rel_def] >>
      Cases_on `b` >> gvs[store_rel_def] >>
      drule store_lookup_assign_Thunk >> rw[] >>
      qexists0 >> reverse $ rw[step_rel_cases]
      >- gvs[state_rel, LUPDATE_DEF, store_lookup_def] >>
      goal_assum drule >> gvs[state_rel] >> simp[LUPDATE_DEF, GSYM ADD1] >>
      irule EVERY2_LUPDATE_same >> simp[store_rel_def])
    >~ [`ForceMutThunk`]
    >- (
      gvs[application_def, sstep] >>
      ntac 4 (TOP_CASE_TAC >> gvs[]) >>
      gvs[state_rel, store_lookup_def, oEL_THM, LIST_REL_EL_EQN] >>
      first_assum $ qspec_then `n` assume_tac >>
      Cases_on `EL n cst'` >> gvs[store_rel_def] >>
      Cases_on `b` >> gvs[store_rel_def] >>
      rw[EL_CONS, PRE_SUB1] >>
      qexists0 >> reverse $ rw[step_rel_cases, store_lookup_def]
      >- (goal_assum drule >> gvs[state_rel, LIST_REL_EL_EQN])
      >- (
        gvs[do_opapp_def] >>
        ntac 4 (FULL_CASE_TAC >> gvs[store_lookup_def])
        ) >>
      Cases_on `dest_anyClosure v` >> gvs[] >>
      Cases_on `x` >> gvs[] >>
      Cases_on `r` >> gvs[] >>
      rw [do_opapp_def] >>
      Cases_on `a` >> rw[] >>
      Cases_on `v` >> gvs[Once v_rel_cases,dest_anyClosure_def]
      >- (
        goal_assum $ drule_at Any >>
        simp[Once cont_rel_cases,state_rel_def,LIST_REL_EL_EQN,opt_bind_def] >>
        gvs [env_rel_def] >> rw[]
        )
      >- (
        Cases_on `ALOOKUP l0 s'` >> gvs[] >>
        Cases_on `x` >> gvs[] >>
        simp[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
        imp_res_tac ALOOKUP_SOME_EL >>
        Cases_on `ALOOKUP l' (var_prefix s')` >> gvs[]
        >- (
          gvs[LIST_REL_EL_EQN] >>
          first_x_assum drule >> rw[] >> pairarg_tac >> gvs[] >>
          drule_all ALOOKUP_ALL_DISTINCT_EL >> rpt strip_tac >> gvs[]
        ) >>
        Cases_on `x` >> gvs[] >>
        qexists `cnenv` >>
        rw[Once cont_rel_cases,state_rel_def,LIST_REL_EL_EQN]
        >- (
          gvs[LIST_REL_EL_EQN] >>
          first_x_assum drule >> rw[] >> pairarg_tac >> gvs[] >>
          drule_all ALOOKUP_ALL_DISTINCT_EL >> rw[]
          )
        >- (
          `v_rel cnenv (Constructor "" []) (Conv NONE [])`
            by gvs[Once v_rel_cases] >>
          drule_all env_rel_nsBind_Recclosure >> rw[] >>
          gvs[LIST_REL_EL_EQN] >>
          first_x_assum drule >> rw[] >> pairarg_tac >> gvs[opt_bind_def] >>
          drule_all ALOOKUP_ALL_DISTINCT_EL >> rw[]
          )
        >- (
          `EVERY (λ(cv,cx,ce). ∃sv. cv = var_prefix sv) l'`
            by (
              rw[EVERY_EL] >> pairarg_tac >> gvs[LIST_REL_EL_EQN] >>
              first_x_assum drule >> rw[] >> pairarg_tac >> gvs[]
              ) >>
          drule_all env_ok_nsBind_Recclosure >> rw[] >> gvs[LIST_REL_EL_EQN] >>
          first_x_assum drule >> rw[] >> pairarg_tac >> gvs[opt_bind_def] >>
          drule_all ALOOKUP_ALL_DISTINCT_EL >> rw[]
          )
        )
      >- gvs[ALL_DISTINCT_MAP_FSTs]
       )
    >- ( (* Update *)
      `LENGTH l0 = 2` by gvs[] >> gvs[LENGTH_EQ_NUM_compute] >>
      rename1 `[lnum;idx;elem]` >> gvs[application_def, sstep] >>
      Cases_on `lnum` >> gvs[] >> Cases_on `idx` >> gvs[] >>
      TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[DISJ_EQ_IMP] >>
      simp[do_app_def] >> drule state_rel_store_lookup >>
      disch_then $ qspec_then `n` assume_tac >> gvs[] >>
      Cases_on `z` >> gvs[store_rel_def] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      TOP_CASE_TAC
      >- ( (* in bounds *)
        `¬(i < 0)` by ARITH_TAC >> simp[] >>
        `¬(Num (ABS i) ≥ LENGTH l'')` by ARITH_TAC >> simp[] >>
        drule store_lookup_assign_Varray >> rw[] >>
        `ABS i = i` by ARITH_TAC >> simp[] >>
        qexists0 >> reverse $ rw[step_rel_cases]
        >- gvs[state_rel, LUPDATE_DEF, store_lookup_def] >>
        goal_assum drule >> gvs[state_rel] >> simp[LUPDATE_DEF, GSYM ADD1] >>
        ntac 2 (irule EVERY2_LUPDATE_same >> simp[store_rel_def])
        )
      >- ( (* out of bounds *)
        qmatch_goalsub_abbrev_tac `cstep_n _ foo` >>
        `foo = Estep (cenv',cst,fp,Exn sub_exn_v,ck')` by (
          unabbrev_all_tac >> simp[AllCaseEqs()] >> ARITH_TAC) >>
        simp[] >> ntac 2 $ pop_assum kall_tac >>
        qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        simp[sub_exn_v_def] >> gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def]
        )
      )
    >- ( (* Sub *)
      `LENGTH l0 = 1` by gvs[] >> gvs[LENGTH_EQ_NUM_compute] >>
      rename1 `[lnum;idx]` >> gvs[application_def, sstep] >>
      Cases_on `lnum` >> gvs[] >> Cases_on `idx` >> gvs[] >>
      TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[DISJ_EQ_IMP] >>
      simp[do_app_def] >> drule state_rel_store_lookup >>
      disch_then $ qspec_then `n` assume_tac >> gvs[] >>
      Cases_on `z` >> gvs[store_rel_def] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      TOP_CASE_TAC
      >- ( (* in bounds *)
        `¬(i < 0)` by ARITH_TAC >> simp[] >>
        `¬(Num (ABS i) ≥ LENGTH l'')` by ARITH_TAC >> simp[] >>
        `ABS i = i` by ARITH_TAC >> simp[] >>
        qexists0 >> rw[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        gvs[LIST_REL_EL_EQN]
        )
      >- ( (* out of bounds *)
        qmatch_goalsub_abbrev_tac `cstep_n _ foo` >>
        `foo = Estep (cenv',cst,fp,Exn sub_exn_v,ck')` by (
          unabbrev_all_tac >> simp[AllCaseEqs()] >> ARITH_TAC) >>
        simp[] >> ntac 2 $ pop_assum kall_tac >>
        qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        simp[sub_exn_v_def] >> gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def]
        )
      )
    >- ( (* Length *)
      gvs[application_def, sstep] >> Cases_on `sv` >> gvs[] >>
      ntac 2 (TOP_CASE_TAC >> gvs []) >> simp[do_app_def] >>
      drule state_rel_store_lookup >>
      disch_then $ qspec_then `n` assume_tac >> gvs[] >>
      Cases_on `z` >> gvs[store_rel_def] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      qexists0 >> rw[step_rel_cases, SF SFY_ss]
      ) >>
    (* AtomOp *)
    gvs[application_def, sstep] >>
    TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
    reverse $ gvs[atom_op_rel_cases, cstep]
    >- ( (* StrEq *)
      gvs[eval_op_SOME] >> simp[do_app_def, do_eq_def, lit_same_type_def] >>
      qexists0 >> rw[step_rel_cases, Boolv_def] >> rpt $ goal_assum $ drule_at Any >>
      gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def]
      )
    >- ( (* Len str *)
      gvs[eval_op_SOME] >> simp[do_app_def] >>
      qexists0 >> rw[step_rel_cases, SF SFY_ss]
      )
    >- ( (* Eq int *)
      gvs[eval_op_SOME] >> simp[do_app_def, do_eq_def, lit_same_type_def] >>
      qexists0 >> rw[step_rel_cases, Boolv_def] >> rpt $ goal_assum $ drule_at Any >>
      gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def]
      )
    >- ( (* opb *)
      gvs[opb_rel_cases] >> gvs[eval_op_SOME] >>
      simp[cstep, do_app_def, opb_lookup_def] >>
      qexists0 >> rw[step_rel_cases, Boolv_def] >> rpt $ goal_assum $ drule_at Any >>
      gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def]
      )
    >- ( (* opn *)
      gvs[opn_rel_cases] >> gvs[eval_op_SOME] >>
      simp[cstep, do_app_def, opn_lookup_def] >>
      qexists0 >> rw[step_rel_cases, SF SFY_ss]
      )
    )
  >- ( (* TwoArgs - second argument to evaluate *)
    qrefine `SUC n` >> simp[cstep_n_def, cstep] >>
    qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
    simp[Once cont_rel_cases] >>
    irule_at Any env_rel_nsBind_alt >> simp[var_prefix_def] >>
    irule_at Any env_ok_nsBind_alt >> simp[]
    )
  >- ( (* TwoArgs - ready to evaluate *)
    last_x_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
    TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
    `aop = Div ∨ aop = Mod ∨ aop = Elem ∨ aop = Substring ∨
     aop = StrLeq ∨ aop = StrLt ∨ aop = StrGeq ∨ aop = StrGt`
     by (CCONTR_TAC >> gvs[]) >> gvs[]
    >- ( (* Div *)
      gvs[eval_op_SOME] >>
      ntac 6 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, do_eq_def, lit_same_type_def] >>
      IF_CASES_TAC >> gvs[] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
      >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) (* div by 0 *) >>
      ntac 4 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opn_lookup_def] >>
      qexists0 >> simp[step_rel_cases, SF SFY_ss]
      )
    >- ( (* Mod *)
      gvs[eval_op_SOME] >>
      ntac 6 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, do_eq_def, lit_same_type_def] >>
      IF_CASES_TAC >> gvs[] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
      >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) (* mod by 0 *) >>
      ntac 4 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opn_lookup_def] >>
      qexists0 >> simp[step_rel_cases, SF SFY_ss]
      )
    >- ( (* Elem str *)
      gvs[eval_op_SOME] >>
      ntac 6 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opb_lookup_def, str_el_def] >>
      rename1 `_ ≤ idx` >> reverse $ Cases_on `0 ≤ idx` >> gvs[]
      >- (
        `idx < 0` by ARITH_TAC >> simp[] >>
        ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
        qexists0 >> simp[step_rel_cases, SF SFY_ss]
        ) >>
      `¬ (idx < 0)` by ARITH_TAC >> simp[] >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
      simp[do_app_def] >>
      ntac 7 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
      simp[do_app_def, opb_lookup_def] >> reverse $ IF_CASES_TAC >> gvs[] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
      >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def] >>
      `¬ (Num (ABS idx) ≥ STRLEN s')` by ARITH_TAC >> simp[] >>
      qrefine `SUC n` >> simp[cstep_n_def, cstep] >>
      simp[do_app_def] >>
      qexists0 >> simp[step_rel_cases] >>
      rpt $ goal_assum $ drule_at Any >> simp[IMPLODE_EXPLODE_I] >>
      `ABS idx = idx` by ARITH_TAC >> simp[]
      )
    >- ( (* Substring2 *)
      gvs[eval_op_SOME] >> rename1 `idx < _` >>
      ntac 4 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def] >>
      ntac 8 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opb_lookup_def] >> IF_CASES_TAC >> gvs[] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
      >- (
        ntac 7 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
        simp[do_app_def, opb_lookup_def] >>
        reverse $ Cases_on `0 < STRLEN s''` >> gvs[] >>
        ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
        >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) >>
        ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
        simp[do_app_def, opn_lookup_def] >>
        ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
        simp[do_app_def, copy_array_def, IMPLODE_EXPLODE_I] >>
        qexists0 >> simp[step_rel_cases, SF SFY_ss]
        ) >>
      ntac 7 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opb_lookup_def] >>
      reverse $ Cases_on `idx < &STRLEN s''` >> gvs[] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
      >- (
        `DROP (Num idx) s'' = []` by (simp[] >> ARITH_TAC) >> simp[] >>
        qexists0 >> simp[step_rel_cases, SF SFY_ss]
        ) >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opn_lookup_def] >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, copy_array_def, IMPLODE_EXPLODE_I] >>
      `¬ (&STRLEN s'' − idx < 0)` by ARITH_TAC >> simp[] >>
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      `ABS idx = idx` by ARITH_TAC >> simp[] >> ARITH_TAC
      )
    >- ( (* StrLeq *)
      gvs[eval_op_SOME] >> rename1 `string_le s1 s2` >>
      ntac 25 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_app_def]) >>
      qmatch_goalsub_abbrev_tac `cenv' with v := new_env` >>
      `env_ok (cenv' with v := new_env)` by (
        unabbrev_all_tac >> gvs[env_ok_def] >> rpt (irule_at Any EQ_REFL >> simp[])) >>
      drule $ cj 2 env_ok_imps >> strip_tac >>
      drule_all strle >>
      disch_then $ qspecl_then [`s1`,`s2`,`cst`,`fp`,`ck'`] assume_tac >> gvs[] >>
      qrefine `n + k` >> simp[cstep_n_add] >>
      qexists0 >> simp[] >> IF_CASES_TAC >> simp[step_rel_cases] >>
      rpt $ goal_assum $ drule_at Any >>
      gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def, Boolv_def]
      )
    >- ( (* StrLt *)
      gvs[eval_op_SOME] >> rename1 `string_lt s1 s2` >>
      ntac 6 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, do_eq_def, lit_same_type_def] >>
      ntac 1 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
      Cases_on `s1 = s2` >> gvs[]
      >- (
        gvs[string_lt_nonrefl] >>
        ntac 1 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
        `nsLookup cenv'.c (Short "False") = SOME (0,TypeStamp "False" 0)` by
          gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def, bool_type_num_def] >>
        simp[do_con_check_def, build_conv_def] >>
        qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def, bool_type_num_def]
        ) >>
      ntac 25 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_app_def]) >>
      qmatch_goalsub_abbrev_tac `cenv' with v := new_env` >>
      `env_ok (cenv' with v := new_env)` by (
        unabbrev_all_tac >> gvs[env_ok_def] >> rpt (irule_at Any EQ_REFL >> simp[])) >>
      drule $ cj 2 env_ok_imps >> strip_tac >>
      drule_all strle >>
      disch_then $ qspecl_then [`s1`,`s2`,`cst`,`fp`,`ck'`] assume_tac >> gvs[] >>
      qrefine `n + k` >> simp[cstep_n_add] >>
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[stringTheory.string_le_def] >> IF_CASES_TAC >> gvs[] >>
      gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def, Boolv_def]
      )
    >- ( (* StrGeq *)
      gvs[eval_op_SOME] >> rename1 `string_ge s1 s2` >>
      ntac 25 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_app_def]) >>
      qmatch_goalsub_abbrev_tac `cenv' with v := new_env` >>
      `env_ok (cenv' with v := new_env)` by (
        unabbrev_all_tac >> gvs[env_ok_def] >> rpt (irule_at Any EQ_REFL >> simp[])) >>
      drule $ cj 2 env_ok_imps >> strip_tac >>
      drule_all strle >>
      disch_then $ qspecl_then [`s2`,`s1`,`cst`,`fp`,`ck'`] assume_tac >> gvs[] >>
      qrefine `n + k` >> simp[cstep_n_add] >>
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[string_ge_def] >> IF_CASES_TAC >> gvs[] >>
      gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def, Boolv_def]
      )
    >- ( (* StrGt *)
      gvs[eval_op_SOME] >> rename1 `string_gt s1 s2` >>
      ntac 26 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_app_def]) >>
      qmatch_goalsub_abbrev_tac `cenv' with v := new_env` >>
      `env_ok (cenv' with v := new_env)` by (
        unabbrev_all_tac >> gvs[env_ok_def] >> rpt (irule_at Any EQ_REFL >> simp[])) >>
      drule $ cj 2 env_ok_imps >> strip_tac >>
      qmatch_goalsub_abbrev_tac `cif::ck'` >> drule_all strle >>
      disch_then $ qspecl_then [`s1`,`s2`,`cst`,`fp`,`cif::ck'`] assume_tac >> gvs[] >>
      qrefine `n + k` >> simp[cstep_n_add] >> unabbrev_all_tac >>
      qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def] >>
      `nsLookup cenv'.c (Short "False") = SOME (0,TypeStamp "False" 0) ∧
       nsLookup cenv'.c (Short "True") = SOME (0,TypeStamp "True" 0)` by
        gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def, bool_type_num_def] >>
      simp[string_gt_le] >> IF_CASES_TAC >> gvs[] >>
      qrefine `SUC n` >> simp[cstep_n_def, cstep] >>
      simp[do_con_check_def, build_conv_def] >>
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def, bool_type_num_def]
      )
    )
  >- ( (* Alloc - second argument to evaluate *)
    qrefine `SUC n` >> simp[cstep_n_def, cstep] >>
    qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
    simp[Once cont_rel_cases] >>
    irule_at Any env_rel_nsBind_alt >> simp[var_prefix_def] >>
    irule_at Any env_ok_nsBind_alt >> simp[]
    )
  >- ( (* Alloc - ready to evaluate *)
    last_x_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
    TOP_CASE_TAC >> gvs[] >>
    ntac 7 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
    simp[do_app_def, opb_lookup_def] >>
    IF_CASES_TAC >> gvs[] >>
    ntac 8 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
    simp[do_app_def, store_alloc_def] >>
    qexists0 >> simp[step_rel_cases] >> gvs[state_rel, ADD1, store_lookup_def] >>
    rpt $ goal_assum $ drule_at Any >> imp_res_tac LIST_REL_LENGTH >>
    simp[store_rel_def] >>
    `ABS i = i` by ARITH_TAC >> simp[LIST_REL_REPLICATE_same]
    )
  >- ( (* Concat *)
    `cnenv_rel cnenv cenv'.c` by gvs[env_rel_def] >>
    drule cnenv_rel_list_type >> strip_tac >> simp[] >>
    reverse TOP_CASE_TAC >> gvs[]
    >- ( (* arguments left to evaluate *)
      qrefine `SUC n` >> simp[cstep_n_def, cstep, list_to_cont_def] >>
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases] >> irule_at Any EQ_REFL >> simp[] >>
      rpt $ goal_assum $ drule_at Any >> simp[list_to_v_def, list_type_num_def]
      ) >>
    pop_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
    TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
    qrefine `SUC n` >> simp[cstep_n_def, cstep, list_to_cont_def] >>
    simp[do_app_def, v_to_list_def, list_type_num_def] >>
    Cases_on `x` >> gvs[concat_def] >>
    drule_all concat_vs_to_string >> rw[] >> simp[vs_to_string_def] >>
    qexists0 >> simp[step_rel_cases, SF SFY_ss]
    )
  >- ( (* Implode *)
    `cnenv_rel cnenv cenv'.c` by gvs[env_rel_def] >>
    drule cnenv_rel_list_type >> strip_tac >> simp[] >>
    reverse TOP_CASE_TAC >> gvs[]
    >- ( (* arguments left to evaluate *)
      qrefine `SUC n` >> simp[cstep_n_def, cstep, list_to_cont_def] >>
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases] >> irule_at Any EQ_REFL >> simp[] >>
      rpt $ goal_assum $ drule_at Any >> simp[list_to_v_def, list_type_num_def]
      ) >>
    pop_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
    TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
    qrefine `SUC n` >> simp[cstep_n_def, cstep, list_to_cont_def] >>
    drule implode_SOME >> strip_tac >> gvs[] >>
    `Conv (SOME (TypeStamp "::" 1)) [cv; list_to_v cvs] =
     list_to_v (MAP (Litv o IntLit) il)` by (
      Cases_on `il` >> gvs[list_to_v_def, list_type_num_def] >>
      AP_TERM_TAC >> gvs[LIST_REL_EL_EQN] >> rw[LIST_EQ_REWRITE] >> gvs[EL_MAP]) >>
    gvs[] >> drule $ cj 3 env_ok_imps >> strip_tac >> gvs[] >>
    drule_all char_list >>
    disch_then $ qspecl_then
      [`il`,`cst`,`fp`,`(Capp Implode [] [],cenv')::ck'`] assume_tac >> gvs[] >>
    qrefine `n + k` >> simp[cstep_n_add] >>
    qrefine `SUC n` >> simp[cstep, do_app_def] >>
    simp[GSYM implode_v_to_char_list_list_to_v, IMPLODE_EXPLODE_I] >>
    qexists0 >> simp[step_rel_cases, SF SFY_ss]
    )
  >- ( (* Substring3 - two args left to evaluate *)
    qrefine `SUC n` >> simp[cstep_n_def, cstep] >>
    qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
    simp[Once cont_rel_cases] >>
    irule_at Any env_rel_nsBind_alt >> simp[var_prefix_def] >>
    irule_at Any env_ok_nsBind_alt >> simp[]
    )
  >- ( (* Substring3 - one arg left to evaluate *)
    qrefine `SUC n` >> simp[cstep_n_def, cstep] >>
    qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
    simp[Once cont_rel_cases] >>
    irule_at Any env_rel_nsBind_alt >> simp[var_prefix_def] >>
    irule_at Any env_ok_nsBind_alt >> simp[]
    )
  >- ( (* Substring3 - ready to evaluate *)
    qmatch_goalsub_abbrev_tac `clet "off" rest1 rest2` >>
    first_x_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
    TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
    `∃s i len. sv = Atom $ Str s ∧ sv2 = Atom $ Int i ∧ sv3 = Atom $ Int len` by
      gvs[eval_op_SOME] >>
    gvs[MAP_EQ_CONS] >> reverse $ TOP_CASE_TAC >> gvs[] >- gvs[AllCaseEqs()] >>
    ntac 6 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
    simp[do_app_def, opb_lookup_def] >>
    Cases_on `len < 0` >> gvs[] >>
    ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
    >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) >>
    simp[Abbr `rest1`] >>
    ntac 3 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
    simp[do_app_def] >>
    ntac 8 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
    simp[do_app_def, opb_lookup_def] >>
    IF_CASES_TAC >> gvs[] >>
    ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
    >- (
      unabbrev_all_tac >>
      ntac 7 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opb_lookup_def] >>
      reverse $ Cases_on `0 < STRLEN s` >> gvs[] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
      >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opn_lookup_def] >>
      ntac 8 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opb_lookup_def] >>
      Cases_on `len < &STRLEN s` >> gvs[] >>
      ntac 9 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
      simp[do_app_def, opn_lookup_def] >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
      simp[do_app_def, copy_array_def, IMPLODE_EXPLODE_I]
      >- (
        `¬ (STRLEN s < Num (ABS len))` by ARITH_TAC >> simp[] >>
        `ABS len = len` by ARITH_TAC >> simp[] >>
        qexists0 >> simp[step_rel_cases, SF SFY_ss]
        )
      >- (
        qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        ARITH_TAC
        )
      )
    >- (
      unabbrev_all_tac >>
      ntac 7 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opb_lookup_def] >>
      reverse $ Cases_on `i < &STRLEN s` >> gvs[] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
      >- (
        qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        ARITH_TAC
        ) >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opn_lookup_def] >>
      ntac 8 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opb_lookup_def] >>
      Cases_on `i + len < &STRLEN s` >> gvs[] >>
      ntac 9 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
      simp[do_app_def, opn_lookup_def] >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
      simp[do_app_def, copy_array_def, IMPLODE_EXPLODE_I]
      >- (
        `¬ (STRLEN s < Num (ABS (i + len)))` by ARITH_TAC >> simp[] >>
        `ABS len = len ∧ ABS i = i` by ARITH_TAC >> simp[] >>
        qexists0 >> simp[step_rel_cases, SF SFY_ss]
        )
      >- (
        `¬ (&STRLEN s − i < 0)` by ARITH_TAC >> simp[] >>
        `ABS (&STRLEN s - i) = (&STRLEN s - i) ∧ ABS i = i` by ARITH_TAC >> simp[] >>
        qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        simp[TAKE_DROP_SWAP] >>
        `Num i + (Num (&STRLEN s - i)) = STRLEN s` by ARITH_TAC >> simp[] >>
        DEP_REWRITE_TAC[TAKE_LENGTH_TOO_LONG] >> ARITH_TAC
        )
      )
    )
  >- ( (* FFI *)
    qmatch_goalsub_abbrev_tac `Let _ _ ffi_rest` >>
    first_x_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
    TOP_CASE_TAC >> gvs[] >>
    ntac 3 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
    `nsLookup cenv'.v (Short "ffi_array") = SOME (Loc T 0)` by gvs[env_ok_def] >>
    simp[] >>
    ntac 3 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
    `∃ws. store_lookup 0 cst = SOME $ W8array ws ∧
          LENGTH ws = max_FFI_return_size + 2` by gvs[state_rel, store_lookup_def] >>
    simp[] >> qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
    irule env_ok_nsBind_alt >> simp[]
    )
QED

Theorem dstep1_rel:
  ∀s d benv.
    dstep_rel s d ∧ (∀n st k. step_n n s ≠ error st k)
  ⇒ ∃n. dstep_rel (step_n 1 s) (step_n benv (SUC n) d) ∧
        ∀ws. dget_ffi_array (step_n benv (SUC n) d) = SOME ws
          ⇒ dget_ffi_array d = SOME ws
Proof
  reverse $ rw[Once dstep_rel_cases] >> gvs[]
  >- (simp[dstep_rel_cases, sstep, SF SFY_ss] >> irule_at Any EQ_REFL)
  >- (simp[dstep_rel_cases, sstep, SF SFY_ss] >> irule_at Any EQ_REFL)
  >- (simp[dstep_rel_cases, sstep, SF SFY_ss] >> irule_at Any EQ_REFL) >>
  drule step1_rel >> simp[] >> strip_tac >> gvs[] >>
  `cstep_n (SUC n) (Estep (cenv,dst.refs,dst.fp_state,ceve,ck)) ≠ Edone` by (
    CCONTR_TAC >> gvs[step_rel_cases]) >>
  qrefine `m + n` >> simp[SUC_ADD_SYM, itree_semanticsPropsTheory.step_n_add] >>
  drule $ SRULE [] cstep_n_to_dstep_n >>
  disch_then $ qspecl_then
    [`benv`,`locs`,`Pvar "prog"`,`[CdlocalG lenv genv (final_gc flag)]`] assume_tac >>
  gvs[] >> pop_assum kall_tac >>
  reverse $ Cases_on
    `cstep_n (SUC n) (Estep (cenv,dst.refs,dst.fp_state,ceve,ck))` >> gvs[]
  >- fs[Once step_rel_cases]
  >- (
    qpat_x_assum `step_rel _ _` mp_tac >>
    simp[step_rel_cases, dstep_rel_cases] >> strip_tac >> gvs[SF SFY_ss] >>
    irule_at Any EQ_REFL
    ) >>
  PairCases_on `p` >> gvs[] >>
  drule $ iffLR step_rel_cases >> simp[] >> strip_tac >> gvs[]
  >- (qexists0 >> simp[dstep, dstep_rel_cases] >> irule_at Any EQ_REFL)
  >- (
    reverse $ Cases_on `sk'` >> gvs[]
    >- (qexists0 >> simp[dstep, dstep_rel_cases] >> irule_at Any EQ_REFL) >>
    gvs[Once cont_rel_cases] >> qrefine `SUC m` >> simp[dstep] >>
    simp[astTheory.pat_bindings_def, pmatch_def] >>
    reverse $ rw[final_gc_def]
    >- (ntac 2 (qrefine `SUC m` >> simp[dstep]) >> simp[dstep_rel_cases]) >>
    ntac 2 (qrefine `SUC m` >> simp[dstep]) >>
    simp[dstep, astTheory.pat_bindings_def, smallStepTheory.collapse_env_def] >>
    ntac 6 (qrefine `SUC m` >> simp[cstep, dstep, do_app_def]) >>
    simp[astTheory.pat_bindings_def, pmatch_def] >>
    ntac 2 (qrefine `SUC m` >> simp[dstep]) >> simp[dstep_rel_cases]
    )
  >- (
    reverse $ Cases_on `sk'` >> gvs[]
    >- (qexists0 >> simp[dstep, dstep_rel_cases] >> irule_at Any EQ_REFL) >>
    gvs[Once cont_rel_cases] >>
    qrefine `SUC m` >> simp[dstep, dstep_rel_cases, SF SFY_ss]
    )
QED

Theorem dstep_n_rel:
  ∀n s d benv.
    dstep_rel s d ∧ (∀n st k. step_n n s ≠ error st k)
  ⇒ ∃m. n ≤ m ∧ dstep_rel (step_n n s) (step_n benv m d) ∧
        ∀ws. dget_ffi_array (step_n benv m d) = SOME ws ⇒ dget_ffi_array d = SOME ws
Proof
  Induct >> rw[] >- (qexists_tac `0` >> simp[dstep]) >>
  last_x_assum drule >> simp[] >>
  disch_then $ qspec_then `benv` assume_tac >> gvs[] >>
  qrefine `SUC (m + k)` >> simp[SUC_ADD_SYM] >>
  once_rewrite_tac[ADD_COMM] >> simp[itree_semanticsPropsTheory.step_n_add] >>
  drule $ iffLR dstep_rel_cases >> reverse strip_tac >> gvs[step_n_alt]
  >- (simp[dstep_rel_cases, sstep, SF SFY_ss] >> irule_at Any EQ_REFL)
  >- (simp[dstep_rel_cases, sstep, SF SFY_ss] >> irule_at Any EQ_REFL)
  >- (simp[dstep_rel_cases, sstep, SF SFY_ss] >> irule_at Any EQ_REFL) >>
  drule dstep1_rel >> disch_then $ qspec_then `benv` mp_tac >> impl_tac
  >- (rw[] >> last_x_assum $ qspec_then `n' + n` mp_tac >> simp[step_n_add]) >>
  strip_tac >> gvs[] >> goal_assum drule >> simp[]
QED

Theorem step_until_halt_rel:
  ∀s d benv.
    dstep_rel s d ∧ step_until_halt s ≠ Err
  ⇒ next_res_rel (step_until_halt s) (step_until_halt benv d) ∧
    (∀dst out locs p dk. step_until_halt benv d = Act dst out locs p dk
      ⇒ ∃ws. store_lookup 0 dst.refs = SOME (W8array ws) ∧ dget_ffi_array d = SOME ws)
Proof
  PairCases >> rpt gen_tac >> strip_tac >>
  drule step_until_halt_no_err_step_n >> strip_tac >>
  simp[step_until_halt_def, itree_semanticsTheory.step_until_halt_def] >>
  DEEP_INTRO_TAC some_intro >> reverse strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- (
    qsuff_tac `∀n. ¬is_halt (step_n benv n d)` >> rw[next_res_rel_cases] >>
    rw[] >> pop_assum $ qspec_then `n` assume_tac >>
    drule_all dstep_n_rel >> disch_then $ qspecl_then [`n`,`benv`] assume_tac >> gvs[] >>
    `¬is_halt (step_n benv m d)` by metis_tac[dstep_rel_is_halt] >>
    CCONTR_TAC >> gvs[] >> drule is_halt_step_n_const >> simp[] >>
    Cases_on `n = m` >> gvs[] >> qexists_tac `m` >> simp[] >> CCONTR_TAC >> gvs[]
    ) >>
  drule_all dstep_n_rel >> disch_then $ qspecl_then [`x`,`benv`] assume_tac >> gvs[] >>
  `is_halt (step_n benv m d)` by metis_tac[dstep_rel_is_halt] >>
  DEEP_INTRO_TAC some_intro >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule_then rev_drule is_halt_step_n_eq >> strip_tac >> gvs[] >>
  drule $ iffLR dstep_rel_cases >> strip_tac >> gvs[] >>
  simp[next_res_rel_cases] >> gvs[Once step_rel_cases]
QED

Theorem compile_itree_rel:
    safe_itree (sinterp sr st sk) ∧
    dstep_rel (sr,st,sk) (step_n benv n dr)
  ⇒ itree_rel (sinterp sr st sk) (interp benv dr)
Proof
  qsuff_tac
    `∀s d.
      (∃sr st sk benv n dr.
        s = sinterp sr st sk ∧ d = interp benv dr ∧
        safe_itree (sinterp sr st sk) ∧
        dstep_rel (sr,st,sk) (step_n benv n dr)
        ) ∨
      (∃ch conf ws f.
        s = Ret (FinalFFI (ch,conf) f) ∧
        d = Ret (FinalFFI (ExtCall ch, compile_conf conf, ws) (compile_final_ffi f)))
    ⇒ itree_rel s d`
  >- (
    rw[] >> first_x_assum irule >> disj1_tac >>
    rpt $ goal_assum $ drule_at Any >> simp[]
    ) >>
  ho_match_mp_tac itree_rel_coind >> rw[] >>
  `interp benv dr = interp benv (step_n benv n dr)` by simp[interp_take_steps] >>
  pop_assum SUBST_ALL_TAC >> qmatch_goalsub_abbrev_tac `interp benv d'` >>
  `step_until_halt (sr,st,sk) ≠ Err` by (
    gvs[Once sinterp] >> FULL_CASE_TAC >> gvs[] >>
    gvs[Once pure_semanticsTheory.safe_itree_cases]) >>
  drule_all step_until_halt_rel >> disch_then $ qspec_then `benv` assume_tac >>
  gvs[next_res_rel_cases]
  >- (once_rewrite_tac[sinterp, interp] >> simp[])
  >- (once_rewrite_tac[sinterp, interp] >> simp[]) >>
  ntac 3 disj2_tac >> simp[Once sinterp, Once interp] >>
  drule $ iffLR dstep_rel_cases >> rw[] >> gvs[] >>
  drule $ iffLR step_rel_cases >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `ExpVal _ _ ffi_exp` >>
  `LENGTH ws = max_FFI_return_size + 2` by gvs[state_rel, store_lookup_def] >>
  simp[] >> conj_tac >- simp[compile_conf_def] >>
  reverse conj_tac >- simp[compile_conf_def] >>
  rpt gen_tac >> strip_tac >> reverse IF_CASES_TAC >> gvs[]
  >- gvs[compile_input_rel_def, compile_conf_def, compile_final_ffi_def] >>
  disj1_tac >> irule_at Any EQ_REFL >>
  gvs[compile_input_rel_def] >> irule_at Any EQ_REFL >>
  simp[GSYM PULL_EXISTS] >> conj_tac
  >- (
    last_x_assum mp_tac >> simp[Once sinterp] >>
    simp[Once pure_semanticsTheory.safe_itree_cases] >>
    disch_then $ qspec_then `INR s` mp_tac >> simp[]
    ) >>
  unabbrev_all_tac >>
  ntac 7 (qrefine `SUC m` >> simp[dstep, cstep]) >>
  simp[namespaceTheory.nsOptBind_def] >>
  `nsLookup cenv.v (Short "ffi_array") = SOME (Loc T 0)` by gvs[env_ok_def] >>
  simp[] >> qrefine `SUC m` >> simp[dstep, cstep, do_app_def] >>
  Cases_on `dst.refs` >> gvs[store_lookup_def, LUPDATE_DEF] >>
  ntac 9 (qrefine `SUC m` >> simp[dstep, cstep, do_app_def]) >>
  simp[store_lookup_def] >>
  ntac 21 (qrefine `SUC m` >> simp[dstep, cstep, do_app_def]) >>
  simp[opb_lookup_def, opn_lookup_def, do_if_def] >>
  `&(256 * (STRLEN s DIV 256) MOD dimword (:8)) + &(STRLEN s MOD dimword (:8)) =
    &(STRLEN s) : int` by (
      simp[wordsTheory.dimword_def, wordsTheory.dimindex_8] >>
      gvs[max_FFI_return_size_def] >> ARITH_TAC) >>
  pop_assum SUBST_ALL_TAC >> simp[] >>
  ntac 9 (qrefine `SUC m` >> simp[dstep, cstep, do_app_def]) >>
  simp[store_lookup_def, copy_array_def, integerTheory.INT_ADD_CALCULATE] >>
  qmatch_goalsub_abbrev_tac `StrLit str1` >>
  `str1 = s` by (
    unabbrev_all_tac >> simp[TAKE_APPEND, GSYM MAP_TAKE] >>
    simp[ws_to_chars_def, MAP_MAP_o, combinTheory.o_DEF, IMPLODE_EXPLODE_I]) >>
  pop_assum SUBST_ALL_TAC >>
  Cases_on `ck'` >> gvs[]
  >- (
    qrefine `SUC m` >> simp[dstep] >>
    simp[astTheory.pat_bindings_def, pmatch_def] >>
    reverse $ rw[final_gc_def] >> ntac 2 (qrefine `SUC m` >> simp[dstep]) >>
    simp[dstep_rel_cases] >> gvs[Once cont_rel_cases] >>
    simp[astTheory.pat_bindings_def] >>
    ntac 6 (qrefine `SUC m` >> simp[cstep, dstep, do_app_def]) >>
    simp[astTheory.pat_bindings_def, pmatch_def] >>
    ntac 2 (qrefine `SUC m` >> simp[dstep])
    ) >>
  qexists0 >> simp[dstep, store_lookup_def] >>
  simp[dstep_rel_cases, step_rel_cases, PULL_EXISTS] >>
  irule_at Any EQ_REFL >> goal_assum drule >> gvs[state_rel] >>
  qpat_x_assum `cont_rel _ _ _` mp_tac >> rw[Once cont_rel_cases]
QED

Theorem compile_safe_itree:
    safe_itree (sinterp sr st sk) ∧
    dstep_rel (sr,st,sk) (step_n benv n dr)
  ⇒ safe_itree ffi_convention (interp benv dr)
Proof
  rw[] >> dxrule_all compile_itree_rel >> rename1 `itree_rel a b` >>
  qsuff_tac `∀b. (∃a. itree_rel a b) ⇒ safe_itree ffi_convention b`
  >- (rw[PULL_EXISTS] >> res_tac) >>
  ho_match_mp_tac safe_itree_coind >> rw[] >> gvs[Once itree_rel_cases] >>
  rw[ffi_convention_def] >> Cases_on `s` >> gvs[]
  >- (
    pop_assum $ qspec_then
      `case x of FFI_failed => FFI_failure | _ => FFI_divergence` mp_tac >>
    CASE_TAC >> simp[compile_final_ffi_def] >> disch_then $ irule_at Any
    )
  >- (first_x_assum $ irule_at Any >> simp[SF SFY_ss])
QED


(****************************** Lifting to cexp ******************************)

Inductive csop_rel:
  csop_rel (AppOp : csop) Opapp ∧
  (atom_op_rel aop op ⇒ csop_rel (AtomOp aop) op) ∧
  csop_rel Length Alength ∧
  csop_rel Sub Asub ∧
  csop_rel Update Aupdate ∧
  csop_rel (AllocMutThunk Evaluated) (ThunkOp $ AllocThunk F) ∧
  csop_rel (AllocMutThunk NotEvaluated) (ThunkOp $ AllocThunk T) ∧
  csop_rel (UpdateMutThunk Evaluated) (ThunkOp $ UpdateThunk F) ∧
  csop_rel (UpdateMutThunk NotEvaluated) (ThunkOp $ UpdateThunk T) ∧
  csop_rel ForceMutThunk (ThunkOp ForceThunk)
End

Inductive cexp_compile_rel:
[~IntLit:]
  cexp_compile_rel cnenv (IntLit i : cexp) (ast$Lit $ IntLit i)

[~StrLit:]
  cexp_compile_rel cnenv (StrLit s) (Lit $ StrLit s)

[~Tuple:]
  (LIST_REL (cexp_compile_rel cnenv) ses ces
    ⇒ cexp_compile_rel cnenv (App (Cons $ strlit "") ses) (Con NONE ces))

[~Constructor:]
  (LIST_REL (cexp_compile_rel cnenv) ses ces ∧
   ALOOKUP cnenv $ explode cn = SOME (tyid,ar) ∧
   ar = LENGTH ses ∧ cn ≠ strlit ""
    ⇒ cexp_compile_rel cnenv (App (Cons cn) ses) (Con (SOME $ Short $ explode cn) ces))

[~Var:]
  cexp_compile_rel cnenv (Var v) (var (cexp_var_prefix v))

[~App:]
  (csop_rel sop cop ∧ LIST_REL (cexp_compile_rel cnenv) ses ces
    ⇒ cexp_compile_rel cnenv (App sop ses) (App cop ces))

[~TwoArgs:]
  (cexp_compile_rel cnenv se1 ce1 ∧ cexp_compile_rel cnenv se2 ce2 ∧
   (if aop = Div then rest = div
    else if aop = Mod then rest = mod
    else if aop = Elem then rest = elem_str
    else if aop = Substring then rest = substring2
    else if aop = StrLeq then rest = strleq
    else if aop = StrLt then rest = strlt
    else if aop = StrGeq then rest = strgeq
    else aop = StrGt ∧ rest = strgt)
    ⇒ cexp_compile_rel cnenv (App (AtomOp aop) [se1;se2])
                        (clet "v2" ce2 $ clet "v1" ce1 rest))

[~Concat:]
  (LIST_REL (cexp_compile_rel cnenv) ses ces
    ⇒ cexp_compile_rel cnenv (App (AtomOp Concat) ses) (App Strcat [list_to_exp ces]))

[~Implode:]
  (LIST_REL (cexp_compile_rel cnenv) ses ces
    ⇒ cexp_compile_rel cnenv (App (AtomOp Implode) ses)
                        (App Implode [capp (var "char_list") (list_to_exp ces)]))

[~Substring3:]
  (LIST_REL (cexp_compile_rel cnenv) [se1;se2;se3] [ce1;ce2;ce3]
    ⇒ cexp_compile_rel cnenv (App (AtomOp Substring) [se1; se2; se3])
                        (clet "l" ce3 $ clet "i" ce2 $ clet "s" ce1 substring3))

[~Alloc:]
  (cexp_compile_rel cnenv se1 ce1 ∧ cexp_compile_rel cnenv se2 ce2
    ⇒ cexp_compile_rel cnenv (App Alloc [se1;se2])
                        (clet "v2" ce2 $ clet "v1" ce1 alloc))

[~FFI:]
  (cexp_compile_rel cnenv se ce ∧ ch ≠ strlit ""
    ⇒ cexp_compile_rel cnenv (App (FFI ch) [se])
                        (clet "s" ce $
                          Let NONE (App (FFI $ explode ch)
                            [var "s"; var "ffi_array"]) $ ffi))

[~Lam:]
  (cexp_compile_rel cnenv se ce
    ⇒ cexp_compile_rel cnenv (Lam (SOME x) se) (Fun (cexp_var_prefix x) ce))

[~Letrec:]
  (LIST_REL
      (λ(sv,sx,se) (cv,cx,ce).
        cexp_var_prefix sv = cv ∧ cexp_var_prefix sx = cx ∧
        cexp_compile_rel cnenv se ce)
      sfuns cfuns ∧
   ALL_DISTINCT (MAP FST cfuns) ∧
   cexp_compile_rel cnenv se ce
    ⇒ cexp_compile_rel cnenv (Letrec sfuns se) (ast$Letrec cfuns ce))

[~Let:]
  (cexp_compile_rel cnenv se1 ce1 ∧ cexp_compile_rel cnenv se2 ce2
    ⇒ cexp_compile_rel cnenv (Let (SOME x) se1 se2)
                             (Let (SOME $ cexp_var_prefix x) ce1 ce2))

[~If:]
  (LIST_REL (cexp_compile_rel cnenv) [se;se1;se2] [ce;ce1;ce2]
    ⇒ cexp_compile_rel cnenv (If se se1 se2) (If ce ce1 ce2))

[~CaseNone:]
  (EVERY (λ(cn,vs,_). ALL_DISTINCT vs ∧ ∃stamp'.
    ALOOKUP cnenv $ explode cn = SOME (stamp',LENGTH vs) ∧ same_type stamp' stamp) scss ∧
   LIST_REL
    (λ(cn,vs,se) (pat,ce). cexp_compile_rel cnenv se ce ∧ pat = cexp_pat_row cn vs)
    scss ccss
    ⇒ cexp_compile_rel cnenv (Case sv scss NONE)
                             (Mat (var (cexp_var_prefix sv)) ccss))

[~CaseSome:]
  (EVERY (λ(cn,vs,_). ALL_DISTINCT vs ∧ ∃stamp'.
    ALOOKUP cnenv $ explode cn = SOME (stamp',LENGTH vs) ∧ same_type stamp' stamp) scss ∧
   LIST_REL
    (λ(cn,vs,se) (pat,ce). cexp_compile_rel cnenv se ce ∧ pat = cexp_pat_row cn vs)
    scss ccss ∧
   EVERY (λ(cn,ar). ∃stamp'.
    ALOOKUP cnenv $ explode cn = SOME (stamp',ar) ∧ same_type stamp' stamp) scany ∧
   cexp_compile_rel cnenv suse cuse
    ⇒ cexp_compile_rel cnenv (Case sv scss (SOME (scany, suse)))
                             (Mat (var (cexp_var_prefix sv)) (ccss ++ [Pany,cuse])))

[~TupleCase:]
  (cexp_compile_rel cnenv sce cce ∧ ALL_DISTINCT vs
    ⇒ cexp_compile_rel cnenv (Case sv [strlit "",vs,sce] NONE)
                             (Mat (var (cexp_var_prefix sv))
                                [(cexp_pat_row (strlit "") vs, cce)]))

[~Raise:]
  (cexp_compile_rel cnenv se ce
    ⇒ cexp_compile_rel cnenv (Raise se) (Raise ce))

[~Handle:]
  (cexp_compile_rel cnenv se1 ce1 ∧ cexp_compile_rel cnenv se2 ce2
    ⇒ cexp_compile_rel cnenv (Handle se1 x se2)
                        (Handle ce1 [(Pvar $ cexp_var_prefix x, ce2)]))
End

(* We have to be careful here with lining up type definitions in Pure and CakeML.
   CakeML assumes the following initial namespace:
      Exceptions: 0 -> Bind, 1 -> Chr, 2 -> Div, 3 -> Subscript
      Types: 0 -> Bool, 1 -> List
   Pure has the following initial namespace:
      Exception: 0 -> Subscript
      Types: 0 -> List

   In compilation, we have to take care that the type stamps line up.
*)

Overload t_offset = ``1n``;
Overload e_offset = ``3n``;
Overload t_init = ``2n``;
Overload e_init = ``4n``;

Definition ns_rel_def:
  ns_rel (ns :exndef # typedefs) senv ⇔
    prim_types_ok senv ∧
    (∀n cn ts. oEL n (FST ns) = SOME (cn, ts)
      ⇒ ALOOKUP senv (explode cn) =
        SOME (ExnStamp (n +   e_offset  ), LENGTH ts)) ∧
    (∀n ar cndefs. oEL n (SND ns) = SOME (ar, cndefs) ⇒
      ∀cn ts. MEM (cn, ts) cndefs ⇒
        ALOOKUP senv (explode cn) =
        SOME (TypeStamp (explode cn) (n +   t_offset  ), LENGTH ts))
End


(***** Lemmas *****)

Theorem csop_rel_sop_rel:
  csop_rel scop op ⇒ op_rel (sop_of scop) op
Proof
  rw[csop_rel_cases] >> rw[op_rel_cases]
QED

Theorem cexp_var_prefix[simp]:
  cexp_var_prefix cv = var_prefix (explode cv)
Proof
  rw[cexp_var_prefix_def, var_prefix_def]
QED

Theorem cexp_pat_row[simp]:
  cexp_pat_row cn vs = pat_row (explode cn) (MAP explode vs)
Proof
  rw[cexp_pat_row_def, pat_row_def] >> gvs[] >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  Cases_on `cn` >> gvs[]
QED

Theorem compile_rel_cexp_compile_rel:
  ∀cnenv se ce. cexp_compile_rel cnenv se ce ⇒ compile_rel cnenv (exp_of se) ce
Proof
  gen_tac >> ho_match_mp_tac cexp_compile_rel_ind >>
  rw[] >> simp[Once compile_rel_cases] >>
  gvs[LIST_REL_MAP1, combinTheory.o_DEF, SF ETA_ss]
  >- (Cases_on `cn` >> gvs[])
  >- metis_tac[csop_rel_sop_rel]
  >- (
    simp[op_rel_cases, atom_op_rel_cases] >>
    irule_at Any EQ_REFL >> simp[]
    )
  >- (
    simp[op_rel_cases, atom_op_rel_cases] >>
    irule_at Any EQ_REFL >> simp[]
    )
  >- (Cases_on `ch` >> gvs[])
  >- (
    gvs[LIST_REL_EL_EQN] >> rw[] >> rpt (pairarg_tac >> gvs[]) >>
    last_x_assum drule >> strip_tac >> gvs[]
    )
  >- (
    disj1_tac >> qexists_tac `stamp` >> gvs[EVERY_MAP, LAMBDA_PROD]
    )
  >- (
    qexists_tac `stamp` >> gvs[EVERY_MAP, LAMBDA_PROD]
    )
QED

Theorem compile_op_CakeOp:
  compile_op op = CakeOp cop ⇒ csop_rel op cop
Proof
  Cases_on `op` >> gvs[compile_op_def, csop_rel_cases]
  >- (
    Cases_on `a` >> rw[] >> gvs[compile_atomop_def, atom_op_rel_cases] >>
    gvs[opn_rel_cases, opb_rel_cases]
    ) >>
  Cases_on `c` >> rw[] >> gvs[compile_op_def]
QED

Theorem ns_cns_arities_ns_rel:
  it ∈ ns_cns_arities ns ∧ ns_rel ns cnenv ⇒
  ∃tyid. ∀cn ar. (cn, ar) ∈ it ⇒
    ∃tyid'. ALOOKUP cnenv (explode cn) = SOME (tyid', ar) ∧ same_type tyid' tyid
Proof
  PairCases_on `ns` >> rw[ns_cns_arities_def, ns_rel_def]
  >- (
    qexists_tac `ExnStamp any` >> rw[MEM_MAP, EXISTS_PROD, MEM_EL, PULL_EXISTS] >>
    pop_assum $ assume_tac o GSYM >> gvs[oEL_THM] >>
    last_x_assum $ drule_all >> gvs[same_type_def]
    )
  >- (
    gvs[prim_types_ok_def] >> qexists_tac `TypeStamp any bool_type_num` >>
    rw[] >> gvs[same_type_def]
    )
  >- (
    last_x_assum mp_tac >> simp[MEM_MAP, EXISTS_PROD, MEM_EL] >> strip_tac >> gvs[] >>
    pop_assum $ assume_tac o GSYM >> gvs[oEL_THM] >> first_x_assum drule >> rw[] >>
    qexists_tac `TypeStamp any (n + t_offset)` >> rw[MEM_MAP, EXISTS_PROD] >>
    first_x_assum drule >> rw[same_type_def]
    )
QED

Definition cns_ok_def:
  cns_ok ns t ⇔
  cns_arities_ok ns {s | (∃s0. s0 ∈ t ∧ s = IMAGE (implode ## I) s0)}
End

Theorem cns_ok_SUBSET:
  cns_ok ns t1 ∧ t ⊆ t1 ⇒ cns_ok ns t
Proof
  fs [cns_ok_def,pure_typingTheory.cns_arities_ok_def,SUBSET_DEF]
  \\ metis_tac []
QED

Theorem cns_ok_UNION:
  cns_ok ns t1 ⇒
  cns_ok ns (t1 ∪ {{("",0)}; {("True",0)}; {("False",0)}})
Proof
  fs [cns_ok_def,pure_typingTheory.cns_arities_ok_def, PULL_EXISTS]
  \\ rw []
  >- first_x_assum $ drule_then irule
  >- simp [IMAGE_SING, mlstringTheory.implode_def]
  \\ rename1 ‘ns_cns_arities ns’
  \\ PairCases_on ‘ns’
  \\ fs [IMAGE_UNION, IMAGE_SING, mlstringTheory.implode_def,
         pure_typingTheory.ns_cns_arities_def]
  \\ qexists_tac ‘{(«True»,0); («False»,0)}’
  \\ simp []
QED

Theorem image_implode_lemma:
  IMAGE (implode ## I) s = {(strlit l, x)} ⇔ s = {(l,x)}
Proof
  simp[EXTENSION, EXISTS_PROD, FORALL_PROD, EQ_IMP_THM, PULL_EXISTS,
       mlstringTheory.implode_def, FORALL_AND_THM] >> metis_tac[]
QED

Theorem compile_cexp_compile_rel:
  cexp_wf e ∧ ns_rel ns cnenv ∧
  cns_arities_ok ns { s | ∃s0. s0 ∈ state_cexp$cns_arities e ∧
                               s = IMAGE (implode ## I) s0 }
  ⇒ cexp_compile_rel cnenv e (compile e)
Proof
  qid_spec_tac `e` >> recInduct compile_ind >> rw[compile_def] >>
  gvs[cns_arities_ok_def, cns_arities_def, cexp_wf_def]
  >- ( (* Var *)
    simp[Once cexp_compile_rel_cases]
    )
  >- ( (* App *)
    TOP_CASE_TAC >> gvs[]
    >- ( (* normal App *)
      simp[Once cexp_compile_rel_cases] >> disj1_tac >>
      drule compile_op_CakeOp >> rw[] >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
      last_x_assum irule >> simp[EL_MEM] >>
      gvs[EVERY_EL, MEM_MAP, PULL_EXISTS, MEM_EL] >> metis_tac[]
      )
    >- ( (* TwoArgs *)
      reverse $ Cases_on `op` >> gvs[compile_op_def, op_args_ok_def]
      >- (Cases_on `c` >> gvs[compile_op_def, op_args_ok_def])
      >- (Cases_on `c` >> gvs[compile_op_def, op_args_ok_def])
      >- (gvs[LENGTH_EQ_NUM_compute, oEL_THM] >> simp[Once cexp_compile_rel_cases]) >>
      Cases_on `a` >> gvs[compile_atomop_def, op_args_ok_def] >>
      gvs[LENGTH_EQ_NUM_compute, oEL_THM] >> simp[Once cexp_compile_rel_cases]
      ) >>
    Cases_on `op` >> gvs[compile_op_def]
    >- ( (* Cons / Tuple *)
      IF_CASES_TAC >> gvs[] >>
      simp[Once cexp_compile_rel_cases] >>
      gvs[LIST_REL_EL_EQN, EL_MAP, GSYM PULL_EXISTS] >> reverse $ rw[]
      >~ [‘ALOOKUP _ (explode m)’] >- (
        Cases_on ‘m’ >>
        gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, MEM_MAP,
            image_implode_lemma] >>
        gvs[mlstringTheory.implode_def] >>
        drule_all ns_cns_arities_ns_rel >> rw[] >>
        pop_assum drule >> strip_tac >> simp[] >>
        gvs[GSYM mlstringTheory.implode_def]
        ) >>
      last_x_assum irule >> simp[EL_MEM] >>
      gvs[EVERY_EL, MEM_MAP, PULL_EXISTS, MEM_EL] >> metis_tac[]
      )
    >~ [`FFI`]
    >- ( (* FFI *)
      gvs[op_args_ok_def, LENGTH_EQ_NUM_compute, oEL_THM] >>
      simp[Once cexp_compile_rel_cases]
      )
    >~ [`AllocMutThunk`]
    >- (Cases_on `c` >> gvs[compile_op_def, op_args_ok_def])
    >~ [`UpdateMutThunk`]
    >- (Cases_on `c` >> gvs[compile_op_def, op_args_ok_def]) >>
    Cases_on `a` >> gvs[compile_atomop_def, op_args_ok_def]
    >- ( (* Lit *)
      Cases_on `l` >> gvs[op_args_ok_def] >> simp[Once cexp_compile_rel_cases]
      )
    >- ( (* Concat *)
      simp[Once cexp_compile_rel_cases] >> disj2_tac >>
      irule_at Any EQ_REFL >> gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
      last_x_assum irule >> simp[EL_MEM] >>
      gvs[EVERY_EL, MEM_MAP, MEM_EL, PULL_EXISTS] >> metis_tac[]
      )
    >- ( (* Implode *)
      simp[Once cexp_compile_rel_cases] >> disj2_tac >>
      irule_at Any EQ_REFL >> gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
      last_x_assum irule >> simp[EL_MEM] >>
      gvs[EVERY_EL, MEM_MAP, MEM_EL, PULL_EXISTS] >> metis_tac[]
      )
    >- ( (* Substring2 *)
      gvs[LENGTH_EQ_NUM_compute, oEL_THM] >>
      simp[Once cexp_compile_rel_cases]
      )
    >- ( (* Substring3 *)
      gvs[LENGTH_EQ_NUM_compute, oEL_THM] >>
      simp[Once cexp_compile_rel_cases]
      )
    )
  >- ( (* Lam *)
    simp[Once cexp_compile_rel_cases]
    )
  >- ( (* Letrec *)
    simp[Once cexp_compile_rel_cases] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, LIST_REL_EL_EQN, EL_MAP] >>
    rw[]
    >- (
      pairarg_tac >> gvs[] >> last_x_assum irule >> gvs[EVERY_EL] >>
      last_x_assum drule >> simp[] >> strip_tac >>
      simp[MEM_EL, PULL_EXISTS] >> goal_assum $ drule_at Any >> simp[] >>
      rw[] >> first_x_assum irule >>
      dsimp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> disj1_tac >>
      goal_assum drule >> simp[MEM_MAP, MEM_EL, PULL_EXISTS] >>
      goal_assum $ drule_at Any >> simp[]
      )
    >- (
      `MAP (λ(a,b,c). var_prefix (explode a)) funs =
        MAP (var_prefix o explode) (MAP FST funs)` by
          simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      simp[] >> irule ALL_DISTINCT_MAP_INJ >> simp[var_prefix_def]
      )
    )
  >- ( (* Let *)
    simp[Once cexp_compile_rel_cases]
    )
  >- ( (* If *)
    simp[Once cexp_compile_rel_cases]
    )
  >- ( (* Case *)
    simp[Once cexp_compile_rel_cases, PULL_EXISTS, SF CONJ_ss] >>
    Cases_on `∃vs rest. css = [(«»,vs,rest)] ∧ d = NONE` >> gvs[] >>
    Cases_on `d` >> gvs[]
    >- (
      simp[Once CONJ_SYM] >> rw[GSYM PULL_EXISTS]
      >- (
        gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
        pairarg_tac >> gvs[] >> last_x_assum irule >>
        gvs[EVERY_EL, PULL_EXISTS, image_implode_lemma, MEM_MAP] >>
        last_x_assum drule >> strip_tac >> gvs[] >>
        simp[MEM_EL, PULL_EXISTS] >> goal_assum $ drule_at Any >> simp[] >>
        rw[] >> first_x_assum irule >> rpt $ disj2_tac >>
        simp[MEM_MAP, EXISTS_PROD, MEM_EL, PULL_EXISTS] >>
        rpt $ goal_assum $ drule_at Any >> simp[]
        ) >>
      gvs[EVERY_MEM, DISJ_IMP_THM, FORALL_AND_THM, MEM_MAP, PULL_EXISTS,
          image_implode_lemma, FORALL_PROD]
      >- (
        gvs[LIST_TO_SET_EQ_SING] >> Cases_on `css` >> gvs[] >>
        PairCases_on `h` >> gvs[] >> Cases_on `h0` >> gvs[] >>
        Cases_on `t` >> gvs[] >> PairCases_on `h` >> gvs[] >> Cases_on `h0` >>
        gvs[]
        ) >>
      drule_all ns_cns_arities_ns_rel >> strip_tac >> gvs[] >>
      qexists_tac `tyid` >> rw[] >> gvs[] >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      first_x_assum irule >> gvs[SUBSET_DEF] >>
      first_x_assum irule >> simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS]  >>
      goal_assum $ drule_at Any >> simp[]
      )
    >- (
      namedCases_on `x` ["scany suse"] >> gvs[] >>
      simp[Once CONJ_SYM, GSYM CONJ_ASSOC] >> rw[GSYM PULL_EXISTS]
      >- (
        gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
        pairarg_tac >> gvs[] >> last_x_assum irule >>
        gvs[EVERY_EL, PULL_EXISTS, image_implode_lemma, MEM_MAP] >>
        last_x_assum drule >> strip_tac >> gvs[] >>
        simp[MEM_EL, PULL_EXISTS] >> goal_assum $ drule_at Any >> simp[] >>
        rw[] >> first_x_assum irule >> rpt $ disj2_tac >>
        simp[MEM_MAP, EXISTS_PROD, MEM_EL, PULL_EXISTS] >>
        rpt $ goal_assum $ drule_at Any >> simp[]
        ) >>
      gvs[EVERY_MEM, DISJ_IMP_THM, FORALL_AND_THM, MEM_MAP, PULL_EXISTS,
          image_implode_lemma, FORALL_PROD]
      >- (
        dxrule $ cj 1 $ iffRL SUBSET_ANTISYM_EQ >> rw[] >>
        `MEM (implode "") (MAP FST css)` by (
          Cases_on `css` >> gvs[] >> PairCases_on `h` >> gvs[] >>
          Cases_on `h0` >> gvs[mlstringTheory.implode_def]) >>
        `MEM (implode "") (MAP FST scany)` by (
          Cases_on `scany` >> gvs[] >> PairCases_on `h` >> gvs[] >>
          Cases_on `h0` >> gvs[mlstringTheory.implode_def]) >>
        gvs[ALL_DISTINCT_APPEND]
        ) >>
      drule_all ns_cns_arities_ns_rel >> strip_tac >> gvs[] >>
      qexists_tac `tyid` >> rw[] >> gvs[]
      >- (
        first_x_assum irule >> gvs[SUBSET_DEF] >>
        last_x_assum irule >> simp[EXISTS_PROD, MEM_MAP, PULL_EXISTS]
        )
      >- (
        first_x_assum drule >> strip_tac >> gvs[] >>
        first_x_assum irule >> gvs[SUBSET_DEF] >>
        first_x_assum irule >> simp[EXISTS_PROD, MEM_MAP, PULL_EXISTS] >>
        goal_assum $ drule_at Any >> simp[]
        )
      )
    )
  >- ( (* Raise *)
    simp[Once cexp_compile_rel_cases]
    )
  >- ( (* Handle *)
    simp[Once cexp_compile_rel_cases]
    )
QED


(****************************** CakeML semantics ******************************)

Theorem check_dup_ctors_ALL_DISTINCT[simp]:
  check_dup_ctors (tvs,tn,condefs) ⇔ ALL_DISTINCT (MAP FST condefs)
Proof
  rw[check_dup_ctors_def] >> AP_TERM_TAC >>
  Induct_on `condefs` >> rw[] >> pairarg_tac >> gvs[]
QED

Triviality build_constrs_MAP[simp]:
  build_constrs stamp (MAP (λ(cn,tys). cn, MAP f tys) cndefs) =
  build_constrs stamp cndefs
Proof
  Induct_on `cndefs` >> rw[build_constrs_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
QED


(****************************** Relating namespaces ******************************)

(********** Building a `cnenv` **********)

Definition initial_cnenv_def:
  initial_cnenv = [
    ("True", TypeStamp "True" bool_type_num, 0n);
    ("False", TypeStamp "False" bool_type_num, 0n);
    ("[]", TypeStamp "[]" list_type_num, 0n);
    ("::", TypeStamp "::" list_type_num, 2n);
    ("Subscript", subscript_stamp, 0n)
    ]
End

Overload cnenv_of_tdefs = ``λtdefs.
  FLAT (MAPi (λn (ar,cndefs).
      MAP (λ(cn,ts). explode cn, TypeStamp (explode cn) (n + t_init), LENGTH ts) cndefs) tdefs)``

Overload cnenv_of_exns = ``λexns.
    MAPi (λn (cn,ts). (explode cn, ExnStamp (n + e_init), LENGTH ts)) exns``


(***** Lemmas *****)

Theorem ALOOKUP_cnenv_of_tdefs_NONE:
  ALOOKUP (cnenv_of_tdefs tdefs) k = NONE ⇔
    ¬ MEM (implode k) (MAP FST $ FLAT $ MAP SND tdefs)
Proof
  rw[ALOOKUP_NONE, MEM_MAP, EXISTS_PROD] >>
  rw[MEM_FLAT, indexedListsTheory.MEM_MAPi, PULL_FORALL] >> eq_tac >> rw[]
  >- (
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[PULL_EXISTS] >>
    last_x_assum $ assume_tac o SRULE [MEM_EL] >> gvs[EL_MAP] >>
    goal_assum drule >> pairarg_tac >> gvs[] >>
    simp[MEM_MAP, EXISTS_PROD, SF SFY_ss] >>
    first_assum $ irule_at Any >> simp[]
    )
  >- (
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    pairarg_tac >> gvs[MEM_MAP, EXISTS_PROD] >>
    goal_assum $ drule_at Any >> simp[MEM_EL] >> goal_assum drule >> simp[]
    )
QED

Theorem ALOOKUP_MAP_MAP':
  (∀x y. f x = f y ⇔ x = y) ⇒
  ALOOKUP (MAP (λ(k,v). (f k, g k v)) al) (f a) =
  ALOOKUP (MAP (λ(k,v). (k, g k v)) al) a
Proof
  Induct_on ‘al’ >> simp[FORALL_PROD]
QED

Theorem ALOOKUP_cnenv_of_tdefs_SOME_lemma[local]:
  ∀tdefs n ar cndefs k ts m.
  ALL_DISTINCT (MAP FST $ FLAT $ MAP SND tdefs) ∧
  oEL n tdefs = SOME (ar,cndefs) ∧ MEM (k,ts) cndefs
  ⇒
  ALOOKUP (FLAT (MAPi (λn (ar,cndefs).
      MAP (λ(cn,ts). (explode cn, TypeStamp (explode cn) (n + m + t_init),
                      LENGTH ts)) cndefs) tdefs)) (explode k) =
      SOME (TypeStamp (explode k) (n + m + t_init), LENGTH ts)
Proof
  Induct >> rw[] >> gvs[oEL_THM] >> Cases_on `n` >> gvs[]
  >- (
    simp[ALOOKUP_APPEND, ALOOKUP_MAP_2, ALOOKUP_MAP_MAP'] >>
    drule_at Any ALOOKUP_ALL_DISTINCT_MEM >> gvs[ALL_DISTINCT_APPEND]
    ) >>
  pairarg_tac >> gvs[] >>
  simp[ALOOKUP_APPEND, ALOOKUP_MAP_2, ALOOKUP_MAP_MAP'] >>
  `ALOOKUP cndefs' k = NONE` by (
    simp[ALOOKUP_NONE] >> gvs[ALL_DISTINCT_APPEND] >>
    CCONTR_TAC >> gvs[] >>
    first_x_assum drule >> gvs[MEM_MAP, MEM_FLAT, EXISTS_PROD, PULL_EXISTS] >>
    pop_assum kall_tac >> goal_assum $ drule_at Any >> simp[MEM_EL] >>
    goal_assum drule >> simp[]) >>
  simp[] >> gvs[ALL_DISTINCT_APPEND] >>
  last_x_assum drule_all >> simp[combinTheory.o_DEF, ADD1] >>
  disch_then $ qspec_then `m + 1` mp_tac >> simp[]
QED

Theorem ALOOKUP_cnenv_of_tdefs_SOME =
 ALOOKUP_cnenv_of_tdefs_SOME_lemma |> SPEC_ALL |>
 Q.INST [`m` |-> `0`] |> SRULE [];

Theorem ALOOKUP_cnenv_of_tdefs_SOME_imp_lemma[local]:
  ∀tdefs m cn res.
  ALOOKUP (FLAT (MAPi (λn (ar,cndefs).
      MAP (λ(cn,ts). (explode cn, TypeStamp (explode cn) (n + m + t_init),
                      LENGTH ts))
          cndefs) tdefs)) (explode cn) =
      SOME res
  ⇒ ∃n ar cndefs ts.
      oEL n tdefs = SOME (ar,cndefs) ∧ MEM (cn,ts) cndefs ∧
      res = (TypeStamp (explode cn) (n + m + t_init), LENGTH ts)
Proof
  Induct >> rw[] >> pairarg_tac >> gvs[ALOOKUP_APPEND] >>
  reverse FULL_CASE_TAC >> gvs[]
  >- (
    gvs[ALOOKUP_MAP_2, oEL_THM, ALOOKUP_MAP_MAP'] >> imp_res_tac ALOOKUP_MEM >>
    goal_assum drule >> simp[]
    ) >>
  gvs[combinTheory.o_DEF, ADD1] >>
  last_x_assum $ qspec_then `m + 1` assume_tac >> gvs[] >>
  last_x_assum drule >> strip_tac >> gvs[] >>
  qexists `SUC n` >> gvs[oEL_THM] >> goal_assum drule >> simp[]
QED

Theorem ALOOKUP_cnenv_of_tdefs_SOME_imp =
 ALOOKUP_cnenv_of_tdefs_SOME_imp_lemma |> SPEC_ALL |>
 Q.INST [`m` |-> `0`, ‘cn’ |-> ‘implode cnn’] |> SRULE [];

Theorem ALOOKUP_cnenv_of_exns_NONE:
  ALOOKUP (cnenv_of_exns exns) k = NONE ⇔ ¬ MEM (implode k) (MAP FST exns)
Proof
  rw[ALOOKUP_NONE, MEM_MAP, EXISTS_PROD] >>
  rw[indexedListsTheory.MEM_MAPi, PULL_FORALL] >> eq_tac >> rw[]
  >- (
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[PULL_EXISTS] >>
    last_x_assum $ assume_tac o SRULE [MEM_EL] >> gvs[] >>
    goal_assum $ drule_at Any >> pairarg_tac >> gvs[]
    )
  >- (
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    pairarg_tac >> gvs[] >> simp[MEM_EL] >> goal_assum drule >> simp[]
    )
QED

Theorem ALOOKUP_cnenv_of_exns_SOME_lemma[local]:
  ∀exns n cn ts m.
    ALL_DISTINCT (MAP FST exns) ∧ oEL n exns = SOME (cn,ts) ⇒
    ALOOKUP (MAPi (λn (cn,ts).
                     (explode cn, ExnStamp (n + m + e_init), LENGTH ts)) exns)
            (explode cn) =
    SOME (ExnStamp (n + m + e_init), LENGTH ts)
Proof
  Induct >> rw[] >> gvs[oEL_THM] >> pairarg_tac >> gvs[] >> Cases_on `n` >> gvs[] >>
  rw[] >-  gvs[MEM_MAP, EXISTS_PROD, MEM_EL] >>
  simp[combinTheory.o_DEF, ADD1] >> last_x_assum drule_all >>
  disch_then $ qspec_then `m + 1` mp_tac >> simp[]
QED

Theorem ALOOKUP_cnenv_of_exns_SOME =
 ALOOKUP_cnenv_of_exns_SOME_lemma |> SPEC_ALL |>
 Q.INST [`m` |-> `0`] |> SRULE [];

Theorem ALOOKUP_cnenv_of_exns_SOME_imp_lemma[local]:
  ∀exns m cn res.
    ALOOKUP (MAPi (λn (cn,ts).
                     (explode cn, ExnStamp (n + m + e_init), LENGTH ts)) exns)
            (explode cn) =
    SOME res ⇒
    ∃n ts. oEL n exns = SOME (cn, ts) ∧
           res = (ExnStamp (n + m + e_init), LENGTH ts)
Proof
  Induct >> rw[] >> pairarg_tac >> gvs[ALOOKUP_APPEND] >>
  FULL_CASE_TAC >> gvs[] >- simp[oEL_THM] >>
  gvs[combinTheory.o_DEF, ADD1] >>
  last_x_assum $ qspec_then `m + 1` assume_tac >> gvs[] >>
  last_x_assum drule >> strip_tac >> gvs[] >>
  qexists `SUC n` >> gvs[oEL_THM]
QED

Theorem ALOOKUP_cnenv_of_exns_SOME_imp =
 ALOOKUP_cnenv_of_exns_SOME_imp_lemma |> SPEC_ALL |>
 Q.INST [`m` |-> `0`, ‘cn’ |-> ‘implode cnn’] |> SRULE [];


(********** Building a CakeML namespace **********)

Definition build_exns_def:
  build_exns next_stamp [] = alist_to_ns [] ∧
  build_exns next_stamp ((cn,ts)::rest) =
    nsAppend (build_exns (next_stamp + 1n) rest)
             (nsSing (explode cn) (LENGTH ts, ExnStamp next_stamp))
End

Definition build_typedefs_def:
  build_typedefs next_stamp [] = alist_to_ns [] ∧
  build_typedefs next_stamp ((ar,cndefs)::rest) =
    nsAppend (build_typedefs (next_stamp + 1) rest)
             (alist_to_ns $ REVERSE $ build_constrs next_stamp $
              MAP (λ(cn,tys). (explode cn, MAP (K cunit) tys)) cndefs)
End


(***** Lemmas *****)

Theorem nsLookup_build_exns_NONE:
  ¬ MEM (implode cn) (MAP FST exns) ⇒
  nsLookup (build_exns n exns) (Short cn :(string,string) id) = NONE
Proof
  qid_spec_tac `n` >> Induct_on `exns` >> rw[build_exns_def] >>
  PairCases_on `h` >> rw[build_exns_def] >>
  simp[nsLookup_nsAppend_none] >> strip_tac >> gvs[]
QED

Theorem nsLookup_build_typedefs_NONE:
  ¬ MEM (implode cn) (MAP FST $ FLAT $ MAP SND tdefs) ⇒
  nsLookup (build_typedefs n tdefs) (Short cn :(string,string) id) = NONE
Proof
  qid_spec_tac `n` >> Induct_on `tdefs` >> rw[build_typedefs_def] >>
  PairCases_on `h` >> rw[build_typedefs_def] >>
  simp[nsLookup_nsAppend_none, id_to_mods_def] >> gvs[] >>
  simp[nsLookup_alist_to_ns_none, ALOOKUP_NONE] >>
  simp[build_constrs_def, MAP_REVERSE] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
  simp[MEM_MAP, FORALL_PROD] >> rw[] >> gvs[MEM_MAP, PULL_EXISTS]
QED

Theorem nsLookup_build_exns_SOME:
  ∀exns n cn ts m.
  ALL_DISTINCT (MAP FST exns) ∧
  oEL n exns = SOME (cn, ts) ⇒
  nsLookup (build_exns m exns) (Short (explode cn) :(string,string) id) =
    SOME (LENGTH ts, ExnStamp (n + m))
Proof
  Induct >> rw[build_exns_def, oEL_THM] >>
  PairCases_on `h` >> gvs[] >> Cases_on `n` >> gvs[build_exns_def] >>
  simp[nsLookup_nsAppend_some, nsLookup_build_exns_NONE, id_to_mods_def] >>
  `m + SUC n' = (m + 1) + n'` by simp[] >> pop_assum SUBST_ALL_TAC >>
  first_x_assum irule >> simp[oEL_THM]
QED

Theorem nsLookup_build_typedefs_SOME:
  ∀tdefs n ar cndefs cn ts m.
  ALL_DISTINCT (MAP FST $ FLAT $ MAP SND (tdefs : typedefs)) ∧
  oEL n tdefs = SOME (ar, cndefs) ∧
  MEM (cn, ts) cndefs ⇒
  nsLookup (build_typedefs m tdefs) (Short (explode cn) :(string,string) id) =
    SOME (LENGTH ts, TypeStamp (explode cn) (n + m))
Proof
  Induct >> rw[build_typedefs_def, oEL_THM] >> gvs[ALL_DISTINCT_APPEND] >>
  PairCases_on `h` >> gvs[] >> reverse $ Cases_on `n` >> gvs[build_typedefs_def] >>
  simp[nsLookup_nsAppend_some, id_to_mods_def]
  >- (disj1_tac >> gvs[oEL_THM] >> last_x_assum drule_all >> simp[]) >>
  DEP_REWRITE_TAC[nsLookup_build_typedefs_NONE] >> simp[] >>
  first_x_assum $ irule_at Any >> simp[MEM_MAP, EXISTS_PROD, SF SFY_ss] >>
  simp[nsLookup_alist_to_ns_some, build_constrs_def] >>
  DEP_REWRITE_TAC[alookup_distinct_reverse] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
  simp[ALOOKUP_MAP_2] >> drule_all ALOOKUP_ALL_DISTINCT_MEM >>
  rw[]
  >- (‘(λ(x,y:type list). explode x) = explode o FST’
        by simp[FUN_EQ_THM, FORALL_PROD] >>
      simp[GSYM MAP_MAP_o]) >>
  simp[ALOOKUP_MAP_MAP', ALOOKUP_MAP_2]
QED

Theorem step_over_exndef:
  ∀exns benv dst env envl envg k p prog. ∃n.
    step_n benv n
     (Dstep dst (Env env) (CdlocalG envl envg (compile_exndef exns ++ p::prog) :: k)) =
    Dstep
     (dst with next_exn_stamp := dst.next_exn_stamp + LENGTH exns)
     (Decl p)
     (CdlocalG envl
      (<| v := nsEmpty; c := build_exns dst.next_exn_stamp exns |>
        +++ env +++ envg)
      prog :: k)
Proof
  Induct >> rw[]
  >- (
    simp[build_exns_def, compile_exndef_def] >>
    qrefine `SUC n` >> simp[dstep] >> qexists0 >> simp[dstep] >>
    simp[dstate_component_equality, extend_dec_env_def]
    ) >>
  PairCases_on `h` >> rename1 `(cn,ts)` >>
  simp[compile_exndef_def, build_exns_def] >>
  ntac 2 (qrefine `SUC n` >> simp[dstep]) >>
  qmatch_goalsub_abbrev_tac `Dstep dst' (Env sing)` >>
  qmatch_goalsub_abbrev_tac `CdlocalG _ (comp_env +++ _ +++ _)` >>
  `comp_env =
    <| v := nsEmpty; c := build_exns (dst.next_exn_stamp + 1) exns |>
      +++ sing` by (
    unabbrev_all_tac >> simp[extend_dec_env_def]) >>
  pop_assum $ SUBST_ALL_TAC >>
  last_x_assum $ qspecl_then
    [`benv`,`dst'`,`sing`,`envl`,`env +++ envg`,`k`,`p`,`prog`] assume_tac >>
  gvs[] >> qrefine `m + n` >> simp[itree_semanticsPropsTheory.step_n_add] >>
  qexists0 >> simp[dstep] >>
  unabbrev_all_tac >> gvs[ADD1]
QED

Theorem ALL_DISTINCT_MAPexplode[simp]:
  ALL_DISTINCT (MAP (λ(k,v). explode k) l) ⇔ ALL_DISTINCT (MAP FST l)
Proof
  Induct_on ‘l’ >> simp[FORALL_PROD, MEM_MAP]
QED

Theorem step_over_typedefs:
  ∀tdefs benv dst env envl envg k p prog.
    EVERY (λtdef. ALL_DISTINCT (MAP FST (SND tdef))) tdefs ⇒
  ∃n.
    step_n benv n
     (Dstep dst (Env env) (CdlocalG envl envg (compile_typedefs tdefs ++ p::prog) :: k)) =
    Dstep
     (dst with next_type_stamp := dst.next_type_stamp + LENGTH tdefs)
     (Decl p)
     (CdlocalG envl
      (<| v := nsEmpty; c := build_typedefs dst.next_type_stamp tdefs |> +++ env +++ envg)
      prog :: k)
Proof
  Induct >> rw[]
  >- (
    simp[build_typedefs_def, compile_typedefs_def] >>
    qrefine `SUC n` >> simp[dstep] >> qexists0 >> simp[dstep] >>
    simp[dstate_component_equality, extend_dec_env_def]
    ) >>
  PairCases_on `h` >> rename1 `(ar,cndefs)` >>
  simp[compile_typedefs_def, build_typedefs_def] >>
  ntac 2 (qrefine `SUC n` >> simp[dstep]) >> simp[build_tdefs_def] >>
  qpat_abbrev_tac `cndefs_ns = alist_to_ns _` >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >> gvs[] >>

  qmatch_goalsub_abbrev_tac `Dstep dst' (Env sing)` >>
  qmatch_goalsub_abbrev_tac `CdlocalG _ (comp_env +++ _ +++ _)` >>
  ‘comp_env =
    <| v := nsEmpty; c := build_typedefs (dst.next_type_stamp + 1) tdefs |> +++ sing’ by (
    unabbrev_all_tac >> simp[extend_dec_env_def]) >>
  pop_assum $ SUBST_ALL_TAC >>
  last_x_assum $ qspecl_then
    [`benv`,`dst'`,`sing`,`envl`,`env +++ envg`,`k`,`p`,`prog`] assume_tac >>
  gvs[] >> qrefine `m + n` >> simp[itree_semanticsPropsTheory.step_n_add] >>
  qexists0 >> simp[dstep] >>
  unabbrev_all_tac >> gvs[ADD1]
QED

Theorem step_over_compile_namespace:
  ∀ns benv dst k p prog.
    EVERY (λtdef. ALL_DISTINCT (MAP FST (SND tdef))) (SND ns) ⇒
  ∃n.
    step_n benv n (Dstep dst (Decl (Dlocal [] (compile_namespace ns ++ p::prog))) k) =
    Dstep
      (dst with <| next_type_stamp := dst.next_type_stamp + LENGTH (SND ns);
                   next_exn_stamp := dst.next_exn_stamp + LENGTH (FST ns) |>)
      (Decl p)
      (CdlocalG empty_dec_env
        <| v := nsEmpty;
           c := nsAppend (build_typedefs dst.next_type_stamp (SND ns))
                         (build_exns dst.next_exn_stamp (FST ns)) |>
        prog :: k)
Proof
  rw[] >> ntac 2 (qrefine `SUC n` >> simp[dstep]) >>
  PairCases_on `ns` >> rename1 `(exndef,tdefs)` >> gvs[compile_namespace_def] >>
  qspecl_then [`exndef`,`benv`,`dst`,`empty_dec_env`,`empty_dec_env`, `empty_dec_env`,
    `k`, `Dlet unknown_loc Pany (Con NONE [])`,`compile_typedefs tdefs ++ p::prog`]
  assume_tac step_over_exndef >> gvs[] >>
  qrefine `m + n` >> simp[itree_semanticsPropsTheory.step_n_add, APPEND_ASSOC_CONS] >>
  qrefine `SUC m` >> simp[dstep, astTheory.pat_bindings_def] >>
  qrefine `SUC m` >> simp[dstep, cstep, do_con_check_def, build_conv_def] >>
  qrefine `SUC m` >> simp[dstep, pmatch_def, astTheory.pat_bindings_def] >>
  simp[GSYM smallStepTheory.empty_dec_env_def] >>
  qmatch_goalsub_abbrev_tac `Dstep dst'` >>
  qmatch_goalsub_abbrev_tac `CdlocalG _ exn_env` >>
  drule step_over_typedefs >>
  disch_then $ qspecl_then [`benv`,`dst'`,`empty_dec_env`,`empty_dec_env`,`exn_env`,
    `k`,`p`,`prog`] assume_tac >> gvs[] >>
  qrefine `m + n'` >> simp[itree_semanticsPropsTheory.step_n_add] >>
  qexists0 >> simp[dstep] >> unabbrev_all_tac >>
  gvs[dstate_component_equality, extend_dec_env_def]
QED

Theorem every_exp_one_con_check_list_to_exp:
  EVERY (every_exp (one_con_check env)) es ∧
  nsLookup env (Short "[]") = SOME (0,stamp1) ∧
  nsLookup env (Short "::") = SOME (2,stamp2)
  ⇒ every_exp (one_con_check env) (list_to_exp es)
Proof
  Induct_on `es` >> rw[list_to_exp_def, do_con_check_def]
QED

Theorem every_exp_one_con_check_compile:
  cexp_compile_rel cnenv se ce ∧
  cnenv_rel cnenv cml_ns
  ⇒ every_exp (one_con_check cml_ns) ce
Proof
  Induct_on `cexp_compile_rel` >> reverse $ rw[] >>
  gvs[do_con_check_def, EVERY_EL, LIST_REL_EL_EQN] >> rw[] >> gvs[]
  >- (pairarg_tac >> gvs[] >> first_x_assum drule >> pairarg_tac >> gvs[])
  >- (pairarg_tac >> gvs[] >> first_x_assum drule >> pairarg_tac >> gvs[])
  >- (pairarg_tac >> gvs[] >> first_x_assum drule >> pairarg_tac >> gvs[])
  >- (
    irule every_exp_one_con_check_list_to_exp >> gvs[EVERY_EL] >>
    gvs[cnenv_rel_def, prim_types_ok_def] >> metis_tac[]
    )
  >- (
    irule every_exp_one_con_check_list_to_exp >> gvs[EVERY_EL] >>
    gvs[cnenv_rel_def, prim_types_ok_def] >> metis_tac[]
    )
  >- (
    gvs[cnenv_rel_def, prim_types_ok_def] >>
    first_x_assum $ qspec_then `"True"` mp_tac >> simp[]
    )
  >- (
    gvs[cnenv_rel_def, prim_types_ok_def] >>
    first_x_assum $ qspec_then `"False"` mp_tac >> simp[]
    )
  >- (
    gvs[cnenv_rel_def, prim_types_ok_def] >>
    first_x_assum $ qspec_then `"False"` mp_tac >> simp[]
    )
  >- (gvs[cnenv_rel_def] >> first_x_assum drule >> simp[])
QED



(********** Key namespace result **********)

Triviality namespace_ok_append_cn_imps:
  ∀ns ns'. namespace_ok (append_ns (ns0,ns1) (ns'0,ns'1)) ⇒
  (∀cn. MEM cn (MAP FST ns0) ∨ MEM cn (MAP FST $ FLAT $ MAP SND ns1) ⇒
    ¬ MEM cn (MAP FST ns'0) ∧
    ¬ MEM cn (MAP FST $ FLAT $ MAP SND ns'1)) ∧
  (∀cn. MEM cn (MAP FST ns'0) ∨ MEM cn (MAP FST $ FLAT $ MAP SND ns'1) ⇒
    ¬ MEM cn (MAP FST ns0) ∧
    ¬ MEM cn (MAP FST $ FLAT $ MAP SND ns1)) ∧
  (∀cn.  explode cn ∈ reserved_cns ∧ explode cn ≠ "Subscript" ⇒
    ¬ MEM cn (MAP FST ns'0) ∧
    ¬ MEM cn (MAP FST $ FLAT $ MAP SND ns'1) ∧
    ¬ MEM cn (MAP FST ns0) ∧
    ¬ MEM cn (MAP FST $ FLAT $ MAP SND ns1)) ∧
  (∀cn. MEM cn (MAP FST ns'0) ⇒ ¬ MEM cn (MAP FST $ FLAT $ MAP SND ns'1))
Proof
  rw[namespace_ok_def] >>
  ‘FINITE reserved_cns’ by simp[reserved_cns_def] >>
  gvs[ALL_DISTINCT_APPEND, MEM_MAP, PULL_EXISTS, EXISTS_PROD, FORALL_PROD,
      MEM_SET_TO_LIST, DISJ_IMP_THM, FORALL_AND_THM] >>
  metis_tac[mlstringTheory.implode_explode, mlstringTheory.explode_implode]
QED

Theorem ns_to_cml_ns:
  namespace_ok (append_ns initial_namespace (exndef,tdefs)) ∧
  cml_ns = nsAppend (build_typedefs t_init tdefs) $
           nsAppend (build_exns e_init exndef) $
           start_env.c
  ⇒ ∃cnenv.
      ns_rel (append_ns initial_namespace (exndef,tdefs)) cnenv ∧
      cnenv_rel cnenv cml_ns
Proof
  rw[] >>
  qexists_tac `initial_cnenv ++ cnenv_of_tdefs tdefs ++ cnenv_of_exns exndef` >>
  rw[]
  >- ( (* ns_rel *)
    rw[ns_rel_def]
    >- simp[prim_types_ok_def, ALOOKUP_APPEND, initial_cnenv_def]
    >- ( (* exception *)
      gvs[oEL_THM, EL_APPEND_EQN, AllCaseEqs()]
      >- ( (* Subscript *)
        gvs[initial_namespace_def] >>
        simp[ALOOKUP_APPEND, initial_cnenv_def, subscript_stamp_def]
        ) >>
      gvs[EVAL ``LENGTH (FST initial_namespace)``] >>
      Cases_on `n` >> gvs[ADD1] >> rename1 `EL n` >>
      simp[ALOOKUP_APPEND] >>
      `MEM cn (MAP FST exndef)` by (
        simp[MEM_EL, EL_MAP, SF CONJ_ss] >> goal_assum drule >> simp[]) >>
      `ALOOKUP initial_cnenv (explode cn) = NONE` by (
        simp[ALOOKUP_NONE, initial_cnenv_def] >>
        drule $ SRULE [] namespace_ok_append_cn_imps >>
        gvs[initial_namespace_def, reserved_cns_def] >>
        rpt strip_tac >> rpt (first_x_assum $ qspec_then ‘cn’ assume_tac) >>
        gvs[] >> metis_tac[mlstringTheory.implode_explode,
                           mlstringTheory.implode_def,
                           mlstringTheory.explode_implode]) >>
      simp[] >>
      `ALOOKUP (cnenv_of_tdefs tdefs) (explode cn) = NONE` by (
        simp[ALOOKUP_cnenv_of_tdefs_NONE] >>
        drule $ SRULE [] namespace_ok_append_cn_imps >> metis_tac[]) >>
      simp[] >> irule ALOOKUP_cnenv_of_exns_SOME >> simp[oEL_THM] >>
      gvs[namespace_ok_def, ALL_DISTINCT_APPEND]
      )
    >- ( (* type *)
      gvs[oEL_THM, EL_APPEND_EQN, AllCaseEqs()]
      >- ( (* List *)
        gvs[initial_namespace_def] >>
        gvs[ALOOKUP_APPEND, initial_cnenv_def, list_type_num_def]
        ) >>
      gvs[EVAL ``LENGTH (SND initial_namespace)``] >>
      Cases_on `n` >> gvs[ADD1] >> rename1 `EL n` >>
      simp[ALOOKUP_APPEND] >>
      `MEM cn (MAP FST $ FLAT $ MAP SND tdefs)` by (
        simp[MEM_MAP, MEM_FLAT, EXISTS_PROD, PULL_EXISTS] >>
        goal_assum $ drule_at Any >> simp[MEM_EL] >>
        goal_assum drule >> simp[]) >>
      `ALOOKUP initial_cnenv (explode cn) = NONE` by (
        simp[ALOOKUP_NONE, initial_cnenv_def] >>
        drule $ SRULE [] namespace_ok_append_cn_imps >>
        gvs[initial_namespace_def, reserved_cns_def] >>
        metis_tac[mlstringTheory.implode_explode,
                  mlstringTheory.implode_def,
                  mlstringTheory.explode_implode]) >>
      simp[AllCaseEqs()] >> disj2_tac >>
      simp[] >> irule ALOOKUP_cnenv_of_tdefs_SOME >>
      simp[oEL_THM] >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND]
      )
    )
  >- ( (* cnenv_rel *)
    rw[cnenv_rel_def]
    >- ( (* prim_types_ok *)
      simp[prim_types_ok_def, ALOOKUP_APPEND, initial_cnenv_def]
      )
    >- ( (* uniqueness *)
      gvs[ALOOKUP_APPEND, AllCaseEqs()] >>
      imp_res_tac ALOOKUP_cnenv_of_tdefs_SOME_imp >>
      imp_res_tac ALOOKUP_cnenv_of_exns_SOME_imp >> gvs[] >>
      gvs[initial_cnenv_def, AllCaseEqs(), subscript_stamp_def] >>
      gvs[mlstringTheory.implode_def]
      )
    >- (
      gvs[ALOOKUP_APPEND, AllCaseEqs()] >>
      imp_res_tac ALOOKUP_cnenv_of_tdefs_SOME_imp >>
      imp_res_tac ALOOKUP_cnenv_of_exns_SOME_imp >> gvs[]
      >- (
        `MEM (implode cn) (MAP FST exndef)` by (
          gvs[oEL_THM, MEM_EL, EL_MAP, SF CONJ_ss] >> goal_assum drule >> simp[]) >>
        qsuff_tac `cn ∉ reserved_cns ∨ cn = "Subscript"` >- rw[reserved_cns_def] >>
        drule $ SRULE [] namespace_ok_append_cn_imps >>
        metis_tac[mlstringTheory.explode_implode,
                  mlstringTheory.implode_explode]
        )
      >- (
        `MEM (implode cn) (MAP FST $ FLAT $ MAP SND tdefs)` by (
          simp[MEM_MAP, MEM_FLAT, EXISTS_PROD, PULL_EXISTS] >>
          goal_assum $ drule_at Any >> simp[MEM_EL] >> gvs[oEL_THM] >>
          goal_assum drule >> simp[]) >>
        qsuff_tac `cn ∉ reserved_cns ∨ cn = "Subscript"` >- rw[reserved_cns_def] >>
        drule $ SRULE [] namespace_ok_append_cn_imps >>
        metis_tac[mlstringTheory.explode_implode,
                  mlstringTheory.implode_explode]
        )
      >- gvs[initial_cnenv_def, AllCaseEqs()]
      )
    >- ( (* Constructors match *)
      gvs[ALOOKUP_APPEND, AllCaseEqs()] >>
      imp_res_tac ALOOKUP_cnenv_of_tdefs_SOME_imp >>
      imp_res_tac ALOOKUP_cnenv_of_exns_SOME_imp >> gvs[] >>
      gvs[ALOOKUP_cnenv_of_tdefs_NONE, ALOOKUP_cnenv_of_exns_NONE] >>
      simp[nsLookup_nsAppend_some, nsLookup_nsAppend_none, id_to_mods_def] >>
      simp[nsLookup_build_typedefs_NONE, nsLookup_build_exns_NONE]
      >- (
        drule_at Any nsLookup_build_exns_SOME >>
        disch_then $ qspec_then `e_init` mp_tac >> impl_tac >> rw[] >>
        gvs[namespace_ok_def, ALL_DISTINCT_APPEND]
        )
      >- (
        drule_at Any nsLookup_build_typedefs_SOME >> disch_then $ drule_at Any >>
        impl_tac >> rw[] >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND]
        )
      >- (
        disj2_tac >>
        DEP_REWRITE_TAC[nsLookup_build_typedefs_NONE, nsLookup_build_exns_NONE] >>
        reverse $ conj_tac
        >- (
          gvs[initial_cnenv_def, AllCaseEqs(), start_env_def, nsLookup_def] >>
          simp[bool_type_num_def, list_type_num_def, subscript_stamp_def]
          ) >>
        drule $ SRULE [] $ cj 1 namespace_ok_append_cn_imps >>
        simp[initial_namespace_def, DISJ_IMP_THM, FORALL_AND_THM] >>
        strip_tac >> drule ALOOKUP_MEM >> simp[initial_cnenv_def] >>
        strip_tac >> gvs[] >> simp[mlstringTheory.implode_def] >>
        `"True" ∈ reserved_cns ∧ "False" ∈ reserved_cns` by simp[reserved_cns_def] >>
        drule $ SRULE [] $ cj 3 namespace_ok_append_cn_imps >>
        disch_then (imp_res_tac o SRULE [] o Q.GEN ‘cnn’ o
                    Q.SPEC ‘implode cnn’) >> gvs[mlstringTheory.implode_def]
        )
      )
    >- ( (* TypeStamp well-formed *)
      gvs[ALOOKUP_APPEND, AllCaseEqs()] >>
      imp_res_tac ALOOKUP_cnenv_of_tdefs_SOME_imp >>
      imp_res_tac ALOOKUP_cnenv_of_exns_SOME_imp >> gvs[] >>
      gvs[initial_cnenv_def, AllCaseEqs(), subscript_stamp_def]
      )
    )
QED



(****************************** compile_correct ******************************)

Theorem compile_correct:
  cexp_wf e ∧
  cns_ok ns (state_cexp$cns_arities e) ∧
  namespace_init_ok ns ∧
  safe_itree (itree_of (exp_of e))
  ⇒ itree_rel (itree_of (exp_of e))
              (itree_semantics (compile_with_preamble c ns e)) ∧
    safe_itree ffi_convention (itree_semantics (compile_with_preamble c ns e))
Proof
  simp[itree_of_def, semantics_def, itree_semantics_def, cns_ok_def] >> strip_tac >>
  irule_at Any compile_itree_rel >> irule_at Any compile_safe_itree >>
  goal_assum drule >> qrefinel [`n`,`n`] >> simp[] >>
  simp[dstep_rel_cases, step_rel_cases, PULL_EXISTS] >>
  qrefinel [`_`,`_`,`_`,`_`,`c.do_final_gc`] >>
  simp[Once cont_rel_cases, env_rel_def, state_rel] >>
  gvs[namespace_init_ok_def] >>
  simp[compile_with_preamble_def, initial_namespace_def, preamble_def] >>
  qmatch_goalsub_abbrev_tac `[ffi_array;strle_dec;char_list_dec]` >>
  ntac 2 $ once_rewrite_tac[GSYM APPEND_ASSOC] >>
  qmatch_goalsub_abbrev_tac `compile_namespace _ ++ prog` >>
  qspecl_then [`ns'`,`start_env`,`start_dstate`,`[]`,`HD prog`,`TL prog`]
    mp_tac step_over_compile_namespace >>
  impl_tac
  >- (
    `ALL_DISTINCT (MAP FST (FLAT (MAP SND (SND ns'))))` by (
      gvs[namespace_ok_def, ALL_DISTINCT_APPEND]) >>
    gvs[MAP_FLAT] >> drule ALL_DISTINCT_FLAT_IMP >> rw[EVERY_MEM] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    gvs[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >>
    PairCases_on `tdef` >> first_x_assum drule >> gvs[]
    ) >>
  strip_tac >> gvs[Abbr `prog`] >>
  ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC] >> rewrite_tac[APPEND]) >> simp[] >>
  qrefine `m + n` >> simp[itree_semanticsPropsTheory.step_n_add] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `Dstep dst'` >> qpat_abbrev_tac `cml_ns = nsAppend _ _` >>
  simp[Abbr `ffi_array`] >>
    ntac 6 (qrefine `SUC m` >> simp[dstep, cstep, astTheory.pat_bindings_def]) >>
    simp[do_app_def, integerTheory.INT_ADD_CALCULATE, store_alloc_def] >>
    qrefine `SUC m` >> simp[dstep, cstep, astTheory.pat_bindings_def, pmatch_def] >>
  simp[Abbr `strle_dec`, strle_exp_def] >>
    ntac 2 (qrefine `SUC m` >> simp[dstep, cstep, astTheory.pat_bindings_def]) >>
    qmatch_goalsub_abbrev_tac `COND condition` >>
    `condition` by (
      unabbrev_all_tac >> simp[do_con_check_def, SF CONJ_ss] >>
      simp[smallStepTheory.collapse_env_def, extend_dec_env_def] >>
      once_rewrite_tac[DECIDE ``x ∧ y ⇔ (x = T) ∧ (y = T)``] >>
      rewrite_tac[AllCaseEqs()] >>
      rw[EXISTS_PROD, nsLookup_nsAppend_some, id_to_mods_def] >>
      rpt $ irule_at Any OR_INTRO_THM2 >> simp[nsLookup_nsAppend_none] >>
      DEP_REWRITE_TAC[nsLookup_build_typedefs_NONE, nsLookup_build_exns_NONE] >>
      simp[start_env_def, nsLookup_def] >>
      qmatch_goalsub_abbrev_tac `implode cn` >>
      gvs[namespace_ok_def, initial_namespace_def, ALL_DISTINCT_APPEND] >>
      ntac 2 $ first_x_assum $ qspec_then `implode cn` mp_tac >>
      simp[Abbr `cn`, MEM_MAP, mlstringTheory.implode_def] >>
      DEP_REWRITE_TAC[MEM_SET_TO_LIST] >> simp[reserved_cns_def]) >>
    simp[] >> ntac 2 $ pop_assum kall_tac >>
    qrefine `SUC m` >> simp[dstep, cstep, astTheory.pat_bindings_def] >>
  simp[Abbr `char_list_dec`, char_list_exp_def] >>
    qrefine `SUC m` >> simp[dstep, cstep, astTheory.pat_bindings_def] >>
    qmatch_goalsub_abbrev_tac `COND condition` >>
    `condition` by (
      unabbrev_all_tac >> simp[do_con_check_def, SF CONJ_ss] >>
      simp[smallStepTheory.collapse_env_def, extend_dec_env_def] >>
      once_rewrite_tac[DECIDE ``x ∧ y ⇔ (x = T) ∧ (y = T)``] >>
      rewrite_tac[AllCaseEqs()] >>
      rw[EXISTS_PROD, nsLookup_nsAppend_some, id_to_mods_def] >>
      rpt $ irule_at Any OR_INTRO_THM2 >> simp[nsLookup_nsAppend_none] >>
      DEP_REWRITE_TAC[nsLookup_build_typedefs_NONE, nsLookup_build_exns_NONE] >>
      simp[start_env_def, nsLookup_def, mlstringTheory.implode_def] >>
      qmatch_goalsub_abbrev_tac `MEM cn _` >>
      gvs[namespace_ok_def, initial_namespace_def, ALL_DISTINCT_APPEND] >>
      first_x_assum $ qspec_then `cn` mp_tac >> simp[]) >>
    simp[] >> ntac 2 $ pop_assum kall_tac >>
    ntac 2 (qrefine `SUC m` >> simp[dstep, cstep, astTheory.pat_bindings_def]) >>
  qexists0 >> simp[dstep, Abbr `dst'`] >>
  simp[start_dstate_def, smallStepTheory.collapse_env_def] >>
  simp[extend_dec_env_def, build_rec_env_def] (* slow step *) >>
  irule_at Any $ SRULE [SimpRHS] $ SCONV []
    ``condition ∧ a = res ∧ rest ⇒ (if condition then a else b) = res ∧ rest`` >>
  irule_at Any every_exp_one_con_check_compile >>
  simp[env_ok_def, nsLookup_nsAppend_some] >>
  simp[strle_v_def, char_list_v_def, strle_exp_def, char_list_exp_def] >>
  irule_at Any compile_rel_cexp_compile_rel >> qexists `e` >>
  rpt $ irule_at Any compile_cexp_compile_rel >> rpt $ goal_assum $ drule_at Any >>
  PairCases_on `ns'` >> rename1 `append_ns _ (exns,tdefs)` >>
  drule ns_to_cml_ns >> gvs[start_dstate_def] >> strip_tac >> gvs[] >>
  rpt $ goal_assum drule >> simp[] >> gvs[cnenv_rel_def, prim_types_ok_def]
QED

(**********)

val _ = export_theory ();
