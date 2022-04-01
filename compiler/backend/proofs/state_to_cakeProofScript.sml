(*
  Correctness for compilation from stateLang to CakeML
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     rich_listTheory arithmeticTheory;
open semanticPrimitivesTheory itree_semanticsTheory;
open pure_miscTheory pure_configTheory stateLangTheory;

val _ = new_theory "state_to_cakeProof";


(****************************************)

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
  atom_op_rel Elem Strsub ∧
  atom_op_rel StrEq Equality
End

Inductive op_rel:
  op_rel AppOp Opapp ∧
  (atom_op_rel aop op ⇒ op_rel (AtomOp aop) op) ∧
  op_rel Alloc Aalloc ∧
  op_rel Ref Opref ∧
  op_rel Length Alength ∧
  op_rel Sub Asub ∧
  op_rel UnsafeSub Asub_unsafe ∧
  op_rel Update Aupdate ∧
  op_rel UnsafeUpdate Aupdate_unsafe
End


Overload capp = ``λce1 ce2. ast$App Opapp [ce1; ce2]``;
Overload int  = ``λi. ast$Lit $ IntLit i``;
Overload clet = ``λs e1 e2. ast$Let (SOME s) e1 e2``;
Overload ifeq = ``λ(a,b) e1 e2. ast$If (App Equality [a;b]) e1 e2``;
Overload iflt = ``λ(a,b) e1 e2. ast$If (App (Opb Lt) [a;b]) e1 e2``
Overload var  = ``λs. ast$Var $ Short s``;

(*
  if v2 = 0 then 0 else Divide v1 v2
*)
Overload div =
  ``ifeq (var "v2", int 0) (int 0) (App (Opn Divide) [var "v1"; var "v2"])``;

(*
  if v2 = 0 then 0 else Modulo v1 v2
*)
Overload mod =
  ``ifeq (var "v2", int 0) (int 0) (App (Opn Modulo) [var "v1"; var "v2"])``;

(*
  let strlen = LENGTH s in
  let off = if i < 0 then 0 else i in
  if off < strlen then
    CopyStrStr s off (strlen - off)
    else ""
*)
Overload substring2 =
  ``clet "strlen" (App Strlen [var "s"]) $
    clet "off" (iflt (var "i", int 0) (int 0) (var "i")) $
    iflt (var "off", var "strlen")
      (App CopyStrStr [var "s"; var "off"; App (Opn Minus) [var "strlen"; var "off"]])
      (Lit $ StrLit "")``;

(*
  λs i l.
    if l < 0 then "" else
      let strlen = LENGTH s in
      let off = if i < 0 then 0 else i in
      if off < strlen then
        let off_l = off + l in
        let end = (if off_l < strlen then off_l else strlen) in
        CopyStrStr s off (end - off)
      else ""
*)
Overload substring3 =
  ``iflt (var "l", int 0) (Lit $ StrLit "") $
    clet "strlen" (App Strlen [var "s"]) $
    clet "off" (iflt (var "i", int 0) (int 0) (var "i")) $
    iflt (var "off", var "strlen") (
      clet "off_l" (App (Opn Plus) [var "off"; var "l"]) $
      clet "end" (ifflt (var "off_l", var "strlen") (var "off_l") (var "strlen")) $
      App CopyStrStr [var "s"; var "off"; App (Opn Minus) [var "end"; var "off"]])
      (Lit $ StrLit "")``;

(*
  λch ce.
    App (FFI ch) [ce; var "ffi_array"];
    let len0 = Int (ffi_array[0]) in
    let len1 = Int (ffi_array[1]) in
    let len = (len1 * 256) + len0 in
    let len = (if 4094 < len then 4094 else len) in
    CopyAw8Str ffi_array 2 len
*)
Overload ffi =
  ``λch. Let NONE (App (FFI ch) [var "s"; var "ffi_array"]) $
      clet "len0" (App (WordToInt W8) [(App Aw8sub_unsafe [var "ffi_array"; int 0])]) $
      clet "len1" (App (WordToInt W8) [(App Aw8sub_unsafe [var "ffi_array"; int 1])]) $
      clet "len" (App (Opn Plus) [App (Opn Times) [var "len1"; int 256]; var "len0"]) $
      clet "len" (iflt (int 4094, var "len") (int 4094) (var "len")) $
      App CopyAw8Str [var "ffi_array"; int 2; var "len"]``;

(* TODO list_to_v exists in CakeML - is there a list_to_exp already? *)
(* right to left evaluation should hold for this too *)
Definition list_to_exp_def:
  list_to_exp [] = Con (SOME $ Short "[]") [] ∧
  list_to_exp (e::es) = Con (SOME $ Short "::") [e; list_to_exp es]
End

Inductive compile_rel:
[~IntLit:]
  compile_rel cnenv (App (AtomOp (Lit $ Int i)) []) (Lit $ IntLit i) ∧

[~StrLit:]
  compile_rel cnenv (App (AtomOp (Lit $ Str s)) []) (Lit $ StrLit s) ∧

[~Tuple:]
  (LIST_REL (compile_rel cnenv) ses ces
    ⇒ compile_rel cnenv (App (Cons "") ses) (Con NONE ces)) ∧

[~Constructor:]
  (LIST_REL (compile_rel cnenv) ses ces ∧
   ALOOKUP cnenv cn = SOME (tyid,ar) ∧
   ar = LENGTH ses ∧ cn ≠ ""
    ⇒ compile_rel cnenv (App (Cons cn) ses) (Con (SOME $ Short cn) ces)) ∧

[~Var:]
  compile_rel cnenv (stateLang$Var v) (Var (Short (var_prefix v))) ∧

[~App:]
  (op_rel sop cop ∧ LIST_REL (compile_rel cnenv) ses ces
    ⇒ compile_rel cnenv (App sop ses) (App cop ces)) ∧

[~Divide:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2
    ⇒ compile_rel cnenv (App (AtomOp Div) [se1;se2])
                        (clet "v2" ce2 $ clet "v1" ce1 div)) ∧

[~Mod:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2
    ⇒ compile_rel cnenv (App (AtomOp Mod) [se1;se2])
                        (clet "v2" ce2 $ clet "v1" ce1 mod)) ∧

[~Concat:]
  (LIST_REL (compile_rel cnenv) ses ces
    ⇒ compile_rel cnenv (App (AtomOp Concat) ses) (App Strcat [list_to_exp ces])) ∧

[~Implode:]
  (LIST_REL (compile_rel cnenv) ses ces
    ⇒ compile_rel cnenv (App (AtomOp Implode) ses) (App Implode [list_to_exp ces])) ∧

[~Substring2:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2
    ⇒ compile_rel cnenv (App (AtomOp Substring) [se1; se2])
                        (clet "i" ce2 $ clet "s" ce1 $ substring2)) ∧

[~Substring3:]
  (LIST_REL (compile_rel cnenv) [se1;se2;se3] [ce1;ce2;ce3]
    ⇒ compile_rel cnenv (App (AtomOp Substring) [se1; se2; se3])
                        (clet "l" ce3 $ clet "i" ce2 $ clet "s" ce1 substring3)) ∧

(* TODO
[~StrLt:]
[~StrLeq:]
[~StrGt:]
[~StrGeq:]
*)

[~FFI:]
  (compile_rel cnenv se ce
    ⇒ compile_rel cnenv (App (FFI ch) [se]) (clet "s" ce (ffi ch))) ∧

[~Lam:]
  (compile_rel cnenv se ce
    ⇒ compile_rel cnenv (stateLang$Lam (SOME x) se) (Fun (var_prefix x) ce)) ∧

[~Letrec:]
  (LIST_REL
      (λ(sv,se) (cv,cx,ce).
        var_prefix sv = cv ∧
        ∃sx se'. se = Lam (SOME sx) se' ∧ var_prefix sx = cx ∧ compile_rel cnenv se' ce)
      sfuns cfuns ∧
    compile_rel cnenv se ce
    ⇒ compile_rel cnenv (stateLang$Letrec sfuns se) (ast$Letrec cfuns ce)) ∧

[~Let:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2
    ⇒ compile_rel cnenv (Let (SOME x) se1 se2) (Let (SOME $ var_prefix x) ce1 ce2)) ∧

[~If:]
  (LIST_REL (compile_rel cnenv) [se;se1;se2] [ce;ce1;ce2]
    ⇒ compile_rel cnenv (If se se1 se2) (If ce ce1 ce2)) ∧

[~Case:]
  (compile_rel cnenv se ce ∧
   EVERY (λ(cn,vs,_). ALOOKUP cnenv cn = SOME (tyid, LENGTH vs)) scss ∧
   LIST_REL (λ(cn,vs,se) (pat,ce). compile_rel cnenv se ce ∧
      pat = Pas ((if cn = "" then Pcon NONE else Pcon (SOME $ Short cn))
                  (MAP (Pvar o var_prefix) vs)) (var_prefix sv)) scss ccss
    ⇒ compile_rel cnenv (Case se sv scss) (Mat (Var $ Short cv) ccss)) ∧

[~Raise:]
  (compile_rel cnenv se ce
    ⇒ compile_rel cnenv (Raise se) (Raise ce)) ∧

[~Handle:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2
    ⇒ compile_rel cnenv (Handle se1 x se2) (Handle ce1 [(Pvar $ var_prefix x, ce2)]))
End

Definition cnenv_rel_def:
  cnenv_rel senv cenv =
    ∀cn tyid ar. ALOOKUP senv cn = SOME (tyid,ar) ⇒
      nsLookup cenv (Short cn) = SOME (ar,tyid)
End

Inductive v_rel:
[~Tuple:]
  (LIST_REL (v_rel cnenv) svs cvs
    ⇒ v_rel cnenv (Constructor "" svs) (Conv NONE cvs)) ∧

[~Constructor:]
  (LIST_REL (v_rel cnenv) svs cvs ∧
   ALOOKUP cnenv cn = SOME (tyid,ar) ∧
   ar = LENGTH svs ∧ cn ≠ ""
    ⇒ v_rel cnenv (Constructor cn svs) (Conv (SOME tyid) cvs)) ∧

[~Closure:]
  (compile_rel cnenv se ce ∧
   env_rel cnenv senv cenv
   ⇒ v_rel cnenv (Closure (SOME sx) senv se) (Closure cenv (var_prefix sx) ce)) ∧

[~Recclosure:]
  (compile_rel cnenv se ce ∧
   env_rel cnenv senv cenv ∧
   LIST_REL (λ(sv,se) (cv,cx,ce).
        var_prefix sv = cv ∧
        ∃sx se'. se = Lam (SOME sx) se' ∧ var_prefix sx = cx ∧ compile_rel cnenv se' ce)
      sfuns cfuns
   ⇒ v_rel cnenv (stateLang$Recclosure sfuns senv sx)
                 (Recclosure cenv cfuns (var_prefix sx))) ∧

[~IntLit:]
  v_rel cnenv (Atom $ Int i) (Litv $ IntLit i) ∧

[~StrLit:]
  v_rel cnenv (Atom $ Str s) (Litv $ StrLit s) ∧

[~Loc:]
  v_rel cnenv (Atom $ Loc n) (Loc (n + 1)) ∧ (* leave space for FFI array *)

[~env_rel:]
  (cnenv_rel cnenv cenv.c ∧
   (∀sx sv.
      ALOOKUP senv sx = SOME sv ⇒
      ∃cv. nsLookup cenv.v (Short $ var_prefix sx) = SOME cv ∧ v_rel cnenv sv cv)
    ⇒ env_rel cnenv senv cenv)
End

Theorem env_rel_def = cj 2 v_rel_cases;

Definition env_ok_def:
  env_ok env ⇔
    nsLookup env.v (Short "ffi_array") = SOME (semanticPrimitives$Loc 0) ∧
    nsLookup env.c (Short "::") = SOME (2, TypeStamp "::" 1) ∧
    nsLookup env.c (Short "[]") = SOME (0, TypeStamp "[]" 1)
End

Definition state_ok_def:
  state_ok st ⇔
    ∃ws. store_lookup 0 st = SOME $ W8array ws ∧ LENGTH ws = max_FFI_return_size
End

Definition list_to_cont_def:
  list_to_cont env [] = [] ∧
  list_to_cont env (e::es) =
    (Ccon (SOME $ Short "::") [] [e], env) :: (list_to_cont env es)
End

Inductive cont_rel:
[~TupleK:]
  (LIST_REL (v_rel cnenv) svs cvs ∧
   LIST_REL (compile_rel cnenv) ses ces ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (Cons "") svs ses :: sk)
                     ((Ccon NONE cvs ces, cenv) :: ck)) ∧

[~ConsK:]
  (LIST_REL (v_rel cnenv) svs cvs ∧
   LIST_REL (compile_rel cnenv) ses ces ∧
   ALOOKUP cnenv cn = SOME (tyid,ar) ∧
   ar = LENGTH ses ∧ cn ≠ "" ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (Cons cn) svs ses :: sk)
                     ((Ccon (SOME $ Short cn) cvs ces, cenv) :: ck)) ∧

[~AppK:]
  (op_rel sop cop ∧
   LIST_REL (v_rel cnenv) svs cvs ∧
   LIST_REL (compile_rel cnenv) ses ces ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv sop svs ses :: sk)
                     ((Capp cop cvs ces, cenv) :: ck)) ∧

[~Divide1:]
  (compile_rel cnenv se1 ce1 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Div) [] [se1] :: sk)
                     ((Clet (SOME "v2") (clet "v1" ce1 div), cenv) :: ck)) ∧

[~Divide2:]
  (nsLookup cenv.v (Short "v2") = SOME cv2 ∧ v_rel cnenv sv2 cv2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Div) [sv2] [] :: sk)
                     ((Clet (SOME "v1") div, cenv) :: ck)) ∧

[~Modulo1:]
  (compile_rel cnenv se1 ce1 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Mod) [] [se1] :: sk)
                     ((Clet (SOME "v2") (clet "v1" ce1 mod), cenv) :: ck)) ∧

[~Modulo2:]
  (nsLookup cenv.v (Short "v2") = SOME cv2 ∧ v_rel cnenv sv2 cv2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Mod) [sv2] [] :: sk)
                     ((Clet (SOME "v1") mod, cenv) :: ck)) ∧

[~Concat:]
  (LIST_REL (compile_rel cnenv) ses ces ∧
   LIST_REL (v_rel cnenv) svs cvs ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
  ⇒ cont_rel cnenv
    (AppK senv (AtomOp Concat) svs ses :: sk)
    ((Ccon (SOME $ Short "::") [list_to_v cvs] [], cenv)
        :: list_to_cont cenv ces ++ ck)) ∧

[~Implode:]
  (LIST_REL (compile_rel cnenv) ses ces ∧
   LIST_REL (v_rel cnenv) svs cvs ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
  ⇒ cont_rel cnenv
    (AppK senv (AtomOp Implode) svs ses :: sk)
    ((Ccon (SOME $ Short "::") [list_to_v cvs] [], cenv)
        :: list_to_cont cenv ces ++ ck)) ∧

[~Substring2_1:]
  (compile_rel cnenv se1 ce1 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Substring) [] [se1] :: sk)
                     ((Clet (SOME "i") (clet "s" ce1 substring2), cenv) :: ck)) ∧

[~Substring2_2:]
  (nsLookup cenv.v (Short "i") = SOME cv2 ∧ v_rel cnenv sv2 cv2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Substring) [sv2] [] :: sk)
                     ((Clet (SOME "s") substring2, cenv) :: ck)) ∧

[~Substring3_1:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Substring) [] [se2;se1] :: sk)
        ((Clet (SOME "l") (clet "i" ce2 $ clet "s" ce1 substring3), cenv) :: ck)) ∧

[~Substring3_2:]
  (nsLookup cenv.v (Short "l") = SOME cv3 ∧
   v_rel cnenv sv3 cv3 ∧ compile_rel cnenv se1 ce1 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Substring) [sv3] [se1] :: sk)
                     ((Clet (SOME "i") (clet "s" ce1 substring3), cenv) :: ck)) ∧

[~Substring3_3:]
  (nsLookup cenv.v (Short "l") = SOME cv3 ∧ nsLookup cenv.v (Short "i") = SOME cv2 ∧
   v_rel cnenv sv3 cv3 ∧ v_rel cnenv sv2 cv2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Substring) [sv2;sv3] [] :: sk)
                      ((Clet (SOME "s") substring3, cenv) :: ck)) ∧

(* TODO
[~StrLt:]
[~StrLeq:]
[~StrGt:]
[~StrGeq:]
*)

[~FFI:]
  (cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (FFI ch) [] [] :: sk)
                     ((Clet (SOME "s") (ffi ch), cenv) :: ck)) ∧

[~LetK:]
  (compile_rel cnenv se ce ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (LetK senv (SOME x) se :: sk)
                     ((Clet (SOME $ var_prefix x) ce, cenv) :: ck)) ∧

[~IfK:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (IfK senv se1 se2 :: sk)
                     ((Cif ce1 ce2, cenv) :: ck)) ∧

[~CaseK:]
  (EVERY (λ(cn,vs,_). ALOOKUP cnenv cn = SOME (tyid, LENGTH vs)) scss ∧
   LIST_REL (λ(cn,vs,se) (pat,ce). compile_rel cnenv se ce ∧
      pat = Pas ((if cn = "" then Pcon NONE else Pcon (SOME $ Short cn))
                  (MAP (Pvar o var_prefix) vs)) (var_prefix sv)) scss ccss ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (CaseK senv sv scss :: sk)
                     ((Cmat ccss bind_exn_v, cenv) :: ck)) ∧

[~RaiseK:]
  (cont_rel cnenv sk ck
    ⇒ cont_rel cnenv (RaiseK :: sk) ((Craise, cenv) :: ck)) ∧

[~HandleK:]
  (compile_rel cnenv se ce ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (HandleK senv x se :: sk)
                     ((Chandle [(Pvar $ var_prefix x, ce)], cenv) :: ck))
End


(**********)

val _ = export_theory ();
