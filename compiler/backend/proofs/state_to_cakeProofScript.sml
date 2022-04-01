(*
  Correctness for compilation from stateLang to CakeML
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     rich_listTheory arithmeticTheory
open pure_miscTheory pure_configTheory stateLangTheory itree_semanticsTheory;

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


Overload capp = ``λce1 ce2. App Opapp [ce1; ce2]``;
Overload int  = ``λi. Lit $ IntLit i``;
Overload clet = ``λs e1 e2. Let (SOME s) e1 e2``;
Overload ifeq = ``λ(a,b) e1 e2. If (App Equality [a;b]) e1 e2``;
Overload iflt = ``λ(a,b) e1 e2. If (App (Opb Lt) [a;b]) e1 e2``
Overload var  = ``λs. Var $ Short s``;

(*
  λv2 v1. if v2 = 0 then 0 else Divide v1 v2
*)
Overload div =
  ``λce1 ce2. clet "v2" ce2 $ clet "v1" ce1 $
      ifeq (var "v2", int 0) (int 0) (App (Opn Divide) [var "v1"; var "v2"])``;

(*
  λv2 v1. if v2 = 0 then 0 else Modulo v1 v2
*)
Overload mod =
  ``λce1 ce2. clet "v2" ce2 $ clet "v1" ce1 $
      ifeq (var "v2", int 0) (int 0) (App (Opn Modulo) [var "v1"; var "v2"])``;

(*
  λs i.
    let strlen = LENGTH s in
    let off = if i < 0 then 0 else i in
    if off < strlen then
      CopyStrStr s off (strlen - off)
      else ""
*)
Overload substring2 =
  ``λce_str ce_int. clet "i" ce_int $ clet "s" ce_str $
      clet "strlen" (App Strlen [var "s"]) $
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
  ``λce_str ce_int ce_len. clet "l" ce_len $ clet "i" ce_int $ clet "s" ce_str $
      iflt (var "l", int 0) (Lit $ StrLit "") $
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
  ``λch ce. clet "s" ce $
      Let NONE (App (FFI ch) [var "s"; var "ffi_array"]) $
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
   ar = LENGTH ses
    ⇒ compile_rel cnenv (App (Cons cn) ses) (Con (SOME $ Short cn) ces)) ∧

[~Var:]
  compile_rel cnenv (stateLang$Var v) (Var (Short (var_prefix v))) ∧

[~App:]
  (op_rel sop cop ∧ LIST_REL (compile_rel cnenv) ses ces
    ⇒ compile_rel cnenv (App sop ses) (App cop ces)) ∧

[~Divide:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2
    ⇒ compile_rel cnenv (App (AtomOp Mod) [se1;se2]) (mod ce1 ce2)) ∧

[~Concat:]
  (LIST_REL (compile_rel cnenv) ses ces
    ⇒ compile_rel cnenv (App (AtomOp Concat) ses) (App Strcat (list_to_exp ces))) ∧

[~Implode:]
  (LIST_REL (compile_rel cnenv) ses ces
    ⇒ compile_rel cnenv (App (AtomOp Implode) ses) (App Implode (list_to_exp ces))) ∧

[~Substring2:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2
    ⇒ compile_rel cnenv (App (AtomOp Substring) [se1; se2]) (substring2 ce1 ce2)) ∧

[~Substring3:]
  (LIST_REL (compile_rel cnenv) [se1;se2;se3] [ce1;ce2;ce3]
    ⇒ compile_rel cnenv
        (App (AtomOp Substring) [se1; se2; se3]) (substring3 ce1 ce2 ce3)) ∧

(* TODO
[~StrLt:]
[~StrLeq:]
[~StrGt:]
[~StrGeq:]
*)

[~FFI:]
  (compile_rel cnenv se ce
    ⇒ compile_rel cnenv (App (FFI ch) [se]) (ffi ch ce)) ∧

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
  (var_prefix sv = cv ∧
   compile_rel cnenv se ce ∧
   EVERY (λ(cn,vs,_). ALOOKUP cnenv cn = SOME (tyid, LENGTH vs)) scss ∧
   LIST_REL (λ(cn,vs,se) (pat,ce). compile_rel cnenv se ce ∧
      pat = (if cn = "" then Pcon NONE else Pcon (SOME $ Short cn))
              (MAP (Pvar o var_prefix) vs))
      (scss : (string # string list # stateLang$exp) list)ccss
    ⇒ compile_rel cnenv (Case se sv scss)
      (Let (SOME cv) ce (Mat (Var $ Short cv) ccss))) ∧

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
   ar = LENGTH svs
    ⇒ v_rel cnenv (Constructor cn svs) (Conv (SOME tyid) cvs)) ∧

[~Closure:]
  (compile_rel cnenv se ce ∧
   var_prefix sx = cx ∧
   env_rel cnenv senv cenv
   ⇒ v_rel cnenv (Closure (SOME sx) senv se) (Closure cenv cv ce)) ∧

[~Recclosure:]
  (compile_rel cnenv se ce ∧
   var_prefix sx = cx ∧
   env_rel cnenv senv cenv ∧
   LIST_REL (λ(sv,se) (cv,cx,ce).
        var_prefix sv = cv ∧
        ∃sx se'. se = Lam (SOME sx) se' ∧ var_prefix sx = cx ∧ compile_rel cnenv se' ce)
      sfuns cfuns
   ⇒ v_rel cnenv (stateLang$Recclosure sfuns senv sx) (Recclosure cenv cfuns cv)) ∧

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

Definition venv_ok_def:
  venv_ok env ⇔ nsLookup env.v (Short "ffi_array") = SOME (Loc 0)
End

Definition state_ok_def:
  state_ok st ⇔
    ∃ws. store_lookup 0 st = SOME $ W8array ws ∧ LENGTH ws = max_FFI_return_size
End


(**********)

val _ = export_theory ();
