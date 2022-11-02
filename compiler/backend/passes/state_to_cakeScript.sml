(*
  Compiler from stateLang to CakeML
 *)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     rich_listTheory arithmeticTheory;
open semanticPrimitivesTheory;
open pure_miscTheory pure_configTheory pure_typingTheory state_cexpTheory;

val _ = new_theory "state_to_cake";

val _ = set_grammar_ancestry ["pure_typing", "state_cexp", "semanticPrimitives"]


(********** Primitives operation implementations **********)

Overload capp = ``λce1 ce2. ast$App Opapp [ce1; ce2]``;
Overload int  = ``λi. ast$Lit $ IntLit i``;
Overload clet = ``λs e1 e2. ast$Let (SOME s) e1 e2``;
Overload ifeq = ``λ(a,b) e1 e2. ast$If (App Equality [a;b]) e1 e2``;
Overload iflt = ``λ(a,b) e1 e2. ast$If (App (Opb Lt) [a;b]) e1 e2``
Overload var  = ``λs. ast$Var $ Short s``;
Overload tt = ``Con (SOME $ Short $ "True") []``;
Overload ff = ``Con (SOME $ Short $ "False") []``;

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
  if v2 < 0 then -1 else
  let strlen = LENGTH v1 in
    if v2 < strlen then Ord (Strsub v1 v2) else -1
*)
Overload elem_str =
  ``iflt (var "v2", int 0) (int (-1)) $
    clet "strlen" (App Strlen [var "v1"]) $
    iflt (var "v2", var "strlen")
      (App Ord [App Strsub [var "v1"; var "v2"]])
      (int (-1))``

(*
  letrec char_list l =
  case l of
  | []   => []
  | h::t => CHR (h % 256) :: char_list t
*)
Definition char_list_exp_def:
  char_list_exp = [
    "char_list", "l",
      Mat (var "l") [
        (Pcon (SOME (Short "[]")) [], Con (SOME (Short "[]")) []);
        (Pcon (SOME (Short "::")) [Pvar "h"; Pvar "t"],
          Con (SOME (Short "::")) [
            App Chr [App (Opn Modulo) [var "h"; int 256]];
            (capp (var "char_list") (var "t")) ])
        ]
    ]
End

(*
  let strlen = LENGTH v1 in
  let off = if v2 < 0 then 0 else v2 in
  if off < strlen then
    CopyStrStr v1 off (strlen - off)
    else ""
*)
Overload substring2 =
  ``clet "strlen" (App Strlen [var "v1"]) $
    clet "off" (iflt (var "v2", int 0) (int 0) (var "v2")) $
    iflt (var "off", var "strlen")
      (App CopyStrStr [var "v1"; var "off"; App (Opn Minus) [var "strlen"; var "off"]])
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
      clet "end" (iflt (var "off_l", var "strlen") (var "off_l") (var "strlen")) $
      App CopyStrStr [var "s"; var "off"; App (Opn Minus) [var "end"; var "off"]])
      (Lit $ StrLit "")``;

Definition strle_def:
  strle (n : num) s1 s2 len1 len2 =
    if len1 ≤ n then T else if len2 ≤ n then F else
    let o1 = ORD (EL n s1); o2 = ORD (EL n s2) in
    if o1 < o2 then T
    else if o1 = o2 then strle (n + 1) s1 s2 len1 len2
    else F
Termination
  WF_REL_TAC `measure (λ(n,_,_,len1,_). len1 - n)`
End

Definition strle_exp_def:
  strle_exp = [
    "strle", "n",
      Fun "s1" $ Fun "s2" $ Fun "len1" $ Fun "len2" $
      If (App (Opb Leq) [var "len1"; var "n"]) tt $
      If (App (Opb Leq) [var "len2"; var "n"]) ff $
      clet "o1" (App Ord [App Strsub [var "s1"; var "n"]]) $
      clet "o2" (ast$App Ord [App Strsub [var "s2"; var "n"]]) $
      iflt (var "o1", var "o2") tt $
      ifeq (var "o1", var "o2")
        (capp (capp (capp (capp (capp (var "strle") (App (Opn Plus) [var "n"; int 1]))
          (var "s1")) (var "s2")) (var "len1")) (var "len2"))

        ff]
End

(* strle 0 v1 v2 *)
Overload strleq =
  ``clet "len1" (App Strlen [var "v1"]) $ clet "len2" (App Strlen [var "v2"]) $
    capp (capp (capp (capp (capp (var "strle") (int 0))
      (var "v1")) (var "v2")) (var "len1")) (var "len2")``;

(* if v1 = v2 then F else strleq v1 v2 *)
Overload strlt = ``ifeq (var "v1", var "v2") ff strleq``;

(* if strleq v1 v2 then F else T *)
Overload strgt = ``If strleq ff tt``;

(* strle 0 v2 v1 *)
Overload strgeq =
  ``clet "len1" (App Strlen [var "v1"]) $ clet "len2" (App Strlen [var "v2"]) $
    capp (capp (capp (capp (capp (var "strle") (int 0))
      (var "v2")) (var "v1")) (var "len2")) (var "len1")``;

(*
  let len = (if v1 < 0 then 0 else v1) in Aalloc v1 v2
*)
Overload alloc =
  ``clet "len" (iflt (var "v1", int 0) (int 0) (var "v1")) $
    App Aalloc [var "len"; var "v2"]``;

(*
    let len0 = Int (ffi_array[0]) in
    let len1 = Int (ffi_array[1]) in
    let len = (len1 * 256) + len0 in
    let len = (if max_FFI_return_size < len then max_FFI_return_size else len) in
    CopyAw8Str ffi_array 2 len
*)
Overload ffi =
  ``clet "len0" (App (WordToInt W8) [(App Aw8sub_unsafe [var "ffi_array"; int 0])]) $
    clet "len1" (App (WordToInt W8) [(App Aw8sub_unsafe [var "ffi_array"; int 1])]) $
    clet "len" (App (Opn Plus) [App (Opn Times) [var "len1"; int 256]; var "len0"]) $
    clet "len" (
      iflt (int &max_FFI_return_size, var "len")
      (int &max_FFI_return_size) (var "len")) $
    App CopyAw8Str [var "ffi_array"; int 2; var "len"]``;


(********** Preamble **********)

Overload cunit = ``Attup []``;

Overload compile_exn =
  ``λcn tys:type list.
      Dexn unknown_loc (explode cn) (REPLICATE (LENGTH tys) cunit)``;

Overload compile_tdef =
  ``λcndefs. Dtype unknown_loc (* TODO type names? *)
      [([],"",
        MAP (λ(cn,tys:type list). (explode cn, MAP (K cunit) tys)) cndefs)]``;


Definition compile_exndef_def:
  compile_exndef ([] :exndef) = [] ∧
  compile_exndef ((cn, tys) :: exns) = compile_exn cn tys :: compile_exndef exns
End

Definition compile_typedefs_def:
  compile_typedefs ([] :typedefs) = [] ∧
  compile_typedefs ((ar, cndefs) :: tdefs) =
    compile_tdef cndefs :: compile_typedefs tdefs
End

Definition compile_namespace_def:
  compile_namespace ns =
    compile_exndef (FST ns) ++
    [Dlet unknown_loc Pany $ Con NONE []] ++ (* simplifies a proof considerably *)
    compile_typedefs (SND ns)
End

Definition preamble_def:
  preamble ns =
    compile_namespace ns ++
    [
      Dlet unknown_loc (Pvar "ffi_array")
        (App Aw8alloc [Lit (IntLit (&max_FFI_return_size + 2)); Lit (Word8 0w)]);
      Dletrec unknown_loc strle_exp;
      Dletrec unknown_loc char_list_exp;
    ]
End


(********** Helper functions **********)

(* right to left evaluation holds for this too *)
Definition list_to_exp_def:
  list_to_exp [] = Con (SOME $ Short "[]") [] ∧
  list_to_exp (e::es) = Con (SOME $ Short "::") [e; list_to_exp es]
End

Definition failure_def:
  failure = Mat (Con NONE []) [] : ast$exp
End

Definition cexp_var_prefix_def:
  cexp_var_prefix cv = explode $ strcat (strlit "pure_") cv
End

Definition cexp_pat_row_def:
  cexp_pat_row cn vs =
    (if cn = strlit "" then Pcon NONE else Pcon (SOME $ Short $ explode cn))
      (MAP (Pvar o cexp_var_prefix) vs)
End


(********** Compilation functions **********)

Datatype:
  compile_op = CakeOp ast$op | TwoArgs ast$exp | Other
End

Definition compile_atomop_def:
  compile_atomop Add       = CakeOp $ Opn Plus ∧
  compile_atomop Sub       = CakeOp $ Opn Minus ∧
  compile_atomop Mul       = CakeOp $ Opn Times ∧
  compile_atomop Lt        = CakeOp $ Opb Lt ∧
  compile_atomop Leq       = CakeOp $ Opb Leq ∧
  compile_atomop Gt        = CakeOp $ Opb Gt ∧
  compile_atomop Geq       = CakeOp $ Opb Geq ∧
  compile_atomop Eq        = CakeOp $ Equality ∧
  compile_atomop Len       = CakeOp $ Strlen ∧
  compile_atomop StrEq     = CakeOp $ Equality ∧

  compile_atomop Div       = TwoArgs div ∧
  compile_atomop Mod       = TwoArgs mod ∧
  compile_atomop Elem      = TwoArgs elem_str ∧
  compile_atomop StrLeq    = TwoArgs strleq ∧
  compile_atomop StrLt     = TwoArgs strlt ∧
  compile_atomop StrGeq    = TwoArgs strgeq ∧
  compile_atomop StrGt     = TwoArgs strgt ∧

  compile_atomop _         = Other
End

Definition compile_op_def:
  compile_op (AppOp : csop) = CakeOp Opapp ∧
  compile_op (AtomOp aop)   = compile_atomop aop ∧
  compile_op Ref            = CakeOp AallocFixed ∧
  compile_op Length         = CakeOp Alength ∧
  compile_op Sub            = CakeOp Asub ∧
  compile_op UnsafeSub      = CakeOp Asub_unsafe ∧
  compile_op Update         = CakeOp Aupdate ∧
  compile_op UnsafeUpdate   = CakeOp Aupdate_unsafe ∧
  compile_op Alloc          = TwoArgs alloc ∧
  compile_op _              = Other
End

Definition compile_def:
  compile (Var v : cexp) = Var (Short (cexp_var_prefix v)) ∧

  compile (App op es) = (
    let ces = MAP compile es in
    case compile_op op of
    | CakeOp cop => App cop ces
    | TwoArgs impl => (
        case (oEL 0 ces, oEL 1 ces) of
        | SOME ce1, SOME ce2 => clet "v2" ce2 $ clet "v1" ce1 $ impl
        | _ => failure)
    | Other =>
        case op of
        | AtomOp (Lit (Int i)) => Lit (IntLit i)
        | AtomOp (Lit (Str s)) => Lit (StrLit s)
        | AtomOp Concat => App Strcat [list_to_exp ces]
        | AtomOp Implode => App Implode [capp (var "char_list") (list_to_exp ces)]
        | AtomOp Substring => (
            case (oEL 0 ces, oEL 1 ces, oEL 2 ces) of
            | SOME ce1, SOME ce2, SOME ce3 =>
                clet "l" ce3 $ clet "i" ce2 $ clet "s" ce1 $ substring3
            | SOME ce1, SOME ce2, NONE =>
                clet "v2" ce2 $ clet "v1" ce1 $ substring2
            | _ => failure)
        | Cons cn => (if cn = «»
                      then Con NONE ces
                      else Con (SOME $ Short $ explode cn) ces)
        | FFI ch  => (
            case oEL 0 ces of
            | SOME ce =>
                clet "s" ce $ Let NONE
                  (App (FFI $ explode ch) [var "s"; var "ffi_array"]) $ ffi
            | NONE => failure)
        | _ => failure) ∧

  compile (Lam (SOME x) e) = Fun (cexp_var_prefix x) (compile e) ∧

  compile (Letrec funs e) = (
    let cfuns =
      MAP (λ(v,x,e). cexp_var_prefix v, cexp_var_prefix x, compile e) funs in
    Letrec cfuns (compile e)) ∧

  compile (Let (SOME x) e1 e2) =
    Let (SOME $ cexp_var_prefix x) (compile e1) (compile e2) ∧

  compile (If e e1 e2) = If (compile e) (compile e1) (compile e2) ∧

  compile (Case v css d) = (
    let ccss = MAP (λ(cn,vs,e). cexp_pat_row cn vs, compile e) css in
    let d_case = (case d of NONE => [] | SOME (_,e) => [(Pany, compile e)]) in
    Mat (Var (Short (cexp_var_prefix v))) (ccss ++ d_case)) ∧

  compile (Raise e) = Raise (compile e) ∧

  compile (Handle e1 x e2) =
    Handle (compile e1) [(Pvar $ cexp_var_prefix x, compile e2)] ∧

  compile _ = failure
Termination
  WF_REL_TAC `measure cexp_size`
End

(* Remove initial built-in datatypes from ns *)
Definition compile_with_preamble_def:
  compile_with_preamble ns e =
    preamble ((TL ## TL) ns) ++ [Dlet unknown_loc (Pvar "prog") $ compile e]
End


(**********)

val _ = export_theory ();
