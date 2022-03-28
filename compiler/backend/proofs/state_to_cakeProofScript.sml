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
  opn_rel Mul Times ∧
  opn_rel Div Divide ∧
  opn_rel Mod Modulo
End

Inductive opb_rel:
  opb_rel pure_config$Lt ast$Lt ∧
  opb_rel Leq Leq ∧
  opb_rel Gt Gt ∧
  opb_rel Geq Geq
End

(* TODO check argument order *)
Inductive atom_op_rel:
  (opn_rel sopn opn ⇒ atom_op_rel sopn (Opn opn)) ∧
  (opb_rel sopb opb ⇒ atom_op_rel sopb (Opb opb)) ∧
  atom_op_rel Eq Equality ∧
  atom_op_rel Len StrLen ∧
  atom_op_rel Elem StrSub ∧
  atom_op_rel Concat ARB ∧ (* TODO *)
  atom_op_rel Implode Implode ∧
  atom_op_rel Substring ARB ∧ (* TODO *)
  atom_op_rel StrEq Equality ∧
  atom_op_rel StrLt ARB ∧ (* TODO *)
  atom_op_rel StrLeq ARB ∧ (* TODO *)
  atom_op_rel StrGt ARB ∧ (* TODO *)
  atom_op_rel StrGeq ARB (* TODO *)
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
  op_rel UnsafeUpdate Aupdate_unsafe ∧
  op_rel (FFI s) (FFI s)
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


(**********)

val _ = export_theory ();
